Require Import SGA.Notations.
Require SGA.Primitives.

Require Import Coq.Strings.String.
Open Scope string_scope.

Definition readRegisters {reg_t fn_t: Type} (R: reg_t -> type) (Sigma: fn_t -> ExternalSignature)
  : forall idx: reg_t, circuit R Sigma (R idx) :=
  fun idx => CReadRegister (R := R) (Sigma := Sigma) idx.

Module Ex1.
  Notation var_t := string.
  Inductive reg_t := R0 | R1.
  Inductive fn_t := Even | Odd.

  Definition R reg : type :=
    match reg with
    | R0 => bits_t 3
    | R1 => bits_t 1
    end.

  Definition Sigma fn : ExternalSignature :=
    match fn with
    | Even => {{ 3 ~> 0 ~> 1}}
    | Odd => {{ 3 ~> 0 ~> 1}}
    end.

  Definition uSigma (fn: fn_t) (_ _: type) : fn_t := fn.

  Definition r idx : R idx :=
    match idx with
    | R0 => Ob~1~0~1
    | R1 => Ob~0
    end.

  Definition sigma idx : Sigma idx :=
    match idx with
    | Even => fun (bs: bits 3) _ => w1 (negb (Bits.lsb bs))
    | Odd => fun (bs: bits 3) _ => w1 (Bits.lsb bs)
    end.

  Example r1 : urule unit var_t reg_t fn_t :=
    (UBind "x" (URead P0 R0)
           (UIf (UCall Even (UVar "x") (UConst Ob))
                (UWrite P0 R1 (UConst Ob~1))
                (UWrite P0 R1 (UConst Ob~1)))).

  Example s1 : uscheduler unit var_t reg_t fn_t :=
    UTry r1 UDone UDone.

  Definition s1_result :=
    Eval compute in interp_scheduler (ContextEnv.(create) r) sigma (tc R Sigma uSigma s1).
  Definition s1_circuit :=
    compile_scheduler (ContextEnv.(create) (readRegisters R Sigma)) (tc R Sigma uSigma s1).
End Ex1.

Module Ex2.
  Definition var_t := string.
  Inductive reg_t := R0 | R1 | R2.
  Inductive ufn_t := UOr | UNot.
  Inductive fn_t := Or (n: nat) | Not (n: nat).

  Definition R r :=
    match r with
    | R0 => bits_t 7
    | R1 => bits_t 7
    | R2 => bits_t 1
    end.

  Definition Sigma fn :=
    match fn with
    | Or n => {{ n ~> n ~> n }}
    | Not n => {{ n ~> 0 ~> n }}
    end.

  Definition uSigma fn (tau1 _: type) :=
    match fn, tau1 with
    | UOr, (bits_t n) => Or n
    | UNot, (bits_t n) => Not n
    end.

  Example negate : urule unit var_t reg_t ufn_t  :=
    UBind "x" (URead P1 R0)
          (UWrite P1 R0 (UVar "x")).

  Example swap_or_replace : urule unit var_t reg_t ufn_t  :=
    UBind "should_swap" (URead P0 R2)
          (UIf (UVar "should_swap")
               (USeq (UWrite P0 R1 (URead P0 R0))
                     (UWrite P0 R0 (URead P0 R1)))
               (UWrite P0 R0 (UCall UOr
                                    (URead P0 R0)
                                    (URead P0 R1)))).

  Example ill_typed_write : urule unit var_t reg_t ufn_t  :=
    UWrite P0 R2 (URead P0 R1).

  Example unbound_variable : urule unit var_t reg_t ufn_t  :=
    UWrite P0 R0 (UVar "y").

  Example sched :=
    UTry swap_or_replace (UTry negate UDone UDone) (UTry negate UDone UDone).

  Example tsched : scheduler var_t R Sigma :=
    tc R Sigma uSigma sched.

  Fail Example tsched : scheduler var_t R Sigma :=
    tc R Sigma uSigma (UTry ill_typed_write UDone UDone).

  Fail Example tsched : scheduler var_t R Sigma :=
    tc R Sigma uSigma (UTry unbound_variable UDone UDone).

  Definition r idx : R idx :=
    match idx with
    | R0 => Ob~0~1~1~0~0~1~0
    | R1 => Ob~1~1~0~0~1~1~0
    | R2 => Ob~1
    end.

  Definition sigma idx : Sigma idx :=
    match idx with
    | Or n => fun bs1 bs2 => Bits.map2 orb bs1 bs2
    | Not n => fun bs _ => Bits.map negb bs
    end.

  Definition tsched_result :=
    Eval compute in interp_scheduler (ContextEnv.(create) r) sigma tsched.
  Definition tsched_circuit :=
    compile_scheduler (ContextEnv.(create) (readRegisters R Sigma)) tsched.
End Ex2.

Module Collatz.
  Definition var_t := string.
  Inductive reg_t := R0.
  Inductive custom_t := .
  Definition ufn_t := interop_ufn_t custom_t.
  Definition fn_t := interop_fn_t custom_t.

  Definition logsz := 5.
  Notation sz := (pow2 logsz).

  Definition R r :=
    match r with
    | R0 => bits_t sz
    end.

  Definition Sigma (fn: custom_t) : ExternalSignature :=
    match fn with
    end.

  Definition uSigma (fn: custom_t) (_ _: type) : custom_t :=
    match fn with
    end.

  Definition r idx : R idx :=
    match idx with
    | R0 => Ob~0~1~0~1~0~1~1~1~1~0~0~0~1~1~0~0~0~0~1~0~1~0~1~1~1~1~0~0~0~1~1~0
    end.

  (* TODO bug report *)
  (* Notation "!!!!" := ltac:(exact (true, false, tt)). *)
  (* Compute match (true, true, tt) with *)
  (*         | !!!! => 1 *)
  (*         end. *)

  Definition sigma idx : Sigma idx :=
    match idx with
    end.

  Open Scope sga.

  Definition divide_collatz : urule unit var_t reg_t ufn_t :=
    Let "v" <- R0#read0 in
    Let "odd" <- USel[[$"v", UConst (Bits.zero logsz)]] in
    If UNot[[$"odd"]] Then
       R0#write0(ULsr[[$"v", UConst Ob~1]])
    Else
      fail
    EndIf.

  Definition TimesThree (ex: uexpr unit var_t reg_t ufn_t) :=
    UUIntPlus[[ULsl[[ex, UConst Ob~1]], ex]]%sga_expr.

  Definition multiply_collatz : urule unit var_t reg_t ufn_t :=
    Let "v" <- R0#read1 in
    Let "odd" <- USel[[$"v", UConst (Bits.zero logsz)]] in
    If $"odd" Then
       R0#write1(UUIntPlus[[TimesThree ($"v"),
                            UConst (Bits.one sz)]])
    Else
       fail
    EndIf.

(* Bug report *)
(* Require Import Coq.extraction.Extraction. *)
(* (* Extraction Language JSON. *) *)
(* Set Extraction KeepSingleton. *)
(* Extraction Collatz.reg_t. *)

  Definition iSigma := interop_Sigma Sigma.
  Definition iuSigma := interop_uSigma uSigma.
  Definition isigma := interop_sigma sigma.
  Definition cr := ContextEnv.(create) r.

  Definition collatz : scheduler _ _ _ :=
    tc R iSigma iuSigma (divide_collatz |> multiply_collatz |> done).

  Notation compute t :=
    ltac:(let tt := type of t in
          let t := (eval lazy in t) in
          exact (t: tt)) (only parsing).

  Definition result :=
    compute (interp_scheduler cr isigma collatz).
  Definition divide_result :=
    compute (interp_rule cr isigma CtxEmpty log_empty log_empty
                         (tc R iSigma iuSigma divide_collatz)).
  Definition multiply_result :=
    compute (interp_rule cr isigma CtxEmpty log_empty log_empty
                         (tc R iSigma iuSigma multiply_collatz)).

  Definition circuit :=
    compile_scheduler (ContextEnv.(create) (readRegisters R iSigma)) collatz.

  Definition package :=
    {| vp_reg_t := reg_t;
       vp_reg_types := R;
       vp_reg_init := r;
       vp_reg_finite := _;
       vp_reg_Env := ContextEnv;

       vp_custom_fn_t := custom_t;
       vp_custom_fn_types := Sigma;

       vp_reg_names r := match r with
                        | R0 => "R0"
                        end;
       vp_custom_fn_names fn := match fn with
                               end;

       vp_circuit := circuit;
    |}.
End Collatz.
