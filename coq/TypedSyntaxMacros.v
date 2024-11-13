(*! Tools | Functions defined on typed ASTs !*)
Require Export Koika.Member Koika.TypedSyntax.
Require Import Koika.Primitives Koika.TypedSemantics.
Import Specif.SigTNotations.
Import PrimTyped.
From Coq Require BinaryString OctalString HexString HexadecimalString DecimalString.
Require Import Ascii.

Section TypedSyntaxMacros.
  Context {pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t: Type}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  Notation action := (action pos_t var_t fn_name_t).
  Notation InternalFunction R Sigma sig tau := (InternalFunction pos_t var_t fn_name_t R Sigma sig tau).

  (* filter a single char out of a string *)
  Local Fixpoint filters' (s : string) (a : ascii) : string :=
    match s with
    | EmptyString => EmptyString
    | String c s' => if ascii_dec c a
      then filters' s' a
      else String c (filters' s' a)
    end.
  (* filter a set of chars out of a string *)
  Fixpoint filter_string (s : string) (l : list ascii) : string :=
    match l with
    | a :: l' => filter_string (filters' s a) l'
    | [] => s
    end.
  (* Coq's implementation just silently returns 0 on an invalid string -
    for better error recognition these methods are redefined here returning option *)
  Local Fixpoint num_string_to_option_N' (s : string) (base : N) (convert : Ascii.ascii -> option N) (remainder : option N) : option N :=
    match s with
    | EmptyString => remainder
    | String c s' => num_string_to_option_N' s' base convert
      (match remainder, convert c with
      | Some rem, Some c_v => Some (N.add (N.mul base rem) c_v)
      | _, _ => None
      end)
    end.
  Local Definition num_string_to_option_N (s : string) (base : N) (convert : Ascii.ascii -> option N) : option N :=
    match s with
    | EmptyString => None
    | String _ _ => num_string_to_option_N' s base convert (Some 0%N)
    end.

  Definition bin_string_to_N s := (must (num_string_to_option_N s 2 BinaryString.ascii_to_digit)).
  Definition oct_string_to_N s := (must (num_string_to_option_N s 8 OctalString.ascii_to_digit)).
  Definition dec_string_to_N s := (must (option_map N.of_uint (DecimalString.NilZero.uint_of_string s))).
  Definition hex_string_to_N s := (must (num_string_to_option_N s 16 HexString.ascii_to_digit)).

  (* A koika action which build a struct instance filled 
  with zeroes *)
  Definition struct_init_zeros {sig} (tau: type) : action R Sigma sig tau :=
    Unop (Conv tau Unpack) (Const (tau := bits_t _) (Bits.zeroes (type_sz tau))).

  (* Transforming a list of actions into a sequence of
  substitute operations to initialize a struct *)
  Fixpoint struct_init
    {sig} (s_sig: struct_sig)
    (fields: list {idx : struct_index s_sig & action R Sigma sig (field_type s_sig idx)})
    : action R Sigma sig _ :=
    match fields with
    | (idx; act) :: fields' =>
      Binop (Struct2 SubstField s_sig idx) (struct_init s_sig fields') act
    | [] => struct_init_zeros (struct_t s_sig)
    end.

  (* The struct's signature needs to be known to check if a given field exists within
  the struct and to compute its index.

  This signature is inferred by the typechecker when the notation is used. This typeclass
  makes sure that the index computation is deferred and only executed after the signature
  is known *)
  Class FieldSubst {tau sig} {s_sig : struct_sig} (field : string) (a : action R Sigma sig tau) :=
    field_subst : {idx : struct_index s_sig & action R Sigma sig (field_type s_sig idx)}.
  Hint Mode FieldSubst + + + + +  : typeclass_instances.

  Fixpoint struct_init_constr
    (sig: struct_sig) (fields: list {idx : struct_index sig & field_type sig idx})
    : struct_t sig :=
    match fields with
    | (idx; val) :: fields' =>
      BitFuns.subst_field sig.(struct_fields) (struct_init_constr sig fields') idx val
    | [] => value_of_bits Bits.zero
    end.

  Class FieldSubstConstr {T} {sig : struct_sig} (field : string) (val : T) :=
    field_subst_constr : {idx : struct_index sig & field_type sig idx}.
  Hint Mode FieldSubstConstr + + + + : typeclass_instances.

  Class StructIdx sig (f : string) := struct_idx : struct_index sig.

  Section Switch.
    Notation action := (action R Sigma).

    Fixpoint switch {vtau} {sig tau}
      (var: action sig vtau)
      (default: action sig tau)
      (branches: list (action sig vtau * action sig tau)) : action sig tau :=
      match branches with
      | nil => default
      | (label, action) :: branches =>
        If (Binop (Eq _ false) var label)
          action (switch var default branches)
      end.
  End Switch.

  Section Lift.
    Context {reg_t' ext_fn_t': Type}.
    Context {R': reg_t' -> type}.
    Context {Sigma': ext_fn_t' -> ExternalSignature}.

    Class LiftFn {A A' B} (fA: A -> B) (fA': A' -> B) := lift_fn_of {
      lift_fn: A' -> A;
      lift_comm: fA' = (fun a' => fA (lift_fn a'));
    }.
    Context (lR: LiftFn R R')
            (lSigma: LiftFn Sigma Sigma').

    (*
     * Assume you have a function in a Modul:
     * ```
     * Inductive reg_t := reg1.
     * Definition R (r : reg_t) := bits_t 2.
     * Definition func : function R empty_Sigma := <{
     *   fun f () : bits_t 2 =>
     *     read0(reg1)
     * }>.
     * ```
     *
     * This function is typed using the [R] and [Sigma]
     * of the modul. However, to call this function in
     * a composition of modules it needs to be typed with
     * the [super_R] and (possibly) [super_Sigma] of this
     * larger module. (See TypedSyntax.v [InternalCall] -
     * `body` has the same R/Sigma as the retuned type)
     *
     * This function will lift a given action [act]
     *)
    Fixpoint lift
             {sig tau}
             (a: action R' Sigma' sig tau)
      : action R Sigma sig tau := 
      match a with
      | Fail tau => Fail tau
      | Var vr => Var vr
      | Const cst => Const cst
      | Assign vr ex => Assign vr (lift ex)
      | Seq a1 a2 => Seq (lift a1) (lift a2)
      | Bind var ex body => Bind var (lift ex) (lift body)
      | If cond tbranch fbranch => If (lift cond) (lift tbranch) (lift fbranch)
      | Read port idx => rew <- [fun e => _ (e idx)] lR.(lift_comm) in
        Read port (lR.(lift_fn) idx)
      | Write port idx value =>
        Write port (lR.(lift_fn) idx) (lift (rew [fun e => _ (e idx)] lR.(lift_comm) in value))
      | Unop fn arg1 => Unop fn (lift arg1)
      | Binop fn arg1 arg2 => Binop fn (lift arg1) (lift arg2)
      | ExternalCall fn arg =>
        rew <- [fun e => _ (retSig (e fn))] lSigma.(lift_comm) in
        ExternalCall (lift_fn fn)
          (rew [fun e => _ (arg1Sig (e fn))] lSigma.(lift_comm) in lift arg)
      | InternalCall fn args =>
        InternalCall {| int_name := fn.(int_name); int_body := lift fn.(int_body) |}
          (cmapv (fun _ => lift) args)
      | APos pos a => APos pos (lift a)
      end.

    Context {REnv: Env reg_t}.
    Context {REnv': Env reg_t'}.

    (* Definition unlift_REnv
               (f: type -> Type)
               (env: REnv.(env_t) (fun x => f (R x)))
    : REnv'.(env_t) (fun x => f (R' x)).
      set (idk := REnv'.(create) (fun reg: reg_t' => REnv.(getenv) env (lR.(lift_fn) reg))).
      simpl in idk.H
      rewrite <- lR.(lift_comm) in idk.
      (* rew lR.(lift_comm) _ in *)rew lR.(lift_comm) _ in
        REnv'.(create) (fun reg: reg_t' => REnv.(getenv) env (lR.(lift_fn) reg)).

    Definition unlift_sigma
               (sigma: forall f, Sig_denote (Sigma f))
      : forall f, Sig_denote (Sigma' f) :=
      rew <- [fun Sigma' => forall f, Sig_denote (Sigma' f)] lSigma.(lift_ok).(lift_comm) in
        (fun f => sigma (lSigma.(lift_fn) f)).

    Definition lift_REnv
               (f: type -> Type)
               (env: REnv.(env_t) (fun x => f (R x)))
               (env': REnv'.(env_t) (fun x => f (R' x)))
      : REnv.(env_t) (fun x => f (R x)) :=
      Environments.fold_right
        REnv'
        (fun k v acc =>
           (REnv.(putenv))
             acc (lR.(lift_fn) k)
             (rew [fun R' => f (R' k)] lR.(lift_ok).(lift_comm) in v))
        env' env.

    Context (r: REnv.(env_t) R).
    Context (sigma: forall f, Sig_denote (Sigma f)). *)

    (* Lemma lift_unlift_REnv (f: type -> Type):
      forall l, lift_REnv f l (unlift_REnv f l) = l.
    Proof.
      unfold lift_REnv, unlift_REnv, Environments.fold_right.
      induction finite_elements; cbn.
      - reflexivity.
      - intros.
        rewrite IHl. apply put_get_eq.
        unfold eq_rect_r.
        rewrite getenv_rew'.
        rewrite getenv_create.
        rewrite rew_compose.
        apply __magic__.
    Qed. *)

    (* Lemma unlift_lift_REnv (f: type -> Type):
      forall ev ev0, unlift_REnv f (lift_REnv f ev0 ev) = ev.
    Proof.
      unfold lift_REnv, unlift_REnv, Environments.fold_right.
      intros.
      apply equiv_eq; intros k.
      unfold eq_rect_r; rewrite getenv_rew', getenv_create.
      (* LR k is in the list, so must be hit, and by injectivity it's not replaced *)
        apply __magic__.
    Qed. *)

    (* Lemma getenv_unlift_REnv (f: type -> Type) :
      forall ev k,
        REnv'.(getenv) (unlift_REnv f ev) k =
        rew <- [fun R' => f (R' k)] lR.(lift_ok).(lift_comm) in
          REnv.(getenv) ev (lift_fn lR k).
    Proof.
      unfold unlift_REnv; intros.
      unfold eq_rect_r.
Instance LiftId {A B} {fn : A -> B} : @LiftFn A A B fn fn := {|
  lift_fn := id;
  lift_comm := eq_refl;
|}.
      rewrite getenv_rew'.
      rewrite getenv_create; reflexivity.
    Qed. *)

    (* Lemma getenv_lift_REnv_lifted (f: type -> Type) :
      forall ev ev0 k',
        REnv.(getenv) (lift_REnv f ev0 ev) (lift_fn lR k') =
        rew [fun R' => f (R' k')] lR.(lift_ok).(lift_comm) in
          REnv'.(getenv) ev k'.
    Proof.
      apply __magic__.
    Qed. *)

    (* Lemma getenv_lift_REnv_unlifted (f: type -> Type) :
      forall ev ev0 k,
        (forall k', lift_fn lR k' <> k) ->
        REnv.(getenv) (lift_REnv f ev0 ev) k =
        REnv.(getenv) ev0 k.
    Proof.
      apply __magic__.
    Qed. *)
  End Lift.
End TypedSyntaxMacros.

Instance LiftId {A B} {fn : A -> B} : @LiftFn A A B fn fn := {|
  lift_fn := id;
  lift_comm := eq_refl;
|}.

#[export] Hint Extern 1 (@FieldSubst _ _ _ _ _ _ _ _ _ ?sig ?field   ?a) => exact (must (List_assoc field sig.(struct_fields));   a) : typeclass_instances.
#[export] Hint Extern 1 (@FieldSubstConstr _           ?sig ?field ?val) => exact (must (List_assoc field sig.(struct_fields)); val) : typeclass_instances.
Arguments field_subst {pos_t var_t fn_name_t reg_t ext_fn_t} {R Sigma}
  {tau sig} {s_sig} field a {FieldSubst} : assert.
Arguments field_subst_constr {T} {sig} field val {FieldSubstConstr}.
Arguments lift_fn_of {A A' B} {fA fA'} lift_fn lift_comm : assert.


#[export] Instance struct_idx_hd {f t sig nm}:
  StructIdx {| struct_name := nm; struct_fields := (f,t) :: sig |} f := thisone.
#[export] Instance struct_idx_tl {f f' t sig nm}
  {si : StructIdx {| struct_name := nm; struct_fields := sig |} f}:
  StructIdx {| struct_name := nm; struct_fields := (f',t) :: sig |} f := anotherone si.
Arguments struct_idx sig f {StructIdx} : assert.

(* Notation lift_intfun lR lSigma fn :=
  (lift_intfun' (lift lR lSigma) fn). *)

(* Require Import CompactLogs. *)

(* Arguments unlift_sigma {ext_fn_t} {Sigma} {ext_fn_t'} {Sigma'} {lSigma} sigma f _: assert. *)

(* Notation unlift_Log := (unlift_REnv _ LogEntry). *)
(* Notation unlift_r := (unlift_REnv _ type_denote). *)

(* Notation lift_Log := (lift_REnv _ LogEntry). *)
(* Notation lift_r := (lift_REnv _ type_denote). *)
