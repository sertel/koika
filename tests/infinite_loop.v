Require Import Koika.Frontend.

Inductive reg_t :=
| r1
.

Instance FiniteType_r : FiniteType reg_t := _.

Definition R (reg: reg_t) : type :=
  match reg with
  | r1 => bits_t 1
  end.

Definition r (reg: reg_t) : R reg :=
  match reg with
  | r1 => Bits.zero
  end.

Definition f1: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun f1 (i1: bits_t 1) (i2: bits_t 4) : unit_t =>
       let i11 := i1 in
       let i21 := i2 in
       write1(r1, i11)
  }}.

Definition f2: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun f2 (i1: bits_t 1) (i2: bits_t 4) (i3 : bits_t 3) : unit_t =>
       let i11 := i1 in
       let i21 := i2 in
       let i31 := i3 in
       write1(r1, i11)
  }}.

Definition f3: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun f3 (i1: bits_t 1) (i2: bits_t 4) (i3 : bits_t 3) : unit_t =>
       let i11 := i1 in
       let i31 := i3 in
       write1(r1, i11)
  }}.

Definition tc_f1 :=  tc_function R empty_Sigma f1.
Definition tc_f2 :=  tc_function R empty_Sigma f2.
Definition tc_f3 :=  tc_function R empty_Sigma f3.

Definition reg_type (idx:reg_t) := R idx.
Definition Env := env_t ContextEnv reg_type.

Definition tc_and_run_action_on_inputs {sig: tsig var_t} {tau} (e:Env) (a:action R empty_Sigma sig tau) (inputs: context _ _) :=
  (* tc_compute *)
    (interp_action e empty_sigma inputs log_empty log_empty a).

Definition run {sig: tsig var_t} {tau} (a:action R empty_Sigma sig tau) inputs reg_vals :=
  let e := ContextEnv.(create) reg_vals in
  (* let c := tc_and_run_action_on_inputs e a inputs in *)
  (* Only when inlining the below line the compiler flags me an error when no FiniteType instance for reg_t was found! *)
  let c := interp_action e empty_sigma inputs log_empty log_empty a in
  let r := match c with
           | Some (l,o,_) => Some (commit_update e l, o)
           | None => None
           end in
  must r.

Definition run' {sig: tsig var_t} {tau} (a:action R empty_Sigma sig tau) inputs reg_vals :=
  let e := ContextEnv.(create) reg_vals in
  (* let c := tc_and_run_action_on_inputs e a inputs in *)
  (* Only when inlining the below line the compiler flags me an error when no FiniteType instance for reg_t was found! *)
  let c := interp_action e empty_sigma inputs log_empty log_empty a in
  let r := match c with
           | Some (l,o,_) => Some (commit_update e l, o)
           | None => None
           end in
  r.

(* This example works. *)
Example test1:
  let input := #{
   ("i1"   , bits_t _) => Bits.of_nat _ 1;
   ("i2"   , bits_t _) => Bits.of_nat _ 3
                 }# in
  let (ctxt,_) := run tc_f1 input r in

  let o := Bits.to_nat ctxt.[r1] in

  o = 1.
 reflexivity.
Defined.

Print tc_f1.
Compute tc_f1.

Print tc_f2.
Print f2.
Compute tc_f2.

(* http://gallium.inria.fr/blog/coq-eval/ *)
Eval vm_compute in tc_f2.
Eval cbv in tc_f2.
Eval lazy in tc_f2.
(* This deadlocks: Eval cbn in tc_f2. *)
(* This deadlocks: Eval hnf in tc_f2. *)
Eval cbn in tc_f1. (* Takes long but does not deadlock. *)

Eval vm_compute in (
  let input := #{
   ("i1"   , bits_t _) => Bits.of_nat _ 1;
   ("i2"   , bits_t _) => Bits.of_nat _ 3;
   ("i3"   , bits_t _) => Bits.of_nat _ 4
                 }# in
  run tc_f2 input r
  ).

Print must.

(* This deadlocks again:
Eval cbn in (
  let input := #{
   ("i1"   , bits_t _) => Bits.of_nat _ 1;
   ("i2"   , bits_t _) => Bits.of_nat _ 3;
   ("i3"   , bits_t _) => Bits.of_nat _ 4
                 }# in
run tc_f2 input r
  ).
 *)

Locate must.

(* This works: *)
Eval vm_compute in (
  let input := #{
   ("i1"   , bits_t _) => Bits.of_nat _ 1;
   ("i2"   , bits_t _) => Bits.of_nat _ 3;
   ("i3"   , bits_t _) => Bits.of_nat _ 4
                 }# in
  let c := run' tc_f2 input r in
  match c with
    | Some (ctxt, _) => let o := Bits.to_nat ctxt.[r1] in o = 1
    | None => False
  end
).

(* deadlock:
Eval vm_compute in (
  let input := #{
   ("i1"   , bits_t _) => Bits.of_nat _ 1;
   ("i2"   , bits_t _) => Bits.of_nat _ 3;
   ("i3"   , bits_t _) => Bits.of_nat _ 4
                 }# in
  let c := run' tc_f2 input r in
  match must c with
    | (ctxt, _) => let o := Bits.to_nat ctxt.[r1] in o = 1
  end
).
 *)

Eval vm_compute in (
  let input := #{
   ("i1"   , bits_t _) => Bits.of_nat _ 1;
   ("i2"   , bits_t _) => Bits.of_nat _ 3;
   ("i3"   , bits_t _) => Bits.of_nat _ 4
                 }# in
  let c := run' tc_f2 input r in
  must c
).

Print _tc_strategy.
(* Ltac _tc_strategy ::= exact TC_native. *)

(* This deadlocks again:
Eval cbn in (
  let input := #{
   ("i1"   , bits_t _) => Bits.of_nat _ 1;
   ("i2"   , bits_t _) => Bits.of_nat _ 3;
   ("i3"   , bits_t _) => Bits.of_nat _ 4
                 }# in
  let c := run' tc_f2 input r in
  match c with
    | Some (ctxt, _) => let o := Bits.to_nat ctxt.[r1] in o = 1
    | None => False
  end
).
*)

(* This deadlocks as well:
Eval vm_compute in (
  let input := #{
   ("i1"   , bits_t _) => Bits.of_nat _ 1;
   ("i2"   , bits_t _) => Bits.of_nat _ 3;
   ("i3"   , bits_t _) => Bits.of_nat _ 4
                 }# in
  let c := run tc_f2 input r in
  match c with
  | (ctxt, _) => ctxt
  end
).
*)

(* This deadlocks:
Eval vm_compute in (
  let input := #{
   ("i1"   , bits_t _) => Bits.of_nat _ 1;
   ("i2"   , bits_t _) => Bits.of_nat _ 3;
   ("i3"   , bits_t _) => Bits.of_nat _ 4
                 }# in
  let (ctxt,_) := run tc_f2 input r in
  let o := Bits.to_nat ctxt.[r1] in
  o
  ).
 *)

(* This deadlocks too:
Eval vm_compute in (
  let input := #{
   ("i1"   , bits_t _) => Bits.of_nat _ 1;
   ("i2"   , bits_t _) => Bits.of_nat _ 3;
   ("i3"   , bits_t _) => Bits.of_nat _ 4
                 }# in
  let (ctxt,_) := run tc_f2 input r in
  ctxt.[r1]
).
 *)


Example test20:
  let input := #{
   ("i1"   , bits_t _) => Bits.of_nat _ 1;
   ("i2"   , bits_t _) => Bits.of_nat _ 3;
   ("i3"   , bits_t _) => Bits.of_nat _ 4
                 }# in

  match run' tc_f2 input r with
  | Some (ctxt, _) => let o := Bits.to_nat ctxt.[r1] in  o = 1
  | None => False
  end.
(* cbn <- deadlocks again. *)
vm_compute.
reflexivity.
Defined.


(* But this apparently does! *)
Example test21:
  let input := #{
   ("i1"   , bits_t _) => Bits.of_nat _ 1;
   ("i2"   , bits_t _) => Bits.of_nat _ 3;
   ("i3"   , bits_t _) => Bits.of_nat _ 4
                 }# in

  match run' tc_f2 input r with
  | Some (ctxt, _) => let o := Bits.to_nat ctxt.[r1] in  o = 1
  | None => False
  end.
  vm_compute.
reflexivity.
Defined.

Print must.

(* https://plv.csail.mit.edu/blog/unwrapping-options.html#unwrapping-options *)

Definition unwrap {A} (o: option A)
            (not_none: o <> None) : A :=
   match o return _ = o -> A with
   | Some a => fun _ => a
   | None => fun is_none => False_rect _ (not_none is_none)
   end eq_refl.

Definition is_some {A} (o: option A) : bool :=
   if o then true else false.

Lemma is_some_not_none {A} {o: option A} :
   is_some o = true -> o <> None.
 Proof. destruct o. all: cbn. all: congruence. Qed.

Definition unwrap_dec {A} (o: option A)
            (is_some_true: is_some o = true) : A :=
  unwrap o (is_some_not_none is_some_true).

Notation unwrap_dec' o := (unwrap_dec o eq_refl).

Example test22:
  let input := #{
   ("i1"   , bits_t _) => Bits.of_nat _ 1;
   ("i2"   , bits_t _) => Bits.of_nat _ 3;
   ("i3"   , bits_t _) => Bits.of_nat _ 4
                 }# in

  let (ctxt,_) := unwrap_dec' (run' tc_f2 input r) in

  let o := Bits.to_nat ctxt.[r1] in

  o = 1.
  vm_compute.
  reflexivity.
Defined.

(* This example enters into the infinite loop.
   Probably because the dependent type of [must] is too much for
   the evaluation strategy. Even for vm_compute as shown above.
Lemma test22:
  let input := #{
   ("i1"   , bits_t _) => Bits.of_nat _ 1;
   ("i2"   , bits_t _) => Bits.of_nat _ 3;
   ("i3"   , bits_t _) => Bits.of_nat _ 4
                 }# in

  let (ctxt,_) := run tc_f2 input r in

  let o := Bits.to_nat ctxt.[r1] in

  o = 1.
vm_compute.
reflexivity.
Defined.
*)

(* This example enters into the infinite loop.
Example test22:
  tc_compute (
  let input := #{
   ("i1"   , bits_t _) => Bits.of_nat _ 1;
   ("i2"   , bits_t _) => Bits.of_nat _ 3;
   ("i3"   , bits_t _) => Bits.of_nat _ 4
                 }# in

  let (ctxt,_) := run tc_f2 input r in

  let o := Bits.to_nat ctxt.[r1] in

  o = 1).
reflexivity.
Defined.
*)

(* This example works again. *)
Example test30:
  let input := #{
   ("i1"   , bits_t _) => Bits.of_nat _ 1;
   ("i2"   , bits_t _) => Bits.of_nat _ 3;
   ("i3"   , bits_t _) => Bits.of_nat _ 4
                 }# in

  let (ctxt,_) := run tc_f3 input r in

  let o := Bits.to_nat ctxt.[r1] in

  o = 1.
reflexivity.
Defined.

Example test31:
  let input := #{
   ("i1"   , bits_t _) => Bits.of_nat _ 1;
   ("i2"   , bits_t _) => Bits.of_nat _ 3;
   ("i3"   , bits_t _) => Bits.of_nat _ 4
                 }# in

  let (ctxt,_) := run tc_f3 input r in

  let o := Bits.to_nat ctxt.[r1] in

  o = 1.
vm_compute. (* This makes evaluation fast. *)
reflexivity.
Defined.
