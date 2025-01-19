(*! Utilities | Finiteness typeclass !*)
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Arith.
Import ListNotations.
From Coq Require Import Program.Equality.
From Coq Require Import Logic.FinFun.

Require Import Koika.Common.
Open Scope nat_scope. (* TODO avoid string import *)
Import List(length).

Generalizable Variables T A B C.

Ltac simplHyp :=
  match goal with
    | [ H : ex _ |- _ ] => destruct H
    | [ H : ?F ?X = ?F ?Y |- ?G ] =>
      (** This first branch of the [||] fails the whole attempt iff the arguments of the constructor applications are already easy to prove equal. *)
      (assert (X = Y); [ assumption | fail 1 ])
      (** If we pass that filter, then we use injection on [H] and do some simplification as in [inject].
         * The odd-looking check of the goal form is to avoid cases where [injection] gives a more complex result because of dependent typing, which we aren't equipped to handle here. *)
      || (injection H;
        match goal with
          | [ |- X = Y -> G ] =>
            try clear H; intros; try subst
        end)
    | [ H : ?F ?X ?U = ?F ?Y ?V |- ?G ] =>
      (assert (X = Y); [ assumption | assert (U = V); [ assumption | fail 1 ] ])
      || (injection H;
        match goal with
          | [ |- U = V -> X = Y -> G ] =>
            try clear H; intros; try subst
        end)
    | [ H : ?A = ?B |- _ ] =>
      let lA := head A in
      let lB := head B in
      is_constructor lA; is_constructor lB; inversion H; clear H
    | [ H : prod _ _ |- _ ] =>
      destruct H
  end.

Create HintDb finite_type.
Inductive CreateRewriteDB := create_rewrite_db.
#[global] Hint Rewrite (@eq_refl _ create_rewrite_db) : finite_type.

Ltac finite_type_auto :=
  let sintuition := simpl in *; intuition auto with finite_type; try subst;
    repeat (simplHyp; intuition auto with finite_type; try subst); try congruence in

  repeat match goal with
  | _ => progress sintuition
  | _ => progress autorewrite with finite_type in *
  | [ H : ?P |- _ ] => rewrite H by finite_type_auto
  | _ => progress autounfold with finite_type in *
  | _ => progress lia
  end.

Hint Unfold Injective : finite_type.

(* TODO should probably better use FinFun.Listing *)
Class FiniteType {T} := {
  finite_index: T -> nat;
  finite_elements: list T;
  (* Caution: used for computations *)
  finite_surjective: forall a: T, List.nth_error finite_elements (finite_index a) = Some a;
  finite_injective: NoDup (List.map finite_index finite_elements)
}.
Arguments FiniteType: clear implicits.
Arguments finite_surjective [T] [FiniteType] a : assert.

Hint Rewrite finite_surjective : finite_type.
Hint Resolve finite_injective : finite_type.
Hint Resolve seq_NoDup : finite_type.


(* ========================================================================= *)
(*                           FiniteType for Fin.t n                          *)
(* ========================================================================= *)

Fixpoint finite_elements_Fin_t {n} : list (Fin.t n) :=
  match n with
  | O => []
  | S _ => Fin.F1 :: map Fin.FS finite_elements_Fin_t
  end.

Fixpoint finite_index_Fin_t {n} (f : Fin.t n) : nat :=
  match f with
  | Fin.F1 => 0
  | Fin.FS f' => S (finite_index_Fin_t f')
  end.

Lemma finite_index_Fin_t_seq n :
  (map (@finite_index_Fin_t n) finite_elements_Fin_t) = seq 0 n.
Proof.
  induction n as [|n' IH];
    [ | cbn; rewrite map_map; cbn; rewrite <- map_map, IH, seq_shift]; reflexivity.
Qed.

#[local] Hint Rewrite nth_error_map : fin_t.
#[local] Hint Rewrite finite_index_Fin_t_seq : fin_t.

#[refine] Instance fin_t_FiniteType {n} : FiniteType (Fin.t n) := {
  finite_elements := finite_elements_Fin_t;
  finite_index := finite_index_Fin_t;
}.
Proof.
  1: intro a; induction a; try reflexivity; cbn.
  (* 2: eapply (NoDup_map_inv finite_index_Fin_t). *)
  all: autorewrite with fin_t; finite_type_auto.
Defined.


(* ========================================================================= *)
(*                             FiniteType Lemmas                             *)
(* ========================================================================= *)

Definition finite_index_injective `{FT: FiniteType T}:
  Injective finite_index.
Proof.
  repeat match goal with
  | H : _ = _ |- _ => apply (f_equal (nth_error finite_elements)) in H
  | _ => finite_type_auto
  end.
Qed.

Definition finite_index_lt_finite_element `{FT: FiniteType T}:
  forall a, finite_index a < Datatypes.length finite_elements.
Proof.
  intros.
  pose proof (finite_surjective a).
  apply nth_error_Some.
  rewrite H.
  inversion 1.
Qed.

Hint Resolve finite_index_injective Injective_map_NoDup : finite_type.

(* Definition finite_nodup `{FiniteType} :
  NoDup (List.map finite_index finite_elements).
Proof. finite_type_auto. Qed. *)

Definition finite_nodup `{FT: FiniteType T} :
  NoDup finite_elements.
Proof. apply (NoDup_map_inv _ _ finite_injective). Qed.

Fixpoint increasing (l: list nat) :=
  match l with
  | [] => true
  | n1 :: [] => true
  | n1 :: (n2 :: _) as l => andb (Nat.ltb n1 n2) (increasing l)
  end.

Lemma increasing_not_In :
  forall l n, increasing (n :: l) = true -> forall n', n' <= n -> ~ In n' l.
Proof.
  induction l; intros n H n' Hle Habs.
  - auto.
  - apply Bool.andb_true_iff in H; destruct H; apply PeanoNat.Nat.ltb_lt in H.
    destruct Habs as [ ? | ? ]; subst; try lia.
    eapply IHl; [ eassumption | .. | eassumption ]; lia.
Qed.

Lemma increasing_not_In' :
  forall l n, increasing (n :: l) = true -> forall n', n' <? n = true -> ~ In n' (n :: l).
Proof.
  unfold not; intros l n Hincr n' Hlt [ -> | Hin ]; apply PeanoNat.Nat.ltb_lt in Hlt.
  - lia.
  - eapply increasing_not_In;
      [ eassumption | apply Nat.lt_le_incl | eassumption ]; eauto.
Qed.

Lemma increasing_NoDup l:
  increasing l = true -> NoDup l.
Proof.
  induction l as [ | ? l IHl]; cbn; intros H.
  - constructor.
  - destruct l.
    + repeat constructor; inversion 1.
    + apply Bool.andb_true_iff in H; destruct H.
      constructor.
      apply increasing_not_In'; eauto.
      eauto.
Qed.


(* Caution: finite_surjective in used for computations
 *
 * Consequently, its proof term may only contain
 * transparent lemmas. For that, some lemmas from the
 * standard lib are redefined here, but transparent.
 *)

(* This definition provides a trick to create transparent
 * lemmas from opaque ones. (Only works with equalities on nat)
 *
 * This trick is taken from MIT-PLV's blog
 * https://github.com/mit-plv/blog/blob/b484ee3a87445e4d97b8a25b7614856a66354290/content/2020-06-17_computing-with-opaque-proofs.rst
 *)
Definition computational_eq {m n} (opaque_eq: m = n) : m = n :=
  match Nat.eq_dec m n with
  | left transparent_eq => transparent_eq
  | _ => opaque_eq (* dead code; could use [False_rect] *)
  end.

Lemma add_schuffle (a b c: nat):
  a + b + c = b + c + a.
Proof.
  finite_type_auto.
Qed.

(* Transparent proofs of opaque ones *)
Definition add_schuffle_trans (a b c: nat) := computational_eq (add_schuffle a b c).
Definition add_sub_trans (m n : nat) := computational_eq (Nat.add_sub m n).

(* Taken from coq's standard lib + made transparent *)
Theorem le_n_S_trans : forall n m, n <= m -> S n <= S m.
  lia. Defined.
Theorem le_pred_trans : forall n m, n <= m -> pred n <= pred m.
  lia. Defined.
Definition le_S_n_trans (n m : nat) : S n <= S m -> n <= m :=
  (le_pred_trans (S n) (S m)).


Fixpoint nth_error_app1_trans {A} (l l' : list A) n:
  n < length l ->
  nth_error (l ++ l') n = nth_error l n.
Proof.
  intros.
  destruct l, n; cbn in H |- *; try solve [reflexivity + inversion H].
  apply le_S_n_trans in H. eauto.
Defined.

Fixpoint nth_error_app2_trans {A} (l l' : list A) n:
  length l <= n ->
  nth_error (l ++ l') n = nth_error l' (n - length l).
Proof.
  intros.
  destruct l, n; cbn in H |- *; try solve [reflexivity + inversion H].
  apply le_S_n_trans in H. eauto.
Defined.


Fixpoint nth_error_map_trans {A B} (f : A -> B) n (l : list A):
  nth_error (map f l) n = option_map f (nth_error l n).
Proof. destruct l, n; try reflexivity. cbn; eauto. Defined.

Fixpoint map_length_trans {A B} (f : A -> B) (l : list A):
  length (map f l) = length l.
Proof. destruct l; try reflexivity. cbn; eauto. Defined.

Fixpoint nth_error_Some_trans {A} n x (l : list A):
  nth_error l n = Some x -> n < length l.
Proof.
  induction l, n; inversion 1; cbn.
  - auto with arith.
  - apply le_n_S_trans. unfold lt in *. eauto.
Defined.

(* Lemma list_prod_nil_r A B l :
  @list_prod A B l [] = [].
Proof. induction l; auto. Defined. *)

Fixpoint nth_error_prod {A1 A2} (l1: list A1) (l2 : list A2) {struct l1}:
  forall n1 n2 x y,
  nth_error l1 n1 = Some x ->
  nth_error l2 n2 = Some y ->
  nth_error (list_prod l1 l2) (n1 * length l2 + n2) = Some (x,y).
Proof.
  intros n1 n2 x y H1 H2.
  induction l1 as [| a1 l1' IH], n1 in H1, H2, n1, n2 |- *;
  inversion H1; cbn.
  - rewrite nth_error_app1_trans.
    + rewrite nth_error_map_trans, H2. auto.
    + rewrite map_length_trans.
      exact (nth_error_Some_trans _ y _ H2).
  - rewrite nth_error_app2_trans; rewrite map_length_trans;
    try rewrite add_schuffle_trans, add_sub_trans; eauto with arith.
Defined.

Lemma nth_error_prod_fn {A1 A2} (l1: list (A2 -> A1)) (l2 : list A2):
  forall n1 n2 x y,
  nth_error l1 n1 = Some x ->
  nth_error l2 n2 = Some y ->
  nth_error (map (fun '(a,b) => a b) (list_prod l1 l2)) (n1 * length l2 + n2) = Some (x y).
Proof.
  intros n1 n2 x y H1 H2.
  rewrite nth_error_map_trans, (nth_error_prod l1 l2 n1 n2 x y) by assumption; auto.
Defined.

Fixpoint list_fn_dep {A2 A1} (l : list (forall a : A2, A1 a)) (a2 : A2) {struct l} :
  list (A1 a2) :=
  match l with
  | nil => nil
  | cons x l' => x a2 :: list_fn_dep l' a2
  end.

Lemma nth_error_fn_dep {A2 A1} (x : forall a : A2, A1 a) (l: list (forall a : A2, A1 a)) :
  forall n y,
  nth_error l n = Some x ->
  nth_error (list_fn_dep l y) n = Some (x y).
Proof.
  intros n y H.
  induction l as [| a l' IH ] in n, H |- *; destruct n;
    try (inversion H; reflexivity).
  exact (IH _ H).
Defined.

Lemma nth_error_fn {A1 A2} (x: A2 -> A1) (l : list A2):
  forall n y,
  nth_error l n = Some y ->
  nth_error (map x l) n = Some (x y).
Proof.
  intros n y H.
  induction l as [| a l' IH ] in n, H |- *; destruct n;
    try (inversion H; reflexivity).
  exact (IH _ H).
Defined.


Lemma nth_error_nil A n :
  nth_error (@nil A) n = None.
Proof. destruct n; auto. Qed.

Lemma nth_error_cons {A} (a : A) (l : list A):
forall x n,
  nth_error l n = Some x ->
  nth_error (a :: l) (S n) = Some x.
Proof. auto. Defined.

Fixpoint nth_error_app_l {A} (l l' : list A):
  forall n x,
    nth_error l n = Some x ->
    nth_error (l ++ l') n = Some x.
Proof.
  intros; erewrite nth_error_app1_trans.
  - assumption.
  - apply (nth_error_Some_trans _ x _). assumption.
Defined.

Fixpoint nth_error_app_r {A} (l l' : list A):
forall n x,
  nth_error l n = Some x ->
  nth_error (l' ++ l) (n + length l') = Some x.
Proof.
  intros; erewrite nth_error_app2_trans.
  - rewrite add_sub_trans. assumption.
  - auto with arith.
Defined.

  (* nth_error (A'' :: map B'' finite_elements ++ ?l') ?Goal0 = Some C'' *)
Ltac FiniteType_t_clean_up_list :=
  repeat lazymatch goal with
  | [ |- nth_error (_ :: _) _ = _ ] => apply nth_error_cons
  | [ |- nth_error (_ ++ _) _ = _ ] => apply nth_error_app_r
  end.

Hint Resolve nth_error_nil : finite_type.
Hint Rewrite in_app_iff : finite_type.

Lemma not_in_app [A] (l1 l2 : list A) a :
  ~In a (l1 ++ l2) <->
  ~In a l1 /\ ~In a l2.
Proof. finite_type_auto. Qed.


Hint Constructors NoDup : finite_type.
Hint Rewrite NoDup_cons_iff : finite_type.
Hint Resolve In_nth_error : finite_type.

Lemma NoDup_app {A} {l1 l2 : list A} :
  NoDup l1 -> NoDup l2 ->
  (forall i j, i < length l1 -> j < length l2 -> nth_error l1 i <> nth_error l2 j) ->
  NoDup (l1 ++ l2).
Proof.
  (* finite_type_auto. *)
  intros Hl1 Hl2 H.
  induction l1 as [|a1 l1 IH]. auto.
  rewrite <- app_comm_cons.
  constructor.
  - rewrite not_in_app. split.
    * finite_type_auto.
    * intro Hin.
      apply In_nth_error in Hin.
      destruct Hin as [n Hin].
      specialize (H 0 n (Nat.lt_0_succ _) (nth_error_Some_trans _ _ _ Hin)).
      finite_type_auto.
  - rewrite NoDup_cons_iff in Hl1.
    destruct Hl1 as [Hl1in Hl1].
    specialize (IH Hl1).
    pose proof (Hl1' := fun n => H (S n)).
    cbn in Hl1';
    revert Hl1'.
    setoid_rewrite <- Nat.succ_lt_mono.
    auto.
Qed.

Hint Resolve NoDup_app : finite_type.

Lemma NoDup_app2 {A} {l1 l2 : list A} :
  NoDup l1 -> NoDup l2 ->
  (forall i j a b, nth_error l1 i = Some a -> nth_error l2 j = Some b -> a <> b) ->
  NoDup (l1 ++ l2).
Proof.
  intros Hl1 Hl2 H.
  apply NoDup_app; try assumption.
  intros i j Hi Hj. specialize (H i j).
  eapply nth_error_Some in Hi, Hj.
  destruct (nth_error l1 i) as [a|], (nth_error l2 j) as [b|]; inversion 1;
    try specialize (H a b eq_refl eq_refl); auto.
Qed.

Lemma Nat_sub_lt_mono (n m p : nat) :
  n < m -> p <= n-> n - p < m - p.
Proof. lia. Qed.

Lemma NoDup_list_prod {A1 A2} {l1 : list A1} {l2 : list A2} :
  NoDup l1 -> NoDup l2 ->
  NoDup (list_prod l1 l2).
Proof.
  intros Hl1 Hl2.
  induction l1 as [|a1 l1 IH]; cbn.
    apply NoDup_nil.
  rewrite NoDup_cons_iff in Hl1.
  destruct Hl1 as [Hl1in Hl1];
    specialize (IH Hl1); apply NoDup_app;
    try (apply Injective_map_NoDup;
      [unfold Injective; inversion 1|]); auto.
  intros i j Hi Hj.

  induction l1 in i, j, Hi, Hj, Hl1in |- *.
    rewrite nth_error_nil; apply nth_error_Some; auto.
  cbn; destruct (j <? length l2) eqn:Hjlt;
  rewrite ?Nat.ltb_lt, ?Nat.ltb_ge in *;
  [rewrite nth_error_app1|rewrite nth_error_app2]; rewrite ?map_length; auto.
  * rewrite ?nth_error_map.
    destruct (nth_error l2 i) eqn:Hi', (nth_error l2 j) eqn:Hj'; cbn; inversion 1 as [H1].
    + rewrite H1 in Hl1in. cbn in Hl1in. tauto.
    + apply nth_error_None in Hi'.
      rewrite map_length, Nat.lt_nge in Hi. tauto.
  * cbn in Hl1in, Hj.
    specialize (IHl1 (fun a => Hl1in (or_intror a))).
    rewrite app_length, map_length in Hj.
    pose proof (Hj' := Nat_sub_lt_mono _ _ _ Hj Hjlt).
    rewrite Nat.add_comm, Nat.add_sub in Hj'.
    specialize (IHl1 i (j - length l2) Hi Hj').
    auto.
Qed.









(* ========================================================================= *)
(*                   automated resolution for FiniteTypes                    *)
(* ========================================================================= *)

Inductive FiniteType_norec (T: Type) :=
  | finite_type_norec : FiniteType_norec T.

Ltac nth_error_solve_recusive :=
  lazymatch goal with
  | [ |- nth_error _ _ = Some ?z ] => (* check for recursion *)
    let tz := type of z in
    lazymatch goal with
    | [ H: FiniteType_norec tz |- _ ] => fail "Type" tz "is recursive"
    | _ => pose proof (finite_type_norec tz)
    end;
    (* scoping issues *)
    (* let FT := fresh "FT" in
    assert (FT : FiniteType tz) by typeclasses eauto;
    eapply (finite_surjective (FiniteType := FT)) *)
    eapply (finite_surjective (T := tz) (FiniteType := ltac:(typeclasses eauto)))
  end.

Ltac change_to_tuple :=
  let rec build_tup n :=
    lazymatch n with
    | ?C ?a ?b =>
      let a' := build_tup (C a) in
      constr:((a',b))
    | ?C ?a => constr:(a)
    end in
  let rec build_fn n :=
    lazymatch n with
    | ?C ?a ?b =>
      let C' := build_fn (C a) in
      constr:(fun '(x,y) => C' x y)
    | ?C ?a => constr:(C)
    end in
  match goal with
  | |- _ = Some ?con =>
    let tup := build_tup con in
    let con' := build_fn con in
    change con with (con' tup);
    apply map_nth_error
  end.

Ltac FiniteType_t_compute_index :=
  FiniteType_t_clean_up_list;
  lazymatch goal with
  | [ |- nth_error _ _ = Some (?a _) ] =>
      (* let n := numgoals in try (guard n>1;  *)
      (* apply nth_error_app_l; *)
      (* ); *)

      apply nth_error_app_l;
      change_to_tuple;
      nth_error_solve_recusive
  | [ |- nth_error _ _ = Some _ ] =>
    instantiate (1 := 0);
    instantiate (1 := _ :: _);
    reflexivity
  end.

(* Ltac FiniteType_t_nodup_increasing :=
  apply increasing_NoDup;
  vm_compute; reflexivity. *)

Ltac intro_destruct :=
  let a := fresh in
  intro a; destruct a.

Ltac FiniteType_t_destruct :=
  repeat match goal with
  | [ |- context[nth_error _ (_ _) = Some _] ] => instantiate (1 := ltac:(intro_destruct))
  | [ |- context[nth_error _ _ = Some _] ] => idtac
  end;
  intro_destruct.

Lemma nth_error_eq {A1 A2 B} (l1 : list A1) (l2 : list A2) f g i j (a : B) :
  nth_error (map f l1) i = Some a ->
  nth_error (map g l2) j = Some a ->
  ~ (forall a b, f a <> g b).
Proof.
  intros H1 H2 H.
  rewrite nth_error_map in H1, H2.
  destruct (nth_error l1 i) as [a1|] eqn:Hi, (nth_error l2 j) as [a2|]eqn:Hj;
    cbn in H1, H2; inversion H1; inversion H2.
  specialize (H a1 a2). congruence.
Qed.

Lemma nth_error_single A (a a' : A) n :
  nth_error [a] n = Some a' ->
  a = a'.
Proof.
  destruct n; now (inversion 1 as [H']; try rewrite nth_error_nil in H').
Qed.

Lemma nth_error_map_exists A B (f : B -> A) (a : A) l n:
  nth_error (map f l) n = Some a ->
  exists b, f b = a.
Proof.
  intro H.
  induction l as [| b l IH] in n, H |- *.
  rewrite nth_error_nil in H. inversion H.
  destruct n.
  - rewrite nth_error_map in H. cbn in H. eexists b. now inversion H.
  - cbn in H. now specialize (IH _ H).
Qed.

Lemma nth_error_app_or A l1 l2 n (a : A) :
  nth_error (l1 ++ l2) n = Some a ->
  nth_error l1 n = Some a \/ nth_error l2 (n - length l1) = Some a.
Proof.
  intros H.
  destruct (n <? Datatypes.length l1) eqn:Hn.
  + apply Nat.ltb_lt in Hn.
    rewrite nth_error_app1 in H by easy.
    now left.
  + apply Nat.ltb_ge in Hn.
    rewrite nth_error_app2 in H by easy.
    now right.
Qed.

Ltac simpl_ft_no_dup :=
  repeat match goal with
  | _ => progress intros
  | _ => eassumption || discriminate || reflexivity

  | |- and _ _ => constructor
  | |- Injective _ => unfold Injective

  | |- NoDup []        => apply NoDup_nil
  | |- NoDup (_ :: _)  => apply NoDup_cons
  | |- NoDup (_ ++ _)  => apply NoDup_app2
  | |- NoDup (map _ _) => apply Injective_map_NoDup
  | |- NoDup (@finite_elements ?T ?FT) =>
    apply (NoDup_map_inv _ _ (@finite_injective T FT))
  | |- In _ (_ ++ _)   => rewrite in_app_iff
  | |- In _ (map _ _)  => rewrite in_map_iff
  | |- In ?a (?a :: _) => apply in_eq
  | |- In ?a (?b :: _) => apply in_cons
  | |- not _           => intro

  | H: In _ []          |- _ => apply in_nil in H
  | H: In _ (_ ++ _)    |- _ => rewrite in_app_iff in H
  | H: In _ (_ :: _)    |- _ => apply in_inv in H
  | H: In _ (map _ _)   |- _ => rewrite in_map_iff in H

  | H: context[nth_error [] _]             |- _ => rewrite nth_error_nil in H
  | H: context[_ ++ []]                    |- _ => rewrite app_nil_r in H
  | H: context[Datatypes.length (map _ _)] |- _ => rewrite map_length in H

  | H: ex _             |- _ => destruct H
  | H: and _ _          |- _ => destruct H
  | H: or _ _           |- _ => destruct H
  | H: prod _ _         |- _ => destruct H
  (* | H: ?Ind            |- _ =>
    let lInd := head Ind in
    is_ind lInd; destruct H *)
  | H: S _ = S _        |- _ => apply eq_add_S in H
  | H: ?A = ?B          |- _ =>
    let lA := head A in
    let lB := head B in
    is_constructor lA; is_constructor lB; inversion H; subst; clear H

  | H: match ?x with _ => _ end =
      match ?y with _ => _ end |- _ => destruct x,y
  | H: _ + ?a = _ + ?a |- _ => rewrite Nat.add_cancel_r in H
  | H: finite_index ?a = finite_index ?b |- _ =>
    let FI := fresh "FI" in
    pose proof (FI := finite_index_injective _ _ H)

  | H: @finite_index ?A _ ?a = _ + Datatypes.length (@finite_elements ?A _) |- _ =>
    solve [pose proof (finite_index_lt_finite_element a); lia]
  | H: _ + Datatypes.length (@finite_elements ?A _) = @finite_index ?A _ ?a |- _ =>
    solve [pose proof (finite_index_lt_finite_element a); lia]

  | H: nth_error (_ ++ _) _ = Some _ |- _ =>
    apply nth_error_app_or in H; destruct H
  | H: nth_error (map _ _) _ = Some _ |- _ =>
    apply nth_error_map_exists in H; destruct H
  | H: nth_error [_] _ = Some _ |- _ =>
    apply nth_error_single in H

  | _ => progress subst
  (* | H1: nth_error (map _ _) _ = Some ?a,
    H2: nth_error (map _ _) _ = Some ?b,
    Heq: ?a = ?b |- _ =>
      destruct Heq;
      apply (nth_error_eq _ _ _ _ _ _ _ H1 H2) *)
  end.

Ltac FiniteType_t :=
  (* let ft_idx := fresh in
  match goal with
  | |- FiniteType ?t => evar (ft_idx : t -> nat)
  end; *)
  unshelve econstructor;
  [ (* exact (ft_idx) *) (* intro_destruct;  *)shelve
  | shelve
  | FiniteType_t_destruct; [> FiniteType_t_compute_index ..]
  | instantiate (1 := []); simpl_ft_no_dup ].

Hint Extern 1 (FiniteType _) => FiniteType_t : typeclass_instances.

(* ========================================================================= *)
(*                          FiniteType for products                          *)
(* ========================================================================= *)

Lemma Some_not_None [A] (a : A) o:
  o = Some a -> o <> None.
Proof. intros H; rewrite H; inversion 1. Qed.

Lemma length_finite_elements `{FiniteType T} (el : T):
  Datatypes.length (finite_elements) <> 0.
Proof.
  pose proof (H' := @finite_surjective T _ el).
  destruct finite_elements; now try rewrite nth_error_nil in H'.
Qed.

Instance ft_prod `{fta : FiniteType A} `{ftb : FiniteType B} :
  FiniteType (prod A B).
  unshelve econstructor.
  - destruct 1 as [a b];
    exact (fta.(finite_index) a * length ftb.(finite_elements) + ftb.(finite_index) b).
  - exact (list_prod fta.(finite_elements) ftb.(finite_elements)).
  - intros [a b];
    apply nth_error_prod; apply finite_surjective.
  - apply Injective_map_NoDup.
    + unfold Injective. intros [a1 b1] [a2 b2] H.
      f_equal.
      * rewrite (Nat.mul_comm (finite_index a2)) in H.
        apply Nat.div_unique in H.
        rewrite Nat.div_add_l in H by apply (length_finite_elements b1).
        rewrite Nat.div_small, Nat.add_0_r in H.

        auto using (@finite_index_injective A _).
        eapply nth_error_Some, Some_not_None, (finite_surjective b1).
        eapply nth_error_Some, Some_not_None, (finite_surjective b2).
      * rewrite (Nat.mul_comm (finite_index a2)) in H.
        apply Nat.mod_unique in H.
        rewrite Nat.add_comm, Nat.Div0.mod_add, Nat.mod_small in H.

        auto using (@finite_index_injective B _).
        eapply nth_error_Some, Some_not_None, (finite_surjective b1).
        eapply nth_error_Some, Some_not_None, (finite_surjective b2).
    + apply NoDup_list_prod; eapply NoDup_map_inv, finite_injective.
Defined.

Module Examples.
  Inductive t0 := A0 | B0. (* 1+1 = 2 instances *)
  Inductive t1 := A1 | B1 | C1 (x y: t0) | D1. (* 1+2+1 = 4 instances *)
  Inductive t2 := A2 | B2 (x y z: t0) | C2 (x y: t0). (* 1+4+1+2 = 8 instances *)
  Inductive t3 := A3 (x y: t2) (z: t1) | B3 (x y z: t0) | C3. (* 8*8*4 + 2*2*2 + 1 = 265 instances *)

  Inductive t4 n :=
  | A4 (f : Fin.t n).

  Inductive t5 n :=
  | A5 (f : Fin.t n) (x : t0).

  Inductive t7 : nat -> Type :=
  | A7 (y : t1) (n : nat) (f : Fin.t n) (x : t0) : t7 n.

  Inductive t6 : nat -> Type :=
  | A6 : forall n, Fin.t n -> t0 -> t6 n
  | B6 : forall n, Fin.t (S n) -> t0 -> t6 (S n).


  Instance t0_ft : FiniteType t0 := _.

  Instance t0_prod_ft : FiniteType (t0 * t0) := _.

  Instance t0_prod2_ft : FiniteType (t0 * t0 * t0) := _.


  Instance t1_ft : FiniteType t1 := _.
  Instance t2_ft : FiniteType t2 := _.
  Instance t3_ft : FiniteType t3 := _.
  Instance t4_ft n : FiniteType (t4 n).
    econstructor.
    - FiniteType_t_destruct.

      FiniteType_t_clean_up_list.
      apply nth_error_app_l.

      repeat apply nth_error_prod_fn + match goal with
      | |- context[Some (?a _)] => apply (nth_error_fn_dep a)
      end;

      [instantiate (1 := 0);
      instantiate (1 := [_]);
      reflexivity|..].
      (* change_to_tuple. *)
      nth_error_solve_recusive.
    - instantiate (1 := []); simpl_ft_no_dup.
      rewrite ?Nat.mul_0_l, ?Nat.add_0_l in H.
      let FI := fresh "FI" in
      pose proof (FI := finite_index_injective _ _ H); subst.
      reflexivity. admit.
      apply NoDup_list_prod.
      simpl_ft_no_dup.
      cbn in H

  Ltac nth_error_solve_recusive :=
    lazymatch goal with
    | [ |- nth_error _ _ = Some ?z ] =>
      (* check for recursion *)
      let tz := type of z in
      lazymatch goal with
      | [ H: FiniteType_norec tz |- _ ] => fail "Type" tz "is recursive"
      | _ => pose proof (finite_type_norec tz)
      end;
      let FT := fresh "FT" in
      assert (FT : FiniteType tz) by typeclasses eauto;
      eapply (finite_surjective (FiniteType := FT))
      (* eapply (finite_surjective (T := tz) (FiniteType := ltac:(typeclasses eauto))) *)
    end.

      (* destruct H1.
      cbn in H0.
       rewrite nth_error_map in H0.
      destruct (nth_error finite_elements i) eqn:?.
      * destruct p.
        (* cbn in H. *)
        destruct j.
        cbn in H0.
        simpl_ft_no_dup.
        cbn in H0.
        rewrite nth_error_nil in H0.
        simpl_ft_no_dup.
      * simpl_ft_no_dup.
        cbn in H. simpl_ft_no_dup. *)
Defined.

  (* intro a; destruct a.
    FiniteType_t_compute_index. *)
  - instantiate (1 := []). [B1] -> [B1 A0; B1 A1] -> [B1 A0 A0; B1 A0 A1; B1 A1 A0; B1 A1 A1 ]
    rewrite ?app_nil_r.
    rewrite map_map.

    (* rewrite ?list_prod_cons. *)
    Search "map_map".
    apply Injective_map_NoDup. admit.

    apply finite_index_injective.
    cbn. instantiate (1 := []).
    (* Search (_ ++ []). *)
    Search (list_prod (_ :: _) _).
    simpl list_prod.
    apply Injective_map_NoDup. admit.
    apply Injective_map_NoDup. admit.

    apply NoDup_list_prod.
      (* unfold Injective. intro x. destruct x eqn:Hx. intro y. destruct y eqn:Hy. intro. congruence. cbv zeta. inversion 1. *)
      admit.
      Search (NoDup (map _ _)).


      apply nth_error_prod_fn.



  Instance t1f : FiniteType t1.

  Instance t1f : FiniteType t1.
    unshelve econstructor.
    - destruct 1; shelve.
    - shelve.
    - intro_destruct. FiniteType_t_compute_index.
  FiniteType_t_clean_up_list.
  apply nth_error_app_l.
  apply nth_error_prod_fn.
  apply nth_error_prod_fn.
  apply nth_error_fn_dep.

  instantiate (1 := 0).
  instantiate (1 := _ :: _).
  reflexivity.

  (* apply nth_error_fn. *)
  nth_error_solve_recusive.
  nth_error_solve_recusive.
  FiniteType_t_compute_index.
  - instantiate (1 := []).
    instantiate (1 := []).
    vm_compute.
    instantiate (1 := []).
    instantiate (1 := []).




    lazymatch goal with
    | [ |- nth_error _ _ = Some ?con ] =>
      match con with
      | _ _ =>
        apply nth_error_app_l;
        apply nth_error_prod_fn;
        apply nth_error_fn

        (* let func1 := map_function_rec con in
        rewrite (nth_error_map_trans (func1));
        let func2 := prod_function_rec (con) in
        unshelve erewrite func2;
        lazymatch goal with
        | [|-  _ = _ ] => idtac
        | _ => shelve
        end;

        [> .. | simpl; reflexivity] *)




        (*
        nth_error_solve_recusive
      | _ =>
        instantiate (1 := 0);
        instantiate (1 := _ :: _);
        reflexivity *)
      end
    end.
    | instantiate (1 := []); FiniteType_t_nodup_increasing ].
    unshelve econstructor.
    - destruct 1; shelve.
    - shelve.
    - intro nm. destruct nm.
    - evar (counter : nat).
      set (count_s := seq 0 ?counter).
      instantiate (1 := S _) in (value of counter).
      cbn in count_s.
      rapply List.tl.
      match count_s with
      | ?cnt :: _ => apply List.tl


      compute in count_s.
      let a := fresh "a" in
      intro a; case a.
      exact (counter).
      instantiate (1 := S _) in (value of counter).
      let a := fresh "a" in
      intro a; case a.
      exact (counter).
      instantiate (1 := S _) in (value of counter).
      exact (counter).
      instantiate (1 := S _) in (value of counter).
      exact (counter).
    Unshelve. exact 0.
    - shelve.
    - intro a. destruct a.
      instantiate (1 := S _) in (value of counter).

      intro a. case a.
      exact (counter).
      set (counter := S counter).
      + exact (1).
      + exact (@finite_index t0 _).
      + exact _.
    - shelve.
    -

  Instance t0f : FiniteType t0 := _.
  Instance t1f : FiniteType t1 := _.
  Instance t2f : FiniteType t2 := _.
  Instance t3f : FiniteType t3 := _.

  Inductive t_recursive := A_r (x': t_recursive) (y': t0) | B_r.

  Fail Instance t_recursive_f : FiniteType t_recursive := _.

  Inductive t_mut_recursive : Set :=
  | A4 | B4 | C4 (x: t_mut2)
  with t_mut2 : Set :=
  | A5 | B5 (x1: t_mut_recursive) | C5.

  Fail Instance t_mut_recursive_f : FiniteType_t t_mut_recursive := _.
End Examples.
