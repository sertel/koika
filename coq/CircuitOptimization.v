(*! Circuits | Local optimization of circuits !*)
Require Export Koika.Common Koika.Environments Koika.CircuitSemantics Koika.PrimitiveProperties.

Import PrimTyped CircuitSignatures.

Section CircuitOptimizer.
  Context {rule_name_t reg_t ext_fn_t: Type}.

  Context {CR: reg_t -> nat}.
  Context {CSigma: ext_fn_t -> CExternalSignature}.

  Context {rwdata: nat -> Type}.

  Notation Circuit := circuit.
  Notation circuit := (circuit (rule_name_t := rule_name_t) (rwdata := rwdata) CR CSigma).

  Context (csigma: forall f, CSig_denote (CSigma f)).

  Record local_circuit_optimizer :=
    { lco_fn :> forall {sz}, circuit sz -> circuit sz;
      lco_proof: forall {REnv: Env reg_t} (cr: REnv.(env_t) (fun idx => bits (CR idx))) {sz} (c: circuit sz),
          interp_circuit cr csigma (lco_fn c) =
          interp_circuit cr csigma c }.

  Definition lco_opt_compose
             (o1 o2: forall {sz}, circuit sz -> circuit sz) sz (c: circuit sz) :=
    o2 (o1 c).

  Definition lco_compose (l1 l2: local_circuit_optimizer) :=
    {| lco_fn := @lco_opt_compose (l1.(@lco_fn)) (l2.(@lco_fn));
       lco_proof := ltac:(abstract (intros; unfold lco_opt_compose;
                                     cbn; rewrite !lco_proof; reflexivity)) |}.

  Section Utils.
    Context {REnv: Env reg_t}.
    Context (cr: REnv.(env_t) (fun idx => bits (CR idx))).

    Lemma interp_circuit_cast {sz sz'}:
      forall (h: sz = sz') (c: circuit sz),
        interp_circuit cr csigma (rew h in c) = rew h in (interp_circuit cr csigma c).
    Proof. destruct h; reflexivity. Defined.
  End Utils.

  Section Iterated.
    Context (equivb: forall {sz}, circuit sz -> circuit sz -> bool).

    Fixpoint lco_opt_iter
             (o: forall {sz}, circuit sz -> circuit sz)
             (fuel: nat) sz (c: circuit sz) :=
      match fuel with
      | 0 => c
      | S fuel => let c' := o c in if equivb _ c c' then c else lco_opt_iter (@o) fuel _ c'
      end.

    Definition lco_iter (l: local_circuit_optimizer) (fuel: nat) :=
      {| lco_fn := lco_opt_iter (l.(@lco_fn)) fuel;
         lco_proof := ltac:(abstract (induction fuel; cbn; intros;
                                     [ | destruct equivb; try rewrite IHfuel, lco_proof ];
                                     auto)) |}.
  End Iterated.

  Fixpoint unannot {sz} (c: circuit sz) : circuit sz :=
    match c with
    | CAnnot annot c => unannot c
    | c => c
    end.

  Lemma unannot_sound {REnv cr sz} :
    forall (c: circuit sz),
      interp_circuit (REnv := REnv) cr csigma (unannot c) =
      interp_circuit (REnv := REnv) cr csigma c.
  Proof. induction c; eauto. Qed.

  Section Equiv.
    (** This pass performs the following simplifications:
          Or(c, c) -> c
          And(c, c) -> c
          Mux(_, c, c) → c1
          Mux(k, Mux(k', c2, c12), c2) → Mux(k && ~k', c12, c2 )
          Mux(k, Mux(k', c11, c2), c2) → Mux(k &&  k', c11, c2 )
          Mux(k, c1, Mux(k', c1, c22)) → Mux(k ||  k', c1 , c22)
          Mux(k, c1, Mux(k', c21, c1)) → Mux(k || ~k', c1 , c21)
          Mux(k, Mux(k, c11, c12), c2) → Mux(k, c11, c2)
          Mux(k, c1, Mux(k, c21, c22)) → Mux(k, c1, c22)
        [equivb] needs to be sound, but does not need to be complete
        (comparing two circuits can be very costly). **)
    Context (equivb: forall {sz}, circuit sz -> circuit sz -> bool).

    Context (equivb_sound: forall {REnv: Env reg_t} (cr: REnv.(env_t) (fun idx => bits (CR idx)))
                          {sz} (c1 c2: circuit sz),
                equivb _ c1 c2 = true ->
                interp_circuit cr csigma c1 = interp_circuit cr csigma c2).

    Context {REnv: Env reg_t}.
    Context (cr: REnv.(env_t) (fun idx => bits (CR idx))).

    Notation equivb_unannot c1 c2 := (equivb _ (unannot c1) (unannot c2)).

    Lemma equivb_unannot_sound :
      forall {sz} (c1 c2: circuit sz),
        equivb_unannot c1 c2 = true ->
        interp_circuit cr csigma c1 = interp_circuit cr csigma c2.
    Proof.
      intros * H%(equivb_sound _ cr).
      rewrite <- (unannot_sound c1), <- (unannot_sound c2); assumption.
    Qed.

    Definition opt_identical {sz} (c: circuit sz): circuit sz :=
      let keep_first {sz} (c1 c2: circuit sz) (c0: circuit sz) :=
          if equivb_unannot c1 c2 then c1 else c0 in
      match c in Circuit _ _ sz return circuit sz -> circuit sz with
      | CMux k c1 c2 => fun c0 => keep_first c1 c2 c0
      | CAnd c1 c2 => fun c0 => keep_first c1 c2 c0
      | COr c1 c2 => fun c0 => keep_first c1 c2 c0
      | _  => fun c0 => c0
      end c.

    Arguments Bits.and : simpl never.
    Arguments Bits.or : simpl never.

    Lemma opt_identical_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_identical c) = interp_circuit cr csigma c.
    Proof.
      destruct c; cbn; try destruct fn; try reflexivity;
        destruct equivb eqn:Hequivb; cbn;
        repeat match goal with
               | _ => progress bool_simpl
               | [  |- context[if ?x then _ else _] ] => destruct x
               | [ H: equivb_unannot _ _ = true |- _ ] => apply equivb_unannot_sound in H
               | [ H: _ = _ |- _ ] => rewrite H
               | _ => auto
               end.
    Qed.

    Definition opt_muxelim_redundant_l {sz} (c: circuit sz): circuit sz :=
      let annot {sz} (c: circuit sz) := (* CAnnot "simplified_mux" c *) c in
      match c in Circuit _ _ sz return circuit sz -> circuit sz with
      | CMux k c1 c2 =>
        fun c =>
          match unannot c1 in Circuit _ _ sz return circuit sz -> circuit sz -> circuit sz with
          | CMux k' c11 c12 =>
            fun c c2 =>
              if equivb_unannot k k' then
                (* Mux(k, Mux(k, c11, c12), c2) *)
                annot (CMux k c11 c2)
              else c
          | _ =>
            fun c c2 => c
          end c c2
      | _ => fun c => c
      end c.

    Definition opt_muxelim_redundant_r {sz} (c: circuit sz): circuit sz :=
      let annot {sz} (c: circuit sz) := (* CAnnot "simplified_mux" c *) c in
      match c in Circuit _ _ sz return circuit sz -> circuit sz with
      | CMux k c1 c2 =>
        fun c =>
          match unannot c2 in Circuit _ _ sz return circuit sz -> circuit sz -> circuit sz with
          | CMux k' c21 c22 =>
            fun c c1 =>
              if equivb_unannot k k' then
                (* Mux(k, c1, Mux(k, c21, c22)) *)
                annot (CMux k c1 c22)
              else c
          | _ =>
            fun c c1 => c
          end c c1
      | _ => fun c => c
      end c.

    Definition opt_muxelim_nested_l {sz} (c: circuit sz): circuit sz :=
      let annot {sz} (c: circuit sz) := (* CAnnot "nested_mux" c *) c in
      match c in Circuit _ _ sz return circuit sz -> circuit sz with
      | CMux k c1 c2 =>
        fun c =>
          match unannot c1 in Circuit _ _ sz return circuit sz -> circuit sz -> circuit sz with
          | CMux k' c11 c12 =>
            fun c c2 =>
              if equivb_unannot c11 c2 then
                (* Mux(k, Mux(k', c2, c12), c2) *)
                CMux (annot (CAnd k (CNot k'))) c12 c2
              else if equivb_unannot c12 c2 then
                     (* Mux(k, Mux(k', c11, c2), c2) *)
                     CMux (annot (CAnd k k')) c11 c2
                   else c
          | _ =>
            fun c c2 => c
          end c c2
      | _ => fun c => c
      end c.

    Definition opt_muxelim_nested_r {sz} (c: circuit sz): circuit sz :=
      let annot {sz} (c: circuit sz) := (* CAnnot "nested_mux" c *) c in
      match c in Circuit _ _ sz return circuit sz -> circuit sz with
      | CMux k c1 c2 =>
        fun c =>
          match unannot c2 in Circuit _ _ sz return circuit sz -> circuit sz -> circuit sz with
          | CMux k' c21 c22 =>
            fun c c1 =>
              if equivb_unannot c1 c21 then
                (* Mux(k, c1, Mux(k', c1, c22)) *)
                CMux (annot (COr k k')) c1 c22
              else if equivb_unannot c1 c22 then
                     (* Mux(k, c1, Mux(k', c21, c1)) *)
                     CMux (annot (COr k (CNot k'))) c1 c21
                   else c
          | _ =>
            fun c c1 => c
          end c c1
      | _ => fun c => c
      end c.

    Ltac mux_elim_nested_step :=
      match goal with
      | _ => reflexivity
      | _ => congruence
      | _ => progress (intros || simpl)
      | [  |- context[match ?c with _ => _ end] ] =>
        match type of c with circuit _ => destruct c eqn:? end
      | [  |- context[if equivb_unannot ?c ?c' then _ else _] ] =>
        destruct (equivb_unannot c c') eqn:?
      | [ Heq: unannot ?c = _ |- context[interp_circuit _ _ ?c] ] =>
        rewrite <- (unannot_sound c), Heq
      | [  |- context[Bits.single ?c] ] =>
        destruct c as ([ | ] & []) eqn:?
      | [ H: equivb_unannot ?c ?c' = true |- _ ] => apply equivb_unannot_sound in H
      end.

    Lemma opt_muxelim_redundant_l_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_muxelim_redundant_l c) = interp_circuit cr csigma c.
    Proof.
      unfold opt_muxelim_redundant_l; repeat mux_elim_nested_step.
    Qed.

    Lemma opt_muxelim_redundant_r_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_muxelim_redundant_r c) = interp_circuit cr csigma c.
    Proof.
      unfold opt_muxelim_redundant_r; repeat mux_elim_nested_step.
    Qed.

    Lemma opt_muxelim_nested_l_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_muxelim_nested_l c) = interp_circuit cr csigma c.
    Proof.
      unfold opt_muxelim_nested_l; repeat mux_elim_nested_step.
    Qed.

    Lemma opt_muxelim_nested_r_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_muxelim_nested_r c) = interp_circuit cr csigma c.
    Proof.
      unfold opt_muxelim_nested_r; repeat mux_elim_nested_step.
    Qed.

    Definition opt_muxelim {sz} :=
      @lco_opt_compose
        (lco_opt_compose (@opt_muxelim_redundant_l) (@opt_muxelim_redundant_r))
        (lco_opt_compose (@opt_muxelim_nested_l) (@opt_muxelim_nested_r))
        sz.

    Lemma opt_muxelim_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_muxelim c) = interp_circuit cr csigma c.
    Proof.
      intros; unfold opt_muxelim, lco_opt_compose.
      rewrite opt_muxelim_nested_r_sound, opt_muxelim_nested_l_sound,
      opt_muxelim_redundant_r_sound, opt_muxelim_redundant_l_sound;
        reflexivity.
    Qed.
  End Equiv.

  Ltac unannot_rew :=
    repeat match goal with
           | [ Heq: unannot ?c = _ |- context[interp_circuit _ _ ?c] ] =>
             rewrite <- (unannot_sound c), Heq; cbn
           end.

  Section ConstProp.
    Context {REnv: Env reg_t}.
    Context (cr: REnv.(env_t) (fun idx => bits (CR idx))).

    Definition asconst {sz} (c: circuit sz) : option (bits sz) :=
      match unannot c with
      | CConst cst => Some cst
      | c => None
      end.

    (** This pass performs the following simplifications:

        Not(1) => 0
        Not(0) => 1
        And(_, 0) | And(0, _) => 0
        And(c, 1) | And(1, c) => c
        Or(_, 1) | Or(1, _) => 1
        Or(c, 0) | Or(0, c) => c
        Mux(0, x, y) => x
        Mux(1, x, y) => y *)

    Definition isconst {sz} (c: circuit sz) (cst: bits sz) :=
      match asconst c with
      | Some cst' => beq_dec cst cst'
      | None => false
      end.

    Infix "~" := isconst.
    Notation b1 := (Bits.ones _).
    Notation b0 := (Bits.zeroes _).

    Definition opt_constprop' {sz} (c: circuit sz): circuit sz :=
      match unannot c in Circuit _ _ sz return circuit sz -> circuit sz with
      | CNot c =>
        match asconst c with
        | Some cst => fun _ => CConst (Bits.neg cst)
        | c => fun c0 => c0
        end
      | CAnd c1 c2 =>
        if c1 ~ b0 || c2 ~ b0 then fun c0 => CConst b0
        else if c1 ~ b1 then fun c0 => c2
             else if c2 ~ b1 then fun c0 => c1
                  else fun c0 => c0
      | COr c1 c2 =>
        if c1 ~ b1 || c2 ~ b1 then fun c0 => CConst b1
        else if c1 ~ b0 then fun c0 => c2
             else if c2 ~ b0 then fun c0 => c1
                  else fun c0 => c0
      | CMux select c1 c2 =>
        if select ~ b1 then fun _ => c1
        else if select ~ b0 then fun _ => c2
             else fun c0 => c0
      | c => fun c0 => c0
      end c.

    (** This pass performs the following simplification:

        Mux(c, 1, 0) => c
        Mux(c, 0, 1) => Not(c)
        Mux(c, 1, x) => Or(c, x)
        Mux(c, x, 0) => And(c, x) *)

    Notation ltrue := {| vhd := true; vtl := _vect_nil |}.
    Notation lfalse := {| vhd := false; vtl := _vect_nil |}.

    Definition opt_mux_bit1 {sz} (c: circuit sz): circuit sz :=
      match unannot c in Circuit _ _ sz return circuit sz -> circuit sz with
      | @CMux _ _ _ _ _ _ n s c1 c2 =>
        fun c0 =>
          match n return Circuit _ _ n -> Circuit _ _ n -> Circuit _ _ n -> Circuit _ _ n with
               | 1 => fun c0 c1 c2 =>
                       let annot {sz} (c: circuit sz) := (* CAnnot "optimized_mux" c *) c in
                       match asconst c1, asconst c2 with
                       | Some ltrue, Some lfalse => annot s
                       | Some ltrue, _ => annot (COr s c2)
                       | Some lfalse, Some ltrue => annot (CNot s)
                       (* FIXME: these two increase the circuit size *)
                       (* | Some lfalse, _ => annot (CAnd (CNot s) c2) *)
                       (* | _, Some ltrue => annot (COr (CNot s) c1) *)
                       | _, Some lfalse => annot (CAnd s c1)
                       | _, _ => c0
                       end
               | _ => fun c0 c1 c2 => c0
               end c0 c1 c2
      | _ => fun c0 => c0
      end c.

    Definition opt_constprop {sz} (c: circuit sz): circuit sz :=
      match sz as n return (circuit n -> circuit n) with
      | 0 => fun c => CConst Bits.nil
      | _ => fun c => opt_mux_bit1 (opt_constprop' c)
      end c.

    Arguments opt_constprop sz !c : assert.

    Lemma asconst_Some :
      forall {sz} (c: circuit sz) bs,
        asconst c = Some bs ->
        interp_circuit cr csigma c = bs.
    Proof.
      induction c; intros b Heq;
        repeat match goal with
               | _ => progress cbn in *
               | _ => discriminate
               | _ => reflexivity
               | [ H: Some _ = Some _ |- _ ] => inversion H; subst; clear H
               | [ sz: nat |- _ ] => destruct sz; try (tauto || discriminate); []
               end.
      apply IHc; eassumption.
    Qed.

    Lemma isconst_correct {sz} :
      forall (c: circuit sz) cst,
        isconst c cst = true ->
        interp_circuit cr csigma c = cst.
    Proof.
      unfold isconst; intros * Htrue; destruct (asconst c) eqn:Heq.
      - apply asconst_Some in Heq; rewrite beq_dec_iff in Htrue; congruence.
      - congruence.
    Qed.

    Arguments Bits.and : simpl never.
    Arguments Bits.or : simpl never.

    Lemma opt_constprop'_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_constprop' c) = interp_circuit cr csigma c.
    Proof.
      unfold opt_constprop'; intros; destruct (unannot c) eqn:?; cbn.
      Ltac t := match goal with
               | _ => reflexivity
               | _ => progress bool_simpl || bool_step || cleanup_step || unannot_rew || cbn in *
               | [ fn : fbits1 |- _ ] => destruct fn
               | [ fn : fbits2 |- _ ] => destruct fn
               | [  |- context[match asconst ?c with _ => _ end] ] => destruct (asconst c) as [ | ] eqn:?
               | [  |- context[if ?b then _ else _] ] =>
                 match b with context[?bs ~ ?cst] => destruct (bs ~ cst) eqn:? end
               | [ H: asconst _ = Some _ |- _ ] => apply asconst_Some in H
               | [ H: isconst _ _ = true |- _ ] => apply isconst_correct in H
               | [ H: ?x = _ |- context[?x] ] => rewrite H
               | [ H: _ \/ _ |- _ ] => destruct H
               | _ => eauto
               end.
      all: repeat t.
    Qed.

    Lemma opt_mux_bit1_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_mux_bit1 c) = interp_circuit cr csigma c.
    Proof.
      unfold opt_mux_bit1; intros; destruct (unannot c) eqn:?; cbn;
        simpl; try reflexivity; [].
      destruct sz as [ | [ | ] ]; simpl; unannot_rew; try reflexivity; [].
      destruct (asconst c0_2) as [ ([ | ] & []) | ] eqn:Hc2; try reflexivity;
        destruct (asconst c0_3) as [ ([ | ] & []) | ] eqn:Hc3;
        unannot_rew; try reflexivity.
      all: repeat
             match goal with
             | _ => progress (cbn in * || subst || bool_simpl)
             | [ H: asconst ?c = Some ?bs |- _ ] => apply (asconst_Some c bs) in H
             | [ H: interp_circuit _ _ _ = _ |- _ ] => rewrite H
             | [  |- context[interp_circuit _ _ ?c] ] => destruct (interp_circuit _ _ c) as ([ | ] & [])
             | _ => reflexivity || discriminate
             end.
    Qed.

    Lemma opt_constprop_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_constprop c) = interp_circuit cr csigma c.
    Proof.
      unfold opt_constprop; destruct sz.
      - cbn; intros.
        destruct interp_circuit; reflexivity.
      - intros; rewrite opt_mux_bit1_sound, opt_constprop'_sound; reflexivity.
    Qed.
  End ConstProp.

  Section Simplify.
    Context {REnv: Env reg_t}.
    Context (cr: REnv.(env_t) (fun idx => bits (CR idx))).

    Definition opt_simplify {sz} (c: circuit sz): circuit sz :=
      match unannot c in Circuit _ _ sz return circuit sz -> circuit sz with
      | CUnop (Slice sz offset width) c =>
        match eq_dec offset 0, eq_dec sz width with
        | left _, left pr_width => fun c0: circuit width => rew pr_width in c
        | _, _ => fun c0 => c0
        end
      | CBinop (Concat sz1 sz2) c1 c2 =>
        match eq_dec sz1 0, eq_dec sz2 0 with
        | left pr, _ => fun _ => rew <- [fun sz => circuit (sz2 + sz)] pr in rew <- plus_0_r sz2 in c2
        | _, left pr => fun _ => rew <- [fun sz => circuit (sz + sz1)] pr in (c1: circuit (0 + sz1))
        | _, _ => fun c0 => c0
        end
      | _ => fun c0 => c0
      end c.

    Lemma opt_simplify_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_simplify c) = interp_circuit cr csigma c.
    Proof.
      unfold opt_simplify; intros; destruct (unannot c) eqn:? ;
        try destruct fn;
        repeat match goal with
               | _ => reflexivity
               | _ => progress (cbn || subst || unannot_rew)
               | [  |- context[match ?x with _ => _ end] ] => destruct x
               | _ => unfold eq_rect_r; rewrite interp_circuit_cast
               | _ => rewrite vect_app_nil
               | _ => apply eq_rect_eqdec_irrel
               | _ => eauto using slice_full
               end.
    Qed.
  End Simplify.
End CircuitOptimizer.

Arguments unannot {rule_name_t reg_t ext_fn_t CR CSigma rwdata} [sz] c : assert.
Arguments unannot_sound {rule_name_t reg_t ext_fn_t CR CSigma rwdata} csigma [REnv] cr [sz] c : assert.

Arguments opt_constprop {rule_name_t reg_t ext_fn_t CR CSigma rwdata} [sz] c : assert.
Arguments opt_constprop_sound {rule_name_t reg_t ext_fn_t CR CSigma rwdata} csigma [REnv] cr [sz] c : assert.

Arguments opt_identical {rule_name_t reg_t ext_fn_t CR CSigma rwdata} equivb [sz] c : assert.
Arguments opt_identical_sound {rule_name_t reg_t ext_fn_t CR CSigma rwdata} csigma {equivb} equivb_sound [REnv] cr [sz] c : assert.

Arguments opt_muxelim {rule_name_t reg_t ext_fn_t CR CSigma rwdata} equivb [sz] c : assert.
Arguments opt_muxelim_sound {rule_name_t reg_t ext_fn_t CR CSigma rwdata} csigma {equivb} equivb_sound [REnv] cr [sz] c : assert.

Arguments opt_simplify {rule_name_t reg_t ext_fn_t CR CSigma rwdata} [sz] c : assert.
Arguments opt_simplify_sound {rule_name_t reg_t ext_fn_t CR CSigma rwdata} csigma [REnv] cr [sz] c : assert.

Arguments lco_fn {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} l [sz] c : assert.
Arguments lco_proof {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} l {REnv} cr [sz] c : assert.
Arguments lco_compose {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} l1 l2 : assert.
Arguments lco_iter {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} equivb l fuel : assert.

Section LCO.
  Context {rule_name_t reg_t ext_fn_t: Type}.

  Context {CR: reg_t -> nat}.
  Context {CSigma: ext_fn_t -> CExternalSignature}.

  Context {rwdata: nat -> Type}.
  Context (csigma: forall f, CSig_denote (CSigma f)).

  Notation lco := (@local_circuit_optimizer rule_name_t _ _ CR _ rwdata csigma).

  Definition lco_unannot : lco :=
    {| lco_fn := unannot;
       lco_proof := unannot_sound csigma |}.

  Definition lco_constprop : lco :=
    {| lco_fn := opt_constprop;
       lco_proof := opt_constprop_sound csigma |}.

  Definition lco_identical equivb equivb_sound : lco :=
    {| lco_fn := opt_identical equivb;
       lco_proof := opt_identical_sound csigma equivb_sound |}.

  Definition lco_muxelim equivb equivb_sound : lco :=
    {| lco_fn := opt_muxelim equivb;
       lco_proof := opt_muxelim_sound csigma equivb_sound |}.

  Definition lco_simplify : lco :=
    {| lco_fn := opt_simplify;
       lco_proof := opt_simplify_sound csigma |}.

  Definition lco_all equivb equivb_sound : lco :=
    lco_compose lco_constprop
                (lco_compose (lco_identical equivb equivb_sound)
                             (lco_compose (lco_muxelim equivb equivb_sound)
                                          lco_simplify)).

  Definition lco_all_iterated equivb equivb_sound fuel : lco :=
    lco_iter equivb (lco_all equivb equivb_sound) fuel.
End LCO.

Arguments lco_unannot {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} : assert.
Arguments lco_constprop {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} : assert.
Arguments lco_identical {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} {equivb} equivb_sound : assert.
Arguments lco_muxelim {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} {equivb} equivb_sound : assert.
Arguments lco_simplify {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} : assert.
Arguments lco_all {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} {equivb} equivb_sound : assert.
Arguments lco_all_iterated {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} {equivb} equivb_sound fuel : assert.
