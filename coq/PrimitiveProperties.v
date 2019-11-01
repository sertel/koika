Require Import Coq.Lists.List.
Require Import Koika.Primitives.

Import BitFuns.
Import ListNotations.

Ltac min_t :=
  repeat match goal with
         | [ |- context[Min.min ?x ?y] ] =>
           first [rewrite (Min.min_l x y) by min_t | rewrite (Min.min_r x y) by min_t ]
         | _ => omega
         end.

Lemma part_end :
  forall sz sz' (v : bits (sz + sz')),
    part sz sz' v = vect_skipn_plus sz v.
Proof.
  intros.
  apply vect_to_list_inj.
  unfold part, vect_skipn_plus, vect_extend_end_firstn, vect_extend_end.
  autorewrite with vect_to_list.
  min_t; rewrite Nat.sub_diag by omega; cbn.
  rewrite app_nil_r.
  rewrite firstn_skipn.
  rewrite firstn_all2 by (rewrite vect_to_list_length; reflexivity).
  reflexivity.
Qed.

Lemma part_front :
  forall n sz (v: bits (n + sz)) offset width,
    offset + width <= n ->
    part offset width v =
    part offset width (vect_firstn_plus n v).
Proof.
  intros.
  apply vect_to_list_inj.
  unfold part, vect_extend_end_firstn, vect_extend_end, vect_firstn_plus.
  autorewrite with vect_to_list.
  rewrite skipn_firstn, firstn_firstn.
  min_t; reflexivity.
Qed.

Lemma part_correct_le :
  forall fields idx,
    struct_fields_sz (skipn (S (index_to_nat idx)) fields) + type_sz (snd (List_nth fields idx)) <=
    struct_fields_sz fields.
Proof.
  intros.
  change (type_sz (snd (List_nth fields idx))) with (struct_fields_sz [List_nth fields idx]).
  rewrite plus_comm; setoid_rewrite <- list_sum_app; rewrite <- map_app; cbn [List.app].
  rewrite List_nth_skipn_cons_next.
  rewrite <- skipn_map.
  apply list_sum_skipn_le.
Qed.

Lemma part_subst_end :
  forall sz0 sz (bs0: bits (sz0 + sz)) (bs: bits sz),
    part_subst sz0 sz bs0 bs = Bits.app bs (fst (Bits.split bs0)).
Proof.
  unfold Bits.split; intros; rewrite vect_split_firstn_skipn; cbn.
  apply vect_to_list_inj.
  unfold part_subst, vect_skipn_plus, vect_firstn_plus, vect_extend_end_firstn, vect_extend_end.
  autorewrite with vect_to_list.
  rewrite !firstn_app.
  rewrite firstn_length_le by (rewrite vect_to_list_length; omega).
  rewrite !minus_plus, vect_to_list_length, Nat.sub_diag; cbn.
  rewrite firstn_firstn by omega; min_t.
  rewrite (firstn_all2 (n := sz)) by (rewrite vect_to_list_length; omega).
  rewrite app_nil_r; reflexivity.
Qed.

Lemma part_subst_front :
  forall sz0 sz width (bs0: bits (sz0 + sz)) (bs: bits width) offset,
    offset + width <= sz0 ->
    part_subst offset width bs0 bs =
    Bits.app (vect_skipn_plus sz0 bs0) (part_subst offset width (vect_firstn_plus sz0 bs0) bs).
Proof.
  clear.
  intros.
  apply vect_to_list_inj;
    unfold part_subst, vect_skipn_plus, vect_firstn_plus, vect_extend_end_firstn, vect_extend_end.
  autorewrite with vect_to_list.
  rewrite !firstn_app.
  rewrite firstn_length_le by (rewrite vect_to_list_length; omega).
  rewrite vect_to_list_length; cbn.
  rewrite !firstn_firstn; repeat min_t.
  rewrite firstn_length_le by (rewrite vect_to_list_length; omega).
  rewrite <- !app_assoc.
  rewrite skipn_firstn, firstn_firstn.
  min_t.
  rewrite !(firstn_all2 (vect_to_list bs)) by (rewrite vect_to_list_length; omega).
  replace (sz0 + sz - offset - width) with (sz0 + sz - (offset + width)) by omega.
  replace (sz0 - offset - width) with (sz0 - (offset + width)) by omega.
  rewrite <- !skipn_firstn.
  rewrite (firstn_all2 (n := sz0 + sz)) by (rewrite vect_to_list_length; omega).
  rewrite <- skipn_app by (rewrite firstn_length, vect_to_list_length; min_t; omega).
  rewrite List.firstn_skipn.
  reflexivity.
Qed.

Lemma bits_eq_of_value:
  forall {tau: type} (a1 a2: tau),
    bits_eq (bits_of_value a1) (bits_of_value a2) =
    (if eq_dec a1 a2 then Ob~1 else Ob~0).
Proof.
  unfold bits_eq;
    intros; repeat destruct eq_dec;
      try match goal with
          | [ H: bits_of_value _ = bits_of_value _ |- _ ] => apply bits_of_value_inj in H
          end; subst; congruence.
Qed.

Lemma get_field_bits_part:
  forall {sig} (f : struct_index sig) (a : type_denote (struct_t sig)),
    part (field_offset_right sig f) (field_sz sig f) (bits_of_value a) =
    bits_of_value (get_field (struct_fields sig) a f).
Proof.
  intro sig;
    repeat (simpl; unfold struct_index, field_type, field_sz, field_offset_right).
  induction (struct_fields sig) as [ | (nm & tau) l ]; simpl.
  * destruct f.
  * destruct f as [ | f], a; cbn in *; intros.
    -- rewrite part_end, vect_skipn_plus_app.
       reflexivity.
    -- rewrite <- IHl.
       rewrite part_front, vect_firstn_plus_app by apply part_correct_le.
       reflexivity.
Qed.

Lemma subst_field_bits_part_subst:
  forall {sig} (f : struct_index sig) (a1 : type_denote (struct_t sig)) (a2 : field_type sig f),
    part_subst (field_offset_right sig f) (field_sz sig f) (bits_of_value a1) (bits_of_value a2) =
    bits_of_value (tau := struct_t _) (subst_field (struct_fields sig) a1 f a2).
Proof.
  intro sig;
    repeat (simpl; unfold struct_index, field_type, field_sz, field_offset_right).
  induction (struct_fields sig) as [ | (nm & tau) l ]; simpl.
  * destruct f.
  * destruct f as [ | f], a1; cbn in *; intros.
    -- rewrite part_subst_end, vect_split_app.
       reflexivity.
    -- rewrite <- IHl.
       rewrite part_subst_front, vect_firstn_plus_app, vect_skipn_plus_app by apply part_correct_le.
       reflexivity.
Qed.
