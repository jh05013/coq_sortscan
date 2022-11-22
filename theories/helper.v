Require Import ssreflect.
From stdpp Require Import list sorting.

Section div.
  Lemma div_mult_sub_mod x y :
    y ≠ 0 → x `div` y * y = x - x `mod` y.
  Proof.
    intros.
  Admitted.
End div.

Section list.
  Lemma merge_sort_length {A} R l {Dec : ∀ x y : A, Decision (R x y)} :
    length (merge_sort R l) = length l.
  Proof.
  Admitted.
End list.

Section slice.
  Context {A : Type}.
  Implicit Types l : list A.

  (* slice l i j = l[i..i+len) *)
  Definition slice l i len := take len (drop i l).

  Lemma slice_minlen l i len :
    slice l i len = slice l i (len `min` (length l - i)).
  Admitted.

  Lemma slice_to_nil l i len : (i ≥ length l) → slice l i len = [].
  Proof.
    unfold slice. intros H.
  Admitted.

  Lemma slice_nil i len : slice [] i len = [].
  Proof.
  Admitted.

  Lemma slice_nil' l i : slice l i 0 = [].
  Proof. auto. Qed.

  Lemma slice_0 l len : slice l 0 len = take len l.
  Proof. auto. Qed.

  Lemma slice_length l i len :
    i + len ≤ length l → length (slice l i len) = len.
  Proof.
    intros; unfold slice. rewrite take_length drop_length. lia.
  Qed.

  Lemma slice_alternative l i len :
    slice l i len = drop i (take (i + len) l).
  Proof.
  Admitted.
(*
  Lemma slice_length l i len :
    i + len ≤ length l → length (slice l i len) = len.
  Proof.
    unfold slice. intros H1 H2.
    rewrite take_length drop_length. lia.
  Qed.

  Lemma slice_insert_right l i j k v :
    j ≤ k →
    slice (<[k:=v]> l) i j = slice l i j.
  Proof.
    unfold slice. intros H.
    destruct (decide (i ≤ j)).
    - rewrite drop_insert_le; [lia|].
      rewrite take_insert; auto. lia.
    - replace (j-i) with 0 by lia. auto.
  Qed.

  Lemma slice_extend_right l i j v :
    i ≤ j → l !! j = Some v →
    slice l i (S j) = slice l i j ++ [v].
  Proof.
    unfold slice. intros Hij Hj.
    replace (S j - i) with (S (j - i)) by lia.
    rewrite (take_S_r _ _ v); auto. rewrite lookup_drop.
    replace (i + (j - i)) with j by lia. auto.
  Qed.

  Lemma slice_shrink_right l i j v :
    i < j → l !! (j - 1) = Some v →
    slice l i j = slice l i (j - 1) ++ [v].
  Proof.
    intros. replace j with (S (j - 1)) by lia.
    erewrite slice_extend_right; eauto; try lia.
    by replace (S (j - 1)) with j by lia.
  Qed.

  Lemma slice_shrink_left l i j v :
    i < j → l !! i = Some v →
    slice l i j = v :: slice l (S i) j.
  Proof.
    unfold slice. intros Hij Hi.
    replace (j - i) with (S (j - S i)) by lia.
    erewrite drop_S; eauto.
  Qed.
*)

  Lemma take_slice l i len :
    take (i + len) l = take i l ++ slice l i len.
  Proof.
    rewrite -(take_drop i (take (i + len) l)).
    rewrite slice_alternative take_take.
    by replace (i `min` (i + len)) with i by lia.
  Qed.

  Lemma slice_cut l i len :
    l = take i l ++ slice l i len ++ drop (i + len) l.
  Proof.
    rewrite -{1} (take_drop (i + len) l).
    rewrite take_slice. by list_simplifier.
  Qed.
End slice.
