Require Import ssreflect.
From coq_sortscan Require Import helper ops.
From stdpp Require Import sorting list.

Context (R : relation nat)
  `{∀ x y, Decision (R x y)}.
Implicit Types disk mem : list nat.

Section Phase1.
  Definition mem_sort mem (len : nat) :=
    merge_sort R (take len mem) ++ drop len mem.

  (* sort disk[i..i+M) *)
  Definition sort_disk disk mem (i len : nat) :=
    let mem' := read_range_disk disk mem i len 0 in
    let smem' := mem_sort mem' len in
    (write_range_disk disk smem' 0 len i, smem').
  
  Definition phase1_single disk mem (c : nat) :=
    let M := length mem in
    let i := c * M in
    sort_disk disk mem i (M `min` (length disk - i)).

  Fixpoint phase1_loop disk mem (c : nat) :=
    let (disk', mem') := phase1_single disk mem c in
    match c with
    | O => (disk', mem')
    | S c' => phase1_loop disk' mem' c'
    end.

  Definition phase1 disk mem :=
    phase1_loop disk mem (length disk / length mem).

  Lemma mem_sort_length mem len :
    len ≤ length mem → length (mem_sort mem len) = length mem.
  Proof.
    intros H. unfold mem_sort.
  Admitted.

  Lemma mem_sort_take mem len :
    take len (mem_sort mem len) = merge_sort R (take len mem).
  Admitted.

  Lemma mem_sort_app l l' len :
    length l = len →
    mem_sort (l ++ l') len = merge_sort R l ++ l'.
  Admitted.

  Lemma sort_disk_sorted disk mem i len :
    len ≤ length mem → i + len ≤ length disk →
    let disk' := (sort_disk disk mem i len).1 in
    slice disk' i len = merge_sort R (slice disk i len).
  Proof.
    simpl. intros Hmem Hdisk.
    rewrite write_range_disk_lookup; auto.
    { rewrite mem_sort_length; rewrite read_range_disk_length; auto. }
    rewrite slice_0 mem_sort_take -slice_0.
    by rewrite read_range_disk_slice.
  Qed.

  Lemma sort_disk_perm disk mem i len :
    len ≤ length mem → i + len ≤ length disk →
    (sort_disk disk mem i len).1 ≡ₚ disk.
  Proof.
    intros. simpl.
    assert (length (slice disk i len) = len) as Hlen
      by by rewrite slice_length.
    rewrite read_range_disk_eq take_0; simpl.
    rewrite mem_sort_app; auto.
    unfold write_range_disk. rewrite read_range_disk_eq.
    rewrite {4} (slice_cut disk i len).
    do 2 (apply Permutation_app; auto).
    rewrite slice_0.
    assert (len = length (merge_sort R (slice disk i len))) as HMS.
    { rewrite -{1} Hlen. apply Permutation_length.
      symmetry. apply merge_sort_Permutation. }
    rewrite {1} HMS. rewrite take_app.
    apply merge_sort_Permutation.
  Qed.

  Lemma sort_disk_length disk mem i len :
    length (sort_disk disk mem i len).1 = length disk.
  Proof.
    simpl. unfold write_range_disk.
    by rewrite read_range_disk_length.
  Qed.

  Lemma phase1_single_spec disk mem c :
    length mem ≠ 0 → Transitive R → Total R →
    let M := length mem in
    c ≤ length disk / M →
    let disk' := (phase1_single disk mem c).1 in
    disk' ≡ₚ disk ∧
    StronglySorted R (slice disk' (c * M) M).
  Proof.
    unfold phase1_single. intros Hmemnil TRANS TOT Hc.
    assert (c * length mem +
      length mem `min` (length disk - c * length mem)
      ≤ length disk
    ) as Hcle.
    { assert (c * length mem ≤ length disk); try lia.
      trans (length disk `div` length mem * length mem).
      - by apply PeanoNat.Nat.mul_le_mono_r.
      - rewrite div_mult_sub_mod; lia.
    }
    split.
    - apply sort_disk_perm; lia.
    - rewrite slice_minlen sort_disk_length.
      rewrite sort_disk_sorted; try lia.
      by apply StronglySorted_merge_sort.
  Qed.

  Lemma phase1_loop_spec disk mem c :
    length mem ≠ 0 → Transitive R → Total R →
    let M := length mem in
    let disk' := (phase1_loop disk mem c).1 in
    disk' ≡ₚ disk ∧
    ∀ i, i ≤ c → StronglySorted R (slice disk' (i * M) M).
  Admitted.

  Lemma phase1_spec (disk mem : list nat) :
    length mem ≠ 0 → Transitive R → Total R →
    let M := length mem in
    let disk' := (phase1 disk mem).1 in
    disk' ≡ₚ disk ∧
    ∀ i, StronglySorted R (slice disk' (i * M) M).
  Proof.
    intros Hmemnil TRANS TOT.
    destruct (phase1_loop_spec disk mem (length disk / length mem))
      as [HP HSS]; auto.
    intros. split. { apply HP. }
    intros. destruct (decide (i ≤ length disk `div` length mem)).
    - by apply HSS.
    - rewrite slice_to_nil. 2: constructor.
      replace (length disk') with (length disk) by admit.
      replace (length mem) with M in n; auto.
      assert (i*M ≥ S (length disk `div` M)*M) by admit.
      assert (S (length disk `div` M)*M ≥ length disk) by admit.
      lia.
  Admitted.
End Phase1.

Section Phase2.

End Phase2.
