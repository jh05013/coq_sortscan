Require Import ssreflect.
From coq_sortscan Require Import helper ops.
From stdpp Require Import sorting list.

Context (R : relation nat) `{∀ x y, Decision (R x y)}.
Implicit Types data : Data.

Section Phase1.
  Program Definition mem_sort data (len : nat) :=
    let M := mem data in
    {| disk := disk data;
      mem := merge_sort R (take len M) ++ drop len M |}.
  Next Obligation. intros. apply (disk_length data). Qed.
  Next Obligation.
    intros. rewrite app_length merge_sort_length
      take_length drop_length (mem_length data). lia.
  Qed.

  (* sort disk[i..i+M) *)
  Definition sort_disk data (i len : nat) :=
    let data' := read_range_disk data i len 0 in
    write_range_disk (mem_sort data' len) 0 len i.
  
  Definition phase1_single data (c : nat) :=
    let i := c * CAP_MEM in
    sort_disk data i (CAP_MEM `min` (CAP_DISK - i)).

  Fixpoint phase1_loop data (c : nat) :=
    match c with
    | O => phase1_single data 0
    | S c' => phase1_single (phase1_loop data c') (S c')
    end.

  Definition phase1 data :=
    phase1_loop data (CAP_DISK / CAP_MEM).

  Lemma mem_sort_take data len :
    take len (mem (mem_sort data len)) =
      merge_sort R (take len (mem data)).
  Admitted.
(*
  Lemma mem_sort_app l l' len :
    length l = len →
    mem_sort (l ++ l') len = merge_sort R l ++ l'.
  Admitted.
*)
  Lemma sort_disk_sorted data i len :
    len ≤ CAP_MEM → i + len ≤ CAP_DISK →
    slice (disk (sort_disk data i len)) i len =
      merge_sort R (slice (disk data) i len).
  Proof.
    intros Hmem Hdisk.
    rewrite write_range_disk_slice; auto.
    rewrite slice_0 mem_sort_take -slice_0.
    by rewrite read_range_disk_slice.
  Qed.

  Lemma sort_disk_perm data i len :
    len ≤ CAP_MEM → i + len ≤ CAP_DISK →
    disk (sort_disk data i len) ≡ₚ disk data.
  Proof.
    intros. unfold sort_disk.
    assert (length (slice (disk data) i len) = len) as Hlen.
      { rewrite slice_length; auto. by rewrite (disk_length data). }
    rewrite write_range_disk_eq. simpl.
    rewrite read_range_disk_disk slice_0.
    rewrite read_range_disk_eq take_0; simpl.
    rewrite -{2 5} Hlen take_app drop_app.
    assert (length (merge_sort R (slice (disk data) i len)) = len) as HlenM.
      { rewrite merge_sort_length slice_length; auto.
        by rewrite (disk_length data). }
    rewrite -{1} HlenM take_app.
    rewrite {4} (slice_cut (disk data) i len).
    do 2 (apply Permutation_app; auto).
    apply merge_sort_Permutation.
  Qed.

  Lemma phase1_single_spec data c :
    Transitive R → Total R →
    c ≤ CAP_DISK / CAP_MEM →
    let data' := phase1_single data c in
    disk data' ≡ₚ disk data ∧
    StronglySorted R (slice (disk data') (c * CAP_MEM) CAP_MEM).
  Proof.
    unfold phase1_single. intros TRANS TOT Hc.
    assert (c * CAP_MEM +
      CAP_MEM `min` (CAP_DISK - c * CAP_MEM)
      ≤ CAP_DISK
    ) as Hcle.
    { assert (c * CAP_MEM ≤ CAP_DISK); try lia.
      trans (CAP_DISK `div` CAP_MEM * CAP_MEM).
      - by apply PeanoNat.Nat.mul_le_mono_r.
      - rewrite div_mult_sub_mod; try lia. by unfold CAP_MEM.
    }
    split.
    - apply sort_disk_perm; lia.
    - rewrite slice_minlen disk_length.
      rewrite sort_disk_sorted; try lia.
      by apply StronglySorted_merge_sort.
  Qed.

  Lemma phase1_loop_spec data c :
    Transitive R → Total R →
    c ≤ CAP_DISK / CAP_MEM →
    let data' := phase1_loop data c in
    disk data' ≡ₚ disk data ∧
    ∀ i, i ≤ c → StronglySorted R (slice (disk data') (i * CAP_MEM) CAP_MEM).
  Proof.
    intros TRANS TOT Hc.
    induction c; intros.
    - assert (disk data' ≡ₚ disk data ∧
        StronglySorted R (slice (disk data') 0 CAP_MEM)
      ) as [HP HSS].
      { apply phase1_single_spec; auto. }
      split; auto. intros. destruct i; auto. lia.
    - simpl in data'.
      assert (
        disk data' ≡ₚ disk (phase1_loop data c)
        ∧ StronglySorted R (slice (disk data') (S c * CAP_MEM) CAP_MEM)
      ) as [HP HSS].
        { apply phase1_single_spec; auto. }
      assert (c ≤ CAP_DISK `div` CAP_MEM) as Hc' by lia.
      apply IHc in Hc' as [HP0 HSS0].
      split. { etrans; eauto. }
      intros. destruct (decide (i ≤ c)).
      + apply HSS0 in l. unfold data'. admit.
      + assert (i = S c) by lia. by subst.
  Admitted.

  Lemma phase1_spec data :
    Transitive R → Total R →
    let data' := phase1 data in
    disk data' ≡ₚ disk data ∧
    ∀ i, StronglySorted R (slice (disk data') (i * CAP_MEM) CAP_MEM).
  Proof.
    intros TRANS TOT.
    destruct (phase1_loop_spec data (CAP_DISK / CAP_MEM))
      as [HP HSS]; auto.
    intros. split. { apply HP. }
    intros. destruct (decide (i ≤ CAP_DISK `div` CAP_MEM)).
    - by apply HSS.
    - rewrite slice_to_nil. 2: constructor. rewrite disk_length.
      assert (i*CAP_MEM ≥ S (CAP_DISK `div` CAP_MEM)*CAP_MEM) by admit.
      assert (S (CAP_DISK `div` CAP_MEM)*CAP_MEM ≥ CAP_DISK) by admit.
      lia.
  Admitted.
End Phase1.

Section Phase2.
  Program Definition fill_zero data :=
    {| disk := disk data;
      mem := replicate CAP_MEM 0 |}.
  Next Obligation. intros. apply disk_length. Qed.
  Next Obligation. intros. apply replicate_length. Qed.

  Definition 

  Definition find_min data :=
    0.

  Fixpoint phase2_loop data (rem : nat) :=
    match rem with
    | O => []
    | S rem' =>
        let chunk_id := find_min data in
        let i := (CAP_MEM * chunk_id) + read_mem data chunk_id in
        let data' := read_disk data i (CAP_MEM - 1) in
        let v := read_mem data' (CAP_MEM - 1) in
        let data'' := write_const_mem data' chunk_id (S i) in
        v :: phase2_loop data'' rem'
    end.

  Definition phase2 data := phase2_loop data CAP_DISK.
End Phase2.
