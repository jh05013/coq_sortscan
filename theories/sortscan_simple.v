Require Import ssreflect.
From coq_sortscan Require Import helper.
From stdpp Require Import sorting list.

Context {A} (R : relation A) `{∀ x y, Decision (R x y)}
  `{!Total R, !Transitive R, !AntiSymm (=) R, !Reflexive R}.
Implicit Type (mem : list A).
Implicit Type (L : list (list A)).

Section sorted.
  Inductive is_sorted_lists : list (list A) → Prop :=
  | isl_nil : is_sorted_lists ([] : list (list A))
  | isl_S (l : list A) (L' : list (list A)) :
      StronglySorted R l → is_sorted_lists L' →
      is_sorted_lists (l :: L').

  Fixpoint join_lists L :=
    match L with
    | [] => []
    | l::L' => l ++ join_lists L'
    end.

  Definition is_min_of_join L v :=
    ∃ l, merge_sort R (join_lists L) = v :: l.

  Lemma join_lists_pop_Permutation L i v l :
    L !! i = Some (v::l) →
    v :: join_lists (<[i:=l]> L) ≡ₚ join_lists L.
  Proof.
    intros Hi.
    assert (i < length L) as Hlt. by eapply lookup_lt_Some.
    destruct L. { inversion Hlt. }
    revert i l0 L v l Hi Hlt. induction i; intros.
    - simpl in *. by inversion Hi.
    - simpl in *. destruct L. { inversion Hlt. lia. }
      simpl in *. apply IHi in Hi; [|lia].
      etrans. 1: apply Permutation_middle.
      by apply Permutation_app.
  Qed.

  Lemma merge_sort_Permutation_eq l1 l2 :
    merge_sort R l1 = l2 → l1 ≡ₚ l2.
  Proof.
    intros. rewrite -H0. symmetry. apply merge_sort_Permutation.
  Qed.

  Lemma merge_sort_equivalent `{!Total R, !Transitive R} l1 l2 :
    l1 ≡ₚ l2 → merge_sort R l1 = merge_sort R l2.
  Proof.
    intros HP. apply (StronglySorted_unique R);
      try by apply StronglySorted_merge_sort.
    trans l1. 1: apply merge_sort_Permutation.
    trans l2; auto. symmetry. apply merge_sort_Permutation.
  Qed.

  Lemma merge_sort_identity `{!Total R, !Transitive R} l :
    StronglySorted R l → merge_sort R l = l.
  Proof.
    intros HP. apply (StronglySorted_unique R); auto.
    - apply StronglySorted_merge_sort; auto.
    - apply merge_sort_Permutation.
  Qed.

  Lemma merge_sort_criterion l1 l2 :
    l1 ≡ₚ l2 → StronglySorted R l2 →
    merge_sort R l1 = l2.
  Proof.
    intros HP SS.
    replace l2 with (merge_sort R l2).
    - by apply merge_sort_equivalent.
    - by apply merge_sort_identity.
  Qed.

  Lemma is_min_of_join_cons `{!Total R, !Transitive R, !Reflexive R}
  v' l L v :
    is_sorted_lists ((v'::l) :: L) →
    is_min_of_join L v → R v' v →
    is_min_of_join ((v'::l) :: L) v'.
  Proof.
    intros SS [rest Hmin] HR.
    exists (merge_sort R (l ++ join_lists L)). simpl.
    apply merge_sort_criterion.
    - constructor. symmetry. apply merge_sort_Permutation.
    - constructor. { by apply StronglySorted_merge_sort. }
      eapply (Forall_Permutation (R v') _ _ (l ++ join_lists L)).
      { symmetry. apply merge_sort_Permutation. }
      inversion SS; subst. inversion H2; subst.
      assert (StronglySorted R (v :: rest)) as SSvr.
      { rewrite -Hmin. by apply StronglySorted_merge_sort. }
      apply Forall_app; split; auto.
      apply (Forall_impl (R v)).
      + inversion SSvr; subst.
        eapply (Forall_Permutation (R v) _ _ (v :: rest)).
        { rewrite -Hmin. apply merge_sort_Permutation. }
        by constructor.
      + intros. by trans v.
    Unshelve. all: unfold pointwise_relation; auto.
  Qed.

  Lemma is_min_of_join_cons2 `{!Total R, !Transitive R, !Reflexive R}
  v' l L v :
    is_sorted_lists ((v'::l) :: L) →
    is_min_of_join L v → R v v' →
    is_min_of_join ((v'::l) :: L) v.
  Proof.
    intros SS [rest Hmin] HR.
    exists (merge_sort R (v' :: l ++ rest)). simpl.
    apply merge_sort_criterion.
    - trans (v :: v' :: l ++ rest).
      2: { constructor. symmetry. apply merge_sort_Permutation. }
      apply merge_sort_Permutation_eq in Hmin.
      trans (v' :: l ++ v :: rest).
      1: { constructor. apply Permutation_app; auto. }
      rewrite Permutation_swap. constructor.
      by rewrite Permutation_middle.
    - constructor. { by apply StronglySorted_merge_sort. }
      eapply (Forall_Permutation (R v) _ _ (v' :: l ++ rest)).
      { symmetry. apply merge_sort_Permutation. }
      constructor; auto.
      inversion SS; subst. inversion H2; subst.
      assert (StronglySorted R (v :: rest)) as SSvr.
      { rewrite -Hmin. by apply StronglySorted_merge_sort. }
      apply Forall_app; split.
      + apply (Forall_impl (R v')); auto. intros; by trans v'.
      + inversion SSvr; subst. auto.
    Unshelve. all: unfold pointwise_relation; auto.
  Qed.
End sorted.

Section Phase1.
  Fixpoint phase1_loop mem M (z : nat) :=
    match z with
    | O => ([] : list (list A))
    | S z' => (merge_sort R (take M mem)) ::
        phase1_loop (drop M mem) M z'
    end.

  Definition phase1 mem M :=
    phase1_loop mem M (S (length mem)).

  Lemma phase1_loop_correct `{!Transitive R, !Total R} mem M z :
    0 < M → length mem ≤ M * z →
    let L := phase1_loop mem M z in
    is_sorted_lists L ∧ join_lists L ≡ₚ mem.
  Proof.
    revert mem. simpl.
    induction z; intros mem HM Hz; simpl; split.
    - constructor.
    - destruct mem; auto. simpl in Hz. lia.
    - constructor.
      + by apply StronglySorted_merge_sort.
      + apply IHz; auto. rewrite drop_length. lia.
    - assert (mem = take M mem ++ drop M mem) as HTD
        by by rewrite take_drop.
      rewrite {3} HTD. apply Permutation_app.
      + apply merge_sort_Permutation.
      + apply IHz; auto. rewrite drop_length. lia.
  Qed.

  Lemma phase1_correct mem M :
    0 < M →
    let L := phase1 mem M in
    is_sorted_lists L ∧ join_lists L ≡ₚ mem.
  Proof.
    simpl. unfold phase1. intros HM.
    apply phase1_loop_correct; auto.
    destruct M; lia.
  Qed.
End Phase1.

Section Phase2.
  Fixpoint num_elements L :=
    match L with
    | [] => 0
    | l::L' => length l + num_elements L'
    end.

  Definition look_head L i :=
    match L !! i with
    | None | Some [] => None
    | Some (x::l) => Some x
    end.

  Fixpoint find_min L :=
    match L with
    | [] => 0
    | l::L' =>
        let j := S (find_min L') in
        match look_head L j with
        | None => 0
        | Some xj =>
            match l with
            | [] => j
            | x0::l' => if (bool_decide (R x0 xj)) then 0 else j
            end
        end
    end.

  Fixpoint phase2_loop {V} L (f : A → V → V) (v : V) (z : nat) :=
    match z with
    | O => v
    | S z' =>
        let i := find_min L in
        match L !! i with
        | None | Some [] => v
        | Some (x::l) => f x (phase2_loop (<[i:=l]> L) f v z')
        end
    end.

  Definition phase2 {V} L (f : A → V → V) (start : V) :=
    phase2_loop L f start (num_elements L).

  (* proof *)

  Lemma join_lists_empty L :
    num_elements L = 0 → join_lists L = [].
  Proof.
    induction L; auto; intros.
    simpl in *. assert (length a = 0) by lia.
    destruct a; auto. simpl in H1. lia.
  Qed.

  Lemma look_head_empty L i :
    num_elements L = 0 → look_head L i = None.
  Proof.
    revert i. induction L; auto; intros.
    simpl in *. assert (length a = 0) by lia.
    destruct a.
    - rewrite H1 /= in H0. destruct i; auto.
      by apply (IHL i) in H0.
    - simpl in H1. lia.
  Qed.

  Lemma look_head_cons l L i :
    look_head (l :: L) (S i) = look_head L i.
  Proof. auto. Qed.

  Lemma look_head_Some L i v l :
    L !! i = Some (v :: l) → look_head L i = Some v.
  Proof. intros H. unfold look_head. by rewrite H. Qed.

  Lemma phase2_first_correct `{!Transitive R, !Total R} L:
    num_elements L > 0 → is_sorted_lists L →
    let i := find_min L in
    ∃ v l,
      L !! i = Some (v :: l) ∧
      merge_sort R (join_lists L) =
        v :: merge_sort R (join_lists (<[i:=l]> L)).
  Proof.
    intros Hn Hsort. simpl.
    induction L as [|l L']. { inversion Hn. }
    destruct l.
    - apply IHL' in Hn as IHL; clear IHL'; last by inversion Hsort.
      destruct IHL as [v [l [Hmin Hrest]]].
      simpl. rewrite look_head_cons. erewrite look_head_Some; eauto.
    - rename a into v0.
      destruct (le_gt_dec (num_elements L') 0) as [g|g].
      + simpl. rewrite look_head_cons look_head_empty; try lia.
        exists v0, l. split; auto. simpl.
        rewrite join_lists_empty; [lia|]. rewrite app_nil_r.
        assert (StronglySorted R (v0 :: l)) as SS by by inversion Hsort.
        repeat rewrite merge_sort_identity; auto.
        by inversion SS.
      + apply IHL' in g; clear IHL'; last by inversion Hsort.
        destruct g as [vj [l' [Hmin' Hrest']]].
        simpl. rewrite look_head_cons. erewrite look_head_Some; eauto.
        assert (is_min_of_join L' vj) as Hminjoin'. { eexists. eauto. }
        destruct (bool_decide (R v0 vj)) eqn: ER.
        * apply bool_decide_eq_true_1 in ER.
          exists v0, l. split; auto. simpl.
          assert (is_min_of_join ((v0::l) :: L') v0) as Hminjoin.
          { eapply is_min_of_join_cons; eauto. }
          destruct Hminjoin as [rest' Hrest'2].
          simpl in Hrest'2. rewrite Hrest'2.
          assert (rest' = merge_sort R (l ++ join_lists L')) as Heq.
            2: by rewrite Heq.
          assert (StronglySorted R rest') as SSrest'.
          { assert (StronglySorted R (v0 :: rest')).
            - rewrite -Hrest'2. by apply StronglySorted_merge_sort.
            - by inversion H0. }
          apply merge_sort_Permutation_eq,
            Permutation_cons_inv, merge_sort_equivalent in Hrest'2.
          rewrite (merge_sort_identity rest') in Hrest'2; auto.
        * apply bool_decide_eq_false_1, total_not in ER.
          exists vj, l'. split; auto. simpl.
          assert (is_min_of_join ((v0::l) :: L') vj) as Hminjoin.
          { eapply is_min_of_join_cons2; eauto. }
          destruct Hminjoin as [rest' Hrest'2]. rewrite Hrest'2.
          assert (rest' = merge_sort R (v0::l ++
            join_lists (<[find_min L':=l']> L'))
          ) as Heq.
            2: by rewrite Heq.
          assert (StronglySorted R rest') as SSrest'.
          { assert (StronglySorted R (vj :: rest')).
            - rewrite -Hrest'2. by apply StronglySorted_merge_sort.
            - by inversion H0. }
          apply (StronglySorted_unique R); auto.
            1: by apply StronglySorted_merge_sort.
          eapply Permutation_cons_inv. instantiate (1:=vj).
          rewrite -Hrest'2.
          etrans. 1: apply merge_sort_Permutation.
          etrans. 2: apply Permutation_cons. 2: eauto.
          2: symmetry; apply merge_sort_Permutation.
          etrans. 1: {
            symmetry; apply (join_lists_pop_Permutation
              _ (S (find_min L'))
            ). by rewrite lookup_cons.
          }
          auto.
    Qed.

  Lemma sorted_lists_pop L n i v l :
    is_sorted_lists L → S n = num_elements L →
    L !! i = Some (v :: l) →
    is_sorted_lists (<[i:=l]> L) ∧ n = num_elements (<[i:=l]> L).
  Proof.
    revert L n v l. induction i; intros L n v l SS Hn Hi.
    - destruct L; inversion Hi. subst; simpl. clear Hi.
      inversion SS; subst. inversion H2; subst.
      split; auto. by constructor.
    - destruct L; inversion Hi. clear Hi.
      inversion SS; subst.
      remember (num_elements L) as m.
      destruct m.
      { exfalso. clear IHi. revert i H1. induction L; intros.
        - inversion H1.
        - simpl in Heqm. destruct a; simpl in Heqm; try lia.
          inversion H4; subst. destruct i; inversion H1.
          eapply IHL; eauto. by constructor.
      }
      eapply IHi in H4 as [SSm Hm]; eauto.
      split.
      + constructor; auto.
      + simpl in *. rewrite -Heqm in Hn. rewrite -Hm. lia.
  Qed.

  Lemma phase2_correct {V} L (f : A → V → V) (start : V) :
    is_sorted_lists L →
    phase2 L f start = foldr f start (merge_sort R (join_lists L)).
  Proof.
    intros Hsort. unfold phase2.
    remember (num_elements L) as n. revert L start Hsort Heqn.
    induction n; intros.
    { by rewrite join_lists_empty. }
    simpl. destruct (phase2_first_correct L) as [v [l Hv]].
    all: try lia; auto.
    destruct Hv as [Hmin Hv1].
    eapply sorted_lists_pop in Hsort; eauto. destruct Hsort.
    rewrite Hmin Hv1. simpl. rewrite IHn; auto.
  Qed.
End Phase2.

Section combine.
  Definition TPMMS {V} mem M (f : A → V → V) (start : V) :=
    phase2 (phase1 mem M) f start.

  Lemma TPMMS_correct {V} mem M (f : A → V → V) (start : V) :
    0 < M →
    TPMMS mem M f start = foldr f start (merge_sort R mem).
  Proof.
    intros HM. unfold TPMMS.
    apply (phase1_correct mem) in HM as [ISS HP].
    apply (phase2_correct _ f start) in ISS.
    rewrite ISS.
    replace (merge_sort R (join_lists (phase1 mem M)))
      with (merge_sort R mem); auto.
    apply merge_sort_equivalent. by symmetry.
  Qed.
End combine.
