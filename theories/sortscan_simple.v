Require Import ssreflect.
From coq_sortscan Require Import helper.
From stdpp Require Import sorting list.

Context {A} (R : relation A) `{∀ x y, Decision (R x y)}
  `{!Total R, !Transitive R, !AntiSymm (=) R}.
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

  Lemma is_min_of_join_equiv L v :
    is_min_of_join L v ↔
	∀ v' l, v' ∈ l → l ∈ L → R v v'.
  Proof.
  Admitted.

  Lemma is_min_of_join_cons v' l L v :
    is_min_of_join L v → R v v' →
	is_min_of_join ((v'::l) :: L) v'.
  Proof.
	intros Hmin HR. rewrite is_min_of_join_equiv in Hmin.
	rewrite is_min_of_join_equiv. intros a la Ha Hla.
  Admitted.

  Lemma is_min_of_join_cons2 v' l L v :
    is_min_of_join L v → R v' v →
	is_min_of_join ((v'::l) :: L) v.
  Admitted.

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

  Lemma StronglySorted_cons v l :
    StronglySorted R (v :: l) → StronglySorted R l.
  Admitted.

  Lemma StronglySorted_change_head v' v l :
    StronglySorted R (v :: l) → R v' v →
	StronglySorted R (v' :: l).
  Admitted.
End sorted.

Section Phase1.
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
		| Some x =>
	        match l with
		    | [] => j
		    | y::l' => if (bool_decide (R x y)) then 0 else j
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

  Lemma gt_dec : forall a b : nat, {a > b} + {a ≤ b}.
  Proof. Admitted.

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
	- destruct (gt_dec (num_elements L') 0) as [g|g].
	  + apply IHL' in g; clear IHL'; last by inversion Hsort.
	    destruct g as [v' [l' [Hmin' Hrest']]].
		simpl. rewrite look_head_cons. erewrite look_head_Some; eauto.
		assert (is_min_of_join L' v') as Hminjoin'. { eexists. eauto. }
		destruct (bool_decide (R v' a)) eqn: ER.
		* apply bool_decide_eq_true_1 in ER.
		  exists a, l. split; auto. simpl.
		  assert (is_min_of_join ((a::l) :: L') a) as Hminjoin.
		  { eapply is_min_of_join_cons; eauto. }
		  destruct Hminjoin as [rest' Hrest'2].
		  simpl in Hrest'2. rewrite Hrest'2.
		  assert (rest' = merge_sort R (l ++ join_lists L')) as Heq.
		    2: by rewrite Heq.
		  assert (StronglySorted R rest') as SSrest'.
		  { apply (StronglySorted_cons v').
		    apply (StronglySorted_change_head _ a); auto.
			rewrite -Hrest'2. by apply StronglySorted_merge_sort. }
		  apply merge_sort_Permutation_eq,
		    Permutation_cons_inv, merge_sort_equivalent in Hrest'2.
		  rewrite (merge_sort_identity rest') in Hrest'2; auto.
		* apply bool_decide_eq_false_1, total_not in ER.
		  exists v', l'. split; auto. simpl.
		  assert (is_min_of_join ((a::l) :: L') v') as Hminjoin.
		  { eapply is_min_of_join_cons2; eauto. }
		  destruct Hminjoin as [rest' Hrest'2]. rewrite Hrest'2.
		  assert (rest' = merge_sort R (a::l ++
		    join_lists (<[find_min L':=l']> L'))
		  ) as Heq.
		    2: by rewrite Heq.
		  assert (StronglySorted R rest') as SSrest'.
		  { apply (StronglySorted_cons v'). rewrite -Hrest'2.
		    by apply StronglySorted_merge_sort. }
		  apply (StronglySorted_unique R); auto.
		    1: by apply StronglySorted_merge_sort.
		  eapply Permutation_cons_inv. instantiate (1:=v').
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
	  + simpl. rewrite look_head_cons look_head_empty; try lia.
	    exists a, l. split; auto. simpl.
		rewrite join_lists_empty; [lia|]. rewrite app_nil_r.
		assert (StronglySorted R (a :: l)) as SS by by inversion Hsort.
		repeat rewrite merge_sort_identity; auto.
		by apply StronglySorted_cons in SS.
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
	rewrite Hmin Hv1. simpl. rewrite IHn; auto.
	- admit.
	- admit.
  Admitted.
End Phase2.

Section combine.

End combine.

Section query.

End query.
