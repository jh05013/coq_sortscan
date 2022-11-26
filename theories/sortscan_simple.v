Require Import ssreflect.
From coq_sortscan Require Import helper.
From stdpp Require Import sorting list.

Context {A} (R : relation A) `{∀ x y, Decision (R x y)}.
Implicit Type (L : list (list A)).

Section Phase1.
End Phase1.

Section Phase2.
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

  Lemma gt_dec : forall a b : nat, {a > b} + {a ≤ b}.
  Proof. Admitted.

  Lemma join_lists_empty L :
    num_elements L = 0 → join_lists L = [].
  Proof. Admitted.

  Lemma look_head_empty L i :
    num_elements L = 0 → look_head L i = None.
  Proof. Admitted.

  Lemma look_head_cons l L i :
    look_head (l :: L) (S i) = look_head L i.
  Proof. unfold look_head. by rewrite lookup_cons. Qed.

  Lemma look_head_Some L i v l :
    L !! i = Some (v :: l) → look_head L i = Some v.
  Proof. intros H. unfold look_head. by rewrite H. Qed.

  Lemma phase2_first_correct L:
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
		(* use Hmin' to prove v' is minimum among L' *)
		destruct (bool_decide (R v' a)) eqn: ER.
		* exists a, l. split; auto.
		  (* n is minimum among (n::l)::L' *)
		  (* thus, RHS is mergesort (n :: join ...) *)
		  (* mergesort of permutationally equivalent lists are equal *)
		  admit.
		* exists v', l'. split; auto.
		  (* v' is minimum among (n::l)::L' *)
		  (* same as above *)
		  admit.
	  + simpl. rewrite look_head_cons look_head_empty; try lia.
	    exists a, l. split; auto. simpl.
		replace (join_lists L') with ([] : list A) by admit.
		rewrite app_nil_r.
		(* LHS is n::l since strongly sorted *)
		(* RHS is also n::l *)
		admit.
	Admitted.

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
