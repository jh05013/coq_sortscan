From coq_sortscan Require Import helper.
From stdpp Require Import list.

Implicit Types disk mem : list nat.

Definition write_const_disk disk mem (i v : nat) := <[i := v]> disk.
Definition write_const_mem disk mem (i v : nat) := <[i := v]> mem.
Definition read_mem disk mem (i : nat) := mem !! i.

(* copy disk[i] to mem[j] *)
Definition read_disk disk mem (i j : nat) :=
  match disk !! i with
  | None => mem
  | Some v => write_const_mem disk mem j v
  end.

(* copy mem[i] to disk[j] *)
Definition write_disk disk mem (i j : nat) :=
  read_disk mem disk i j.

(* copy disk[i..i+len) to mem[j..j+len) *)
Fixpoint read_range_disk disk mem (i len j : nat) :=
  match len with
  | O => mem
  | S len' => read_range_disk
      disk (read_disk disk mem i j) (S i) len' (S j)
  end.

(* copy mem[i..i+len) to disk[j..j+len) *)
Definition write_range_disk disk mem (i len j : nat) :=
  read_range_disk mem disk i len j.

Lemma read_disk_length disk mem i j :
  length (read_disk disk mem i j) = length mem.
Proof.
  unfold read_disk. destruct (disk !! i) eqn:E; auto.
  unfold write_const_mem. by rewrite insert_length.
Qed.

Lemma read_range_disk_length disk mem i len j :
  length (read_range_disk disk mem i len j) = length mem.
Proof.
  revert disk mem i j. induction len; auto; simpl; intros.
  rewrite IHlen. by rewrite read_disk_length.
Qed.

Lemma read_range_disk_slice disk mem i len j :
  slice (read_range_disk disk mem i len j) j len =
  slice disk i len.
Admitted.

Lemma read_range_disk_eq disk mem i len j :
  read_range_disk disk mem i len j =
  take j mem ++ slice disk i len ++ drop (j+len) mem.
Proof.
  rewrite (slice_cut
    (read_range_disk disk mem i len j) j len
  ).
  rewrite read_range_disk_slice.
Admitted.
  (*
Lemma read_disk_lookup disk mem i j :
  i < length disk → j < length mem →
  (read_disk disk mem i j) !! j = disk !! i.
Admitted.
*)
Lemma write_range_disk_lookup disk mem i len j :
  i+len ≤ length mem → j+len ≤ length disk →
  slice (write_range_disk disk mem i len j) j len =
  slice mem i len.
Admitted.
