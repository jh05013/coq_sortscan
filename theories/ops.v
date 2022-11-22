From coq_sortscan Require Import helper.
From stdpp Require Import list.

Definition CAP_DISK : nat := 100.
Definition CAP_MEM : nat := 16.

Record Data := {
  disk : list nat;
  mem : list nat;
  disk_length : length disk = CAP_DISK;
  mem_length : length mem = CAP_MEM
}.

Implicit Type (data : Data).

Program Definition write_const_disk data (i v : nat) : Data :=
  {| disk := <[i:=v]> (disk data); mem := mem data |}.
Next Obligation. intros. rewrite insert_length. apply (disk_length data). Qed.
Next Obligation. intros. apply (mem_length data). Qed.

Program Definition write_const_mem data (i v : nat) : Data :=
  {| disk := disk data; mem := <[i:=v]> (mem data) |}.
Next Obligation. intros. apply (disk_length data). Qed.
Next Obligation. intros. rewrite insert_length. apply (mem_length data). Qed.

Definition read_mem data (i : nat) := (mem data) !! i.

(* copy disk[i] to mem[j] *)
Definition read_disk data (i j : nat) :=
  match (disk data) !! i with
  | None => data
  | Some v => write_const_mem data j v
  end.

(* copy mem[i] to disk[j] *)
Definition write_disk data (i j : nat) :=
  match (mem data) !! i with
  | None => data
  | Some v => write_const_disk data j v
  end.

(* copy disk[i..i+len) to mem[j..j+len) *)
Fixpoint read_range_disk data (i len j : nat) :=
  match len with
  | O => data
  | S len' => read_range_disk (read_disk data i j) (S i) len' (S j)
  end.

(* copy mem[i..i+len) to disk[j..j+len) *)
Fixpoint write_range_disk data (i len j : nat) :=
  match len with
  | O => data
  | S len' => write_range_disk (write_disk data i j) (S i) len' (S j)
  end.
(*
Lemma read_disk_length data i j :
  length (read_disk data i j) = length mem.
Proof.
  unfold read_disk. destruct (disk !! i) eqn:E; auto.
  unfold write_const_mem. by rewrite insert_length.
Qed.

Lemma read_range_disk_length data i len j :
  length (read_range_disk data i len j) = length mem.
Proof.
  revert data i j. induction len; auto; simpl; intros.
  rewrite IHlen. by rewrite read_disk_length.
Qed.
*)
Lemma read_range_disk_slice data i len j :
  slice (mem (read_range_disk data i len j)) j len =
  slice (disk data) i len.
Admitted.

Lemma read_range_disk_eq data i len j :
  mem (read_range_disk data i len j) =
  take j (mem data) ++ slice (disk data) i len ++ drop (j+len) (mem data).
Proof.
  rewrite (slice_cut (mem (read_range_disk data i len j)) j len).
  rewrite read_range_disk_slice.
Admitted.

Lemma read_range_disk_disk data i len j :
  disk (read_range_disk data i len j) = disk data.
Admitted.

Lemma write_range_disk_slice data i len j :
  i+len ≤ CAP_MEM → j+len ≤ CAP_DISK →
  slice (disk (write_range_disk data i len j)) j len =
  slice (mem data) i len.
Admitted.

Lemma write_range_disk_eq data i len j :
  disk (write_range_disk data i len j) =
  take j (disk data) ++ slice (mem data) i len ++ drop (j+len) (disk data).
Admitted.

Lemma write_range_disk_mem data i len j :
  mem (write_range_disk data i len j) = mem data.
Admitted.
