Section ops.
  (* (disk mem : list nat). *)

  (* write v to disk[i] *)
  Definition write_disk (disk mem : list nat) (i v : nat) :=
    disk. (* <[i := v]> disk *)

  (* write v to mem[i] *)
  Definition write_mem (disk mem : list nat) (i v : nat) :=
    mem. (* <[i := v]> mem *)

  (* copy disk[i] to mem[j] *)
  Definition read_disk (disk mem : list nat) (i j : nat) :=
    disk. (*
    match disk !! i with
    | None => data
    | Some v => write_mem j v
    end. *)

  (* read mem[i] *)
  Definition read_mem (disk mem : list nat) (i : nat) :=
    mem. (* mem !! i. *)

  (* copy disk[i..i+len) to mem[j..j+len) *)
  Fixpoint read_range_disk (disk mem : list nat) (i len j : nat) :=
    match len with
    | O => mem
    | S len' => read_range_disk
        disk (read_disk disk mem i j) (S i) len' (S j)
    end.

  (* copy mem[i..i+len) to disk[j..j+len) *)
  Definition write_range_disk (disk mem : list nat) (i len j : nat) :=
    read_range_disk mem disk i len j.
End ops.

Section Phase1.
  (* sort disk[i..i+M) *)
  Definition sort_disk (disk mem : list nat) (i : nat) :=
    let mem' := read_range_disk disk mem i (length mem) 0 in
    let smem' := mem' in (*sort mem' in*)
    (write_range_disk disk mem i (length mem) 0, smem').

  Fixpoint phase1_loop (disk mem : list nat) (c : nat) :=
    let (disk', mem') := sort_disk disk mem (c * (length mem)) in
    match c with
    | O => (disk', mem')
    | S c' => phase1_loop disk' mem' c'
    end.

  Definition phase1 (disk mem : list nat) :=
    phase1_loop disk mem 0. (* (length disk / length mem). *)

  Lemma phase1_spec (disk mem : list nat) :
    let M := length mem in
    let (disk', mem') := phase1 disk mem in
    forall i, is_sorted (slice disk' (i * M) M).
  Proof. Admitted.
End Phase1.

Section Phase2.

End Phase2.
