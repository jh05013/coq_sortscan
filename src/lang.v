Record Computer : Type := {
  disk : list nat;
  memory : list nat;
}

Inductive Expr :=
| E_Read nat
| E_Le nat nat
.

Inductive Program :=
| P_ReadDisk nat nat
| P_ReadMem nat nat
| P_WriteDisk nat nat
| P_WriteMem nat nat
| P_Output nat
| P_If Expr Program Program
| P_While Expr Program
.

(* smallstep something... *)

