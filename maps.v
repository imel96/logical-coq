Require Export Coq.Strings.String.

Definition beq_string x y :=
  if string_dec x y then true else false.

Definition total_map (A:Type) := string -> A.

Definition t_update {A:Type} (m : total_map A) (x : string) (v : A) :=
  fun x' => if beq_string x x' then v else m x'.

Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

Notation "{ --> d }" := (t_empty d) (at level 0).

(* xxx *)
Lemma t_apply_empty: forall (A: Type) (x: string) (v: A), { --> v } x = v.
Proof.
intros.
trivial.
Qed.
