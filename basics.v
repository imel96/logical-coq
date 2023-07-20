Definition nandb (b1:bool) (b2:bool) : bool :=
match b1 with
  | true => match b2 with
    | true => false
    | false => true
    end
  | false => true
  end.

Definition andb3 (b1:bool) (b2:bool) (b3: bool): bool :=
match b1 with
  | true => match b2 with
    | true => match b3 with
      | true => true
      | false => false
      end
    | false => false
    end
  | false => false
  end.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.
Compute (minustwo 1).

Fixpoint factorial (n: nat) : nat :=
  match n with
    | 0 => 1
    | S n => S n * factorial n
  end.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n => S (plus n m)
  end.

Compute (plus 4 4).

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.
Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Notation "x * y" := (mult x y)
            (at level 40, left associativity)
            : nat_scope.

Print mult_n_O.
Print mult_n_Sm.

Theorem mult_n_1 : forall p : nat,
  mult p (S O) = p.
Proof.
intros.
rewrite <- mult_n_Sm.
rewrite <- mult_n_O.
reflexivity.
Qed.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Definition blt_nat (n m : nat) : bool :=
  match n with
    | 0 => match m with
      | 0 => false
      | S m' => leb n m'
      end
    | S n' => match m with
      | 0 => false
      | S m' => leb n m'
     end
  end.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
intros.
rewrite -> H.
rewrite -> H0.
reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
intros.
rewrite -> H.
simpl.
reflexivity.
Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
intros b c.
destruct c.
intros.
reflexivity.
destruct b.
intros.
rewrite <- H.
reflexivity.
intros.
rewrite <- H.
reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
intros.
destruct n as [ | n'].
- reflexivity.
- reflexivity.
Qed.

Theorem identity_fn_applied_twice:
  forall (f : bool -> bool), (forall (x : bool), f x = x) -> forall (b : bool), f (f b) = b.
Proof.
intros.
rewrite -> H.
rewrite -> H.
reflexivity.
Qed.

Theorem negation_fn_applied_twice:
  forall (f : bool -> bool), (forall (x : bool), f x = negb x) -> forall (b : bool), f (f b) = b.
Proof.
intros.
rewrite -> H.
rewrite -> H.
destruct b.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Inductive comparison : Set :=
  | Eq : comparison (* "equal" *)
  | Lt : comparison (* "less than" *)
  | Gt : comparison.

Inductive letter : Type :=
  | A | B | C | D | F.

Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.

Theorem letter_comparison_Eq :
  forall l, letter_comparison l l = Eq.
Proof.
intros.
destruct l.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
Qed.
