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

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
intros.
induction n.
simpl.
reflexivity.
apply IHn.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite <- IHn.
reflexivity.
Qed.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
intros.
induction n as [|n'].
rewrite <- plus_n_O.
reflexivity.
rewrite <- plus_n_Sm.
rewrite <- IHn'.
simpl.
reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
intros.
induction n as [|n'].
simpl.
rewrite plus_comm.
reflexivity.
simpl.
rewrite IHn'.
reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
intros.
induction n as [|n'].
simpl.
reflexivity.
simpl.
rewrite <- plus_comm.
rewrite IHn'.
simpl.
reflexivity.
Qed.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
intros.
induction n as [|n'].
simpl.
reflexivity.
rewrite IHn'.
simpl.
rewrite negation_fn_applied_twice.
reflexivity.
intros.
reflexivity.
Qed.
