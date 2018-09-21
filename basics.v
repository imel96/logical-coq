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
intros n m o.
intros H.
rewrite -> H.
intros I.
rewrite -> I.
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

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
intros n.
destruct n as [ | n'].
- reflexivity.
- reflexivity.
Qed.
