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

Fixpoint factorial (n: nat) : nat :=
  match n with
    | 0 => 1
    | S n => S n * factorial n
  end.

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
            | S m' => beq_nat n' m' end
  end.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
intros n.
destruct n as [ | n'].
- reflexivity.
- reflexivity.
Qed.

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
intros p.
destruct p as [n m].
simpl.
reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
intros p.
destruct p as [n m].
simpl.
reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition bag := natlist.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
    | nil => 0
    | h :: t => match beq_nat h v with
      | true => S (count v t)
      | false => count v t
     end
  end.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
simpl.
reflexivity.
Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
simpl.
reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  leb 1 (count 1 (1 :: s)) = true.
Proof.
intros s.
simpl.
reflexivity.
Qed.

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd (default: nat) (l: natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition hd_error (l : natlist) : natoption :=
  match l with
    | nil => None
    | h :: t  => Some h
  end.

Example test_hd_error1 : hd_error nil = None.
reflexivity. Qed.

Example test_hd_error2 : hd_error [1] = Some 1.
reflexivity. Qed.

Example test_hd_error3 : hd_error [5;6] = Some 5.
reflexivity. Qed.

Theorem option_elim_hd : forall (l: natlist) (default: nat),
  hd default l = option_elim default (hd_error l).
Proof.
intros l default.
destruct l.
reflexivity.
reflexivity.
Qed.

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
intros x.
destruct x.
simpl.
induction n.
reflexivity.
simpl.
rewrite <- IHn.
reflexivity.
Qed.

Inductive partial_map : Type :=
  | empty : partial_map
  | record : id -> nat -> partial_map -> partial_map.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
    | empty => None
    | record y v d' => if beq_id x y
      then Some v
      else find x d'
  end.

Definition update (d: partial_map) (x: id) (value: nat): partial_map :=
  record x value d.

Theorem update_eq: forall (d: partial_map) (x: id) (v: nat),
    find x (update d x v) = Some v.
Proof.
intros d x v.
unfold update.
simpl.
rewrite <- beq_id_refl.
reflexivity.
Qed.

Theorem update_neq: forall (d: partial_map) (x y: id) (o: nat),
    beq_id x y = false -> find x (update d y o) = find x d.
Proof.
intros d x y o.
simpl.
intros H.
rewrite H.
reflexivity.
Qed.

Module OptionPlayground.

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.
Arguments Some {X} _.
Arguments None {X}.

Inductive list (X: Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
    | nil _ => None
    | cons _ h t => Some h
  end.

Check @hd_error.
Check @nil.

Arguments nil {X}.
Arguments cons {X} _ _.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Example test_hd_error1 : hd_error [1; 2] = Some 1.
simpl.
reflexivity.
Qed.

Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
simpl.
reflexivity.
Qed.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).

Example inversion_ex3 : forall (X : Type) (x y z w : X) (l j : list X),
  x :: y :: l = w :: z :: j ->
  x :: l = z :: j ->
  x = y.
Proof.
intros X x y z w l j.
intros H.
intros G.
inversion G.
inversion H.
reflexivity.
Qed.

Example inversion_ex6 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = nil ->
  y :: l = z :: j ->
  x = z.
Proof.
intros X x y z l j.
intros H.
inversion H.
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
intros P Q.
intros H.
apply H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP. Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~(P /\ ~P).
Proof.
intros P contra.
apply contradiction_implies_anything with (P := P).
apply contra.
Qed.

Theorem dist_not_exists : forall (X: Type) (P: X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
intros X P x H.
unfold not.
destruct H as [y E].
apply E.
apply x.
Qed.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

Fixpoint double (n: nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem ev_double : forall n,
  ev (double n).
Proof.
intros.
induction n.
apply ev_0.
apply ev_SS.
apply IHn.
Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
intros.
inversion H  as [|n' H'].
inversion H'  as [|n'' H''].
apply H''.
Qed.

Theorem even5_nonsense:
  ev 5 -> 2 + 2 = 9.
Proof.
intros.
inversion H.
inversion H1.
inversion H3.
Qed.
