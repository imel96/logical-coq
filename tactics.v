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

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Definition ltb (n m : nat) : bool :=
	match n <=? m with
	| false => false
	| true => negb(m <=? n)
	end.

Example test_ltb1: (ltb 2 2) = false.
Proof.
reflexivity.
Qed.

Example test_ltb2: (ltb 2 4) = true.
Proof.
reflexivity.
Qed.

Example test_ltb3: (ltb 4 2) = false.
Proof.
reflexivity.
Qed.

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

Theorem identity_fn_applied_twice :
	forall (f : bool -> bool), (forall (x : bool), f x = x) ->
		forall (b : bool), f (f b) = b.
Proof.
intros.
rewrite H.
rewrite H.
reflexivity.
Qed.

Theorem negation_fn_applied_twice :
	forall (f : bool -> bool), (forall (x : bool), f x = negb x) ->
		forall (b : bool), f (f b) = b.
Proof.
intros.
destruct b.
	(* case b = true *)
	rewrite H.
	rewrite H.
	simpl.
	reflexivity.
	(* case b = false *)
	rewrite H.
	rewrite H.
	simpl.
	reflexivity.
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

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem eqb_id_refl : forall x, true = eqb_id x x.
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
    | record y v d' => if eqb_id x y
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
rewrite <- eqb_id_refl.
reflexivity.
Qed.

Theorem update_neq: forall (d: partial_map) (x y: id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
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

Example injection_ex3 : forall (X : Type) (x y z w : X) (l j : list X),
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
