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

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ nil = l.
Proof.
intros.
induction l as [|m].
simpl.
reflexivity.
simpl.
rewrite IHl.
reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
intros.
induction l as [|l'].
simpl.
reflexivity.
simpl.
rewrite IHl.
reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
intros.
induction l1 as [|l1'].
simpl.
reflexivity.
simpl.
rewrite IHl1.
reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
intros.
induction l1.
simpl.
rewrite app_nil_r.
reflexivity.
simpl.
rewrite IHl1.
rewrite app_assoc.
reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite rev_app_distr.
rewrite IHl.
simpl.
reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | nil => (nil, nil)
  | (x, y)::tl => (x::fst(split tl), y::snd(split tl))
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
simpl.
reflexivity.
Qed.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Fixpoint filter {X:Type} (test: X -> bool) (l:list X)
  : (list X) :=
  match l with
  | nil => nil
  | h :: t => if test h then h :: (filter test t)
    else filter test t
  end.

Definition gt (x y: nat) : bool :=
  match leb x y with
  | true => false
  | false => true
  end.

Definition filter_even_gt7 (l : list nat) : list nat :=
  match l with
  | nil => nil
  | x::tl => filter evenb (filter (fun x => gt x 7) l)
  end.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof.
simpl.
reflexivity.
Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = nil.
Proof.
simpl.
reflexivity.
Qed.

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X) : (list Y) :=
  match l with
  | nil => nil
  | h::tl => (f h) ++ (flat_map f tl)
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4] = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof.
simpl.
reflexivity.
Qed.

Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Print fold.
Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
unfold fold_length.
unfold length.
intros.
induction l.
simpl.
reflexivity.
rewrite <- IHl.
simpl.
reflexivity.
Qed.

Definition prod_curry {X Y Z : Type}
	(f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type} (f : X -> Y -> Z) (p : X * Y) : Z :=
	f (fst p) (snd p).

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
unfold prod_curry.
unfold prod_uncurry.
intros.
simpl.
reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y),
	prod_uncurry (prod_curry f) p = f p.
Proof.
unfold prod_curry.
unfold prod_uncurry.
intros.
destruct p as [x y].
simpl.
reflexivity.
Qed.
