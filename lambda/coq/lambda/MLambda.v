Require Import Arith.
From lambda Require Import Star Lambda.

Inductive mlambda : Type :=
  | MVar  : nat -> mlambda
  | MAbs  : mlambda -> mlambda
  | MAAbs : mlambda -> mlambda -> mlambda
  | MApp  : mlambda -> mlambda -> mlambda
.

(* Lifting *)

Fixpoint mlift_rec (L : mlambda) (k n: nat) : mlambda :=
  match L with
  | MVar i =>
      if k <=? i
      then MVar (n + i)
      else MVar i
  | MAbs M    => MAbs  (mlift_rec M (S k) n)
  | MApp M N  => MApp  (mlift_rec M k n) (mlift_rec N k n)
  | MAAbs M N => MAAbs (mlift_rec M (S k) n) (mlift_rec N k n)
  end.

Definition mlift (n : nat) (N : mlambda) := mlift_rec N 0 n.

(* Substitution *)

Fixpoint msubst_rec (p: nat) (L N : mlambda) (k : nat)  : mlambda :=
  match L with
  | MVar i =>
    if k + p =? i then mlift p N
                  else MVar i
  | MAbs  M    => MAbs  (msubst_rec (S p) M N k)
  | MApp  M M' => MApp  (msubst_rec p M N k) (msubst_rec p M' N k)
  | MAAbs M M' => MAAbs (msubst_rec (S p) M N k) (msubst_rec p M' N k)
  end.

Definition msubst := msubst_rec 0.

Notation "t 'm[' x '<-' u ']'" := (msubst t u x) (at level 20).

Fixpoint bar (l : mlambda) :=
  match l with
  | MVar i    => Var i
  | MAbs M    => Abs (bar M)
  | MAAbs M N => App (Abs (bar M)) (bar N)
  | MApp M M' => App (bar M) (bar M')
  end.

Fixpoint phi(l: mlambda) : lambda :=
  match l with
  | MVar i    => Var i
  | MAbs M    => Abs (phi M)
  | MApp M M' => App (phi M) (phi M')
  | MAAbs M N => (phi M)[0 <- phi N]
  end.

Lemma bar_phi:
  forall t,
  b_star (bar t) (phi t).
Proof.
  induction t; simpl.
  - apply refl.
  - now apply abs_star.
  - apply star_trans with (M' := App (Abs (phi t1)) (phi t2)).
    + apply app_star; try apply abs_star; assumption.
    + repeat econstructor.
  - now apply app_star.
Qed.

Lemma mlift_rec_neutral:
  forall t n, mlift_rec t n 0 = t.
Proof.
  induction t; intros n'; simpl;
    try (now rewrite IHt);
    try(now rewrite IHt1, IHt2).
  now case (n' <=? n).
Qed.

Lemma mlift_neutral:
  forall t, mlift 0 t = t.
Proof.
  intros t. unfold mlift; apply mlift_rec_neutral.
Qed.

Inductive mb_red : mlambda -> mlambda -> Prop :=
  | mbeta1   : forall M N, mb_red (MApp (MAbs M) N) (msubst M N 0)
  | mbeta2   : forall M N, mb_red (MAAbs M N)       (msubst M N 0)
  | mb_abs   : forall M M', mb_red M M' -> mb_red (MAbs M) (MAbs M')
  | mb_app1  : forall M M' N, mb_red M M' -> mb_red (MApp M N) (MApp M' N)
  | mb_app2  : forall M N N', mb_red N N' -> mb_red (MApp M N) (MApp M N')
  | mb_mabs1 : forall M M' N, mb_red M M' -> mb_red (MApp M N) (MApp M' N)
  | mb_mabs2 : forall M N N', mb_red N N' -> mb_red (MApp M N) (MApp M N')
.

Definition mb_star := star mlambda mb_red.

Lemma phi_subst:
  forall u v x n,
  phi (msubst_rec x u v n) = subst_rec x (phi (u)) (phi v) n.
Proof.
  induction u; intros v x n'; simpl.
  - unfold msubst, subst.
    case (n' + x =? n); auto.
    admit.
  - f_equal. apply IHu.
  - unfold subst. rewrite IHu1, IHu2.
    repeat fold subst.


Lemma phi_beta:
  forall t1 t2,
  mb_star t1 t2 ->
  b_star (phi t1) (phi t2).
Proof.
  intros t1 t2.

