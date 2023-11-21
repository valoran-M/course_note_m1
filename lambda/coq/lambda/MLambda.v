Require Import Arith.
Require Import Lambda.

Inductive mlambda : Type :=
  | MVar  : nat -> mlambda
  | MAbs  : mlambda -> mlambda
  | MAAbs : mlambda -> mlambda -> mlambda
  | MApp  : mlambda -> mlambda -> mlambda
.

Definition subst := subst_rec 0.

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

