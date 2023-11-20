Require Import Arith.
From lambda Require Import Lambda.

Inductive b_parr: lambda -> lambda -> Prop :=
  | refl_p   : forall x, b_parr (Var x) (Var x)
  | betap    : forall M N M' N',
      b_parr M M' -> b_parr N N' ->
      b_parr (App (Abs M) N) (subst M' N' 0)
  | bp_abs   : forall M M', b_parr M M' -> b_parr (Abs M) (Abs M')
  | bp_app   : forall M M' N N',
      b_parr M M' -> b_parr N N' ->
      b_parr (App M N) (App M' N')
.

Definition b_parr_start := star b_parr.

Lemma par_refl:
  forall T,
  b_parr T T.
Proof.
  induction T.
  - constructor.
  - constructor. apply IHT.
  - eapply bp_app; auto.
Qed.

Lemma b_to_par:
  forall T T',
  b_red T T' -> b_parr T T'.
Proof.
  intros T T' H. induction H.
  - constructor; apply par_refl.
  - constructor. apply IHb_red. 
  - econstructor. apply IHb_red.
    apply par_refl.
  - eapply bp_app. apply par_refl.
    apply IHb_red.
Qed.

Lemma par_to_star:
  forall T T',
  b_parr T T' -> b_star T T'.
Proof.
  intros T T' H. induction H.
  - constructor.
  - econstructor. constructor.
    fold b_star. now apply abs_susbst.
  - now apply abs_star.
  - now apply app_star.
Qed.



