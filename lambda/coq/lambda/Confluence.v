From lambda Require Import Star.

(*

      t
     / \
    /   \
  t1     t2
    \   /
     \ /
      u
*)

Definition confluence T (R : T -> T -> Prop) :=
  forall t t1 t2,
  star T R t t1 -> star T R t t2 ->
  exists u, star T R t1 u /\ star T R t2 u.

(* strip *)

Definition strip T (R : T -> T -> Prop) :=
  forall t t1 t2,
  R t t1 -> star T R t t2 ->
  exists u, star T R t1 u /\ star T R t2 u.

Lemma strip_lemma_l:
  forall T R,
  strip T R -> confluence T R.
Proof.
  unfold strip.
  intros T R HS; intros t t1 t2 Ht1.
  generalize dependent t2.
  induction Ht1; intros t2 HT2.
  - exists t2; split; auto; constructor. 
  - destruct (HS M M' t2 H HT2) as [x [HTS1 HTS2]].
    destruct (IHHt1 x HTS1) as [u [HTS1' HTS2']].
    exists u. split; auto.
    eapply star_trans; eauto.
Qed.

