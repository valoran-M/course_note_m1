Inductive star T (R : T -> T -> Prop) : T -> T -> Prop :=
  | refl : forall M, star T R M M
  | step : forall M M' N, R M M' -> star T R M' N -> star T R M N
.

Lemma star_trans:
  forall T R M M' M'', star T R M M' -> star T R M' M'' -> star T R M M''.
Proof.
  intros * Hmm'; generalize dependent M''.
  induction Hmm'; intros M'' Hmm''.
  - easy.
  - econstructor. apply H. now apply IHHmm'.
Qed.


