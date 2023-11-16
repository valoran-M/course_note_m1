Require Import Arith.
Require Import Lia.

Inductive lambda : Type :=
  | Var : nat -> lambda
  | Abs : lambda -> lambda
  | App : lambda -> lambda -> lambda
.

(* Lifting *)

Fixpoint lift_rec (L : lambda) (k n: nat) : lambda :=
  match L with
  | Var i =>
      if k <=? i
      then Var (n + i)
      else Var i
  | Abs M => Abs (lift_rec M (S k) n)
  | App M N => App (lift_rec M k n) (lift_rec N k n)
  end.

Definition lift (n : nat) (N : lambda) := lift_rec N 0 n.

(* Substitution *)

Fixpoint subst_rec (p: nat) (L N : lambda) (k : nat)  : lambda :=
  match L with
  | Var i =>
    if k + p =? i then lift p N
                  else Var i
  | Abs M    => Abs (subst_rec (S p) M N k)
  | App M M' => App (subst_rec p M N k) (subst_rec p M' N k)
  end.

Definition subst := subst_rec 0.

Notation "t '[' x '<-' u ']'" := (subst t u x) (at level 20).

(* star reduction *)

Inductive star (R : lambda -> lambda -> Prop) : lambda -> lambda -> Prop :=
  | refl : forall M, star R M M
  | step : forall M M' N, R M M' -> star R M' N -> star R M N
.

(* Beta-reduction *)

Inductive b_red : lambda -> lambda -> Prop :=
  | beta    : forall M N, b_red (App (Abs M) N) (subst M N 0)
  | b_abs   : forall M M', b_red M M' -> b_red (Abs M) (Abs M')
  | b_app1  : forall M M' N, b_red M M' -> b_red (App M N) (App M' N)
  | b_app2  : forall M N N', b_red N N' -> b_red (App M N) (App M N')
.

Definition b_star := star b_red.

(* free *)
Fixpoint free_rec n' (L : lambda) n :=
  match L with
  | Var v => n + n' =? v
  | Abs l => free_rec (S n') l n
  | App l1 l2 => if free_rec n' l1 n then true else free_rec n' l2 n
  end.

Definition free := free_rec 0.

Lemma lift_neutral:
  forall L n, lift_rec L n 0 = L.
Proof.
  induction L; intros n'; unfold lift; simpl; auto.
  - case (n' <=? n); auto.
  - f_equal. apply IHL.
  - f_equal; [apply IHL1 | apply IHL2].
Qed.

Lemma subst_free_rec:
  forall L V x n,
  free_rec n L x = false ->
  subst_rec n L V x = L.
Proof.
  induction L; intros V x n' Free.
  - simpl in *. now rewrite Free.
  - simpl in *. f_equal. now apply IHL.
  - simpl in *.
    case (free_rec n' L1 x) eqn:Free1. discriminate Free.
    f_equal; [apply IHL1 | apply IHL2]; auto.
Qed.

Lemma free_lift_add:
  forall V x y z,
  free_rec x V y = false ->
  free_rec (x + z) (lift_rec V x z) y = false.
Proof.
  induction V; intros x y z Free; simpl.
  - simpl in Free.
    case (x <=? n) eqn:Hxn.
    + simpl. rewrite Nat.eqb_neq in *. lia.
    + simpl. rewrite Nat.eqb_neq, Nat.leb_gt in *. lia.
  - simpl in Free. rewrite <- Nat.add_succ_l. now apply IHV.
  - simpl in Free.
    case (free_rec x V1 y) eqn:Free2. discriminate.
    rewrite IHV1; auto.
Qed.

Lemma free_lift:
  forall V x z,
  free V x = false ->
  free_rec z (lift_rec V 0 z) x = false.
Proof.
  induction V; intros x z Hf.
  - unfold free in Hf. simpl in *.
    rewrite Nat.eqb_neq in *. lia.
  - unfold free in *. simpl in *.
    rewrite <- Nat.add_1_r, Nat.add_comm.
    now apply free_lift_add.
  - unfold free in Hf. simpl in *.
    case (free_rec 0 V1 x) eqn:Hf1. discriminate.
    rewrite IHV1; auto.
Qed.

Lemma lift_lift:
  forall V n0 z n,
  lift_rec V n (n0 + z) = lift_rec (lift_rec V n n0) (n + n0) z.
Proof.
  induction V; intros n0 z n'.
  - simpl. case (n' <=? n) eqn:Hlt.
    + simpl. assert (H: n' + n0 <=? n0 + n = true).
      { rewrite Nat.leb_le in *. lia. }
      rewrite H. f_equal. lia.
    + simpl. assert (H: n' + n0 <=? n = false).
      { rewrite Nat.leb_gt in *. lia. }
      now rewrite H.
  - simpl. f_equal. apply IHV.
  - simpl. f_equal; [apply IHV1 | apply IHV2]. 
Qed.

Lemma sub_lift:
  forall U V z y n,
  subst_rec (z + n) (lift_rec U n z) V y = lift_rec (subst_rec n U V y) n z.
Proof.
  induction U; intros *.
  - simpl.
    case (n0 <=? n) eqn:Hle.
    + simpl. rewrite (Nat.add_comm z n0), Nat.add_assoc, Nat.add_comm.
      case (y + n0 =? n) eqn:Heq.
      * assert (Heqz: z + (y + n0) =? z + n = true).
        { rewrite Nat.eqb_eq in *. lia. }
        rewrite Heqz. unfold lift.
        apply lift_lift.
      * assert (Heqz: z + (y + n0) =? z + n = false).
        { rewrite Nat.eqb_neq in *. lia. }
        rewrite Heqz. simpl. now rewrite Hle.
    + assert (Hneq: y + n0 =? n = false).
      { rewrite Nat.eqb_neq. rewrite Nat.leb_gt in Hle. lia. }
      rewrite Hneq. simpl. rewrite Hle.
      assert (Hneq': y + (z + n0) =? n = false).
      { rewrite Nat.eqb_neq. rewrite Nat.leb_gt in Hle. lia. }
      now rewrite Hneq'.
  - simpl. f_equal. rewrite <- Nat.add_succ_r. apply IHU.
  - simpl. f_equal; [apply IHU1 | apply IHU2].
Qed.

Lemma comm_subst_rec:
  forall T U V x y n,
  y <> x ->
  free V x = false ->
  subst_rec n (subst_rec n T U x) V y =
  subst_rec n (subst_rec n T V y) (subst_rec 0 U V y) x.
Proof.
  induction T; intros U V x y z Neq_x_y X_free_V; unfold subst; simpl.
  - case (x + z =? n) eqn:Hxn.
    + rewrite Nat.eqb_eq in Hxn. subst.
      rewrite <- Nat.eqb_neq in Neq_x_y.
      simpl.
      assert (Hyzx: y + z =? x + z = false) by (rewrite Nat.eqb_neq in *; lia).
      rewrite Hyzx. simpl.
      rewrite Nat.eqb_refl.
      unfold lift.
      rewrite <- (Nat.add_0_r z) at 1.
      apply sub_lift.
    + case (y + z =? n) eqn:Hyn.
      * rewrite Nat.eqb_eq in Hyn; subst.
        simpl. rewrite Nat.eqb_refl.
        unfold lift. rewrite subst_free_rec; auto.
        now apply free_lift.
      * simpl. now rewrite Hxn, Hyn.
  - f_equal. now apply IHT.
  - f_equal; [apply IHT1 | apply IHT2]; auto.
Qed.

Theorem comm_subst:
  forall T U V x y,
  y <> x ->
  free V x = false ->
  T[x <- U][y <- V] =
  T[y <- V][x <- U[y <- V]].
Proof.
  intros * H F.
  unfold subst.
  now apply comm_subst_rec.
Qed.

