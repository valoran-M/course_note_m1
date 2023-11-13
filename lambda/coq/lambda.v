Require Import Arith.

Inductive lambda : Type :=
  | Var : nat -> lambda
  | Abs : lambda -> lambda
  | App : lambda -> lambda -> lambda
.

(* Lifting *)

Definition relocate (i k n : nat) :=
  if k <=? i
  then n + i
  else i.


Fixpoint lift_rec (L : lambda) (k n: nat) : lambda :=
  match L with
  | Var i => Var (relocate i k n)
  | Abs M => Abs (lift_rec M (S k) n)
  | App M N => App (lift_rec M k n) (lift_rec N k n)
  end.

Definition lift (n : nat) (N : lambda) := lift_rec N 0 n.

(* Substitution *)

Definition insert_Ref (N : lambda) (i k : nat) :=
       if k <? i then Var (pred i)
  else if k =? i then lift k N
                 else Var i.

Fixpoint subst_rec (L N : lambda) (k : nat): lambda :=
  match L with
  | Var i => insert_Ref N i k
  | Abs M => Abs (subst_rec M N (S k))
  | App M M' => App (subst_rec M N k) (subst_rec M' N k)
  end.

Definition subst (N M : lambda) := subst_rec M N 0.


(* star reduction *)

Inductive star (R : lambda -> lambda -> Prop) : lambda -> lambda -> Prop :=
  | refl : forall M, star R M M
  | step : forall M M' N, R M M' -> star R M' N -> star R M N
.

(* Beta-reduction *)

Inductive b_red : lambda -> lambda -> Prop :=
  | beta    : forall M N, b_red (App (Abs M) N) (subst M N)
  | b_abs   : forall M M', b_red M M' -> b_red (Abs M) (Abs M')
  | b_app1  : forall M M' N, b_red M M' -> b_red (App M N) (App M' N)
  | b_app2  : forall M N N', b_red N N' -> b_red (App M N) (App M N')
.

Definition b_star := star b_red.

