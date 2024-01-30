theory TP3
  imports Main
begin

datatype 'a List = Nil | Snoc "'a List" 'a

fun filter
where
  "filter f Nil        = Nil"
| "filter f (Snoc l a) = 
    (if f a
     then  Snoc (filter f l) a
     else filter f l)"

fun map
where
  "map f Nil        = Nil"
| "map f (Snoc l a) = Snoc (map f l) (f a)"

fun concat
  where
  "concat S Nil = S"
| "concat S (Snoc l a) = Snoc (concat S l) a"

lemma aux1 : "map f (concat R S) = concat (map f R) (map f S)"
  by (induct_tac "S") simp+

lemma aux2 : "filter p (filter q S) = filter(\<lambda> x. p x \<and> q x) S"
  by (induct_tac "S") simp+

inductive_set Even :: "int set"
  where a: "0 \<in> Even"
  | b: "n \<in> Even \<Longrightarrow> (n + 2) \<in> Even"
  | c: "n \<in> Even \<Longrightarrow> (n - 2) \<in> Even"

lemma "2 \<in> Even"
  using Even.a Even.b by force

lemma nice_lemma: "x \<in> Even \<Longrightarrow> \<exists>k. x = 2*k"
  apply (erule_tac Even.induct)
    apply (rule_tac x="0" in exI, simp)
    apply (erule exE, rule_tac x="k+1" in exI, simp)
    apply (erule exE, rule_tac x="k-1" in exI, simp)
  done

lemma one_is_not_even: "1 \<notin> Even"
  apply(rule notI)
  apply(drule nice_lemma, erule exE)
  by (simp add: pos_zmult_eq_1_iff)

term "\<lambda>x. x"

value "map Suc (Snoc (Snoc Nil x) 2)"

datatype const =
    Nat nat
  | Bool bool

datatype terms =
    Var string
  | Const const
  | App terms terms
  | Lambda string terms

datatype types =
    TVar string
  | TNat
  | TBool
  | Arrow types types (infixr "\<rightarrow>" 200)

fun instantiate :: "types \<Rightarrow> string \<Rightarrow> types \<Rightarrow> types"
where
  "instantiate (Arrow t1 t2) s t = Arrow (instantiate t1 s t) (instantiate t2 s t)"
| "instantiate TNat s t = TNat"
| "instantiate TBool s t = TBool"
| "instantiate (TVar vs) s t = (if vs = s then t else (TVar vs))"

inductive typing :: "(const \<rightharpoonup> types) \<Rightarrow> (string \<rightharpoonup> types) \<Rightarrow> terms \<Rightarrow> types \<Rightarrow> bool"
    ("_, _ \<turnstile> _ : _" [50, 50, 50] 50)
  where
    Var   : "\<Gamma> x = Some T \<Longrightarrow> \<Sigma>, \<Gamma> \<turnstile> Var x : T"
  | Const : "\<Sigma> c = Some C \<Longrightarrow> \<Sigma>, \<Gamma> \<turnstile> Const c : instantiate C x T"
  | Abs   : "\<Sigma>, \<Gamma> (v \<mapsto> T) \<turnstile> t : U \<Longrightarrow> \<Sigma>, \<Gamma> \<turnstile> Abs v t : (T \<rightarrow> U)"
  | App   : "\<Sigma>, \<Gamma> \<turnstile> t1 : (T2 \<rightarrow> T1) \<Longrightarrow> \<Sigma>, \<Gamma> \<turnstile> t2 : T2 \<Longrightarrow> \<Sigma>, \<Gamma> \<turnstile> (App t1 t2) : T1"





