theory TP2
  imports Main
begin

(* Ex1 *)
lemma q1 : "A \<and> B \<and> C \<longrightarrow> B \<and> A"
  apply (rule impI)
  apply (rule conjI)
   apply (rule_tac Q="C" in conjunct1)
   apply (rule_tac P="A" in conjunct2)
   apply assumption
   apply (rule_tac Q="B" in conjunct1)
  apply (rule_tac Q="C" in conjunct1)
  apply (subst conj_assoc)
  by assumption

lemma q1_2 : "A \<and> B \<and> C \<longrightarrow> B \<and> A"
  apply(rule impI)
  apply(erule conjE)+
  apply (rule conjI)
  by assumption+

lemma q2 : "(\<forall>x. A \<longrightarrow> B(x)) = (A \<longrightarrow> (\<forall>x. B(x)))"
  apply(rule iffI)
   apply(rule impI)
   apply(rule allI)
   apply(erule allE)
   apply(erule impE)
    apply assumption+

  apply(rule allI)
  apply(rule impI)
  apply(erule impE)
   apply assumption
  apply(erule allE)
  by assumption

lemma q7: "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
  apply (subst imp_conv_disj)
  apply (subst imp_conv_disj)
  apply (rule impI)
  apply (erule disjE)
   apply (subst(asm) de_Morgan_disj)
   apply (subst(asm) not_not)
   apply (rule_tac Q="\<not> B" in conjunct1)
  by assumption+

lemma q3 : "(\<forall>x. A(x) \<and> B(x)) = ((\<forall>x. A(x)) \<and> (\<forall>x. B(x)))A"
  sorry

lemma q7 : "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"

  

