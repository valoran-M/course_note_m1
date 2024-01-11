theory Scratch
  imports Main
begin

section \<open>TD1\<close>

typ\<open>int \<Rightarrow> int\<close>
typ\<open>'\<alpha> list \<Rightarrow> '\<beta> set\<close>

term\<open>[1, 2, 3]\<close>
term\<open>\<lambda>x. x\<close>

prop\<open>A \<Longrightarrow> B \<Longrightarrow> C\<close>

term\<open>\<lambda>n. \<lambda> f. \<lambda> x. f (n f x)\<close>

term\<open>(\<lambda>x. \<lambda>y. (\<lambda>z. (\<lambda>x. z x) (\<lambda>y. z y)) (x y))\<close>

definition ZERO  where "ZERO  \<equiv> \<lambda>f x. x "
definition ONE   where "ONE   \<equiv> \<lambda>f x. f x"
definition TWO   where "TWO   \<equiv> \<lambda>f x. f (f x)"
definition THREE where "THREE \<equiv> \<lambda>f x. f (f (f x))"
definition FOUR  where "FOUR  \<equiv> \<lambda>f x. f (f (f (f x)))"
definition FIVE  where "FIVE  \<equiv> \<lambda>f x. f (f (f (f (f x))))"


definition PLUS where "PLUS \<equiv> \<lambda>n m f x. m f (n f x)"

lemma the_first : "PLUS TWO THREE = FIVE"
  unfolding PLUS_def TWO_def THREE_def FIVE_def
  apply(rule refl)
  done

thm the_first
