theory Part1
imports Main
begin

section \<open> Assignment 1 \<close>

datatype ('f, 'v) "term" = Var 'v | Fun 'f "('f, 'v) term list"

text \<open> (a) \<close>

fun fv :: "(('f, 'v) term \<Rightarrow> 'v set)" where
  "fv (Var x) = { x }" |
  "fv (Fun f lst) = \<Union>(set (map fv lst))"

text \<open> (b) \<close>

type_synonym ('f, 'v) subst = "'v \<Rightarrow> ('f, 'v) term"

fun sapply :: "('f, 'v) subst \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term" 
  (infixr "\<cdot>" 67) where
    "sapply \<sigma> (Var x) = \<sigma> x" |
    "sapply \<sigma> (Fun f ts) = Fun f (map (sapply \<sigma>) ts)"

definition scomp :: "('f, 'v) subst \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) subst"
  (infixr "\<circ>s" 75) where
    "(scomp \<sigma> \<tau>) x = sapply \<sigma> (\<tau> x)"

text \<open> (c) \<close>

lemma fv_sapply: "fv (\<sigma> \<cdot> t) = (\<Union> x \<in> fv t. fv (\<sigma> x))"
  apply(induction t rule: fv.induct)
   apply(simp_all)
  done

lemma sapply_cong: 
  assumes "\<And>x. x \<in> fv t \<Longrightarrow> \<sigma> x = \<tau> x"
  shows "\<sigma> \<cdot> t = \<tau> \<cdot> t"
  using assms 
  apply(induction t rule: fv.induct)
   apply(simp_all)
   apply(blast)
  done

lemma scomp_sapply: "(\<sigma> \<circ>s \<tau>)x = \<sigma> \<cdot> (\<tau> x)"
  apply(simp add: scomp_def)
  done

lemma sapply_scomp_distrib: "(\<sigma> \<circ>s \<tau>) \<cdot> t = \<sigma> \<cdot> (\<tau> \<cdot> t)"
  apply(induction t)
   apply(simp_all add: scomp_def)
  done

lemma scomp_assoc: "(\<sigma> \<circ>s \<tau>) \<circ>s \<rho> = \<sigma> \<circ>s (\<tau> \<circ>s \<rho>)"
  apply(simp add: fun_eq_iff scomp_def sapply_scomp_distrib)
  done

lemma sapply_Var[simp]: "Var \<cdot> t = t"
  apply(induction t)
   apply(simp_all add: map_idI)
  done

lemma scomp_Var[simp]: "\<sigma> \<circ>s Var = \<sigma>"
  apply(simp add: fun_eq_iff scomp_def)
  done

lemma Var_scomp[simp]: "Var \<circ>s \<sigma> = \<sigma>"
  apply(simp add: fun_eq_iff scomp_def)
  done

text \<open> (d) \<close>

definition sdom :: "('f, 'v) subst \<Rightarrow> 'v set" where
  "sdom \<sigma> = { x . (\<sigma> x) \<noteq> (Var x)}"

(*
definition sran :: "('f, 'v) subst \<Rightarrow> ('f, 'v) term set" where
 "sran \<sigma> = \<sigma> ` sdom \<sigma>"
*)

definition svran :: "('f, 'v) subst \<Rightarrow> 'v set" where
  "svran \<sigma> = \<Union>(fv ` (\<sigma> ` sdom \<sigma>))"

lemma sdom_Var[simp]: "sdom Var = {}"
  apply(simp add: sdom_def)
  done

lemma svran_Var[simp]: "svran Var = {}"
  apply(simp add: svran_def)
  done

lemma sdom_single_non_trivial[simp]:
  "t \<noteq> Var x \<Longrightarrow> sdom (Var( x := t )) = {x}"
    apply(simp add: fun_upd_def sdom_def)
    done

lemma svran_single_non_trivial[simp]:
  "t \<noteq> Var x \<Longrightarrow> svran (Var( x := t )) = fv t"
    apply(simp add: fun_upd_def svran_def sdom_def)
  done

lemma svapply_svdom_svran:
  "x \<in> fv (\<sigma> \<cdot> t) \<Longrightarrow> x \<in> (fv t - sdom \<sigma>) \<union> svran \<sigma>"
  apply(simp_all add: svran_def sdom_def)
  sorry
  
  











