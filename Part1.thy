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
  apply(induction t)
   apply(simp_all add: svran_def sdom_def)
   apply(metis fv.simps(1) singletonD)
  apply(blast)
  done

lemma sdom_scomp: "sdom (\<sigma> \<circ>s \<tau>) \<subseteq> sdom \<sigma> \<union> sdom \<tau>"
  apply(simp add: sdom_def scomp_def)
  apply(auto)
  done

lemma svran_scomp: "svran (\<sigma> \<circ>s \<tau>) \<subseteq> svran \<sigma> \<union> svran \<tau>"
  apply(simp add: svran_def scomp_def fv_sapply sdom_def)
  apply(force)
  done

section \<open> Assignment 2 \<close>
  
text \<open> (a) \<close>

type_synonym ('f, 'v) equation = "('f, 'v) term \<times> ('f, 'v) term"
type_synonym ('f, 'v) eq_system = "('f, 'v) equation list"

(*TODO: Potentially fix names to proper overloading*)
definition fv_eq :: "('f, 'v) equation \<Rightarrow> 'v set" where
  "fv_eq eq = (fv (fst eq)) \<union> (fv (snd eq))"

definition fv_eq_sys :: "('f, 'v) eq_system \<Rightarrow> 'v set" where
  "fv_eq_sys eq_sys = \<Union>(set (map fv_eq eq_sys))"

definition sapply_eq :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equation \<Rightarrow> ('f, 'v) equation" 
  (infixr "\<cdot>" 67) where
    "sapply_eq \<sigma> eq = (sapply \<sigma> (fst eq), sapply \<sigma> (snd eq))"

definition sapply_eq_sys :: "('f, 'v) subst \<Rightarrow> ('f, 'v) eq_system \<Rightarrow> ('f, 'v) eq_system" 
  (infixr "\<cdot>" 67) where
    "sapply_eq_sys \<sigma> eq_sys = map (sapply_eq \<sigma>) eq_sys"
