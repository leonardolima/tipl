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
   apply(simp add: svran_def sdom_def)
   apply(metis fv.simps(1) singletonD)
  apply(simp add: svran_def sdom_def)
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
type_synonym ('f, 'v) equations = "('f, 'v) equation list"

definition fv_eq :: "('f, 'v) equation \<Rightarrow> 'v set" where
  "fv_eq eq = (fv (fst eq)) \<union> (fv (snd eq))"

fun fv_eqs :: "('f, 'v) equations \<Rightarrow> 'v set" where
  "fv_eqs [] = {}"
| "fv_eqs (eq#s) = (fv_eq eq) \<union> (fv_eqs s)"

definition sapply_eq :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equation \<Rightarrow> ('f, 'v) equation" 
  (infixr "\<cdot>e" 67) where
    "sapply_eq \<sigma> eq = (sapply \<sigma> (fst eq), sapply \<sigma> (snd eq))"

fun sapply_eqs :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equations \<Rightarrow> ('f, 'v) equations" 
  (infixr "\<cdot>s" 67) where
    "sapply_eqs \<sigma> [] = []"
|   "sapply_eqs \<sigma> (eq#s) = (sapply_eq \<sigma> eq) # (sapply_eqs \<sigma> s)"

lemma fv_sapply_eq: "fv_eq (\<sigma> \<cdot>e e) = (\<Union> x \<in> fv_eq e. fv (\<sigma> x))"
  apply(simp add: fv_eq_def sapply_eq_def fv_sapply)
  done

lemma fv_sapply_eqs: "fv_eqs (\<sigma> \<cdot>s s) = (\<Union> x \<in> fv_eqs s. fv (\<sigma> x))"
  apply(induction rule: sapply_eqs.induct)
   apply(simp)
  apply(simp add: fv_sapply_eq)
  done

lemma sapply_scomp_distrib_eq: "(\<sigma> \<circ>s \<tau>) \<cdot>e eq = \<sigma> \<cdot>e (\<tau> \<cdot>e eq)"
  apply(simp add: sapply_eq_def sapply_scomp_distrib)
  done

lemma sapply_scomp_distrib_eqs: "(\<sigma> \<circ>s \<tau>) \<cdot>s eqs = \<sigma> \<cdot>s (\<tau> \<cdot>s eqs)"
  apply(induction eqs)
   apply(simp)
  apply(simp add: sapply_scomp_distrib_eq)
  done

text \<open> (b) \<close>

definition unifies_eq :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equation \<Rightarrow> bool" where
  "(unifies_eq \<sigma> eq) \<longleftrightarrow> (\<sigma> \<cdot> (fst eq) = \<sigma> \<cdot> (snd eq))"

fun unifies :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool" where
  "(unifies \<sigma> []) \<longleftrightarrow> True"
| "(unifies \<sigma> (eq#s)) \<longleftrightarrow> ((unifies_eq \<sigma> eq) \<and> unifies \<sigma> s)"

definition is_mgu :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool" where
  "(is_mgu \<sigma> eqs) \<longleftrightarrow> ((unifies \<sigma> eqs) \<and> (\<forall> \<tau>. (unifies \<tau> eqs) \<longrightarrow> (\<exists> \<rho> . \<tau> = \<rho> \<circ>s \<sigma>)))"

text \<open> (c) \<close>

lemma unifies_sapply_eq: "unifies_eq \<sigma> (\<tau> \<cdot>e eq) \<longleftrightarrow> unifies_eq (\<sigma> \<circ>s \<tau>) eq"
  apply(simp add: sapply_eq_def unifies_eq_def sapply_scomp_distrib)
  done

lemma unifies_sapply: "unifies \<sigma> (\<tau> \<cdot>s eqs) \<longleftrightarrow> unifies (\<sigma> \<circ>s \<tau>) eqs"
  apply(induction eqs)
   apply(simp)
  apply(simp add: unifies_sapply_eq)
  done

section \<open> Assignment 3 \<close>

text \<open> (a) \<close>

(*
definition zipOpt :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list option" where
  "zipOpt l0 l1 = (if (length l0 = length l1) then Some (zip l0 l1) else None)"
*)

(*inline monad notation?*)
fun scomp_opt :: "('f, 'v) subst option \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) subst option"
  where
    "(scomp_opt None \<tau>) = None"
  | "(scomp_opt (Some \<sigma>) \<tau>) = Some (\<sigma> \<circ>s \<tau>)"

(*can we assume wellformed function applications?*)
function (sequential) unify :: "('f, 'v) equations \<Rightarrow> ('f, 'v) subst option" where
  "unify [] = Some Var"
| "unify (eq#s) = (case eq of 
    (Var x, t) \<Rightarrow> if x \<in> (fv t) then 
        scomp_opt (unify (Var(x := t) \<cdot>s s)) (Var(x := t))
      else 
        if t = (Var x) then 
          unify s 
        else 
          None
  | (t, Var x) \<Rightarrow> unify ((Var x, t)#s)
  | (Fun f0 l0, Fun f l1) \<Rightarrow> 
      if (length l0 = length l1) then 
        unify ((zip l0 l1) @ s) 
      else None
  )"
  using fv_eqs.cases apply blast
  by simp_all
termination
  sorry

text \<open> (b) \<close>

lemma unify_soundness_i: "unify eqs = Some \<sigma> \<Longrightarrow> unifies \<sigma> eqs"
  apply(induction eqs rule: unify.induct)
   apply(simp)
  sorry

lemma unify_soundness_ii: "unify eqs = Some \<sigma> \<Longrightarrow> 
  ((\<forall> \<tau>. (unifies \<tau> eqs) \<longrightarrow> (\<exists> \<rho> . \<tau> = \<rho> \<circ>s \<sigma>)))"
  apply(induction eqs rule: unify.induct)
   apply(simp)
  sorry

theorem unify_soundness: "unify eqs = Some \<sigma> \<Longrightarrow> is_mgu \<sigma> eqs"
  by(simp add: is_mgu_def unify_soundness_i unify_soundness_ii)

text \<open> (c) \<close>

theorem unify_completeness: "\<forall> eqs . (\<exists> \<sigma> . unifies \<sigma> eqs) \<longrightarrow> (unify eqs) = Some \<tau>"
  sorry

text \<open> (d) \<close>

lemma unify_fv_sapply: "unify eqs = Some \<sigma> \<Longrightarrow> fv_eqs (\<sigma> \<cdot>s eqs) \<subseteq> fv_eqs eqs"
  sorry

lemma unify_sdom_fv: "unify eqs = Some \<sigma> \<Longrightarrow> sdom \<sigma> \<subseteq> fv_eqs eqs"
  sorry

lemma unify_svran_fv: "unify eqs = Some \<sigma> \<Longrightarrow> svran \<sigma> \<subseteq> fv_eqs eqs"
  sorry

lemma unify_sdom_svran: "unify eqs = Some \<sigma> \<Longrightarrow> sdom \<sigma> \<inter> svran \<sigma> = {}"
  sorry

section \<open> Assignment 4 \<close>

text \<open> (a) \<close>

fun wf_term :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
  "wf_term fa (Var _) = True"
| "wf_term fa (Fun f lst) = ((length lst) = (fa f))"

fun wf_subst :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) subst \<Rightarrow> bool" where
  "wf_subst arity \<sigma> = (\<forall> x. wf_term arity (\<sigma> x))"

fun wf_eq :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) equation \<Rightarrow> bool" where
  "wf_eq arity (t0, t1) = ((wf_term arity t0) \<and> (wf_term arity t1))"

fun wf_eqs :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool" where
  "wf_eqs arity eqs = (\<forall> eq \<in> (set eqs). wf_eq arity eq)"

text \<open> (b) \<close>

lemma wf_term_sapply:
  "\<lbrakk> wf_term arity t; wf_subst arity \<sigma> \<rbrakk> \<Longrightarrow> wf_term arity (\<sigma> \<cdot> t)"
  apply(induction t)
   apply(simp_all)
  done

lemma wf_subst_scomp:
  "\<lbrakk> wf_subst arity \<sigma>; wf_subst arity \<tau> \<rbrakk> \<Longrightarrow> wf_subst arity (\<sigma> \<circ>s \<tau>)"
  apply(simp add: scomp_def wf_term_sapply)
  done

lemma wf_subst_unify:
  "\<lbrakk> unify eqs = Some \<sigma>; wf_eqs arity eqs \<rbrakk> \<Longrightarrow> wf_subst arity \<sigma>"
  sorry
  
  
  
  