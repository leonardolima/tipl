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

lemma fv_eqs_U: "fv_eqs eqs = \<Union>(fv_eq ` set eqs)"
  apply(induction eqs)
  by simp_all

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

(*Termination definitions and lemmas*)
fun tsize :: "('f, 'v) term \<Rightarrow> nat" where
  "tsize (Var x) = 0"
| "tsize (Fun f l) = 1 + (fold (+) (map tsize l) 0)"

fun eqs_size_fst :: "('f, 'v) equations \<Rightarrow> nat" where
  "eqs_size_fst [] = 0"
| "eqs_size_fst ((t, _)#qs) = tsize t + eqs_size_fst qs"

fun term_zip :: "('f, 'v) term list \<Rightarrow> ('f, 'v) term list \<Rightarrow> (('f, 'v) term \<times> ('f, 'v) term) list" where
  "term_zip [] t1 = []"
| "term_zip t0 [] = []"
| "term_zip (h0#t0) (h1#t1) = (h0, h1) # (term_zip t0 t1)"

lemma term_swap_X1 [simp]: 
  "card (fv_eq (Var x, Fun v va) \<union> fv_eqs s) = card (fv_eq (Fun v va, Var x) \<union> fv_eqs s)"
  by(simp add: fv_eq_def)

lemma fv_term_zip: 
 "length l0 = length l1 \<Longrightarrow> (\<Union>x\<in>set (term_zip l0 l1). fv (fst x) \<union> fv (snd x)) = (\<Union> (fv ` set l0) \<union> \<Union> (fv ` set l1))"
  apply(induction l0 l1 rule: term_zip.induct)
    apply(simp_all)
  by blast

lemma term_fun_X1 [simp]:
  "length l0 = length l1 \<Longrightarrow> card (fv_eqs (term_zip l0 l1 @ s)) = card (fv_eq (Fun f0 l0, Fun f0 l1) \<union> fv_eqs s)"
  apply(induction l0 l1 rule: term_zip.induct)
  by(simp_all add: fv_eq_def fv_eqs_U fv_term_zip Un_assoc Un_left_commute)

lemma term_fun_X2 [simp]:
  "length l0 = length l1 \<Longrightarrow> eqs_size_fst (term_zip l0 l1 @ s) < Suc (fold (+) (map tsize l0) 0 + eqs_size_fst s)"
  apply(induction l0 l1 rule: term_zip.induct)
  by (simp_all add: fold_plus_sum_list_rev)

lemma term_simp_X1 [simp]:
  "t = Var x \<Longrightarrow> card (fv_eqs s) \<le> card (fv_eq (Var x, Var x) \<union> fv_eqs s)"
  by(simp add: fv_eq_def card_insert_le)
  
lemma term_unify_X1 [simp]:
  assumes fvt: "x \<notin> fv t"
  shows "card (fv_eqs (Var(x := t) \<cdot>s s)) < card (fv_eq (Var x, t) \<union> fv_eqs s)"
  sorry

(*Unification algorithm*)
fun scomp_opt :: "('f, 'v) subst option \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) subst option"
  where
    "(scomp_opt None \<tau>) = None"
  | "(scomp_opt (Some \<sigma>) \<tau>) = Some (\<sigma> \<circ>s \<tau>)" 

function (sequential) unify :: "('f, 'v) equations \<Rightarrow> ('f, 'v) subst option" where
  "unify [] = Some Var"
| "unify ((Var x, t)#s) = (if x \<notin> (fv t) then 
        scomp_opt (unify (Var(x := t) \<cdot>s s)) (Var(x := t))
      else 
        if t = (Var x) then 
          unify s 
        else 
          None)"
| "unify ((t, Var x)#s) = unify ((Var x, t)#s)"
| "unify ((Fun f0 l0, Fun f1 l1)#s) = (
  if (f0 = f1) \<and> (length l0 = length l1) then 
    unify ((term_zip l0 l1) @ s) 
  else None)"
            apply pat_completeness
            by(simp_all)
termination
  apply(relation "measures[
    (\<lambda> eqs . card (fv_eqs eqs)),
    (\<lambda> eqs . eqs_size_fst eqs),
    (\<lambda> eqs . size eqs)
  ]")
  by(simp_all add: le_imp_less_or_eq)

text \<open> (b) \<close>

lemma unifies_app: "unifies \<sigma> (eqs0 @ eqs) \<Longrightarrow> unifies \<sigma> eqs0 \<and> unifies \<sigma> eqs"
  sorry

lemma temp: 
  assumes assms: "unifies \<sigma> (zip l0 l1 @ s)" and 
      "f0 = f1 \<and> length l0 = length l1" and 
      "unify (zip l0 l1 @ s) = Some \<sigma>"
  shows "map ((\<cdot>) \<sigma>) l0 = map ((\<cdot>) \<sigma>) l1 \<and> unifies \<sigma> s"  
proof -
  from assms have "unifies \<sigma> s" sorry
    then show ?thesis sorry
  qed

lemma unify_soundness_i: "unify eqs = Some \<sigma> \<Longrightarrow> unifies \<sigma> eqs"
  proof(induction eqs rule: unify.induct)
    case 1
    then show ?case by simp
  next
    case (2 x t s)
    then show ?case sorry
  next
    case (3 v va x s)
    then show ?case proof -
      from 3(2) have swap: 
        "unify ((Fun v va, Var x) # s) = unify ((Var x, Fun v va) # s)" by simp
      from 3 swap have
        "unifies \<sigma> ((Var x, Fun v va) # s)" by simp
      then show ?thesis by (simp add: unifies_eq_def)
    qed
  next
    case (4 f0 l0 f1 l1 s)
    then show ?case proof-
      from 4(2) have assms:
        "(f0 = f1 \<and> length l0 = length l1) \<and> (unify (term_zip l0 l1 @ s) = Some \<sigma>)"
        apply(simp)
        by (metis option.distinct(1))
      from 4(1) assms have
        "unifies \<sigma> (term_zip l0 l1 @ s)" by simp
      from assms have eq:
        "unify ((Fun f0 l0, Fun f1 l1) # s) = unify (term_zip l0 l1 @ s)"
        by simp
      from 4(1) assms show ?thesis
        sorry
    qed
  qed

lemma unify_soundness_ii: "unify eqs = Some \<sigma> \<Longrightarrow> 
  ((\<forall> \<tau>. (unifies \<tau> eqs) \<longrightarrow> (\<exists> \<rho> . \<tau> = \<rho> \<circ>s \<sigma>)))"
proof(induction eqs rule: unify.induct)
  case 1
  then show ?case by simp
next
  case (2 x t s)
  then show ?case sorry
next
  case (3 v va x s)
  then show ?case proof -
      from 3(2) have swap: 
        "unify ((Fun v va, Var x) # s) = unify ((Var x, Fun v va) # s)" by simp
      from 3 swap have
        "\<forall>\<tau>. unifies \<tau> ((Var x, Fun v va) # s) \<longrightarrow> (\<exists>\<rho>. \<tau> = \<rho> \<circ>s \<sigma>)" by simp
      then show ?thesis by (simp add: unifies_eq_def)
    qed
next
  case (4 f0 l0 f1 l1 s)
  then show ?case sorry
qed

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
  "wf_term arity (Var _) = True"
| "wf_term arity (Fun f lst) = (((length lst) = (arity f)) \<and> (\<forall> t \<in> set lst. (wf_term arity t)))"

definition wf_subst :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) subst \<Rightarrow> bool" where
  "wf_subst arity \<sigma> = (\<forall> x. wf_term arity (\<sigma> x))"

fun wf_eq :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) equation \<Rightarrow> bool" where
  "wf_eq arity (t0, t1) = ((wf_term arity t0) \<and> (wf_term arity t1))"

definition wf_eqs :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool" where
  "wf_eqs arity eqs = (\<forall> eq \<in> (set eqs). wf_eq arity eq)"

text \<open> (b) \<close>

lemma wf_term_sapply:
  "\<lbrakk> wf_term arity t; wf_subst arity \<sigma> \<rbrakk> \<Longrightarrow> wf_term arity (\<sigma> \<cdot> t)"
  apply(induction t)
   apply(simp_all add: wf_subst_def)
  done

lemma wf_subst_scomp:
  "\<lbrakk> wf_subst arity \<sigma>; wf_subst arity \<tau> \<rbrakk> \<Longrightarrow> wf_subst arity (\<sigma> \<circ>s \<tau>)"
  apply(simp add: wf_subst_def scomp_def wf_term_sapply)
  done

lemma wf_zip: "\<lbrakk>length l0 = length l1; 
    \<forall>t\<in>set l0. wf_term arity t; 
    \<forall>t\<in>set l1. wf_term arity t;
    wf_eqs arity s\<rbrakk> \<Longrightarrow> wf_eqs arity ((term_zip l0 l1)@s)"
  apply(induction rule: term_zip.induct)
  by(simp_all add: wf_eqs_def)

lemma wf_subst_unify:
  "\<lbrakk> unify eqs = Some \<sigma>; wf_eqs arity eqs \<rbrakk> \<Longrightarrow> wf_subst arity \<sigma>"
proof(induction eqs rule: unify.induct)
  case 1
  then show ?case by(simp add: wf_subst_def)
next
  case (2 x t s)
  then show ?case sorry
next
  case (3 v va x s)
  then show ?case by(simp add: wf_eqs_def wf_subst_def)
next
  case (4 f0 l0 f1 l1 s)
  then show ?case proof -
    from 4(2) have s0:
      "f0 = f1 \<and> length l0 = length l1"
      by (simp; metis option.distinct(1))
    from 4(2) have s1:
      "unify (term_zip l0 l1 @ s) = Some \<sigma>"
      by (simp; metis option.distinct(1))
    from 4(3) have s2:
      "(\<forall> t \<in> set l0 . wf_term arity t) \<and> (\<forall> t \<in> set l1 . wf_term arity t)" 
      by(simp add: wf_eqs_def)
    from 4(3) have s3:
      "wf_eqs arity s" 
      by(simp add: wf_eqs_def)
    from s0 s2 s3 have s4:
      "wf_eqs arity ((term_zip l0 l1)@s)"
      by(simp add: wf_zip)
    from 4(1) s0 s1 s4 show ?thesis by simp 
  qed
qed
  
  
  
  