theory Unification
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
  by(simp_all)
  

lemma sapply_cong: "\<lbrakk> \<And>x. x \<in> fv t \<Longrightarrow> \<sigma> x = \<tau> x \<rbrakk> \<Longrightarrow> \<sigma> \<cdot> t = \<tau> \<cdot> t"
  apply(induction t rule: fv.induct)
   apply(simp_all)
  by(blast)

lemma scomp_sapply: "(\<sigma> \<circ>s \<tau>)x = \<sigma> \<cdot> (\<tau> x)"
  by(simp add: scomp_def)
  

lemma sapply_scomp_distrib: "(\<sigma> \<circ>s \<tau>) \<cdot> t = \<sigma> \<cdot> (\<tau> \<cdot> t)"
  apply(induction t)
  by(simp_all add: scomp_def)
  
lemma scomp_assoc: "(\<sigma> \<circ>s \<tau>) \<circ>s \<rho> = \<sigma> \<circ>s (\<tau> \<circ>s \<rho>)"
  by(simp add: fun_eq_iff scomp_def sapply_scomp_distrib)
  
lemma sapply_Var[simp]: "Var \<cdot> t = t"
  apply(induction t)
  by(simp_all add: map_idI)
  
lemma scomp_Var[simp]: "\<sigma> \<circ>s Var = \<sigma>"
  by(simp add: fun_eq_iff scomp_def)

lemma Var_scomp[simp]: "Var \<circ>s \<sigma> = \<sigma>"
  by(simp add: fun_eq_iff scomp_def)
  

text \<open> (d) \<close>

definition sdom :: "('f, 'v) subst \<Rightarrow> 'v set" where
  "sdom \<sigma> = { x . (\<sigma> x) \<noteq> (Var x)}"

definition svran :: "('f, 'v) subst \<Rightarrow> 'v set" where
  "svran \<sigma> = \<Union>(fv ` (\<sigma> ` sdom \<sigma>))"

lemma sdom_Var[simp]: "sdom Var = {}"
  by(simp add: sdom_def)
  
lemma svran_Var[simp]: "svran Var = {}"
  by(simp add: svran_def)
  
lemma sdom_single_non_trivial[simp]:
  "t \<noteq> Var x \<Longrightarrow> sdom (Var( x := t )) = {x}"
  by(simp add: fun_upd_def sdom_def)
    

lemma svran_single_non_trivial[simp]:
  "t \<noteq> Var x \<Longrightarrow> svran (Var( x := t )) = fv t"
  by(simp add: fun_upd_def svran_def sdom_def)

lemma svapply_svdom_svran:
  "x \<in> fv (\<sigma> \<cdot> t) \<Longrightarrow> x \<in> (fv t - sdom \<sigma>) \<union> svran \<sigma>"
  apply(induction t)
   apply(simp_all add: svran_def sdom_def)
   apply(metis fv.simps(1) singletonD)
  by(blast)

lemma sdom_scomp: "sdom (\<sigma> \<circ>s \<tau>) \<subseteq> sdom \<sigma> \<union> sdom \<tau>"
  apply(simp add: sdom_def scomp_def)
  by(auto)
  

lemma svran_scomp: "svran (\<sigma> \<circ>s \<tau>) \<subseteq> svran \<sigma> \<union> svran \<tau>"
  apply(simp add: svran_def scomp_def fv_sapply sdom_def)
  by(force)
  

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

lemma sapply_eqs_map: "sapply_eqs \<sigma> eqs = map (sapply_eq \<sigma>) eqs"
  apply(induction eqs)
  by(simp_all)

lemma fv_sapply_eq: "fv_eq (\<sigma> \<cdot>e e) = (\<Union> x \<in> fv_eq e. fv (\<sigma> x))"
  by(simp add: fv_eq_def sapply_eq_def fv_sapply)
  

lemma fv_sapply_eqs: "fv_eqs (\<sigma> \<cdot>s s) = (\<Union> x \<in> fv_eqs s. fv (\<sigma> x))"
  apply(induction rule: sapply_eqs.induct)
   apply(simp)
  by(simp add: fv_sapply_eq)
  

lemma sapply_scomp_distrib_eq: "(\<sigma> \<circ>s \<tau>) \<cdot>e eq = \<sigma> \<cdot>e (\<tau> \<cdot>e eq)"
  by(simp add: sapply_eq_def sapply_scomp_distrib)
  

lemma sapply_scomp_distrib_eqs: "(\<sigma> \<circ>s \<tau>) \<cdot>s eqs = \<sigma> \<cdot>s (\<tau> \<cdot>s eqs)"
  apply(induction eqs)
   apply(simp)
  by(simp add: sapply_scomp_distrib_eq)
  

text \<open> (b) \<close>

definition unifies_eq :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equation \<Rightarrow> bool" where
  "(unifies_eq \<sigma> eq) \<longleftrightarrow> (\<sigma> \<cdot> (fst eq) = \<sigma> \<cdot> (snd eq))"
(*
fun unifies_eq_fun :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equation \<Rightarrow> bool" where
  "(unifies_eq_fun \<sigma> (t0, t1)) \<longleftrightarrow> (\<sigma> \<cdot> t0 = \<sigma> \<cdot> t1)"
>>>>>>> part1:Part1.thy

lemma unifies_eq_equiv: "unifies_eq = unifies_eq_fun"
  by(simp add: fun_eq_iff unifies_eq_def)
*)
fun unifies :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool" where
  "(unifies \<sigma> []) = True"
| "(unifies \<sigma> (eq#s)) = ((unifies_eq \<sigma> eq) \<and> unifies \<sigma> s)"

lemma unifies_forall: "unifies \<sigma> lst = (\<forall>eq \<in> set lst . unifies_eq \<sigma> eq)"
  apply(induction lst)
  by(simp_all)

definition is_mgu :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool" where
  "(is_mgu \<sigma> eqs) = ((unifies \<sigma> eqs) \<and> (\<forall> \<tau>. (unifies \<tau> eqs) \<longrightarrow> (\<exists> \<rho> . \<tau> = \<rho> \<circ>s \<sigma>)))"

text \<open> (c) \<close>

lemma unifies_sapply_eq: "unifies_eq \<sigma> (\<tau> \<cdot>e eq) \<longleftrightarrow> unifies_eq (\<sigma> \<circ>s \<tau>) eq"
  by(simp add: sapply_eq_def unifies_eq_def sapply_scomp_distrib)
  

lemma unifies_sapply: "unifies \<sigma> (\<tau> \<cdot>s eqs) \<longleftrightarrow> unifies (\<sigma> \<circ>s \<tau>) eqs"
  apply(induction eqs)
  by(simp_all add: unifies_sapply_eq)
  

section \<open> Assignment 3 \<close>

text \<open> (a) \<close>

(*Termination definitions and lemmas*)
fun tsize :: "('f, 'v) term \<Rightarrow> nat" where
  "tsize (Var x) = 0"
| "tsize (Fun f l) = 1 + (fold (+) (map tsize l) 0)"

fun eqs_size_fst :: "('f, 'v) equations \<Rightarrow> nat" where
  "eqs_size_fst [] = 0"
| "eqs_size_fst ((t, _)#qs) = tsize t + eqs_size_fst qs"

(* equivalent to zip, but allows induction *)
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

lemma set_elems_card: 
  assumes assms: "\<forall> v \<in> setA . v \<in> setB" and "x \<in> setB" and "x \<notin> setA" and "finite setB"
  shows "card setA < card setB"
proof-
  from assms have 
    "setA \<subset> setB" 
    by blast
  from this assms(4) show ?thesis by (simp add: psubset_card_mono)  
qed

lemma fv_finite:
  "finite (fv t)"
  apply(induction t)
  by(simp_all)

lemma term_unify_X1 [simp]:
  assumes fvt: "x \<notin> fv t"
  shows "card (fv_eqs (Var(x := t) \<cdot>s s)) < card (fv_eq (Var x, t) \<union> fv_eqs s)"
proof-
  have
    "finite (fv_eq (Var x, t) \<union> fv_eqs s)"
    by(simp add: fv_eqs_U fv_eq_def fv_finite)
  moreover from fvt have
    "x \<notin> fv_eqs (Var(x := t) \<cdot>s s)"
    by(simp add: fv_sapply_eqs)
  moreover have
    "x \<in> fv_eq (Var x, t) \<union> fv_eqs s"
    by(simp add: fv_eq_def)
  moreover have
    "\<forall> v \<in> fv_eqs (Var(x := t) \<cdot>s s) . v \<in> (fv_eq (Var x, t) \<union> fv_eqs s)"
    by(simp add: fv_sapply_eqs fv_eq_def)
  ultimately show ?thesis by (simp add: set_elems_card)
qed


(*Unification algorithm*)
fun scomp_opt :: "('f, 'v) subst option \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) subst option"
  where
    "(scomp_opt None \<tau>) = None"
  | "(scomp_opt (Some \<sigma>) \<tau>) = Some (\<sigma> \<circ>s \<tau>)" 

function (sequential) unify :: "('f, 'v) equations \<Rightarrow> ('f, 'v) subst option" where
  Base: "unify [] = Some Var"
| UnSi: "unify ((Var x, t)#s) = (if x \<notin> (fv t) then 
        scomp_opt (unify (Var(x := t) \<cdot>s s)) (Var(x := t))
      else 
        if t = (Var x) then 
          unify s 
        else 
          None)"
| Swap: "unify ((t, Var x)#s) = unify ((Var x, t)#s)"
| Fun:  "unify ((Fun f0 l0, Fun f1 l1)#s) = (
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

lemma fun_unifies: "\<lbrakk>length l0 = length l1; f0 = f1 \<rbrakk> \<Longrightarrow> unifies \<sigma> (term_zip l0 l1 @ s) = unifies \<sigma> ((Fun f0 l0, Fun f1 l1)#s)"
  apply(induction rule: term_zip.induct)
  by(simp_all add: unifies_eq_def)

lemma unifies_app: "unifies \<sigma> (l0 @ l1) \<Longrightarrow> unifies \<sigma> l0 \<and> unifies \<sigma> l1"
  by(simp add: unifies_forall)

lemma scomp_opt_fst: "scomp_opt (unify eqs) \<tau> = Some \<rho> \<Longrightarrow> \<exists> \<sigma> . unify eqs = Some \<sigma>"
  by(metis scomp_opt.elims)

lemma subst_redundancy: "x \<notin> fv t \<Longrightarrow> \<sigma> \<circ>s Var(x := t) \<circ>s Var(x := t) = \<sigma> \<circ>s Var(x := t)"
  by(simp only: fun_eq_iff; metis scomp_def fun_upd_apply sapply_cong scomp_Var scomp_assoc)

lemma unify_soundness_i: "unify eqs = Some \<sigma> \<Longrightarrow> unifies \<sigma> eqs"
  proof(induction arbitrary: \<sigma> rule: unify.induct)
    case 1
    then show ?case by simp
  next
    case unsi: (2 x t s)
    then show ?case proof-
      have "x \<notin> fv t \<or> ~ x \<notin> fv t" by simp
      then consider "x \<notin> fv t" | "~ x \<notin> fv t" by blast
      then show ?case proof(cases)
        case 1
        then show ?thesis proof-
          from 1 unsi(3) have opt:
            "scomp_opt (unify (Var(x := t) \<cdot>s s)) (Var(x := t)) = Some \<sigma>"
            by simp
          hence
            "\<exists> \<sigma> . unify (Var(x := t) \<cdot>s s) = Some \<sigma>"
            by (simp add: scomp_opt_fst)
          then obtain \<sigma>p where sigp_unify:
            "unify (Var(x := t) \<cdot>s s) = Some \<sigma>p"
            by(rule exE)
          from this opt have sig:
            "\<sigma> = \<sigma>p \<circ>s Var(x := t)" by simp
          from sigp_unify 1 unsi.IH(1) have 
            "unifies \<sigma>p (Var(x := t) \<cdot>s s)" 
            by simp
          from this sig 1 have
            "unifies \<sigma> s"
            by(simp add: unifies_sapply subst_redundancy scomp_assoc)
          moreover from sig 1 have
            "unifies_eq \<sigma> (Var x, t)"
            by (simp add: unifies_eq_def; metis fun_upd_apply sapply_cong scomp_Var scomp_sapply)
         ultimately show ?thesis by simp
        qed
      next
        case 2
        then show ?thesis proof-
          from 2 unsi(3) have
            "t = Var x"
            by fastforce
          moreover from this unsi(3) have
            "unify s = Some \<sigma>"
            by simp
          ultimately show ?thesis using unsi(2) 2 by(simp add: unifies_eq_def)
        qed
      qed
    qed
  next
    case (3 v va x s)
    then show ?case by (simp add: unifies_eq_def)
  next
    case (4 f0 l0 f1 l1 s)
    then show ?case proof-
      from 4(2) have
        "(f0 = f1 \<and> length l0 = length l1) \<and> (unify (term_zip l0 l1 @ s) = Some \<sigma>)"
        by (simp; metis option.distinct(1))
      moreover from this 4(1) have
        "unifies \<sigma> (term_zip l0 l1 @ s)" by simp
      ultimately show ?thesis using 4(1) by(simp only: fun_unifies)
    qed
  qed

lemma unify_soundness_ii: "unify eqs = Some \<sigma> \<Longrightarrow> 
  ((\<forall> \<tau>. (unifies \<tau> eqs) \<longrightarrow> (\<exists> \<rho> . \<tau> = \<rho> \<circ>s \<sigma>)))"
proof(induction eqs arbitrary: \<sigma> rule: unify.induct)
  case 1
  then show ?case by simp
next
  case unsi: (2 x t s)
  then show ?case proof-
      have "x \<notin> fv t \<or> ~ x \<notin> fv t" by simp
      then consider "x \<notin> fv t" | "~ x \<notin> fv t" by blast
      then show ?case proof(cases)
        case 1
        then show ?thesis proof-
          from 1 unsi(3) have opt:
            "scomp_opt (unify (Var(x := t) \<cdot>s s)) (Var(x := t)) = Some \<sigma>"
            by simp
          hence
            "\<exists> \<sigma> . unify (Var(x := t) \<cdot>s s) = Some \<sigma>"
            by (simp add: scomp_opt_fst)
          then obtain \<sigma>p where sigp_unify:
            "unify (Var(x := t) \<cdot>s s) = Some \<sigma>p"
            by(rule exE)
          from this opt have sig:
            "\<sigma> = \<sigma>p \<circ>s Var(x := t)" by simp
          from sigp_unify 1 unsi.IH(1) have IS:
            "\<forall>\<tau>. unifies \<tau> (Var(x := t) \<cdot>s s) \<longrightarrow> (\<exists>\<rho>. \<tau> = \<rho> \<circ>s \<sigma>p)"
            by simp
          have "\<forall>\<tau>. unifies \<tau> ((Var x, t) # s) \<longrightarrow> (\<exists>\<rho>. \<tau> = \<rho> \<circ>s \<sigma>)" proof(rule allI)
            fix \<tau>
            show "unifies \<tau> ((Var x, t) # s) \<longrightarrow> (\<exists>\<rho>. \<tau> = \<rho> \<circ>s \<sigma>)"
            proof(rule impI)
              assume asm: "unifies \<tau> ((Var x, t) # s)"
              show "(\<exists>\<rho>. \<tau> = \<rho> \<circ>s \<sigma>)" proof-
                from asm have
                  "\<tau> x = \<tau> \<cdot> t" and "unifies \<tau> s"
                  by(simp_all add: unifies_eq_def)
                moreover from this 1 have t_def:
                  "\<tau> \<circ>s Var(x := t) = \<tau>"
                  by(simp add: fun_eq_iff scomp_sapply)
                ultimately have
                  "unifies \<tau> (Var(x := t) \<cdot>s s)"
                  by(simp add: unifies_sapply)
                from this IS obtain \<rho> where
                  "\<tau> = \<rho> \<circ>s \<sigma>p"
                  by blast
                hence
                  "\<tau> \<circ>s Var(x := t) = \<rho> \<circ>s \<sigma>p \<circ>s Var(x := t)"
                  by (simp add: scomp_assoc)
                from this t_def sig have
                  "\<tau> = \<rho> \<circ>s \<sigma>"
                  by auto
                then show ?thesis
                  by auto
              qed
            qed
          qed
          then show ?thesis by simp
        qed
      next
        case 2
        then show ?thesis proof-
          from 2 unsi(3) have
            "t = Var x"
            by fastforce
          moreover from this unsi(3) have
            "unify s = Some \<sigma>"
            by simp
          ultimately show ?thesis using unsi(2) 2 by(simp add: unifies_eq_def)
        qed
      qed
  qed
next
  case (3 v va x s)
  then show ?case by (simp add: unifies_eq_def) 
next
  case (4 f0 l0 f1 l1 s)
  then show ?case proof-
      fix \<tau> 
      from 4(2) have
        "(f0 = f1 \<and> length l0 = length l1) \<and> (unify (term_zip l0 l1 @ s) = Some \<sigma>)"
        by(simp; metis option.distinct(1))
      moreover from this 4(1) have
        "\<forall>\<tau>. unifies \<tau> (term_zip l0 l1 @ s) \<longrightarrow> (\<exists>\<rho>. \<tau> = \<rho> \<circ>s \<sigma>)" 
        by simp
      ultimately show ?thesis 
        by (metis fun_unifies)
    qed
  qed

theorem unify_soundness: "unify eqs = Some \<sigma> \<Longrightarrow> is_mgu \<sigma> eqs"
  by(simp add: is_mgu_def unify_soundness_i unify_soundness_ii)

text \<open> (c) \<close>

lemma unifies_wf: "unifies_eq \<sigma> (Fun f0 l0, Fun f1 l1) \<Longrightarrow> f0 = f1 \<and> length l0 = length l1"
  by (simp add: unifies_eq_def; metis length_map)

lemma unifies_zip: "map ((\<cdot>) \<sigma>) l0 = map ((\<cdot>) \<sigma>) l1 \<Longrightarrow> unifies \<sigma> (term_zip l0 l1)"
  apply(induction rule: term_zip.induct)
  by(simp_all add: unifies_eq_def)

(* denotes whether the first term is contained in the second term*)
fun in_term :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" 
  (infixr "tin" 67) where
  "in_term t (Var x) = (t = Var x)"
| "in_term t (Fun f l) = ((t = Fun f l) \<or> (\<exists> t0 \<in> set l . in_term t t0))"

lemma fold_eq_sum_list: "(fold (+) (l :: nat list) 0) = (sum_list l)"
  apply(induction l)
   apply simp
  by (simp add: fold_plus_sum_list_rev)

lemma in_args_size: 
  assumes assms: "t0 \<in> set l"
  shows "tsize t0 < tsize (Fun f l)"
proof-
  from assms(1) have
    "tsize t0 \<in> set (map tsize l)"
    by simp
  moreover from this have
    "tsize t0 \<le> sum_list (map tsize l)"
    by(simp only: member_le_sum_list)
  moreover from this have
    "tsize t0 \<le> (fold (+) (map tsize l) 0)"
    by(simp add: fold_eq_sum_list)
  ultimately show ?thesis by simp
qed

lemma in_term_size: "\<lbrakk> t tin t0 \<rbrakk> \<Longrightarrow> tsize t \<le> tsize t0"
proof(induction t0 rule: in_term.induct)
  case (1 t x)
  then show ?case by simp
next
  case IS: (2 t f l)
  then show ?case proof-
    from IS(2) have "(t = Fun f l) \<or> (\<exists> t0 \<in> set l . in_term t t0)" by simp
    then consider "(t = Fun f l)" | "(\<exists> t0 \<in> set l . in_term t t0)" by blast
    then show ?case proof(cases)
      case 1
      then show ?thesis using IS by simp
    next
      case 2
      then show ?thesis proof-
        from 2 obtain t0 where t0l: "t0 \<in> set l" and tt0: "t tin t0"
          by auto
        from this IS(1) have 
          "tsize t \<le> tsize t0"
          by blast
        moreover from t0l have 
          "tsize t0 < tsize (Fun f l)"
          by(simp only: in_args_size)
        ultimately show ?thesis by simp
      qed
    qed
  qed
qed

lemma fv_in_term: "x \<in> fv t \<Longrightarrow> (Var x) tin t"
  by(induction t rule: term.induct; simp; auto)

lemma in_itself: "t tin t"
  apply(induction t)
  by simp_all

lemma in_term_sapply: "t tin t0 \<Longrightarrow> (\<sigma> \<cdot> t) tin (\<sigma> \<cdot> t0)"
  apply(induction t0 rule: term.induct)
   apply(simp add: in_itself)
  by(simp add: in_itself; auto)  

lemma sapply_size:
  assumes assms: "x \<in> fv t" and "t \<noteq> Var x"
  shows "tsize (\<sigma> \<cdot> t) > tsize (\<sigma> x)"
proof-
  from assms(1) have
    "Var x tin t"
    by(simp only: fv_in_term)
  hence
    "(\<sigma> \<cdot> Var x) tin \<sigma> \<cdot> t"
    using in_term_sapply by fastforce
  hence sigx:
    "\<sigma> x tin \<sigma> \<cdot> t"
    by simp
  from assms obtain f l where t_def:
    "\<sigma> \<cdot> t = Fun f l"
    by (metis fv_in_term in_term.elims(2) sapply.simps(2))
  from this assms sigx obtain t0 where
    "t0 \<in> set l" and sigx_t0: "\<sigma> x tin t0"
    by (smt (z3) \<open>Var x tin t\<close> image_eqI in_term.elims(2) in_term_sapply list.set_map sapply.simps(1) sapply.simps(2) term.inject(2))
  from this t_def have
    "tsize (t0) < tsize (\<sigma> \<cdot> t)"
    by(simp only: in_args_size)
  moreover from sigx_t0 have
    "tsize (\<sigma> x) \<le> tsize t0"
    by(simp only: in_term_size)
  ultimately show ?thesis by simp
qed

lemma case_occurs:
  assumes assms: "x \<in> fv t" and "unifies \<sigma> ((Var x, t) # s)"
  shows "t = Var x"
proof(rule ccontr)
  assume cont: "t \<noteq> Var x"
  from cont assms(1) have
    "tsize (\<sigma> \<cdot> t) > tsize (\<sigma> x)"
    by (simp add: sapply_size)
  moreover from assms(2) have
    "tsize (\<sigma> \<cdot> t) = tsize (\<sigma> x)"
    by(simp add: unifies_eq_def)
  ultimately show False by simp
qed

lemma lemma2: "(\<exists> \<sigma> . unifies \<sigma> eqs) \<Longrightarrow> \<not> Option.is_none (unify eqs)"
proof(induction rule: unify.induct)
  case 1
  then show ?case by simp
next
  case unsi: (2 x t s)
  then show ?case proof-
      have "x \<notin> fv t \<or> ~ x \<notin> fv t" by simp
      then consider "x \<notin> fv t" | "~ x \<notin> fv t" by blast
      then show ?case proof(cases)
        case 1
        then show ?thesis proof-
          from unsi(3) obtain \<sigma> where si:
            "unifies \<sigma> ((Var x, t) # s)"
            by(rule exE)
          hence
            "\<sigma> x = \<sigma> \<cdot> t" and sig_s: "unifies \<sigma> s"
            by(simp_all add: unifies_eq_def)
          from this 1 have
            "\<sigma> \<circ>s Var(x := t) = \<sigma>"
            by (simp add: scomp_def ext)
          from this sig_s have
            "unifies \<sigma> (Var(x := t) \<cdot>s s)"
            by (simp add: unifies_sapply)
          from this 1 unsi(1) have
            "\<not> Option.is_none (unify (Var(x := t) \<cdot>s s))"
            by auto
          hence
            "\<not> Option.is_none (scomp_opt (unify (Var(x := t) \<cdot>s s)) (Var(x := t)))"
            using Option.is_none_def by fastforce
          then show ?thesis
            by (simp add: "1")
        qed
      next
        case 2
        then show ?thesis proof-
          from unsi(3) obtain \<sigma> where si:
            "unifies \<sigma> ((Var x, t) # s)"
            by(rule exE)
          hence
            "\<exists> \<sigma> . unifies \<sigma> s"
            by(simp; blast)
          moreover from si 2 have
            "t = Var x"
            by(simp add: case_occurs)
          ultimately show ?thesis using unsi(2) 2 by simp
        qed
      qed
    qed
next
  case (3 v va x s)
  then show ?case proof-
    from 3(2) obtain \<sigma> where "unifies \<sigma> ((Fun v va, Var x) # s)"
      by(rule exE)
    then have 
      "unifies \<sigma> ((Var x, Fun v va) # s)"
      by(simp add: unifies_eq_def)
    then have
      "\<exists>\<sigma>. unifies \<sigma> ((Var x, Fun v va) # s)"
      by blast
    then have
      "\<not> Option.is_none (unify ((Var x, Fun v va) # s))"
      using 3(1) by simp
    then show ?thesis by simp
  qed
next
  case (4 f0 l0 f1 l1 s)
  then show ?case proof-
    from 4(2) obtain \<sigma> where "unifies \<sigma> ((Fun f0 l0, Fun f1 l1) # s)"
      by(rule exE)
    hence
      "unifies_eq \<sigma> (Fun f0 l0, Fun f1 l1)"
      by(simp)
    hence lens:
      "f0 = f1 \<and> length l0 = length l1"
      by(simp add: unifies_wf)
    from 4(2) obtain \<sigma> where "unifies \<sigma> ((Fun f0 l0, Fun f1 l1) # s)"
      by(rule exE)
    hence
      "unifies \<sigma> (term_zip l0 l1 @ s)"
      using lens by(simp only: fun_unifies)
    hence 
      "\<exists> \<sigma> . unifies \<sigma> (term_zip l0 l1 @ s)"
      by blast
    from this lens 4(1) have  
      "\<not> Option.is_none (unify (term_zip l0 l1 @ s))"
      by simp
    moreover have
      "unify (term_zip l0 l1 @ s) = unify ((Fun f0 l0, Fun f1 l1) # s)"
      using lens by simp
    ultimately show ?thesis by(simp)
  qed
qed
        
theorem unify_completeness: "(\<exists> \<sigma> . unifies \<sigma> eqs \<longrightarrow> unify eqs = Some \<sigma>)"
  by (metis is_none_simps(1) lemma2 option.exhaust_sel) 

text \<open> (d) \<close>

lemma fv_swap:
  "fv_eq (t0, t1) = fv_eq (t1, t0)"
  by(simp add: fv_eq_def; blast)

lemma fv_fun:
  "length l0 = length l1 \<Longrightarrow> fv_eqs ((Fun f0 l0, Fun f1 l1) # s) = fv_eqs ((term_zip l0 l1) @ s)"
proof(induction rule: term_zip.induct)
  case (1 t1)
  then show ?case by (simp add: fv_eq_def)
next
  case (2 v va)
  then show ?case by simp
next
  case (3 h0 t0 h1 t1)
  then show ?case proof-
    from 3(2) have lens:
      "length t0 = length t1"
      by simp
    have
      "fv_eqs ((Fun f0 (h0 # t0), Fun f1 (h1 # t1)) # s) = fv h0 \<union> fv h1 \<union> fv_eqs ((Fun f0 t0, Fun f1 t1) # s)"
      by(simp add: fv_eq_def; auto)
    moreover have
      "... = fv h0 \<union> fv h1 \<union> fv_eqs (term_zip t0 t1 @ s)"
      using "3.IH" lens by(simp)
    moreover have
      "... = fv_eqs (term_zip (h0 # t0) (h1 # t1) @ s)"
      by(simp add: fv_eq_def)
    ultimately show ?thesis by simp
  qed
qed


lemma lemma1: "fv (\<sigma> \<cdot> t) \<subseteq> (fv t - sdom \<sigma>) \<union> svran \<sigma>"
  apply(induction t)
   apply(meson subsetI svapply_svdom_svran)
  by auto

lemma lemma1_eq: "fv_eq (\<sigma> \<cdot>e eq) \<subseteq> (fv_eq eq - sdom \<sigma>) \<union> svran \<sigma>"
  apply(induction eq)
  apply(simp add: fv_eq_def sapply_eq_def)
  by (smt (verit) Diff_subset_conv Un_Diff inf_sup_aci(5) le_supI1 lemma1)

lemma lemma1_eqs: "fv_eqs (\<sigma> \<cdot>s eqs) \<subseteq> (fv_eqs eqs - sdom \<sigma>) \<union> svran \<sigma>"
proof(induction eqs rule: fv_eqs.induct)
  case 1
  then show ?case by simp
next
  case (2 eq s)
  then show ?case proof-
    have 
      "fv_eqs (\<sigma> \<cdot>s (eq # s)) = fv_eq (\<sigma> \<cdot>e eq) \<union> fv_eqs (\<sigma> \<cdot>s s)"
      by simp
    moreover have
      "fv_eq (\<sigma> \<cdot>e eq) \<subseteq> (fv_eq eq - sdom \<sigma>) \<union> svran \<sigma>"
      by (simp only: lemma1_eq)
    ultimately show ?thesis
      using "2" by auto
  qed
qed

lemma lemma1_eqs_single: "x \<notin> fv t \<Longrightarrow> fv_eqs (Var(x := t) \<cdot>s s) \<subseteq> fv t \<union> fv_eqs s"
using lemma1_eqs by(smt (verit, del_insts) Diff_iff Diff_insert_absorb Un_Diff Un_commute fv.simps(1) 
                                  insert_Diff1 sdom_single_non_trivial singletonI subset_eq svran_single_non_trivial)

lemma unify_svran_fv: "unify eqs = Some \<sigma> \<Longrightarrow> svran \<sigma> \<subseteq> fv_eqs eqs"
proof(induction arbitrary: \<sigma> rule: unify.induct)
  case 1
  then show ?case by simp
next
  case unsi: (2 x t s)
  then show ?case proof-
    have "x \<notin> fv t \<or> ~ x \<notin> fv t" by simp
    then consider "x \<notin> fv t" | "~ x \<notin> fv t" by blast
    then show ?case proof(cases)
      case 1
      then show ?thesis proof-
        from 1 unsi(3) have opt:
          "scomp_opt (unify (Var(x := t) \<cdot>s s)) (Var(x := t)) = Some \<sigma>"
          by simp
        hence
          "\<exists> \<sigma> . unify (Var(x := t) \<cdot>s s) = Some \<sigma>"
          by (simp add: scomp_opt_fst)
        then obtain \<sigma>p where sigp_unify:
          "unify (Var(x := t) \<cdot>s s) = Some \<sigma>p"
          by(rule exE)
        from this opt have sig:
          "\<sigma> = \<sigma>p \<circ>s Var(x := t)" by simp
        from sigp_unify 1 unsi.IH(1) have IS:
          "svran \<sigma>p \<subseteq> fv_eqs (Var(x := t) \<cdot>s s)"
          by simp
        from this sig have
          "svran \<sigma> \<subseteq> fv t \<union> fv_eqs (Var(x := t) \<cdot>s s)"
          by (smt (verit) Un_assoc Un_commute fun_upd_triv le_supI2 scomp_Var sup.orderE svran_scomp svran_single_non_trivial)
        moreover have
          "fv_eqs ((Var x, t) # s) = { x } \<union> fv t \<union> fv_eqs s"
          by (simp add: fv_eq_def)
        moreover from 1 lemma1_eqs_single have
          "fv_eqs (Var(x := t) \<cdot>s s) \<subseteq> fv t \<union> fv_eqs s"
          by metis
        ultimately show ?thesis
          by blast
      qed
    next
      case 2
      then show ?thesis proof-
        from 2 unsi(3) have t:
          " t = Var x"
          by fastforce
        moreover from unsi(3) have
          "unify s = Some \<sigma>"
          by (simp add: calculation)
        ultimately show ?thesis using unsi(2) 2 by auto 
      qed
    qed
  qed
next
  case (3 v va x s)
  then show ?case by(simp add: fv_swap)
next
  case (4 f0 l0 f1 l1 s)
  then show ?case proof-
    from 4(2) have
      "f0 = f1 \<and> length l0 = length l1"
      by (metis Fun option.discI)
    moreover from 4(2) have
      "unify (term_zip l0 l1 @ s) = Some \<sigma>"
      by (simp add: calculation)
    ultimately show ?thesis using 4(1) by(simp only: fv_fun)
  qed
qed

lemma unify_fv_sapply: "unify eqs = Some \<sigma> \<Longrightarrow> fv_eqs (\<sigma> \<cdot>s eqs) \<subseteq> fv_eqs eqs"
proof(induction eqs arbitrary: \<sigma> rule: unify.induct)
  case 1
  then show ?case by simp
next
  case unsi: (2 x t s)
  then show ?case proof-
    have "x \<notin> fv t \<or> ~ x \<notin> fv t" by simp
    then consider "x \<notin> fv t" | "~ x \<notin> fv t" by blast
    then show ?case proof(cases)
      case 1
      then show ?thesis proof-
        from 1 unsi(3) have opt:
          "scomp_opt (unify (Var(x := t) \<cdot>s s)) (Var(x := t)) = Some \<sigma>"
          by simp
        hence
          "\<exists> \<sigma> . unify (Var(x := t) \<cdot>s s) = Some \<sigma>"
          by (simp add: scomp_opt_fst)
        then obtain \<sigma>p where sigp_unify:
          "unify (Var(x := t) \<cdot>s s) = Some \<sigma>p"
          by(rule exE)
        from this opt have sig:
          "\<sigma> = \<sigma>p \<circ>s Var(x := t)" by simp
        from sigp_unify 1 unsi.IH(1) have IS:
          "fv_eqs (\<sigma>p \<cdot>s Var(x := t) \<cdot>s s) \<subseteq> fv_eqs (Var(x := t) \<cdot>s s)"
          by simp
        from this sig have
          "fv_eqs (\<sigma> \<cdot>s s) \<subseteq> fv_eqs (Var(x := t) \<cdot>s s)"
          by(simp only: sapply_scomp_distrib_eqs)
        moreover from this 1 have
          "svran \<sigma> \<subseteq> fv t \<union> fv_eqs s"
          by (smt (verit, ccfv_threshold) Un_absorb2 fun_upd_triv inf_sup_ord(3) lemma1_eqs_single order_trans
              scomp_Var sig sigp_unify sup.mono svran_scomp svran_single_non_trivial unify_svran_fv)
        ultimately show ?thesis
          by (meson Diff_subset dual_order.trans le_supI lemma1_eqs unify_svran_fv unsi.prems)
      qed
    next
      case 2
      then show ?thesis proof-
        from 2 unsi(3) have t:
          " t = Var x"
          by fastforce
        moreover from unsi(3) have un_s:
          "unify s = Some \<sigma>"
          by (simp add: calculation)
        ultimately have
          "fv_eqs (\<sigma> \<cdot>s s) \<subseteq> fv_eqs s"
          using unsi(2) by simp
        moreover have 
          "fv_eqs (\<sigma> \<cdot>s ((Var x, t) # s)) = fv (\<sigma> x) \<union> fv_eqs (\<sigma> \<cdot>s s)"
          by (simp add: fv_eq_def sapply_eq_def t)
        moreover from t have 
          "fv_eqs ((Var x, t) # s) = { x } \<union> fv_eqs s"
          by(simp add: fv_eq_def)
        moreover have
          "fv (\<sigma> x) \<subseteq> { x } \<union> fv_eqs s"
        proof-
          from lemma1 have
            "fv (\<sigma> x) \<subseteq> { x } - sdom \<sigma> \<union> svran \<sigma>"
            by (metis fv.simps(1) sapply.simps(1))
          moreover from un_s unify_svran_fv have
            "svran \<sigma> \<subseteq> fv_eqs s"
            by blast
          ultimately show ?thesis by blast
        qed
        ultimately show ?thesis
          by blast
      qed
    qed
  qed
next
  case (3 v va x s)
  then show ?case by(simp add: fv_sapply_eqs sapply_eq_def fv_swap)
next
  case (4 f0 l0 f1 l1 s)
  then show ?case proof-
    from 4(2) have
      "f0 = f1 \<and> length l0 = length l1"
      by (simp; metis option.distinct(1))
    moreover from 4(2) have
      "unify (term_zip l0 l1 @ s) = Some \<sigma>"
      by (simp add: calculation)
    ultimately have 
      "fv_eqs (\<sigma> \<cdot>s (term_zip l0 l1 @ s)) \<subseteq> fv_eqs (term_zip l0 l1 @ s)" 
      using 4(1) by simp
    from this 4 show ?thesis by(simp only: fv_sapply_eqs fv_fun; metis Fun fv_fun option.simps(3))
  qed
qed

lemma unify_sdom_fv: "unify eqs = Some \<sigma> \<Longrightarrow> sdom \<sigma> \<subseteq> fv_eqs eqs"
proof(induction eqs arbitrary: \<sigma> rule: unify.induct)
  case 1
  then show ?case by simp
next
  case unsi: (2 x t s)
  then show ?case proof-
    have "x \<notin> fv t \<or> ~ x \<notin> fv t" by simp
    then consider "x \<notin> fv t" | "~ x \<notin> fv t" by blast
    then show ?case proof(cases)
      case 1
      then show ?thesis proof-
        from 1 unsi(3) have opt:
          "scomp_opt (unify (Var(x := t) \<cdot>s s)) (Var(x := t)) = Some \<sigma>"
          by simp
        hence
          "\<exists> \<sigma> . unify (Var(x := t) \<cdot>s s) = Some \<sigma>"
          by (simp add: scomp_opt_fst)
        then obtain \<sigma>p where sigp_unify:
          "unify (Var(x := t) \<cdot>s s) = Some \<sigma>p"
          by(rule exE)
        from this opt have sig:
          "\<sigma> = \<sigma>p \<circ>s Var(x := t)" by simp
        from this have
          "sdom \<sigma> \<subseteq> sdom \<sigma>p \<union> { x }"
          by (metis Un_commute fun_upd_idem_iff insert_is_Un scomp_Var sdom_scomp sdom_single_non_trivial subset_insertI)
        moreover from unsi.IH(1) 1 sigp_unify have IS:
          "sdom \<sigma>p \<subseteq> fv_eqs (Var(x := t) \<cdot>s s)"
          by simp
        moreover from 1 have
          "fv_eqs (Var(x := t) \<cdot>s s) \<union> { x } \<subseteq> fv t \<union> fv_eqs s \<union> { x }"
          by (simp add: lemma1_eqs_single subset_insertI2)
        moreover have
          "fv t \<union> fv_eqs s \<union> { x } = fv_eqs ((Var x, t) # s)"
          by (simp add: fv_eq_def)
        ultimately show ?thesis
          by auto
      qed
    next                           
      case 2
      then show ?thesis proof-
        from 2 unsi(3) have t:
          " t = Var x"
          by fastforce
        moreover from unsi(3) have
          "unify s = Some \<sigma>"
          by (simp add: calculation)
        ultimately show ?thesis using unsi(2) 2 by auto 
      qed
    qed
  qed
next
  case (3 v va x s)
  then show ?case by(simp add: fv_swap)
next
  case (4 f0 l0 f1 l1 s)
  then show ?case proof-
    from 4(2) have
      "f0 = f1 \<and> length l0 = length l1"
      by (metis Fun option.discI)
    moreover from 4(2) have
      "unify (term_zip l0 l1 @ s) = Some \<sigma>"
      by (simp add: calculation)
    ultimately show ?thesis using 4(1) by(simp only: fv_fun)
  qed
qed

lemma unify_sdom_svran: "unify eqs = Some \<sigma> \<Longrightarrow> sdom \<sigma> \<inter> svran \<sigma> = {}"
proof(induction arbitrary: \<sigma> rule: unify.induct)
  case 1
  then show ?case by simp
next
  case unsi: (2 x t s)
  then show ?case proof-
    have "x \<notin> fv t \<or> ~ x \<notin> fv t" by simp
    then consider "x \<notin> fv t" | "~ x \<notin> fv t" by blast
    then show ?case proof(cases)
      case 1
      then show ?thesis proof-
        from 1 unsi(3) have opt:
          "scomp_opt (unify (Var(x := t) \<cdot>s s)) (Var(x := t)) = Some \<sigma>"
          by simp
        hence
          "\<exists> \<sigma> . unify (Var(x := t) \<cdot>s s) = Some \<sigma>"
          by (simp add: scomp_opt_fst)
        then obtain \<sigma>p where sigp_unify:
          "unify (Var(x := t) \<cdot>s s) = Some \<sigma>p"
          by(rule exE)
        from this opt have sig:
          "\<sigma> = \<sigma>p \<circ>s Var(x := t)" by simp
        from unsi.IH(1) 1 sigp_unify have IS:
          "sdom \<sigma>p \<inter> svran \<sigma>p = {}"
          by simp
        from sig 1 sigp_unify have
          "svran \<sigma>p \<subseteq> fv_eqs (Var(x := t) \<cdot>s s)"
          using unify_svran_fv by blast
        from this 1 have x_svran_sigp: 
          "x \<notin> svran \<sigma>p"
          by (metis (no_types, lifting) Diff_iff Diff_insert_absorb Un_Diff fv.simps(1) lemma1_eqs 
              sdom_single_non_trivial singletonI subsetD svran_single_non_trivial)
        have 
          "\<not> (\<exists> z . z \<in> sdom \<sigma> \<and> z \<in> svran \<sigma>)"
        proof(rule notI)
          assume "\<exists>z. z \<in> sdom \<sigma> \<and> z \<in> svran \<sigma>"
          then obtain z where z_sdom:
            "z \<in> sdom \<sigma>" and z_svran: "z \<in> svran \<sigma>"
            by blast
          from 1 z_sdom sig have
            "z \<in> sdom \<sigma>p \<union> { x }"
            by (metis fv.simps(1) insertI1 insert_absorb insert_subset sdom_scomp sdom_single_non_trivial)
          moreover from 1 z_svran sig have
            "z \<in> svran \<sigma>p \<union> fv t"
            by (metis fv.simps(1) insertI1 insert_absorb insert_subset svran_scomp svran_single_non_trivial)
          ultimately have z_sdom_sigp:
            "z \<in> sdom \<sigma>p"
            using x_svran_sigp 1 by blast
          from svran_def z_svran obtain y where 
            y_sdom_sig: "y \<in> sdom \<sigma>" and z_fv_sig_y: "z \<in> fv (\<sigma> y)"
            by fast
          then show False proof(cases "x = y")
            case True
            then show ?thesis proof-
              from True sig have 
                "\<sigma> y = \<sigma>p \<cdot> t"
                by (simp add: scomp_sapply)
              from this z_fv_sig_y have
                "z \<in> fv (\<sigma>p \<cdot> t)"
                by simp
              from this lemma1 have
                "z \<in> (fv t) - sdom \<sigma>p \<union> svran \<sigma>p"
                by fast
              from this z_sdom_sigp have
                "z \<in> svran \<sigma>p"
                by simp
              from this IS z_sdom_sigp show ?thesis
                by auto
            qed
          next
            case False
            then show ?thesis proof-
              from False sig have
                "\<sigma> y = \<sigma>p y"
                by (simp add: scomp_sapply)
              from this z_fv_sig_y z_sdom_sigp have
                "z \<in> svran \<sigma>p"
                by (metis Diff_iff Un_commute Un_iff sapply.simps(1) svapply_svdom_svran)
              from this IS z_sdom_sigp show ?thesis
                by auto
            qed
          qed
        qed
        then show ?thesis
          by auto
        qed
    next
      case 2
      then show ?thesis proof-
        from 2 unsi(3) have t:
          " t = Var x"
          by fastforce
        moreover from unsi(3) have
          "unify s = Some \<sigma>"
          by (simp add: calculation)
        ultimately show ?thesis using unsi(2) 2 by simp 
      qed
    qed
  qed
next
  case (3 v va x s)
  then show ?case by simp
next
  case (4 f0 l0 f1 l1 s)
  then show ?case proof-
    from 4(2) have
      "f0 = f1 \<and> length l0 = length l1"
      by (metis Fun option.discI)
    moreover from 4(2) have
      "unify (term_zip l0 l1 @ s) = Some \<sigma>"
      by (simp add: calculation)
    ultimately show ?thesis using 4(1) by simp
  qed
qed

section \<open> Assignment 4 \<close>

text \<open> (a) \<close>

fun wf_term :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
  "wf_term arity (Var _) = True"
| "wf_term arity (Fun f lst) = (((length lst) = (arity f)) \<and> (\<forall> t \<in> set lst. (wf_term arity t)))"

definition wf_subst :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) subst \<Rightarrow> bool" where
  "wf_subst arity \<sigma> = (\<forall> x. wf_term arity (\<sigma> x))"

fun wf_eq :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) equation \<Rightarrow> bool" where
  "wf_eq arity (t0, t1) = ((wf_term arity t0) \<and> (wf_term arity t1))"

lemma wf_eq_terms_wf: "wf_eq arity eq \<longleftrightarrow> wf_term arity (fst eq) \<and> wf_term arity (snd eq)"
  by (metis surjective_pairing wf_eq.simps)

definition wf_eqs :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool" where
  "wf_eqs arity eqs = (\<forall> eq \<in> (set eqs). wf_eq arity eq)"

text \<open> (b) \<close>

lemma wf_term_sapply:
  "\<lbrakk> wf_term arity t; wf_subst arity \<sigma> \<rbrakk> \<Longrightarrow> wf_term arity (\<sigma> \<cdot> t)"
  apply(induction t)
  by(simp_all add: wf_subst_def)

lemma wf_subst_scomp:
  "\<lbrakk> wf_subst arity \<sigma>; wf_subst arity \<tau> \<rbrakk> \<Longrightarrow> wf_subst arity (\<sigma> \<circ>s \<tau>)"
  by(simp add: wf_subst_def scomp_def wf_term_sapply)

lemma wf_zip: "\<lbrakk>length l0 = length l1; 
    \<forall>t\<in>set l0. wf_term arity t; 
    \<forall>t\<in>set l1. wf_term arity t;
    wf_eqs arity s\<rbrakk> \<Longrightarrow> wf_eqs arity ((term_zip l0 l1)@s)"
  apply(induction rule: term_zip.induct)
  by(simp_all add: wf_eqs_def)

lemma wf_single_subst: "\<lbrakk> x \<notin> fv t; wf_term arity t\<rbrakk> \<Longrightarrow> wf_subst arity (Var(x := t))"
  by(simp add: wf_subst_def)

lemma wf_Var: "wf_subst arity Var"
  by(simp add: wf_subst_def)

lemma wf_eq_sapply:
  "\<lbrakk> wf_subst arity \<sigma>; wf_term arity t;  wf_eq arity eq \<rbrakk> \<Longrightarrow> wf_eq arity (\<sigma> \<cdot>e eq)"
  by(simp add: sapply_eq_def wf_eq_terms_wf wf_term_sapply)
  
lemma wf_eqs_sapply: "\<lbrakk> wf_subst arity \<sigma>; wf_term arity t;  wf_eqs arity s \<rbrakk> \<Longrightarrow> wf_eqs arity (\<sigma> \<cdot>s s)"
  apply(induction s)
   apply(simp)
  by(simp add: wf_eqs_def wf_eq_sapply)

lemma wf_subst_unify:
  "\<lbrakk> unify eqs = Some \<sigma>; wf_eqs arity eqs \<rbrakk> \<Longrightarrow> wf_subst arity \<sigma>"
proof(induction arbitrary: \<sigma> rule: unify.induct)
  case 1
  then show ?case by(simp add: wf_subst_def)
next
  case unsi: (2 x t s)
  then show ?case proof-
    from unsi(4)have s_wf:
      "wf_eqs arity s"
      by (simp add: wf_eqs_def)

    have "x \<notin> fv t \<or> ~ x \<notin> fv t" by simp
    then consider "x \<notin> fv t" | "~ x \<notin> fv t" by blast
    then show ?case proof(cases)
      case 1
      then show ?thesis proof-
          from unsi(4) have t_wf:
            "wf_term arity t"
            by(simp add: wf_eqs_def)
          from this 1 s_wf have up_wf:
            "wf_eqs arity (Var(x := t) \<cdot>s s)"
            by(simp add: wf_single_subst wf_eqs_sapply)
          from 1 unsi(3) have opt:
            "scomp_opt (unify (Var(x := t) \<cdot>s s)) (Var(x := t)) = Some \<sigma>"
            by simp
          hence
            "\<exists> \<sigma> . unify (Var(x := t) \<cdot>s s) = Some \<sigma>"
            by (simp add: scomp_opt_fst)
          then obtain \<sigma>p where sigp_unify:
            "unify (Var(x := t) \<cdot>s s) = Some \<sigma>p"
            by(rule exE)
          from this opt have sig:
            "\<sigma> = \<sigma>p \<circ>s Var(x := t)" by simp
          moreover from unsi.IH(1) 1 sigp_unify up_wf have
            "wf_subst arity \<sigma>p"
            by simp
          ultimately show ?thesis using 1
            by(simp add: t_wf wf_single_subst  wf_subst_scomp)
        qed
    next
      case 2
      then show ?thesis proof-
        from 2 unsi(3) have
          "t = Var x"
          by fastforce
        moreover from unsi(3) have
          "unify s = Some \<sigma>"
          by (simp add: calculation)
        ultimately show ?thesis using unsi(2) 2 s_wf by simp
      qed
    qed
  qed
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

end
  