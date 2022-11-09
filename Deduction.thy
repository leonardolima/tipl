theory Deduction
  imports Main Unification Term
begin

section \<open>Assignment 6\<close>

subsection \<open>(a)\<close>

abbreviation "\<iota> \<equiv> Constant ''i''"

inductive deduce :: "msg set \<Rightarrow> msg \<Rightarrow> bool" (infix "\<turnstile>" 72) for T where 
  Ax: "u \<in> T \<Longrightarrow> T \<turnstile> u"
| CompHash: "T \<turnstile> t \<Longrightarrow> T \<turnstile> Hash t"
| CompPair: "\<lbrakk> T \<turnstile> t1; T \<turnstile> t2 \<rbrakk> \<Longrightarrow> T \<turnstile> Pair t1 t2"
| CompSymEncrypt: "\<lbrakk> T \<turnstile> k; T \<turnstile> t \<rbrakk> \<Longrightarrow> T \<turnstile> SymEncrypt k t"
| CompPubKeyEncrypt: "\<lbrakk> T \<turnstile> k; T \<turnstile> t \<rbrakk> \<Longrightarrow> T \<turnstile> PubKeyEncrypt k t"
| CompSig: "\<lbrakk> T \<turnstile> \<iota>; T \<turnstile> t \<rbrakk> \<Longrightarrow> T \<turnstile> Sig \<iota> t"
| ProjL: "T \<turnstile> Pair t1 t2 \<Longrightarrow> T \<turnstile> t1"
| ProjR: "T \<turnstile> Pair t1 t2 \<Longrightarrow> T \<turnstile> t2"
| Sdec: "\<lbrakk> T \<turnstile> SymEncrypt k t; T \<turnstile> k \<rbrakk> \<Longrightarrow> T \<turnstile> t"
| Adec: "T \<turnstile> PubKeyEncrypt \<iota> t \<Longrightarrow> T \<turnstile> t"

lemma "{ Pair m n } \<turnstile> Hash (Pair n m)"
  apply(rule CompHash)
  apply(rule CompPair)
   apply(rule ProjR[of _ "m" "n"])
   apply(rule Ax)
   apply simp
  apply(rule ProjL[of _ "m" "n"])
  apply(rule Ax)
  apply simp
  done

lemma " { \<iota> } \<turnstile> Hash \<iota> "
  apply(rule CompHash)
  apply(rule Ax)
  apply simp
  done

subsection \<open>(b)\<close>

lemma deduce_weaken:
  assumes "G \<turnstile> t" and "G \<subseteq> H"
  shows "H \<turnstile> t"
  using assms
  apply(induction t rule: deduce.induct)
           apply(auto intro: deduce.intros)
  done

lemma deduce_cut:
  assumes "insert t H \<turnstile> u" and "H \<turnstile> t"
  shows "H \<turnstile> u"
  using assms
  apply(induction u rule: deduce.induct)
           apply(auto intro: deduce.intros)
  done

section \<open>Assignment 7\<close>

datatype constraint = 
  Constraint "msg list" "msg list" "msg" ( "((2_/|_)/ \<rhd> _)" [67,67,67] 66)

type_synonym constraint_system = "constraint list"

subsection \<open>(a)\<close>

fun c_M :: "constraint \<Rightarrow> msg list" where
  "c_M (Constraint M _ _) = M"

fun c_A :: "constraint \<Rightarrow> msg list" where
  "c_A (Constraint _ A _) = A"

fun c_t :: "constraint \<Rightarrow> msg" where
  "c_t (Constraint _ _ t) = t"

definition c_fv :: "constraint \<Rightarrow> string set" where
  "c_fv c = union (\<Union> (set (map msg_fv ((c_M c) @ (c_A c))))) (msg_fv (c_t c))"

definition cs_fv :: "constraint_system \<Rightarrow> string set" where
  "cs_fv cs = \<Union> (set (map c_fv cs))"

definition c_sapply :: "msg_subst \<Rightarrow> constraint \<Rightarrow> constraint" where
  "c_sapply \<sigma> c = (map (msg_sapply \<sigma>) (c_M c)) | (map (msg_sapply \<sigma>) (c_A c)) \<rhd> (msg_sapply \<sigma>) (c_t c)"

definition cs_sapply :: "msg_subst \<Rightarrow> constraint_system \<Rightarrow> constraint_system" where
  "cs_sapply \<sigma> cs = map (c_sapply \<sigma>) cs"

lemma c_fv_finite: "finite (c_fv c)"
  using fv_finite unfolding c_fv_def msg_fv_def by auto

lemma cs_fv_finite: "finite (cs_fv cs)"
  using c_fv_finite unfolding cs_fv_def by simp

lemma c_fv_sapply_sdom_svran: "c_fv (c_sapply \<sigma> c) \<subseteq> (c_fv c - msg_sdom \<sigma>) \<union> msg_svran \<sigma>"
  using msg_fv_sapply_sdom_svran[of \<sigma> _]
  unfolding c_fv_def cs_sapply_def c_sapply_def
  by (clarsimp; blast+)

lemma cs_fv_sapply_sdom_svran: "cs_fv (cs_sapply \<sigma> cs) \<subseteq> (cs_fv cs - msg_sdom \<sigma>) \<union> msg_svran \<sigma>"
  using c_fv_sapply_sdom_svran[of \<sigma> _]
  unfolding cs_fv_def cs_sapply_def c_sapply_def
  by (clarsimp; blast+)

lemma cs_cs'_fv: "cs_fv (cs @ cs') = cs_fv cs \<union> cs_fv cs'"
  unfolding cs_fv_def by simp

lemma c_cs'_fv: "cs_fv (c # cs') = c_fv c \<union> cs_fv cs'"
  unfolding cs_fv_def by simp

lemma c_cs_fv: "cs_fv [c] = c_fv c"
  unfolding cs_fv_def by simp

definition sol :: "constraint_system \<Rightarrow> msg_subst set" where
  "sol cs = { \<sigma>. \<forall>c \<in> (set cs). ((set (map (msg_sapply \<sigma>) (c_M c))) \<union> (set (map (msg_sapply \<sigma>) (c_A c)))) \<turnstile> (msg_sapply \<sigma>) (c_t c) }"

subsection \<open>(b)\<close>

lemma sol_inter: "sol (cs1 @ cs2) = sol(cs1) \<inter> sol(cs2)"
  unfolding sol_def by auto

lemma sol_scomp: "\<tau> \<in> sol(cs_sapply \<sigma> cs) \<Longrightarrow> (\<tau> \<circ>m \<sigma>) \<in> sol(cs)"
  unfolding c_sapply_def cs_sapply_def
  by (simp add: msg_scomp_distrib sol_def image_image)
  
subsection \<open>(c)\<close>

inductive rer1 :: "constraint \<Rightarrow> msg_subst \<Rightarrow> constraint_system \<Rightarrow> bool" ("(_)/ \<leadsto>\<^sub>1[_]/ (_) " [64,64,64] 63) where
  Unif: "\<not>(is_Variable t) \<Longrightarrow> u \<in> (set M) \<union> (set A) \<Longrightarrow> Some(\<sigma>) = msg_unify [(t, u)] \<Longrightarrow> 
  M | A \<rhd> t \<leadsto>\<^sub>1[\<sigma>] []"
| CompHash: "M | A \<rhd> (Hash t) \<leadsto>\<^sub>1[Variable] 
  [(M | A \<rhd> t)]"
| CompPair: "M | A \<rhd> (Pair t1 t2) \<leadsto>\<^sub>1[Variable] 
  [(M | A \<rhd> t1), (M | A \<rhd> t2)]"
| CompSymEncrypt: "M | A \<rhd> (SymEncrypt k t) \<leadsto>\<^sub>1[Variable] 
  [(M | A \<rhd> k), (M | A \<rhd> t)]"
| CompPubKeyEncrypt: "M | A \<rhd> (PubKeyEncrypt k t) \<leadsto>\<^sub>1[Variable] 
  [(M | A \<rhd> k), (M | A \<rhd> t)]"
| CompSig: "M | A \<rhd> (Sig \<iota> t) \<leadsto>\<^sub>1[Variable] 
  [M | A \<rhd> \<iota>, M | A \<rhd> t]"
| Proj: "(M1 @ (Pair u v) # M2) | A \<rhd> t \<leadsto>\<^sub>1[Variable] 
  [(M1 @ (u # v # M2)) | ((Pair u v) # A) \<rhd> t]"
| Sdec: "(M1 @ (SymEncrypt k u) # M2) | A \<rhd> t \<leadsto>\<^sub>1[Variable] 
  [(M1 @ (u # M2)) | ((SymEncrypt k u) # A) \<rhd> t, (M1 @ M2) | ((SymEncrypt k u) # A) \<rhd> k]"
| Adec: "(M1 @ (PubKeyEncrypt \<iota> u) # M2) | A \<rhd> t \<leadsto>\<^sub>1[Variable] 
  [(M1 @ (u # M2)) | ((PubKeyEncrypt \<iota> u) # A) \<rhd> t]"
| Ksub: "(M1 @ (PubKeyEncrypt (Variable x) u) # M2) | A \<rhd> t \<leadsto>\<^sub>1[Variable(x := \<iota>)] 
  [c_sapply (Variable(x := \<iota>)) ((M1 @ (PubKeyEncrypt (Variable x) u) # M2) | A \<rhd> t)]"

inductive rer :: "constraint_system \<Rightarrow> msg_subst \<Rightarrow> constraint_system \<Rightarrow> bool" ( "_/ \<leadsto>[_]/ _ " [73,73,73] 72) where
  Context: "c \<leadsto>\<^sub>1[\<sigma>] cs \<Longrightarrow> (cs'1 @ (c # cs'2)) \<leadsto>[\<sigma>] (cs @ (cs_sapply \<sigma> (cs'1 @ cs'2)))"

inductive rer_star :: "constraint_system \<Rightarrow> msg_subst \<Rightarrow> constraint_system \<Rightarrow> bool" ( "_/ \<leadsto>*[_]/ _ " [73,73,73] 72) where
  Refl: "cs \<leadsto>*[Variable] cs"
| Trans: "cs \<leadsto>[\<sigma>] cs'' \<Longrightarrow> cs'' \<leadsto>*[\<tau>] cs' \<Longrightarrow> cs \<leadsto>*[(\<tau> \<circ>m \<sigma>)] cs'"

section \<open>Assignment 8\<close>

subsection \<open>(a)\<close>

definition is_simple_c :: "constraint \<Rightarrow> bool" where
  "is_simple_c c = is_Variable (c_t c)"

definition is_simple_cs :: "constraint_system \<Rightarrow> bool" where
  "is_simple_cs cs = (\<forall>c \<in> (set cs). is_simple_c c)"

definition red :: "constraint_system \<Rightarrow> msg_subst set" where
  "red cs = {\<tau> \<circ>m \<sigma> | \<tau> \<sigma>. (\<exists>cs'. cs \<leadsto>*[\<sigma>] cs' \<and> is_simple_cs cs' \<and> \<tau> \<in> sol(cs'))}"

lemma rer1_red: 
  assumes "c \<leadsto>\<^sub>1[\<sigma>] cs" and "\<tau> \<in> sol(cs)"
  shows "(\<tau> \<circ>m \<sigma>) \<in> sol([c])"
  using assms
proof(cases rule: rer1.cases)
  case (Unif t u M A)
  then have "\<sigma> \<cdot>m t = \<sigma> \<cdot>m u"
    using msg_unify_unifies[of "[(t,u)]" \<sigma>] unifies_forall
    unfolding msg_unifies_def by (simp add: msg_sapply_def unifies_eq_def)
  then have "set (map ((\<cdot>m) \<tau>) (map ((\<cdot>m) \<sigma>) (M @ A))) \<turnstile> (\<tau> \<cdot>m (\<sigma> \<cdot>m t))"
    using Unif(4) Ax[of "(\<tau> \<cdot>m \<sigma> \<cdot>m t)"] by auto
  then have "set (map ((\<cdot>m) (\<tau> \<circ>m \<sigma>)) (M @ A)) \<turnstile> ((\<tau> \<circ>m \<sigma>) \<cdot>m t)"
    by (simp add: msg_scomp_distrib)
  then show ?thesis 
    using Unif(1) unfolding sol_def by simp
next
  case (CompHash M A t)
  have "set (map ((\<cdot>m) \<tau>) (M @ A)) \<turnstile> (\<tau> \<cdot>m t)"
    using assms(2) CompHash(3)
    unfolding sol_def
    by (simp add: Un_assoc image_Un)
  then have "set (map ((\<cdot>m) \<tau>) (M @ A)) \<turnstile> (\<tau> \<cdot>m (Hash t))" 
    using deduce.CompHash[of "set (map ((\<cdot>m) \<tau>) (M @ A))" "\<tau> \<cdot>m t"]
    by (simp add: msg_sapply_def)
  then show ?thesis
    using CompHash(1,2) unfolding sol_def by simp
next
  case (CompPair M A t1 t2)
  have "set (map ((\<cdot>m) \<tau>) (M @ A)) \<turnstile> (\<tau> \<cdot>m t1)"
    using assms CompPair
    unfolding sol_def
    by (simp add: Un_assoc image_Un)
  moreover have "set (map ((\<cdot>m) \<tau>) (M @ A)) \<turnstile> (\<tau> \<cdot>m t2)"
    using assms CompPair
    unfolding sol_def
    by (simp add: Un_assoc image_Un)
  ultimately have "set (map ((\<cdot>m) \<tau>) (M @ A)) \<turnstile> (\<tau> \<cdot>m (Pair t1 t2))" 
    using deduce.CompPair[of "set (map ((\<cdot>m) \<tau>) (M @ A))" "\<tau> \<cdot>m t1" "\<tau> \<cdot>m t2"]
    by (simp add: msg_sapply_def)
  then show ?thesis
    using CompPair unfolding sol_def by simp
next
  case (CompSymEncrypt M A k t)
  have "set (map ((\<cdot>m) \<tau>) (M @ A)) \<turnstile> (\<tau> \<cdot>m t)"
    using assms CompSymEncrypt
    unfolding sol_def
    by (simp add: Un_assoc image_Un)
  moreover have "set (map ((\<cdot>m) \<tau>) (M @ A)) \<turnstile> (\<tau> \<cdot>m k)"
    using assms CompSymEncrypt
    unfolding sol_def
    by (simp add: Un_assoc image_Un)
  ultimately have "set (map ((\<cdot>m) \<tau>) (M @ A)) \<turnstile> (\<tau> \<cdot>m (SymEncrypt k t))" 
    using deduce.CompSymEncrypt[of "set (map ((\<cdot>m) \<tau>) (M @ A))" "\<tau> \<cdot>m k" "\<tau> \<cdot>m t"]
    by (simp add: msg_sapply_def)
  then show ?thesis
    using CompSymEncrypt unfolding sol_def by simp
next
  case (CompPubKeyEncrypt M A k t)
  have "set (map ((\<cdot>m) \<tau>) (M @ A)) \<turnstile> (\<tau> \<cdot>m t)"
    using assms CompPubKeyEncrypt
    unfolding sol_def
    by (simp add: Un_assoc image_Un)
  moreover have "set (map ((\<cdot>m) \<tau>) (M @ A)) \<turnstile> (\<tau> \<cdot>m k)"
    using assms CompPubKeyEncrypt
    unfolding sol_def
    by (simp add: Un_assoc image_Un)
  ultimately have "set (map ((\<cdot>m) \<tau>) (M @ A)) \<turnstile> (\<tau> \<cdot>m (PubKeyEncrypt k t))" 
    using deduce.CompPubKeyEncrypt[of "set (map ((\<cdot>m) \<tau>) (M @ A))" "\<tau> \<cdot>m k" "\<tau> \<cdot>m t"]
    by (simp add: msg_sapply_def)
  then show ?thesis
    using CompPubKeyEncrypt unfolding sol_def by simp
next
  case (CompSig M A t)
  have "set (map ((\<cdot>m) \<tau>) (M @ A)) \<turnstile> (\<tau> \<cdot>m t)"
    using assms CompSig
    unfolding sol_def
    by (simp add: Un_assoc image_Un)
  moreover have "set (map ((\<cdot>m) \<tau>) (M @ A)) \<turnstile> (\<tau> \<cdot>m \<iota>)"
    using assms CompSig
    unfolding sol_def
    by simp
  ultimately have "set (map ((\<cdot>m) \<tau>) (M @ A)) \<turnstile> (\<tau> \<cdot>m (Sig \<iota> t))" 
    using deduce.CompSig[of "set (map ((\<cdot>m) \<tau>) (M @ A))" "\<tau> \<cdot>m t"]
    by (simp add: msg_sapply_def)
  then show ?thesis
    using CompSig
    unfolding sol_def
    by simp
next
  (* Reminder: here we need to apply cut twice *)
  case (Proj M1 u v M2 A t)
  have ax_app: "set (map ((\<cdot>m) \<tau>) (M1 @ Pair u v # M2 @ A)) \<turnstile> (\<tau> \<cdot>m (Pair u v))"
    by (rule Ax; simp)
  have tau_u_deriv: "set (map ((\<cdot>m) \<tau>) (M1 @ Pair u v # M2 @ A)) \<turnstile> (\<tau> \<cdot>m u)"
    using ax_app deduce.ProjL[of _ "(\<tau> \<cdot>m u)" "(\<tau> \<cdot>m v)"]
    by (simp add: msg_sapply_def)
  have tau_v_deriv: "set (map ((\<cdot>m) \<tau>) (M1 @ Pair u v # M2 @ A)) \<turnstile> (\<tau> \<cdot>m v)"
    using ax_app deduce.ProjR[of _ "(\<tau> \<cdot>m u)" "(\<tau> \<cdot>m v)"]
    by (simp add: msg_sapply_def)
  have u_deriv: "set (M1 @ v # Pair u v # M2 @ A) \<turnstile> u"
    using deduce.ProjL[of _ u v] ax_app
    by (simp; meson Ax insertCI)
  then have u_deriv': "set (map ((\<cdot>m) \<tau>) (M1 @ v # Pair u v # M2 @ A)) \<turnstile> (\<tau> \<cdot>m u)"
    using deduce.ProjL[of _ "(\<tau> \<cdot>m u)" "(\<tau> \<cdot>m v)"] ax_app msg_sapply_def
    by (simp add: Ax)
  have tau_t_1: "set (map ((\<cdot>m) \<tau>) (M1 @ u # v # Pair u v # M2 @ A)) \<turnstile> (\<tau> \<cdot>m t)"
    using assms Proj
    unfolding sol_def
    by (simp add: Un_assoc image_Un insert_commute)
  then have "set (map ((\<cdot>m) \<tau>) (M1 @ v # Pair u v # M2 @ A)) \<turnstile> (\<tau> \<cdot>m t)"
    using assms Proj tau_u_deriv deduce_cut u_deriv'
    by auto
  then have "set (map ((\<cdot>m) \<tau>) (M1 @ Pair u v # M2 @ A)) \<turnstile> (\<tau> \<cdot>m t)"
    using assms Proj deduce_cut
    by (smt (verit, best) Un_insert_right image_insert list.set_map list.simps(15) set_append tau_v_deriv)
  then show ?thesis 
    using assms Proj
    unfolding sol_def
    by (simp add: Un_assoc)
next
  case (Sdec M1 k u M2 A t)
  have "set (map ((\<cdot>m) \<tau>) (M1 @ SymEncrypt k u # M2 @ A)) \<turnstile> (\<tau> \<cdot>m k)"
    using assms Sdec
    unfolding sol_def
    by (simp add: Un_assoc image_Un)
  moreover have "set (map ((\<cdot>m) \<tau>) (M1 @ SymEncrypt k u # M2 @ A)) \<turnstile> (\<tau> \<cdot>m (SymEncrypt k u))"
    by (rule Ax; simp)
  ultimately have "set (map ((\<cdot>m) \<tau>) (M1 @ SymEncrypt k u # M2 @ A)) \<turnstile> (\<tau> \<cdot>m u)"
    using deduce.Sdec[of "set (map ((\<cdot>m) \<tau>) (M1 @ SymEncrypt k u # M2 @ A))" "(\<tau> \<cdot>m k)" "(\<tau> \<cdot>m u)"]
    by (simp add: msg_sapply_def)
  moreover have "set (map ((\<cdot>m) \<tau>) (M1 @ u # SymEncrypt k u # M2 @ A)) \<turnstile> (\<tau> \<cdot>m t)"
    using assms Sdec
    unfolding sol_def
    by (simp add: Un_assoc image_Un insert_commute)
  ultimately have "set (map ((\<cdot>m) \<tau>) (M1 @ SymEncrypt k u # M2 @ A)) \<turnstile> (\<tau> \<cdot>m t)"
    by (simp add: deduce_cut)
  then show ?thesis
    using assms Sdec
    unfolding sol_def
    by (simp add: Un_assoc)
next
  case (Adec M1 u M2 A t)
  have "set (map ((\<cdot>m) \<tau>) (M1 @ PubKeyEncrypt \<iota> u # M2 @ A)) \<turnstile> (\<tau> \<cdot>m (PubKeyEncrypt \<iota> u))"
    by (rule Ax; simp)
  then have "set (map ((\<cdot>m) \<tau>) (M1 @ PubKeyEncrypt \<iota> u # M2 @ A)) \<turnstile> (\<tau> \<cdot>m u)"
    using deduce.Adec[of "set (map ((\<cdot>m) \<tau>) (M1 @ PubKeyEncrypt \<iota> u # M2 @ A))" "(\<tau> \<cdot>m u)"]
    by (simp add: msg_sapply_def)
  moreover have "set (map ((\<cdot>m) \<tau>) (M1 @ u # PubKeyEncrypt \<iota> u # M2 @ A)) \<turnstile> (\<tau> \<cdot>m t)"
    using assms Adec
    unfolding sol_def
    by (simp add: Un_assoc image_Un insert_commute)
  ultimately have "set (map ((\<cdot>m) \<tau>) (M1 @ PubKeyEncrypt \<iota> u # M2 @ A)) \<turnstile> (\<tau> \<cdot>m t)"
    by (simp add: deduce_cut)
  then show ?thesis
    using assms Adec
    unfolding sol_def
    by (simp add: Un_assoc)
next
  case (Ksub M1 x u M2 A t)
  then show ?thesis
    using assms
    by (simp add: cs_sapply_def sol_scomp)
qed

lemma rer_red: 
  assumes "cs \<leadsto>[\<sigma>] cs'" and "\<tau> \<in> sol(cs')"
  shows "(\<tau> \<circ>m \<sigma>) \<in> sol(cs)"
  using assms
proof(cases rule: rer.cases)
  case (Context c cs cs'1 cs'2)
  have "\<tau> \<in> sol(cs_sapply \<sigma> (cs'1 @ cs'2))"
    using assms(2) Context(2) unfolding sol_def by simp
  then have "(\<tau> \<circ>m \<sigma>) \<in> sol(cs'1 @ cs'2)"
    using sol_scomp[of \<tau> \<sigma> "(cs'1 @ cs'2)"] 
    unfolding sol_def by auto
  moreover have "(\<tau> \<circ>m \<sigma>) \<in> sol([c])"
    using assms Context rer1_red[of c \<sigma> cs \<tau>]
    unfolding sol_def by simp
  ultimately show ?thesis
    using Context unfolding sol_def by simp
qed

lemma rer_star_red:
  assumes "cs \<leadsto>*[\<sigma>] cs'"
    and "is_simple_cs cs'"
    and "\<tau> \<in> sol(cs')"
  shows "(\<tau> \<circ>m \<sigma>) \<in> sol(cs)"
  using assms
proof(induction rule: rer_star.induct)
  case (Refl cs)
  then show ?case by auto
next
  case (Trans cs \<sigma> cs'' \<tau> cs')
  then show ?case 
    using rer_red[of cs \<sigma> cs''] msg_scomp_assoc
    by (simp; fastforce)
qed

theorem red_soundness: "red cs \<subseteq> sol(cs)"
  using sol_def red_def rer_star_red by auto

subsection \<open>(b)\<close>

fun \<theta> :: "msg \<Rightarrow> nat" where
  "\<theta> (Variable x) = 1"
| "\<theta> (Constant c) = 1"
| "\<theta> (Hash t) = \<theta> t + 1"
| "\<theta> (Pair t1 t2) = \<theta> t1 + \<theta> t2 + 1"
| "\<theta> (SymEncrypt k t) = \<theta> k + \<theta> t + 1"
| "\<theta> (PubKeyEncrypt k t) = \<theta> k + \<theta> t + 1"
| "\<theta> (Sig k t) = \<theta> k + \<theta> t + 1"

fun \<chi> :: "msg \<Rightarrow> nat" where
  "\<chi> (Variable x) = 1"
| "\<chi> (Constant c) = 1"
| "\<chi> (Hash t) = \<chi> t + 1"
| "\<chi> (Pair t1 t2) = \<chi> t1 * \<chi> t2 + 1"
| "\<chi> (SymEncrypt k t) = \<chi> t + \<theta> k + 1"
| "\<chi> (PubKeyEncrypt k t) = \<chi> t + 1"
| "\<chi> (Sig k t) = \<chi> t + 1"

definition \<chi>_list :: "msg list \<Rightarrow> nat" where
  "\<chi>_list msg_list = prod_list (map \<chi> msg_list)"

definition weight :: "constraint \<Rightarrow> nat" where
  "weight c = \<chi>_list (c_M c) * \<theta> (c_t c)"

lemma \<theta>_positive: "\<theta> m \<ge> 1"
  by(induction m; simp)

lemma \<chi>_positive: "\<chi> m \<ge> 1"
  by(induction m; simp)

lemma \<chi>_list_positive: "\<chi>_list l \<ge> 1"
proof(induction l)
  case Nil
  then show ?case 
    using \<chi>_positive unfolding \<chi>_list_def by simp
next
  case (Cons a l)
  then show ?case
    using \<chi>_positive unfolding \<chi>_list_def by simp
qed

lemma \<chi>_list_pair_ineq: "\<chi>_list (M1 @ u # v # M2) < \<chi>_list (M1 @ Pair u v # M2)"
  using \<chi>_list_positive
  unfolding \<chi>_list_def 
  by (auto simp add: Suc_le_lessD)

lemma weight_positive: "weight c \<ge> 1"
proof(cases c)
  case (Constraint M A t)
  then show ?thesis 
    using \<chi>_list_positive \<theta>_positive
    unfolding weight_def by simp
qed

definition \<eta>_1 :: "constraint_system \<Rightarrow> nat" where
  "\<eta>_1 cs = card (cs_fv cs)"

definition \<eta>_2 :: "constraint_system \<Rightarrow> nat" where
  "\<eta>_2 cs = sum_list (map weight cs)"

lemma cs_sapply_id: "cs_sapply Variable cs = cs"
proof(induction cs)
  case Nil
  then show ?case 
    unfolding cs_sapply_def by simp
next
  case (Cons a cs)
  then show ?case 
    using msg_var_sapply 
    unfolding cs_sapply_def c_sapply_def msg_sapply_def
    by (cases a; simp)
qed

lemma fv_x_\<iota>: 
  assumes "\<sigma> = Variable(x := \<iota>)"
    and "x \<in> c_fv c"
  shows "c_fv(c_sapply \<sigma> c) \<union> {x} \<subseteq> c_fv(c)"
proof -
  have \<sigma>_sdom: "msg_sdom \<sigma> = {x}"
    using assms msg_sdom_single_non_trivial[of \<iota> x] by simp
  moreover have \<sigma>_svran: "msg_svran \<sigma> = msg_fv \<iota>"
    using assms msg_svran_single_non_trivial[of \<iota> x] by simp
  moreover have \<sigma>_cs:  "c_fv (c_sapply \<sigma> c) \<subseteq> (c_fv(c) - msg_sdom \<sigma>) \<union> msg_svran \<sigma>"
    using c_fv_sapply_sdom_svran[of \<sigma> c] by simp
  ultimately show ?thesis
    using assms unfolding msg_fv_def by auto
qed

lemma c_cs_fv_subseteq: 
  assumes "c  \<leadsto>\<^sub>1[\<sigma>] cs"
  shows "cs_fv(cs @ (cs_sapply \<sigma> cs')) \<subseteq> cs_fv(c # cs')"
  using assms
proof(cases rule: rer1.cases)
  case (Unif t u M A)
  have "cs_fv (cs_sapply \<sigma> cs') \<subseteq> (cs_fv(cs') - msg_sdom \<sigma>) \<union> msg_svran \<sigma>"
    using cs_fv_sapply_sdom_svran[of \<sigma> cs'] by simp
  moreover have "msg_svran \<sigma> \<subseteq> c_fv c"
    using Unif(1,4,5) msg_unify_svran_fv[of "[(t, u)]" \<sigma>]
    by (auto simp add: c_fv_def msg_fv_eqs_def msg_fv_eq_def)
  ultimately show ?thesis
    using Unif(2) c_cs'_fv[of c cs'] by auto
next
  case (Ksub M1 x u M2 A t)
  have \<sigma>_sdom: "msg_sdom \<sigma> = {x}"
    using Ksub msg_sdom_single_non_trivial[of \<iota> x] by simp
  moreover have \<sigma>_svran: "msg_svran \<sigma> = msg_fv \<iota>"
    using Ksub msg_svran_single_non_trivial[of \<iota> x] by simp
  moreover have fv_subseteq: "cs_fv(cs) \<subseteq> c_fv(c)"
    using Ksub cs_fv_sapply_sdom_svran[of \<sigma> cs'] c_fv_sapply_sdom_svran \<sigma>_sdom \<sigma>_svran
    unfolding msg_fv_def
    by (simp add: cs_fv_def; fastforce)
  ultimately have "cs_fv (cs @ cs_sapply \<sigma> cs') \<subseteq> (cs_fv(cs @ cs') - msg_sdom \<sigma>) \<union> msg_svran \<sigma>"
    using Ksub(2,3) cs_fv_sapply_sdom_svran[of \<sigma> cs'] c_fv_sapply_sdom_svran
    unfolding msg_fv_def
    by (simp add: cs_cs'_fv cs_fv_def; fastforce)
  also have "... \<subseteq> cs_fv(c # cs')"
    using Ksub(2) \<sigma>_sdom \<sigma>_svran fv_subseteq 
    unfolding cs_fv_def msg_fv_def
    by auto
  finally show ?thesis by simp
qed (auto simp add: cs_fv_def c_fv_def cs_sapply_id msg_fv_def)

lemma c_cs_fv_noteq: 
  assumes "c  \<leadsto>\<^sub>1[\<sigma>] cs"
    and "\<sigma> \<noteq> Variable"
  shows "cs_fv(cs @ (cs_sapply \<sigma> cs')) \<noteq> cs_fv(c # cs')"
  using assms
proof(cases rule: rer1.cases)
  case (Unif t u M A)
  obtain x where x_sdom: "x \<in> msg_sdom(\<sigma>)"
    using assms msg_not_var
    unfolding msg_sdom_def sdom_def
    by (simp; blast)
  moreover have "msg_sdom(\<sigma>) \<subseteq> c_fv(c)"
    using Unif(1,4,5) msg_unify_sdom_fv[of "[(t, u)]" \<sigma>]
    unfolding c_fv_def msg_fv_eqs_def msg_fv_eq_def
    by auto
  ultimately have "x \<in> cs_fv(c # cs')"
    unfolding cs_fv_def by auto
  moreover have "cs_fv (cs_sapply \<sigma> cs') \<subseteq> (cs_fv(cs') - msg_sdom \<sigma>) \<union> msg_svran \<sigma>"
    using cs_fv_sapply_sdom_svran[of \<sigma> cs'] by simp
  moreover have "msg_sdom(\<sigma>) \<inter> msg_svran(\<sigma>) = {}"
    using Unif(5) msg_unify_sdom_svran[of "[(t, u)]" \<sigma>] by simp
  ultimately show ?thesis
    using Unif(2) x_sdom by auto
next
  case (Ksub M1 x u M2 A t)
  have c_cs: "cs_fv cs = c_fv (c_sapply \<sigma> c)"
    using Ksub unfolding cs_fv_def by simp
  have \<sigma>_sdom: "msg_sdom \<sigma> = {x}"
    using Ksub msg_sdom_single_non_trivial[of \<iota> x] by simp
  have \<sigma>_svran: "msg_svran \<sigma> = msg_fv \<iota>"
    using Ksub msg_svran_single_non_trivial[of \<iota> x] by simp
  have sdom_svran: "msg_sdom(\<sigma>) \<inter> msg_svran(\<sigma>) = {}"
    using \<sigma>_sdom \<sigma>_svran unfolding msg_fv_def by simp
  have x_in_c: "x \<in> c_fv c"
    using Ksub unfolding c_fv_def msg_fv_def by simp
  have \<sigma>_cs':  "cs_fv (cs_sapply \<sigma> cs') \<subseteq> (cs_fv(cs') - msg_sdom \<sigma>) \<union> msg_svran \<sigma>"
    using cs_fv_sapply_sdom_svran[of \<sigma> cs'] by simp
  moreover have fv_subseteq: "cs_fv(cs) \<union> {x} \<subseteq> c_fv(c)"
    using c_cs fv_x_\<iota>[OF Ksub(2), of c] x_in_c by simp
  ultimately show ?thesis 
    using Ksub cs_cs'_fv[of cs "cs_sapply \<sigma> cs'"] c_cs'_fv[of c cs'] \<sigma>_sdom \<sigma>_svran sdom_svran \<sigma>_cs'
    by (simp; smt (verit, best) DiffE Un_iff \<sigma>_sdom \<sigma>_svran c_cs_fv c_fv_sapply_sdom_svran insertI1 subset_Un_eq)
qed (auto simp add: assms)

lemma c_cs_\<eta>2_w:
  assumes "c  \<leadsto>\<^sub>1[Variable] cs"
  shows "\<eta>_2(cs) < weight(c)"
  using assms
proof(cases rule: rer1.cases)
  case (Unif t u M A)
  then show ?thesis
    using weight_positive[of c]
    unfolding \<eta>_2_def
    by simp
next
  case (CompHash M A t)
  have "weight (M|A \<rhd>t) = (\<chi>_list M * (\<theta> t))"
    unfolding weight_def
    by simp
  also have "... < (\<chi>_list M * (\<theta> t + 1))"
    using \<theta>_positive \<chi>_positive \<chi>_list_positive
    by (simp add: Suc_le_lessD)
  also have "... = (\<chi>_list M * (\<theta> (Hash t)))"
    by simp
  also have "... = weight (M|A \<rhd> Hash t)"
    using weight_def 
    by simp
  also have "... = weight (c)"
    using CompHash
    by simp
  finally show ?thesis
    using CompHash unfolding \<eta>_2_def by auto
next
  case (CompPair M A t1 t2)
  have "weight (M|A \<rhd>t1) + weight (M|A \<rhd>t2) = (\<chi>_list M * (\<theta> t1)) + (\<chi>_list M * (\<theta> t2))"
    unfolding weight_def
    by simp
  also have "... < \<chi>_list M * (\<theta> t1 + \<theta> t2 + 1)"
    subsubsection \<open>HERE\<close>
    using \<theta>_positive \<chi>_positive \<chi>_list_positive
    by (simp add: discrete distrib_left)
  also have "... = \<chi>_list M * (\<theta> (Pair t1 t2))"
    by simp
  also have "... = weight (M|A \<rhd> Pair t1 t2)"
    using weight_def 
    by simp
  also have "... = weight (c)"
    using CompPair
    by simp
  finally show ?thesis
    using CompPair unfolding \<eta>_2_def by auto
next
  case (CompSymEncrypt M A k t)
  have "weight (M|A \<rhd>k) + weight (M|A \<rhd>t) = (\<chi>_list M * (\<theta> k)) + (\<chi>_list M * (\<theta> t))"
    unfolding weight_def
    by simp
  also have "... < \<chi>_list M * (\<theta> k + \<theta> t + 1)"
    using \<theta>_positive \<chi>_positive \<chi>_list_positive
    by (simp add: discrete distrib_left)
  also have "... = \<chi>_list M * (\<theta> (SymEncrypt k t))"
    by simp
  also have "... = weight (M|A \<rhd> (SymEncrypt k t))"
    using weight_def 
    by simp
  also have "... = weight (c)"
    using CompSymEncrypt
    by simp
  finally show ?thesis
    using CompSymEncrypt
    unfolding \<eta>_2_def unfolding \<eta>_2_def by auto
next
  case (CompPubKeyEncrypt M A k t)
  have "weight (M|A \<rhd>k) + weight (M|A \<rhd>t) = (\<chi>_list M * (\<theta> k)) + (\<chi>_list M * (\<theta> t))"
    unfolding weight_def
    by simp
  also have "... < \<chi>_list M * (\<theta> k + \<theta> t + 1)"
    using \<theta>_positive \<chi>_positive \<chi>_list_positive
    by (simp add: discrete distrib_left)
  also have "... = \<chi>_list M * (\<theta> (PubKeyEncrypt k t))"
    by simp
  also have "... = weight (M|A \<rhd> (PubKeyEncrypt k t))"
    using weight_def 
    by simp
  also have "... = weight (c)"
    using CompPubKeyEncrypt
    by simp
  finally show ?thesis
    using CompPubKeyEncrypt unfolding \<eta>_2_def by auto
next
  case (CompSig M A t)
  have "weight (M|A \<rhd>\<iota>) + weight (M|A \<rhd>t) = (\<chi>_list M * (\<theta> \<iota>)) + (\<chi>_list M * (\<theta> t))"
    unfolding weight_def
    by simp
  also have "... < \<chi>_list M * (\<theta> \<iota> + \<theta> t + 1)"
    using \<theta>_positive \<chi>_positive \<chi>_list_positive
    by (simp add: discrete distrib_left)
  also have "... = \<chi>_list M * (\<theta> (Sig \<iota> t))"
    by simp
  also have "... = weight (M|A \<rhd> (Sig \<iota> t))"
    using weight_def 
    by simp
  also have "... = weight (c)"
    using CompSig
    by simp
  finally show ?thesis
    using CompSig unfolding \<eta>_2_def by auto
next
  case (Proj M1 u v M2 A t)
  have pair_ineq: "(\<chi> u) * (\<chi> v) < (\<chi> (Pair u v))"
    by auto
  then show ?thesis
    using Proj Suc_le_eq \<theta>_positive \<chi>_list_pair_ineq
    unfolding \<eta>_2_def weight_def 
    by auto
next
  case (Sdec M1 k u M2 A t)
  have "weight ((M1 @ u # M2)|(SymEncrypt k u # A) \<rhd>t) + weight ((M1 @ M2)|(SymEncrypt k u # A)\<rhd>k)
        = ((\<chi>_list (M1 @ M2) * (\<chi> u) * (\<theta> t)) + (\<chi>_list (M1 @ M2) * (\<theta> k)))"
    unfolding weight_def \<chi>_list_def
    by auto
  also have "... < ((\<chi>_list (M1 @ M2) * (\<chi> u) * (\<theta> t)) + (\<chi>_list (M1 @ M2) * ((\<theta> k) + 1) * (\<theta> t)))"
    using \<theta>_positive \<chi>_positive \<chi>_list_positive
    by (clarsimp; metis One_nat_def Suc_le_lessD add.commute add_lessD1 less_add_same_cancel2 n_less_n_mult_m nat_mult_1_right order_less_le)
  also have "... = (\<chi>_list (M1 @ M2) * (\<chi> u + \<theta> k + 1) * (\<theta> t))"
    by (simp add: add_mult_distrib add_mult_distrib2)
  also have "... = (\<chi>_list (M1 @ M2) * (\<chi> (SymEncrypt k u)) * (\<theta> t))"
    by simp
  also have "... = weight ((M1 @ (SymEncrypt k u) # M2)|A \<rhd>t)"
    unfolding weight_def \<chi>_list_def
    by (simp add: mult.commute mult.left_commute)
  also have "... = weight(c)"
    using Sdec unfolding weight_def by simp
  finally show ?thesis
    using Sdec unfolding \<eta>_2_def by auto
next
  case (Adec M1 u M2 A t)
  have "weight ((M1 @ u # M2)|(PubKeyEncrypt \<iota> u # A) \<rhd>t) = (\<chi>_list (M1 @ M2) * (\<chi> u) * (\<theta> t))"
    unfolding weight_def \<chi>_list_def
    by auto
  also have "... < (\<chi>_list (M1 @ M2) * (\<chi> u + 1) * (\<theta> t))"
    using \<theta>_positive \<chi>_positive \<chi>_list_positive Suc_le_eq 
    by auto
  also have "... = (\<chi>_list (M1 @ M2) * (\<chi> (PubKeyEncrypt \<iota> u)) * (\<theta> t))"
    by simp
  also have "... = weight ((M1 @ (PubKeyEncrypt \<iota> u) # M2)|A \<rhd>t)"
    unfolding weight_def \<chi>_list_def
    by (simp add: distrib_left)
  also have "... = weight(c)"
    using Adec unfolding weight_def by simp
  finally show ?thesis
    using Adec unfolding \<eta>_2_def by auto
next
  subsubsection \<open>HERE\<close>
  case (Ksub M1 x u M2 A t)
  have "Variable \<noteq> Variable(x := \<iota>)"
    by (metis fun_upd_def msg.distinct(1))
  then show ?thesis using Ksub by simp
qed

lemma cs_fv_perm: "cs_fv (c # cs'1 @ cs'2) = cs_fv (cs'1 @ c # cs'2)"
  unfolding cs_fv_def by auto

lemma wf_cs_\<eta>1:
  assumes "c \<leadsto>\<^sub>1[\<sigma>] cs"
    and "cs' = cs'1 @ c # cs'2"
    and "cs'' = cs @ cs_sapply \<sigma> (cs'1 @ cs'2)"
  shows "\<eta>_1 cs'' \<le> \<eta>_1 cs'"
proof -
  have "cs_fv (cs @ cs_sapply \<sigma> (cs'1 @ cs'2)) \<subseteq> cs_fv (c # cs'1 @ cs'2)"
    using assms c_cs_fv_subseteq[of c \<sigma> cs "(cs'1 @ cs'2)"] by simp
  moreover have "... = cs_fv (cs'1 @ c # cs'2)"
      using cs_fv_perm by simp
  ultimately have "cs_fv (cs @ cs_sapply \<sigma> (cs'1 @ cs'2)) \<subseteq> cs_fv (cs'1 @ c # cs'2)"
    by simp
  then show ?thesis
    using assms cs_fv_finite[of "(cs'1 @ c # cs'2)"] card_mono
    unfolding \<eta>_1_def by simp
qed

lemma wf_cs_\<eta>2:
  assumes "c \<leadsto>\<^sub>1[Variable] cs"
    and "cs' = cs'1 @ c # cs'2"
    and "cs'' = cs @ cs_sapply Variable (cs'1 @ cs'2)"
  shows "\<eta>_2 cs'' < \<eta>_2 cs'"
proof -
  have "cs'' = cs @ (cs'1 @ cs'2)"
    using assms cs_sapply_id[of "cs'1 @ cs'2"] by simp
  moreover have "\<eta>_2 cs < weight c"
    using assms c_cs_\<eta>2_w[of c cs] by simp
  ultimately show ?thesis
    using assms(2) cs_fv_finite[of "(cs'1 @ c # cs'2)"] card_mono
    unfolding \<eta>_2_def by simp
qed

lemma wf_cs:
  assumes "cs \<leadsto>[\<sigma>] cs'" 
  shows "(cs', cs) \<in> measures [\<eta>_1, \<eta>_2]"
  using assms
proof(cases rule: rer.cases)
  case (Context c cs'' cs'1 cs'2)
  from this(3,1,2) show ?thesis
  proof(cases rule: rer1.cases)
    case (Unif t u M A)
    have rer1_Unif: "c \<leadsto>\<^sub>1[\<sigma>] []"
      using Unif rer1.intros(1) by simp
    then have "cs_fv (cs'' @ cs_sapply \<sigma> (cs'1 @ cs'2)) \<subseteq> cs_fv (c # cs'1 @ cs'2)"
      using Unif(2) c_cs_fv_subseteq[of c \<sigma> "[]" "(cs'1 @ cs'2)"] by simp
    also have perm_eq: "... = cs_fv (cs'1 @ c # cs'2)"
      using cs_fv_perm by simp
    ultimately have "cs_fv (cs'' @ cs_sapply \<sigma> (cs'1 @ cs'2)) \<subseteq> cs_fv (cs'1 @ c # cs'2)"
      by simp
    then show ?thesis
      using Context(1-3) cs_fv_finite[of "(cs'1 @ c # cs'2)"]
      unfolding \<eta>_1_def \<eta>_2_def 
      by (simp; metis \<eta>_2_def add.left_commute add_less_cancel_right c_cs_\<eta>2_w c_cs_fv_noteq cs_sapply_id map_append perm_eq psubsetI psubset_card_mono sum_list_append)
  next
    subsubsection \<open>HERE\<close>
    case (CompHash M A t)
    have "\<eta>_1 cs' \<le> \<eta>_1 cs"
      using Context wf_cs_\<eta>1[of c \<sigma> cs'' _ cs'1 cs'2] by simp
    moreover have "\<eta>_2 cs' < \<eta>_2 cs" 
      using Context CompHash wf_cs_\<eta>2[of c cs'' cs cs'1 cs'2 cs'] by simp
    ultimately show ?thesis by auto
  next
    case (CompPair M A t1 t2)
    have "\<eta>_1 cs' \<le> \<eta>_1 cs"
      using Context wf_cs_\<eta>1[of c \<sigma> cs'' _ cs'1 cs'2] by simp
    moreover have "\<eta>_2 cs' < \<eta>_2 cs" 
      using Context CompPair wf_cs_\<eta>2[of c cs'' cs cs'1 cs'2 cs'] by simp
    ultimately show ?thesis by auto
  next
    case (CompSymEncrypt M A k t)
    have "\<eta>_1 cs' \<le> \<eta>_1 cs"
      using Context wf_cs_\<eta>1[of c \<sigma> cs'' _ cs'1 cs'2] by simp
    moreover have "\<eta>_2 cs' < \<eta>_2 cs" 
      using Context CompSymEncrypt wf_cs_\<eta>2[of c cs'' cs cs'1 cs'2 cs'] by simp
    ultimately show ?thesis by auto
  next
    case (CompPubKeyEncrypt M A k t)
    have "\<eta>_1 cs' \<le> \<eta>_1 cs"
      using Context wf_cs_\<eta>1[of c \<sigma> cs'' _ cs'1 cs'2] by simp
    moreover have "\<eta>_2 cs' < \<eta>_2 cs" 
      using Context CompPubKeyEncrypt wf_cs_\<eta>2[of c cs'' cs cs'1 cs'2 cs'] by simp
    ultimately show ?thesis by auto
  next
    case (CompSig M A t)
    have "\<eta>_1 cs' \<le> \<eta>_1 cs"
      using Context wf_cs_\<eta>1[of c \<sigma> cs'' _ cs'1 cs'2] by simp
    moreover have "\<eta>_2 cs' < \<eta>_2 cs" 
      using Context CompSig wf_cs_\<eta>2[of c cs'' cs cs'1 cs'2 cs'] by simp
    ultimately show ?thesis by auto
  next
    case (Proj M1 u v M2 A t)
    have "\<eta>_1 cs' \<le> \<eta>_1 cs"
      using Context wf_cs_\<eta>1[of c \<sigma> cs'' _ cs'1 cs'2] by simp
    moreover have "\<eta>_2 cs' < \<eta>_2 cs" 
      using Context Proj wf_cs_\<eta>2[of c cs'' cs cs'1 cs'2 cs'] by simp
    ultimately show ?thesis by auto
  next
    case (Sdec M1 k u M2 A t)
    have "\<eta>_1 cs' \<le> \<eta>_1 cs"
      using Context wf_cs_\<eta>1[of c \<sigma> cs'' _ cs'1 cs'2] by simp
    moreover have "\<eta>_2 cs' < \<eta>_2 cs" 
      using Context Sdec wf_cs_\<eta>2[of c cs'' cs cs'1 cs'2 cs'] by simp
    ultimately show ?thesis by auto
  next
    case (Adec M1 u M2 A t)
    have "\<eta>_1 cs' \<le> \<eta>_1 cs"
      using Context wf_cs_\<eta>1[of c \<sigma> cs'' _ cs'1 cs'2] by simp
    moreover have "\<eta>_2 cs' < \<eta>_2 cs" 
      using Context Adec wf_cs_\<eta>2[of c cs'' cs cs'1 cs'2 cs'] by simp
    ultimately show ?thesis by auto
  next
    case (Ksub M1 x u M2 A t)
    have "cs_fv (cs'' @ cs_sapply \<sigma> (cs'1 @ cs'2)) \<subseteq> cs_fv (c # cs'1 @ cs'2)"
      using Context(3) c_cs_fv_subseteq[of c \<sigma> "cs''" "(cs'1 @ cs'2)"] by simp
    moreover have perm_eq: "... = cs_fv (cs'1 @ c # cs'2)"
      using cs_fv_perm by simp
    ultimately have cs_fv_subseteq: "cs_fv (cs'' @ cs_sapply \<sigma> (cs'1 @ cs'2)) \<subseteq> cs_fv (cs'1 @ c # cs'2)"
      by simp
    have "\<sigma> \<noteq> Variable" using Ksub(2)
      by (simp add: fun_upd_idem_iff)
    then have "cs_fv (cs'' @ cs_sapply \<sigma> (cs'1 @ cs'2)) \<noteq> cs_fv (c # cs'1 @ cs'2)"
      using Context(3) c_cs_fv_noteq[of c \<sigma> "cs''" "(cs'1 @ cs'2)"] by simp
    then have "cs_fv (cs'' @ cs_sapply \<sigma> (cs'1 @ cs'2)) \<noteq> cs_fv (cs'1 @ c # cs'2)"
      using perm_eq by simp
    then show ?thesis
      using Context(1,2) cs_fv_subseteq
      unfolding \<eta>_1_def \<eta>_2_def 
      by (simp add: cs_fv_finite[of "(cs'1 @ c # cs'2)"] psubset_card_mono)
  qed
qed
  
theorem wf_red: "wf ({(cs', cs). \<exists>\<sigma>. cs \<leadsto>[\<sigma>] cs'})"
  using wf_subset[of "measures [\<eta>_1, \<eta>_2]" "{(cs', cs). \<exists>\<sigma>. cs \<leadsto>[\<sigma>] cs'}"] wf_cs by fastforce

end