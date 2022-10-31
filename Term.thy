theory Term
  imports Main Unification
begin

section \<open>Assignment 5\<close>

subsection \<open>(a)\<close>

datatype msg =
  is_Variable : Variable string
| Constant string
| Hash msg
| Pair msg msg
| SymEncrypt msg msg
| PubKeyEncrypt msg msg 
| Sig msg msg

subsection \<open>(b)\<close>

datatype symbol =
  Constant_Symbol string
| Hash_Symbol 
| Pair_Symbol  
| SymEncrypt_Symbol
| PubKeyEncrypt_Symbol
| Sig_Symbol

fun arity :: "symbol \<Rightarrow> nat" where
  "arity (Constant_Symbol _) = 0"
| "arity Hash_Symbol = 1"
| "arity Pair_Symbol = 2"
| "arity SymEncrypt_Symbol = 2"
| "arity PubKeyEncrypt_Symbol = 2"
| "arity Sig_Symbol = 2"

subsection \<open>(c)\<close>

fun embed :: "msg \<Rightarrow> (symbol, string) term" where
  "embed (Variable x) = Var x"
| "embed (Constant c) = Fun (Constant_Symbol c) []"
| "embed (Hash m) = Fun Hash_Symbol [embed m]"
| "embed (Pair m1 m2) = Fun Pair_Symbol [embed m1, embed m2]"
| "embed (SymEncrypt m1 m2) = Fun SymEncrypt_Symbol [embed m1, embed m2]"
| "embed (PubKeyEncrypt m1 m2) = Fun PubKeyEncrypt_Symbol [embed m1, embed m2]"
| "embed (Sig m1 m2) = Fun Sig_Symbol [embed m1, embed m2]"

fun msg_of_term :: "(symbol, string) term \<Rightarrow> msg" where
  "msg_of_term (Var x) = Variable x"
| "msg_of_term (Fun (Constant_Symbol c) []) = Constant c"
| "msg_of_term (Fun Hash_Symbol [m]) = Hash (msg_of_term m)"
| "msg_of_term (Fun Pair_Symbol [m1, m2]) = Pair (msg_of_term m1) (msg_of_term m2)"
| "msg_of_term (Fun SymEncrypt_Symbol [k, m]) = SymEncrypt (msg_of_term k) (msg_of_term m)"
| "msg_of_term (Fun PubKeyEncrypt_Symbol [k, m]) = PubKeyEncrypt (msg_of_term k) (msg_of_term m)"
| "msg_of_term (Fun Sig_Symbol [k, m]) = Sig (msg_of_term k) (msg_of_term m)"
| "msg_of_term _ = undefined"

lemma wf_term_embed [simp]: "wf_term arity (embed m)"
  by (induction m) simp_all

lemma msg_of_term_embed [simp]: "msg_of_term (embed m) = m"
  by (induction m) simp_all

lemma arity_upper_bound: "arity s = Suc (Suc (Suc x)) \<longleftrightarrow> False"
  by (cases s) simp_all

lemma embed_msg_of_term [simp]: "wf_term arity t \<Longrightarrow> embed (msg_of_term t) = t"
  apply(induction t rule: msg_of_term.induct)
                      apply(simp_all add: arity_upper_bound)
  apply(metis arity_upper_bound)
  done

lemma wf_subst_embed [simp]: "wf_subst arity (embed \<circ> \<sigma>)"
  by (simp add: wf_subst_def)

lemma msg_of_term_inject:
"\<lbrakk> wf_term arity t1; wf_term arity t2 \<rbrakk>
\<Longrightarrow> msg_of_term t1 = msg_of_term t2 \<longleftrightarrow> t1 = t2"
  using embed_msg_of_term by fastforce

subsection \<open>(d)\<close>

type_synonym msg_equation = "msg \<times> msg"
type_synonym msg_equations = "msg_equation list"
type_synonym symbol_subst = "string \<Rightarrow> (symbol, string) term"
type_synonym msg_subst = "string \<Rightarrow> msg"

definition msg_fv :: "msg \<Rightarrow> string set" where
  "msg_fv m = fv (embed m)"

definition msg_sapply :: "msg_subst \<Rightarrow> msg \<Rightarrow> msg" (infixr "\<cdot>m" 67) where
  "msg_sapply \<sigma> m = msg_of_term ((embed \<circ> \<sigma>) \<cdot> (embed m))"

definition msg_scomp :: "msg_subst \<Rightarrow> msg_subst \<Rightarrow> msg_subst" (infixl "\<circ>m" 55) where 
  "msg_scomp \<sigma> \<tau> = msg_of_term \<circ> ((embed \<circ> \<sigma>) \<circ>s (embed \<circ> \<tau>))"

definition msg_fv_eq :: "msg_equation \<Rightarrow> string set" where
  "msg_fv_eq eq = (msg_fv (fst eq) \<union> msg_fv (snd eq))"

definition msg_fv_list :: "msg list \<Rightarrow> string set" where
  "msg_fv_list mlist = \<Union>(set (map msg_fv mlist))"

definition msg_fv_eqs :: "msg_equations \<Rightarrow> string set" where
  "msg_fv_eqs eqs = \<Union>(set (map msg_fv_eq eqs))"

lemma fv_sapply: "msg_fv (\<sigma> \<cdot>m t) = fv ((embed \<circ> \<sigma>) \<cdot> (embed t))"
  by (simp add: msg_fv_def msg_sapply_def wf_term_sapply)

definition msg_sdom :: "msg_subst \<Rightarrow> string set" where
  "msg_sdom \<sigma> = sdom (embed \<circ> \<sigma>)"

definition msg_svran :: "msg_subst \<Rightarrow> string set" where
  "msg_svran \<sigma> = svran (embed \<circ> \<sigma>)"

lemma msg_sdom_var [simp]: "msg_sdom Variable = {}"
  by (simp add: msg_sdom_def sdom_def)

lemma msg_svran_var [simp]: "msg_svran Variable = {}"
  by (simp add: msg_svran_def svran_def sdom_def)

lemma msg_not_var: "t \<noteq> Variable x \<Longrightarrow> embed t \<noteq> Var x"
  using msg_of_term_embed[of t] by force

lemma msg_sdom_single_non_trivial [simp]: "t \<noteq> Variable x \<Longrightarrow> msg_sdom (Variable(x:=t)) = {x}"
  by (simp add: msg_sdom_def sdom_def msg_not_var)

lemma msg_svran_single_non_trivial [simp]: "t \<noteq> Variable x \<Longrightarrow> msg_svran (Variable(x:=t)) = msg_fv t" 
  by (auto simp add: msg_svran_def svran_def sdom_def msg_not_var msg_fv_def)

lemma msg_sdomI: "\<sigma> x \<noteq> Variable x \<Longrightarrow> x \<in> msg_sdom \<sigma>"
  by (simp add: msg_sdom_def sdom_def msg_not_var)

lemma msg_fv_sapply_sdom_svran: "msg_fv (\<sigma> \<cdot>m t) \<subseteq> (msg_fv t - msg_sdom \<sigma>) \<union> msg_svran \<sigma>"
  unfolding msg_sdom_def msg_svran_def
  using svapply_svdom_svran msg_fv_def msg_sapply_def fv_sapply
  by (simp) fastforce

lemma msg_sdom_scomp: "msg_sdom (\<sigma> \<circ>m \<tau>) \<subseteq> msg_sdom \<sigma> \<union> msg_sdom \<tau>"
  unfolding msg_sdom_def
  using sdom_scomp
  by (auto simp add: msg_scomp_def sdom_def scomp_sapply)

lemma embed_msg_of_term_comp: "Term.embed \<circ> (msg_of_term \<circ> (Term.embed \<circ> \<sigma>) \<circ>s (Term.embed \<circ> \<tau>)) = (Term.embed \<circ> \<sigma>) \<circ>s (Term.embed \<circ> \<tau>)"
  unfolding comp_def scomp_def
  by (simp add: wf_subst_def wf_term_sapply)

lemma msg_svran_scomp: "msg_svran (\<sigma> \<circ>m \<tau>) \<subseteq> msg_svran \<sigma> \<union> msg_svran \<tau>"
  using svran_scomp[of "(embed \<circ> \<sigma>)" "(embed \<circ> \<tau>)"]
  unfolding msg_svran_def msg_scomp_def
  by (simp add: embed_msg_of_term_comp)

lemma msg_scomp_distrib: "(\<sigma> \<circ>m \<tau>) \<cdot>m t = \<sigma> \<cdot>m (\<tau> \<cdot>m t)"
  using sapply_scomp_distrib[of "(embed \<circ> \<sigma>)" "(embed \<circ> \<tau>)" "(embed t)"]
  unfolding msg_scomp_def msg_sapply_def
  by (simp add: embed_msg_of_term_comp wf_term_sapply)

lemma msg_scomp_assoc: 
  "(\<sigma> \<circ>m \<tau>) \<circ>m \<upsilon> = \<sigma> \<circ>m (\<tau> \<circ>m \<upsilon>)"
  using msg_scomp_distrib 
  unfolding msg_scomp_def scomp_def msg_sapply_def
  by fastforce
  
lemma msg_var_sapply [simp]: "Variable \<cdot>m t = t"
  using sapply_Var[of "embed t"]
  unfolding msg_sapply_def
  by (simp add: sapply_cong)

lemma msg_var_sig: "Variable \<cdot>m (\<sigma> \<cdot>m x) = \<sigma> \<cdot>m x"
  using msg_var_sapply by simp

lemma msg_var_scomp [simp]: "\<sigma> \<circ>m Variable = \<sigma>"
  using scomp_Var[of "embed \<circ> \<sigma>"]
  unfolding msg_scomp_def comp_def
  by auto

definition msg_unifies_eq :: "msg_subst \<Rightarrow> msg_equation \<Rightarrow> bool" where
  "msg_unifies_eq \<sigma> eq = unifies_eq (embed \<circ> \<sigma>) (embed (fst eq), embed (snd eq))"

lemma msg_unifies_eq_alt: "msg_unifies_eq \<sigma> eq = (\<sigma> \<cdot>m fst(eq) = \<sigma> \<cdot>m snd(eq))"
  unfolding msg_unifies_eq_def unifies_eq_def
  by (simp add: wf_term_sapply msg_sapply_def msg_of_term_inject)

definition msg_unifies :: "msg_subst \<Rightarrow> msg_equations \<Rightarrow> bool" where
  "msg_unifies \<sigma> eqs = unifies (embed \<circ> \<sigma>) (map (\<lambda>eq. map_prod embed embed eq) eqs)"

(* remember: corresponding definition is a recursive function *)
lemma msg_unifies_alt: "msg_unifies \<sigma> eqs = (\<forall>eq \<in> set eqs. msg_unifies_eq \<sigma> eq)"
  apply(simp add: msg_unifies_def Unification.unifies_forall)
  using msg_unifies_eq_def by auto

definition msg_unify :: "msg_equations \<Rightarrow> msg_subst option" where
  "msg_unify eqs = map_option ((\<circ>) msg_of_term) (unify (map (\<lambda>eq. map_prod embed embed eq) eqs))"

definition msg_is_mgu :: "msg_subst \<Rightarrow> msg_equations \<Rightarrow> bool" where
  "msg_is_mgu \<sigma> eqs = is_mgu (embed \<circ> \<sigma>) (map (\<lambda>eq. map_prod embed embed eq) eqs)"

lemma temp: " (\<forall>\<tau>. (\<forall>eqa\<in>set eqs. \<tau> \<cdot> Term.embed (fst eqa) = \<tau> \<cdot> Term.embed (snd eqa)) \<longrightarrow>
          (\<exists>\<rho>. \<tau> = \<rho> \<circ>s (Term.embed \<circ> \<sigma>))) = (\<forall>\<tau>. (\<forall>eqa\<in>set eqs.
              (Term.embed \<circ> \<tau>) \<cdot> Term.embed (fst eqa) =
              (Term.embed \<circ> \<tau>) \<cdot> Term.embed (snd eqa)) \<longrightarrow>
          (\<exists>\<rho>. \<tau> = msg_of_term \<circ> (Term.embed \<circ> \<rho>) \<circ>s (Term.embed \<circ> \<sigma>)))"
  sorry

lemma msg_is_mgu_alt: "msg_is_mgu \<sigma> eqs = (msg_unifies \<sigma> eqs \<and> (\<forall>\<tau>. (msg_unifies \<tau> eqs \<longrightarrow> (\<exists>\<rho>. \<tau> = \<rho> \<circ>m \<sigma>))))"
  apply(simp add: msg_scomp_def unifies_forall unifies_eq_def msg_is_mgu_def is_mgu_def msg_unifies_def)
  sorry

lemma msg_unify_svran_fv: "msg_unify eqs = Some \<sigma> \<Longrightarrow> msg_svran \<sigma> \<subseteq> msg_fv_eqs eqs"
  using unify_svran_fv[of _ "embed \<circ> \<sigma>"]
  unfolding msg_unify_def msg_svran_def msg_fv_eqs_def msg_fv_eq_def msg_fv_def
  sorry

lemma msg_unify_sdom_fv: "msg_unify eqs = Some \<sigma> \<Longrightarrow> msg_sdom \<sigma> \<subseteq> msg_fv_eqs eqs"
  sorry

lemma msg_unify_sdom_svran: "msg_unify eqs = Some \<sigma> \<Longrightarrow> msg_sdom \<sigma> \<inter> msg_svran \<sigma> = {}"
  sorry
  
subsection \<open>(e)\<close>

lemma msg_unify_unifies:
  "msg_unify MU = Some \<sigma> \<Longrightarrow> msg_unifies \<sigma> MU"
proof-
  have mu_wf: 
    "wf_eqs arity (map (map_prod Term.embed Term.embed) MU)"
    by(simp add: wf_eqs_def wf_eq_terms_wf)
  assume "msg_unify MU = Some \<sigma>"
  hence
    "\<exists>z. unify (map (map_prod Term.embed Term.embed) MU) = Some z \<and>
        msg_of_term \<circ> z = \<sigma>"
    by (simp add: msg_unify_def)
  then obtain z where unify:
    "unify (map (map_prod Term.embed Term.embed) MU) = Some z" and z_def:
        "msg_of_term \<circ> z = \<sigma>"
    by auto
  from this mu_wf have
    "wf_subst arity z"
    by (simp only: wf_subst_unify)
  hence
    "z = embed \<circ> (msg_of_term \<circ> z)"
    by(simp add: fun_eq_iff wf_subst_def)
  moreover from unify have unifies:
    "unifies z (map (map_prod Term.embed Term.embed) MU)"
    by (simp only: unify_soundness_i)
  ultimately show ?thesis using z_def
    by (simp add: msg_unifies_def)
qed
  
subsection \<open>(f)\<close>

lemma msg_unify_mgu: 
  "msg_unify MU = Some \<sigma> \<Longrightarrow> msg_unifies \<tau> MU \<Longrightarrow> \<exists> s. \<tau> = s \<circ>m \<sigma>"
  sorry

lemma msg_unify_soundness:
  "msg_unify MU = Some \<sigma> \<Longrightarrow> msg_is_mgu \<sigma> MU"
  using is_mgu_def msg_is_mgu_alt msg_is_mgu_def msg_unify_mgu msg_unify_unifies by blast

end