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

lemma wf_term_embed [simp]: "wf_term arity (embed msg)"
  apply(induction msg)
  by simp_all

lemma msg_of_term_embed [simp]: "msg_of_term (embed msg) = msg"
  apply(induction msg)
  by simp_all

lemma upper_bound_arity: "arity s = Suc (Suc (Suc x)) \<longleftrightarrow> False"
  apply(cases s)
  by simp_all

lemma embed_msg_of_term [simp]: "wf_term arity t \<Longrightarrow> embed (msg_of_term t) = t"
  apply(induction t rule: msg_of_term.induct)
                      apply(simp_all add: upper_bound_arity)
  apply(metis upper_bound_arity)
  done

lemma wf_subst_embed [simp]: "wf_subst arity (embed \<circ> \<sigma>)"
  by (simp add: wf_subst_def)

lemma msg_of_term_inject:
"\<lbrakk> wf_term arity t1; wf_term arity t2 \<rbrakk>
\<Longrightarrow> msg_of_term t1 = msg_of_term t2 \<longleftrightarrow> t1 = t2"
  by (metis embed_msg_of_term)

subsection \<open>(d)\<close>
type_synonym msg_equation = "msg \<times> msg"
type_synonym msg_equations = "msg_equation list"
type_synonym symbol_subst = "string \<Rightarrow> (symbol, string) term"
type_synonym msg_subst = "string \<Rightarrow> msg"

definition msg_fv :: "msg \<Rightarrow> string set" where
  "msg_fv m = fv (embed m)"

definition msg_sapply :: "msg_subst \<Rightarrow> msg \<Rightarrow> msg" (infixr "\<cdot>m" 67) where
  "msg_sapply \<sigma> m = msg_of_term ((embed \<circ> \<sigma>) \<cdot> (embed m))"

definition msg_scomp :: "msg_subst \<Rightarrow> msg_subst \<Rightarrow> msg_subst" (infixl "\<circ>m" 55)
  where "msg_scomp \<sigma> \<tau> = msg_of_term \<circ> ((embed \<circ> \<sigma>) \<circ>s (embed \<circ> \<tau>))"

definition msg_fv_eq :: "msg_equation \<Rightarrow> string set" where
  "msg_fv_eq eq = (msg_fv (fst eq) \<union> msg_fv (snd eq))"

definition msg_fv_eqs :: "msg_equations \<Rightarrow> string set" where
  "msg_fv_eqs eqs = \<Union>(set (map msg_fv_eq eqs))"

lemma fv_sapply: "msg_fv (\<sigma> \<cdot>m t) = fv ((embed \<circ> \<sigma>) \<cdot> (embed t))"
  by (simp add: fv_sapply msg_fv_def msg_sapply_def wf_term_sapply)

definition msg_sdom :: "msg_subst \<Rightarrow> string set" where
  "msg_sdom \<sigma> = sdom (embed \<circ> \<sigma>)"

definition msg_svran :: "msg_subst \<Rightarrow> string set" where
  "msg_svran \<sigma> = svran (embed \<circ> \<sigma>)"

lemma msg_sdom_var [simp]: "msg_sdom Variable = {}"
  by(simp add: msg_sdom_def sdom_def)

lemma msg_svran_var [simp]: "msg_svran Variable = {}"
  by(simp add: msg_svran_def svran_def sdom_def)

lemma msg_var_ineq: "t \<noteq> Variable x \<Longrightarrow> embed t \<noteq> Var x"
  by(metis msg_of_term.simps(1) msg_of_term_embed)

lemma msg_sdom_single_non_trivial [simp]: "t \<noteq> Variable x \<Longrightarrow> msg_sdom (Variable(x:=t)) = {x}"
  by(simp add: msg_sdom_def sdom_def msg_var_ineq)

lemma msg_svran_single_non_trivial [simp]: "t \<noteq> Variable x \<Longrightarrow> msg_svran (Variable(x:=t)) = msg_fv t" 
  by(auto simp add: msg_svran_def svran_def sdom_def msg_var_ineq msg_fv_def)

lemma msg_sdomI: "\<sigma> x \<noteq> Variable x \<Longrightarrow> x \<in> msg_sdom \<sigma>"
  by(simp add: msg_sdom_def sdom_def msg_var_ineq)

lemma msg_fv_sapply_sdom_svran: "msg_fv (\<sigma> \<cdot>m t) \<subseteq> (msg_fv t - msg_sdom \<sigma>) \<union> msg_svran \<sigma>"
  unfolding msg_sdom_def msg_svran_def
  using svapply_svdom_svran msg_fv_def msg_sapply_def fv_sapply
  by (simp; fastforce)

lemma msg_sdom_scomp: "msg_sdom (\<sigma> \<circ>m \<tau>) \<subseteq> msg_sdom \<sigma> \<union> msg_sdom \<tau>"
  unfolding msg_sdom_def
  using sdom_scomp
  by (auto simp add: msg_scomp_def sdom_def scomp_sapply)

(* TODO: Rewrite this proof *)
lemma msg_svran_scomp: "msg_svran (\<sigma> \<circ>m \<tau>) \<subseteq> msg_svran \<sigma> \<union> msg_svran \<tau>"
  using svran_scomp[of "(embed \<circ> \<sigma>)" "(embed \<circ> \<tau>)"]
  unfolding msg_svran_def svran_def sdom_def
  apply (simp add: msg_scomp_def scomp_def fv_sapply)
  apply (smt (verit, best) Collect_cong Sup.SUP_cong embed_msg_of_term wf_subst_embed wf_term_embed wf_term_sapply)
  done

(* TODO: Rewrite this proof *)
lemma msg_scomp_distrib: 
  "(\<sigma> \<circ>m \<tau>) \<cdot>m t = \<sigma> \<cdot>m (\<tau> \<cdot>m t)"
  using sapply_scomp_distrib[of "(embed \<circ> \<sigma>)" "(embed \<circ> \<tau>)" "(embed t)"] 
  apply (simp add: msg_scomp_def scomp_def msg_sapply_def)
  apply (smt (verit, best) comp_apply embed_msg_of_term sapply_cong scomp_sapply wf_subst_embed wf_term_embed wf_term_sapply)
  done

lemma msg_scomp_assoc: 
  "(\<sigma> \<circ>m \<tau>) \<circ>m \<upsilon> = \<sigma> \<circ>m (\<tau> \<circ>m \<upsilon>)"
  using msg_scomp_distrib msg_sapply_def
  unfolding msg_scomp_def scomp_def msg_sapply_def
  by fastforce
  
lemma msg_var_sapply[simp]: "Variable \<cdot>m t = t"
  using sapply_Var[of "embed t"]
  unfolding msg_sapply_def
  by (simp add: sapply_cong)

lemma msg_var_sig: "Variable \<cdot>m (\<sigma> \<cdot>m x) = \<sigma> \<cdot>m x"
  using msg_var_sapply
  by simp

lemma msg_var_scomp[simp]: "\<sigma> \<circ>m Variable = \<sigma>"
  using scomp_Var[of "embed \<circ> \<sigma>"]
  unfolding msg_scomp_def comp_def
  by auto

definition msg_unifies_eq :: "msg_subst \<Rightarrow> msg_equation \<Rightarrow> bool" where
  "msg_unifies_eq \<sigma> pair = unifies_eq (embed \<circ> \<sigma>) (embed (fst pair), embed (snd pair))"

lemma msg_unifies_eq_alt: "msg_unifies_eq \<sigma> pair = (\<sigma> \<cdot>m fst(pair) = \<sigma> \<cdot>m snd(pair))"
  unfolding msg_unifies_eq_def
  by (simp add: wf_term_sapply msg_sapply_def msg_of_term_inject unifies_eq_def)

definition msg_unifies :: "msg_subst \<Rightarrow> msg_equations \<Rightarrow> bool" where
  "msg_unifies \<sigma> pairs = unifies (embed \<circ> \<sigma>) (map (\<lambda>pair. map_prod embed embed pair) pairs)"

(* remember: corresponding definition is a recursive function *)
lemma msg_unifies_alt: "msg_unifies \<sigma> pairs = (\<forall>pair \<in> set pairs. msg_unifies_eq \<sigma> pair)"
  unfolding msg_unifies_eq_def msg_unifies_def
  apply (auto simp add: unifies_eq_def)
  sorry

definition msg_unify :: "msg_equations \<Rightarrow> msg_subst option" where
  "msg_unify pairs = map_option ((\<circ>) msg_of_term) (unify (map (\<lambda>pair. map_prod embed embed pair) pairs))"

definition msg_is_mgu :: "msg_subst \<Rightarrow> msg_equations \<Rightarrow> bool" where
  "msg_is_mgu \<sigma> pairs = is_mgu (embed \<circ> \<sigma>) (map (\<lambda>pair. map_prod embed embed pair) pairs)"

lemma msg_is_mgu_alt: "msg_is_mgu \<sigma> msg_pairs = (msg_unifies \<sigma> msg_pairs \<and> (\<forall>\<tau>. (msg_unifies \<tau> msg_pairs \<longrightarrow> (\<exists>\<tau>'. (\<tau> = \<tau>' \<circ>m \<sigma>)))))"
  apply(simp only: msg_is_mgu_def)
  apply(simp only: is_mgu_def)
  (* apply(simp only: unifies_eq_def)
  apply(simp only: msg_unifiess_alt)
  apply (rule iffI)
   apply(intro iffI impI conjI; clarsimp)
    apply fastforce *)
  sorry

lemma msg_unify_svran_fv: "msg_unify eqs = Some \<sigma> \<Longrightarrow> msg_svran \<sigma> \<subseteq> msg_fv_eqs eqs"
  using unify_svran_fv[of _ "embed \<circ> \<sigma>"]
  unfolding msg_unify_def msg_svran_def msg_fv_eqs_def msg_fv_eq_def msg_fv_def
  sorry
  
subsection \<open>(e)\<close>

lemma msg_unify_unifies:
  "msg_unify MU = Some \<sigma> \<Longrightarrow> msg_unifies \<sigma> MU"
  sorry
  
subsection \<open>(f)\<close>

lemma msg_unify_mgu: 
  "msg_unify MU = Some \<sigma> \<Longrightarrow> msg_unifies \<tau> MU \<Longrightarrow> \<exists> s. \<tau> = s \<circ>m \<sigma>"
  sorry

lemma msg_unify_soundness:
  "msg_unify MU = Some \<sigma> \<Longrightarrow> msg_is_mgu \<sigma> MU"
  sorry

end