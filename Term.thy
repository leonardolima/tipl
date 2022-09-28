theory Term
  imports Main Unification
begin

(***********************************)
(*                                 *)
(*                                 *)
(*          Assignment 5           *)
(*                                 *)
(*                                 *)
(***********************************)

(* (a) *)
datatype msg =
  is_Variable : Variable string
| Constant string
| Hash msg
| Pair msg msg
| SymEncrypt msg msg
| PubKeyEncrypt msg msg 
| Sig msg msg

(* (b) *)
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

(* (c) *)
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
    by(simp_all add: upper_bound_arity)

lemma wf_subst_embed [simp]: "wf_subst arity (embed \<circ> \<sigma>)"
  by (simp add: wf_subst_def)

lemma msg_of_term_inject:
"\<lbrakk> wf_term arity t1; wf_term arity t2 \<rbrakk>
\<Longrightarrow> msg_of_term t1 = msg_of_term t2 \<longleftrightarrow> t1 = t2"
  by (metis embed_msg_of_term)

(* (d) *)
type_synonym msg_equation = "msg \<times> msg"
type_synonym msg_equations = "msg_equation list"
type_synonym symbol_subst = "string \<Rightarrow> (symbol, string) term"
type_synonym msg_subst = "string \<Rightarrow> msg"

definition msg_fv :: "msg \<Rightarrow> string set" where
  "msg_fv m = fv (embed m)"

definition msg_sapply :: "msg_subst \<Rightarrow> msg \<Rightarrow> msg" where
  "msg_sapply \<sigma> m = msg_of_term ((embed \<circ> \<sigma>) \<cdot> (embed m))"

definition msg_scomp :: "msg_subst \<Rightarrow> msg_subst \<Rightarrow> msg_subst" where
  "msg_scomp \<sigma> \<tau> = msg_of_term \<circ> ((embed \<circ> \<sigma>) \<circ>s (embed \<circ> \<tau>))"

fun msg_unifies :: "msg_subst \<Rightarrow> msg_equation \<Rightarrow> bool" where
  "msg_unifies \<sigma> (m1, m2) = unifies (embed \<circ> \<sigma>) (embed m1, embed m2)"

definition msg_unifiess :: "msg_subst \<Rightarrow> msg_equations \<Rightarrow> bool" where
  "msg_unifiess \<sigma> eqs = (\<forall> eq \<in> set eqs. msg_unifies \<sigma> eq)"

definition msg_unify :: "msg_equations \<Rightarrow> msg_subst option" where
  "msg_unify msg_pairs = map_option ((\<circ>) msg_of_term) (unify (map (\<lambda>(m1, m2). map_prod embed embed (m1, m2)) msg_pairs))"

(* (e) *)
lemma msg_unify_unifiess:
  "msg_unify MU = Some \<sigma> \<Longrightarrow> msg_unifiess \<sigma> MU"
  sorry
  
(* (f) *)
lemma msg_unify_mgu: 
  "msg_unify MU = Some \<sigma> \<Longrightarrow> msg_unifiess \<tau> MU \<Longrightarrow> \<exists> s. \<tau> = msg_scomp s \<sigma>"
  sorry

end