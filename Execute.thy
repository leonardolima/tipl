theory Execute
  imports Main Unification Term Deduction
begin

section \<open>Assignment 9\<close>

subsection \<open>(a)\<close>

definition solve_Unif :: "constraint \<Rightarrow> (constraint_system \<times> msg_subst) list" where
  "solve_Unif c = (if \<not>(is_Variable (c_t c)) then
                     (foldr (\<lambda>u acc. let subst = msg_unify [((c_t c), u)] in
                                     if Option.is_none subst then acc
                                     else ([], (Option.the subst)) # acc) ((c_M c) @ (c_A c)) [])
                   else [])"

fun solve_Comp :: "constraint \<Rightarrow> (constraint_system \<times> msg_subst) list" where
  "solve_Comp (M | A \<rhd> (Hash t)) = [([M | A \<rhd> t], Variable)]"
| "solve_Comp (M | A \<rhd> (Pair t1 t2)) = [([M | A \<rhd> t1, M | A \<rhd> t2], Variable)]"
| "solve_Comp (M | A \<rhd> (SymEncrypt k t)) = [([M | A \<rhd> k, M | A \<rhd> t], Variable)]"
| "solve_Comp (M | A \<rhd> (PubKeyEncrypt k t)) = [([M | A \<rhd> k, M | A \<rhd> t], Variable)]"
| "solve_Comp (M | A \<rhd> (Sig \<iota> t)) = [([M | A \<rhd> \<iota>, M | A \<rhd> t], Variable)]"
| "solve_Comp _ = []"

definition solve_Proj :: "constraint \<Rightarrow> (constraint_system \<times> msg_subst) list" where
  "solve_Proj c = concat (map (\<lambda>m. case m of Pair t1 t2 \<Rightarrow> let A = c_A c in
                                                           let M = filter (\<lambda>m'. m \<noteq> m') (c_M c) in
                                                           [([(t1 # t2 # M) | (Pair t1 t2 # A) \<rhd> (c_t c)], Variable)]
                                   | _ \<Rightarrow> []) (c_M c))"

definition solve_Sdec :: "constraint \<Rightarrow> (constraint_system \<times> msg_subst) list" where
  "solve_Sdec c = concat (map (\<lambda>m. case m of SymEncrypt k u \<Rightarrow> let A = c_A c in
                                                               let M = filter (\<lambda>m'. m \<noteq> m') (c_M c) in
                                                               [([(u # M) | (SymEncrypt k u # A) \<rhd> (c_t c), M | (SymEncrypt k u # A) \<rhd> k], Variable)]
                                   | _ \<Rightarrow> []) (c_M c))"

definition solve_Adec :: "constraint \<Rightarrow> (constraint_system \<times> msg_subst) list" where
  "solve_Adec c = concat (map (\<lambda>m. case m of PubKeyEncrypt \<iota> u \<Rightarrow> let A = c_A c in
                                                                  let M = filter (\<lambda>m'. m \<noteq> m') (c_M c) in
                                                                  [([(u # M) | (PubKeyEncrypt \<iota> u # A) \<rhd> (c_t c)], Variable)]
                                   | _ \<Rightarrow> []) (c_M c))"

definition solve_Ksub :: "constraint \<Rightarrow> (constraint_system \<times> msg_subst) list" where
  "solve_Ksub c = concat (map (\<lambda>m. case m of PubKeyEncrypt (Variable x) u \<Rightarrow> let A = c_A c in
                                                                             let M = filter (\<lambda>m'. m \<noteq> m') (c_M c) in
                                                                             [([c_sapply (Variable(x := \<iota>)) ((PubKeyEncrypt (Variable x) u # M) | A \<rhd> (c_t c))], Variable(x := \<iota>))]
                                   | _ \<Rightarrow> []) (c_M c))"

definition solve_rer :: "constraint_system \<Rightarrow> (constraint_system \<times> msg_subst) list" where
  "solve_rer cs = (let single_res = List.maps (\<lambda>c. let unif = solve_Unif c in
                                                   let comp = solve_Comp c in
                                                   let proj = solve_Proj c in
                                                   let sdec = solve_Sdec c in
                                                   let adec = solve_Adec c in
                                                   let ksub = solve_Ksub c in
                                                   (unif @ comp @ proj @ sdec @ adec @ ksub)) cs in
                   let \<sigma>s = map (\<lambda>(_, \<sigma>). \<sigma>) single_res in
                   foldr (\<lambda>\<sigma> acc. map (\<lambda>(cs, \<sigma>'). (cs_sapply \<sigma> cs, \<sigma>')) acc) \<sigma>s single_res)"

subsection \<open>(b)\<close>

primrec map_until :: "((constraint_system \<times> msg_subst) \<Rightarrow> (constraint_system \<times> msg_subst) option) \<Rightarrow> 
  (constraint_system \<times> msg_subst) list \<Rightarrow> (constraint_system \<times> msg_subst) option" where
  "map_until f [] = None" 
| "map_until f (x # xs) = (let res = f x in 
                           if Option.is_none res then (map_until f xs)
                           else res)"

function search :: "constraint_system \<Rightarrow> (constraint_system \<times> msg_subst) option" where
  "search cs = (if is_simple_cs cs then Some(cs, Variable)
                else (let rer_res = solve_rer cs in 
                      map_until (\<lambda>(cs', \<sigma>). let res = search cs' in 
                                            if Option.is_none res then None
                                            else (let cs'' = fst(the res) in
                                            let \<tau> = snd(the res) in
                                            Some(cs'', \<tau> \<circ>m \<sigma>))) rer_res))"
  by pat_completeness auto
termination
  apply (relation "measures [\<eta>_1, \<eta>_2]")
  subgoal by simp
  subgoal sorry
  done

subsection \<open>(c)\<close>

value "map (\<lambda>(cs, \<sigma>). (cs, map (\<lambda>v. (v, \<sigma> v)) [''A0''])) (solve_Unif ([Variable ''A0''] | [] \<rhd> Constant ''a''))"
value "solve_Proj ([Pair (Variable ''A0'') (Variable ''B0'')] | [] \<rhd> Constant ''t'')"
value "solve_Sdec ([SymEncrypt (Variable ''K'') (Constant ''u'')] | [] \<rhd> Constant ''t'')"
value "solve_Adec ([PubKeyEncrypt \<iota> (Constant ''u'')] | [] \<rhd> Constant ''t'')"
value "map (\<lambda>(cs, \<sigma>). (cs, map (\<lambda>v. (v, \<sigma> v)) [''X''])) (solve_Ksub ([PubKeyEncrypt (Variable ''X'') (Constant ''u'')] | [] \<rhd> Constant ''t''))"
value "map (\<lambda>(cs, \<sigma>). (cs, map (\<lambda>v. (v, \<sigma> v)) [''A0'', ''B0'', ''K1'']))
       (solve_rer [[PubKeyEncrypt (Variable ''B0'') (Pair (Constant ''k0'') (Sig (Variable ''A0'') (Constant ''k0''))), Constant ''a'', Constant ''b'', \<iota>] | [] \<rhd> (PubKeyEncrypt (Constant ''b'') (Pair (Variable ''K1'') (Sig (Constant ''a'') (Variable ''K1''))))])"

value "map_option (\<lambda>(cs, \<sigma>). (cs, map (\<lambda>v. (v, \<sigma> v)) [''A0'', ''B0'', ''K1'', ''Z0''])) 
       (search [ [Constant ''a'', Constant ''b'', \<iota>] | [] \<rhd> (Pair (Variable ''A0'') (Variable ''B0'')), 
                 [PubKeyEncrypt (Variable ''B0'') (Pair (Constant ''k0'') (Sig (Variable ''A0'') (Constant ''k0''))), Constant ''a'', Constant ''b'', \<iota>] | [] \<rhd> (PubKeyEncrypt (Constant ''b'') (Pair (Variable ''K1'') (Sig (Constant ''a'') (Variable ''K1'')))),
                 [SymEncrypt (Variable ''K1'') (Constant ''m1''), PubKeyEncrypt (Variable ''B0'') (Pair (Constant ''k0'') (Sig (Variable ''A0'') (Constant ''k0''))), Constant ''a'', Constant ''b'', \<iota>] | [] \<rhd> (SymEncrypt (Constant ''k0'') (Variable ''Z0'')),
                 [SymEncrypt (Variable ''K1'') (Constant ''m1''), PubKeyEncrypt (Variable ''B0'') (Pair (Constant ''k0'') (Sig (Variable ''A0'') (Constant ''k0''))), Constant ''a'', Constant ''b'', \<iota>] | [] \<rhd> (Pair (Variable ''K1'') (Constant ''m1''))])"

value "map_option (\<lambda>(cs, \<sigma>). (cs, map (\<lambda>v. (v, \<sigma> v)) [''A0'', ''B0'', ''NA1'', ''NB0'']))
       (search [ [Constant ''a'', Constant ''b'', \<iota>] | [] \<rhd> (Pair (Variable ''A0'') (Variable ''B0'')), 
                 [PubKeyEncrypt (Variable ''B0'') (Pair (Constant ''na0'') (Variable ''A0'')),  Constant ''a'', Constant ''b'', \<iota>] | [] \<rhd> (PubKeyEncrypt (Constant ''b'') (Pair (Variable ''NA1'') (Constant ''a''))),
                 [PubKeyEncrypt (Constant ''a'') (Pair (Variable ''NA1'') (Constant ''nb1'')), PubKeyEncrypt (Variable ''B0'') (Pair (Constant ''na0'') (Variable ''A0'')),  Constant ''a'', Constant ''b'', \<iota>] | [] \<rhd> (PubKeyEncrypt (Variable ''A0'') (Pair (Constant ''na0'') (Variable ''NB0''))),
                 [PubKeyEncrypt (Variable ''B0'') (Variable ''NB0''), PubKeyEncrypt (Constant ''a'') (Pair (Variable ''NA1'') (Constant ''nb1'')), PubKeyEncrypt (Variable ''B0'') (Pair (Constant ''na0'') (Variable ''A0'')),  Constant ''a'', Constant ''b'', \<iota>] | [] \<rhd> (PubKeyEncrypt (Constant ''b'') (Constant ''nb1'')),
                 [PubKeyEncrypt (Variable ''B0'') (Variable ''NB0''), PubKeyEncrypt (Constant ''a'') (Pair (Variable ''NA1'') (Constant ''nb1'')), PubKeyEncrypt (Variable ''B0'') (Pair (Constant ''na0'') (Variable ''A0'')),  Constant ''a'', Constant ''b'', \<iota>] | [] \<rhd> (Pair (Variable ''NA1'') (Constant ''nb1''))])"

section \<open>Assignment 9\<close>

subsection \<open>(a)\<close>

lemma inv_Unif:
  assumes "c = (M | A \<rhd> t)"
    and "c \<leadsto>\<^sub>1[\<sigma>] []"
  shows "\<exists>u. \<not>(is_Variable t) \<and> u \<in> (set M) \<union> (set A) \<and> Some(\<sigma>) = msg_unify [(t, u)]"
  using assms(2,1)
proof(cases rule: rer1.cases)
  case (Unif t u M A)
  then show ?thesis
    using assms by auto
qed

lemma solve_Unif_sound: 
  assumes "c = (M | A \<rhd> t)"
    and "solve_Unif (c) = [([], \<sigma>)]"
  shows "c \<leadsto>\<^sub>1[\<sigma>] []"
  sorry

lemma solve_Comp_Hash_sound: 
  assumes "c = (M | A \<rhd> (Hash t))"
    and "\<sigma> = Variable"
    and "cs = [(M | A \<rhd> t)]"
    and "solve_Comp (c) = [(cs, \<sigma>)]"
  shows "c \<leadsto>\<^sub>1[\<sigma>] cs"
  using assms rer1.CompHash by simp

lemma solve_Comp_Pair_sound: 
  assumes "c = (M | A \<rhd> (Pair t1 t2))"
    and "\<sigma> = Variable"
    and "cs = [M | A \<rhd> t1, M | A \<rhd> t2]"
    and "solve_Comp (c) = [(cs, \<sigma>)]"
  shows "c \<leadsto>\<^sub>1[\<sigma>] cs"
  using assms rer1.CompPair by simp

lemma solve_Comp_SymEncrypt_sound: 
  assumes "c = (M | A \<rhd> (SymEncrypt k t))"
    and "\<sigma> = Variable"
    and "cs = [M | A \<rhd> k, M | A \<rhd> t]"
    and "solve_Comp (c) = [(cs, \<sigma>)]"
  shows "c \<leadsto>\<^sub>1[\<sigma>] cs"
  using assms rer1.CompSymEncrypt by simp

lemma solve_Comp_PubKeyEncrypt_sound: 
  assumes "c = (M | A \<rhd> (PubKeyEncrypt k t))"
    and "\<sigma> = Variable"
    and "cs = [M | A \<rhd> k, M | A \<rhd> t]"
    and "solve_Comp (c) = [(cs, \<sigma>)]"
  shows "c \<leadsto>\<^sub>1[\<sigma>] cs"
  using assms rer1.CompPubKeyEncrypt by simp

lemma solve_Comp_Sig_sound: 
  assumes "c = (M | A \<rhd> (Sig \<iota> t))"
    and "\<sigma> = Variable"
    and "cs = [M | A \<rhd> \<iota>, M | A \<rhd> t]"
    and "solve_Comp (c) = [(cs, \<sigma>)]"
  shows "c \<leadsto>\<^sub>1[\<sigma>] cs"
  using assms rer1.CompSig by simp

subsection \<open>(b)\<close>

lemma solve_Unif_comp: 
  assumes "c = (M | A \<rhd> t)"
    and "c \<leadsto>\<^sub>1[\<sigma>] []"
  shows "solve_Unif (c) = [([], \<sigma>)]"
  using inv_Unif[of c M A t \<sigma>] 
  unfolding solve_Unif_def
  apply (simp only: Let_def)
  sorry

lemma solve_Comp_Hash_comp: 
  assumes "c = (M | A \<rhd> (Hash t))"
    and "\<sigma> = Variable"
    and "cs = [(M | A \<rhd> t)]"
    and "c \<leadsto>\<^sub>1[\<sigma>] cs"
  shows "solve_Comp (c) = [(cs, \<sigma>)]"
  using assms by simp

lemma solve_Comp_Pair_comp: 
  assumes "c = (M | A \<rhd> (Pair t1 t2))"
    and "\<sigma> = Variable"
    and "cs = [M | A \<rhd> t1, M | A \<rhd> t2]"
    and "c \<leadsto>\<^sub>1[\<sigma>] cs"
  shows "solve_Comp (c) = [(cs, \<sigma>)]"
  using assms by simp

lemma solve_Comp_SymEncrypt_comp: 
  assumes "c = (M | A \<rhd> (SymEncrypt k t))"
    and "\<sigma> = Variable"
    and "cs = [M | A \<rhd> k, M | A \<rhd> t]"
    and "c \<leadsto>\<^sub>1[\<sigma>] cs"
  shows "solve_Comp (c) = [(cs, \<sigma>)]"
  using assms by simp

lemma solve_Comp_PubKeyEncrypt_comp: 
  assumes "c = (M | A \<rhd> (PubKeyEncrypt k t))"
    and "\<sigma> = Variable"
    and "cs = [M | A \<rhd> k, M | A \<rhd> t]"
    and "c \<leadsto>\<^sub>1[\<sigma>] cs"
  shows "solve_Comp (c) = [(cs, \<sigma>)]"
  using assms by simp

lemma solve_Comp_Sig_comp: 
  assumes "c = (M | A \<rhd> (Sig \<iota> t))"
    and "\<sigma> = Variable"
    and "cs = [M | A \<rhd> \<iota>, M | A \<rhd> t]"
    and "c \<leadsto>\<^sub>1[\<sigma>] cs"
  shows "solve_Comp (c) = [(cs, \<sigma>)]"
  using assms by simp

lemma solve_Proj_comp:
  assumes "c = ((M1 @ (Pair t1 t2) # M2) | A \<rhd> t)"
    and "\<sigma> = Variable"
    and "cs = [(M1 @ (t1 # t2 # M2)) | ((Pair t1 t2) # A) \<rhd> t]"
    and "c \<leadsto>\<^sub>1[\<sigma>] cs"
  shows "solve_Proj (c) = [(cs, \<sigma>)]"
  using assms
  unfolding solve_Proj_def
  apply (simp add: Let_def concat_def)
  sorry

lemma solve_Sdec_comp:
  assumes "c = (M1 @ (SymEncrypt k t) # M2) | A \<rhd> t"
    and "\<sigma> = Variable"
    and "cs = [(M1 @ (u # M2)) | ((SymEncrypt k t) # A) \<rhd> t, (M1 @ M2) | ((SymEncrypt k t) # A) \<rhd> k]"
    and "c \<leadsto>\<^sub>1[\<sigma>] cs"
  shows "solve_Sdec (c) = [(cs, \<sigma>)]"
  using assms
  unfolding solve_Sdec_def
  apply (simp add: Let_def concat_def)
  sorry

lemma solve_Adec_comp:
  assumes "c = (M1 @ (PubKeyEncrypt \<iota> u) # M2) | A \<rhd> t"
    and "\<sigma> = Variable"
    and "cs = [(M1 @ (u # M2)) | ((PubKeyEncrypt \<iota> u) # A) \<rhd> t]"
    and "c \<leadsto>\<^sub>1[\<sigma>] cs"
  shows "solve_Adec (c) = [(cs, \<sigma>)]"
  using assms
  unfolding solve_Adec_def
  apply (simp add: Let_def concat_def)
  sorry

lemma solve_Ksub_comp:
  assumes "c = (M1 @ (PubKeyEncrypt (Variable x) u) # M2) | A \<rhd> t"
    and "\<sigma> = Variable(x := \<iota>)"
    and "cs = [c_sapply (Variable(x := \<iota>)) ((M1 @ (PubKeyEncrypt (Variable x) u) # M2) | A \<rhd> t)]"
    and "c \<leadsto>\<^sub>1[\<sigma>] cs"
  shows "solve_Ksub (c) = [(cs, \<sigma>)]"
  using assms
  unfolding solve_Ksub_def
  apply (simp add: Let_def concat_def)
  sorry

end