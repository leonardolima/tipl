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
  "solve_Proj c = concat (map (\<lambda>m. case m of Pair u v \<Rightarrow> let A = c_A c in
                                                         let M = filter (\<lambda>m'. m = m') (c_M c) in
                                                         [([(u # v # M) | (Pair u v # A) \<rhd> (c_t c)], Variable)]
                                   | _ \<Rightarrow> []) (c_M c))"

definition solve_Sdec :: "constraint \<Rightarrow> (constraint_system \<times> msg_subst) list" where
  "solve_Sdec c = concat (map (\<lambda>m. case m of SymEncrypt k u \<Rightarrow> let A = c_A c in
                                                               let M = filter (\<lambda>m'. m = m') (c_M c) in
                                                               [([(u # M) | (SymEncrypt k u # A) \<rhd> (c_t c), (c_M c) | (SymEncrypt k u # A) \<rhd> k], Variable)]
                                   | _ \<Rightarrow> []) (c_M c))"

definition solve_Adec :: "constraint \<Rightarrow> (constraint_system \<times> msg_subst) list" where
  "solve_Adec c = concat (map (\<lambda>m. case m of PubKeyEncrypt \<iota> u \<Rightarrow> let A = c_A c in
                                                                  let M = filter (\<lambda>m'. m = m') (c_M c) in
                                                                  [([(u # M) | (PubKeyEncrypt \<iota> u # A) \<rhd> (c_t c)], Variable)]
                                   | _ \<Rightarrow> []) (c_M c))"

definition solve_Ksub :: "constraint \<Rightarrow> (constraint_system \<times> msg_subst) list" where
  "solve_Ksub c = concat (map (\<lambda>m. case m of PubKeyEncrypt (Variable x) u \<Rightarrow> let A = c_A c in
                                                                             let M = filter (\<lambda>m'. m = m') (c_M c) in
                                                                             [([c_sapply (Variable(x := \<iota>)) ((PubKeyEncrypt (Variable x) u # M) | A \<rhd> (c_t c))], Variable)]
                                   | _ \<Rightarrow> []) (c_M c))"

definition solve_rer :: "constraint_system \<Rightarrow> (constraint_system \<times> msg_subst) list" where
  "solve_rer cs = concat (map (\<lambda>c. let unif = solve_Unif c in
                                   let comp = solve_Comp c in
                                   let proj = solve_Proj c in
                                   let sdec = solve_Sdec c in
                                   let adec = solve_Adec c in
                                   let ksub = solve_Ksub c in
                                   (unif @ comp @ proj @ sdec @ adec @ ksub)) cs)"

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
  sorry

subsection \<open>(c)\<close>

value "search [ [Constant ''a'', Constant ''b'', \<iota>] | [] \<rhd> (Pair (Variable ''A0'') (Variable ''B0'')), 
                [PubKeyEncrypt (Variable ''B0'') (Pair (Constant ''k0'') (Sig (Variable ''A0'') (Constant ''k0''))), Constant ''a'', Constant ''b'', \<iota>] | [] \<rhd> (PubKeyEncrypt (Constant ''b'') (Pair (Variable ''K1'') (Sig (Constant ''a'') (Variable ''K1'')))),
                [SymEncrypt (Variable ''K1'') (Constant ''m1''), PubKeyEncrypt (Variable ''B0'') (Pair (Constant ''k0'') (Sig (Variable ''A0'') (Constant ''k0''))), Constant ''a'', Constant ''b'', \<iota>] | [] \<rhd> (SymEncrypt (Constant ''k0'') (Variable ''Z0'')),
                [SymEncrypt (Variable ''K1'') (Constant ''m1''), PubKeyEncrypt (Variable ''B0'') (Pair (Constant ''k0'') (Sig (Variable ''A0'') (Constant ''k0''))), Constant ''a'', Constant ''b'', \<iota>] | [] \<rhd> (Pair (Variable ''K1'') (Constant ''m1''))]"

value "search [ [Constant ''a'', Constant ''b'', \<iota>] | [] \<rhd> (Pair (Variable ''A0'') (Variable ''B0'')), 
              [PubKeyEncrypt (Variable ''B0'') (Pair (Constant ''na0'') (Variable ''A0'')),  Constant ''a'', Constant ''b'', \<iota>] | [] \<rhd> (PubKeyEncrypt (Constant ''b'') (Pair (Variable ''NA1'') (Constant ''a''))),
              [PubKeyEncrypt (Constant ''a'') (Pair (Variable ''NA1'') (Constant ''nb1'')), PubKeyEncrypt (Variable ''B0'') (Pair (Constant ''na0'') (Variable ''A0'')),  Constant ''a'', Constant ''b'', \<iota>] | [] \<rhd> (PubKeyEncrypt (Variable ''A0'') (Pair (Constant ''na0'') (Variable ''NB0''))),
              [PubKeyEncrypt (Variable ''B0'') (Variable ''NB0''), PubKeyEncrypt (Constant ''a'') (Pair (Variable ''NA1'') (Constant ''nb1'')), PubKeyEncrypt (Variable ''B0'') (Pair (Constant ''na0'') (Variable ''A0'')),  Constant ''a'', Constant ''b'', \<iota>] | [] \<rhd> (PubKeyEncrypt (Constant ''b'') (Constant ''nb1'')),
              [PubKeyEncrypt (Variable ''B0'') (Variable ''NB0''), PubKeyEncrypt (Constant ''a'') (Pair (Variable ''NA1'') (Constant ''nb1'')), PubKeyEncrypt (Variable ''B0'') (Pair (Constant ''na0'') (Variable ''A0'')),  Constant ''a'', Constant ''b'', \<iota>] | [] \<rhd> (Pair (Variable ''NA1'') (Constant ''nb1''))]"

end