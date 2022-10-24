theory Execute
  imports Main Unification Term Deduction
begin

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
| "solve_Comp _ = undefined"

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

function search :: "constraint_system \<Rightarrow> (constraint_system \<times> msg_subst) option" where
  "search cs = (let rer_res = solve_rer cs in None)"
  by pat_completeness auto
termination
  sorry

end