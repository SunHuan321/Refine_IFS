theory PiCore_IFS
  imports "PiCore/PiCore_Semantics" SecurityModel VHelper
begin

record ('l,'k,'s,'prog,'d) action = 
        actk :: "('l,'k,'s,'prog) actk"
        eventof :: "('l,'k,'s, 'prog) event"
        domain ::  "'d"

locale InfoFlow = event ptran petran fin_com
  for ptran :: "'Env \<Rightarrow> (('s,'prog) pconf \<times> ('s,'prog) pconf) set" 
  and petran :: "'Env \<Rightarrow> ('s,'prog) pconf \<Rightarrow> ('s,'prog) pconf \<Rightarrow> bool"  ("_ \<turnstile> _ -pe\<rightarrow> _" [81,81,81] 80) 
  and fin_com :: "'prog"
  +
  fixes \<Gamma> :: "'Env"
    and C0 ::  "('l,'k,'s, 'prog) pesconf"
    and step :: "('l,'k,'s, 'prog, 'd) action \<Rightarrow> (('l,'k,'s, 'prog) pesconf \<times> ('l,'k,'s, 'prog) pesconf) set"
    and interference :: "'d \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<leadsto> _)" [70,71] 60)
    and vpeq ::  "'s \<Rightarrow> 'd \<Rightarrow> 's \<Rightarrow> bool" ("(_ \<sim>_\<sim> _)" [70,69,70] 60)
    and obs ::  "'s \<Rightarrow> 'd \<Rightarrow> 'o" (infixl "\<guillemotright>"  55)
    and dome :: "'s  \<Rightarrow> ('l,'k,'s, 'prog) event \<Rightarrow> 'd"
  assumes vpeq_transitive : "\<forall> a b c u. (a \<sim> u \<sim> b) \<and> (b \<sim> u \<sim> c) \<longrightarrow> (a \<sim> u \<sim> c)"
    and   vpeq_symmetric : "\<forall> a b u. (a \<sim> u \<sim> b) \<longrightarrow> (b \<sim> u \<sim> a)"
    and   vpeq_reflexive : "\<forall> a u. (a \<sim> u \<sim> a)"
    and   step_def : "step a \<equiv> {(P, Q). (\<Gamma> \<turnstile> P -pes-(actk a)\<rightarrow> Q) \<and> 
                                ((\<exists>e k. actk a = ((EvtEnt e)\<sharp>k) \<and> eventof a = e 
                                  \<and> dome (gets P)  e = domain a) \<or>
                                  (\<exists>c k. actk a = ((Cmd c)\<sharp>k) \<and> eventof a = (getx P) k 
                                  \<and> dome (gets P) (eventof a) = domain a))}"
    (*and   step_def : "step a \<equiv> {(P,Q). (P -pes-(actk a)\<rightarrow> Q) \<and> (*domc dome P (actk a)*) 
                                dom_helper dome (gets P) (getx P) (Act (actk a)) (K (actk a)) = domain a}"*)
begin

definition vpeqC :: "('l,'k,'s, 'prog) pesconf \<Rightarrow> 'd \<Rightarrow> ('l,'k,'s, 'prog) pesconf \<Rightarrow> bool" ("(_ \<sim>._.\<sim> _)" [70,71] 60)
   where "vpeqC C1 u C2 \<equiv> (gets C1) \<sim>u\<sim> (gets C2)"

lemma vpeqC_transitive: "\<forall> a b c u. (a \<sim>.u.\<sim> b) \<and> (b \<sim>.u.\<sim> c) \<longrightarrow> (a \<sim>.u.\<sim> c)"
  using vpeq_transitive vpeqC_def by blast

lemma vpeqC_symmetric: "\<forall> a b u. (a \<sim>.u.\<sim> b) \<longrightarrow> (b \<sim>.u.\<sim> a)"
  using vpeq_symmetric vpeqC_def by blast

lemma vpeqC_reflexive: "\<forall> a u. (a \<sim>.u.\<sim> a)"
  by (simp add: vpeq_reflexive vpeqC_def)

definition obsC :: " ('l,'k,'s,'prog) pesconf \<Rightarrow> 'd \<Rightarrow> 'o" (infixl "\<guillemotright>."  55)
  where "C \<guillemotright>. d= (gets C) \<guillemotright> d"

interpretation SM_IFS C0 step domain obsC vpeqC interference
  using SM_IFS_def vpeqC_reflexive vpeqC_symmetric vpeqC_transitive by blast

definition nextC :: "('l,'k,'s,'prog) pesconf \<Rightarrow> ('l,'k,'s,'prog,'d) action \<Rightarrow>  ('l,'k,'s,'prog) pesconf set" where
  "nextC P a \<equiv> {Q. (P,Q)\<in>step a}"
      
primrec runC :: "('l,'k,'s,'prog,'d) action list \<Rightarrow> (('l,'k,'s,'prog) pesconf \<times> ('l,'k,'s,'prog) pesconf) set" where
  run_Nil:  "runC [] = Id " |
  run_Cons: "runC (a#as) = {(P,Q). (\<exists>R. (P,R) \<in> step a \<and> (R,Q) \<in> runC as)}"

definition reachablec :: "('l,'k,'s,'prog) pesconf \<Rightarrow> ('l,'k,'s,'prog) pesconf \<Rightarrow> bool" ("(_ \<hookrightarrow> _)" [70,71] 60) where
  "reachablec C1 C2 \<equiv>  (\<exists>as. (C1,C2) \<in> runC as)"

definition reachablec0 :: "('l,'k,'s,'prog) pesconf \<Rightarrow> bool"  where
  "reachablec0 C \<equiv> reachablec C0 C"

lemma run_equiv : "runC as = run as"
  apply (induct as, simp)
  by (simp add: relcomp_unfold)

lemma reachablec_equiv : "reachablec C1 C2 = reachable C1 C2"
  by (simp add: reachable_def reachablec_def run_equiv)

lemma reachable0_equiv : "reachablec0 C = reachable0  C"
  by (simp add: reachable0_def reachablec0_def reachablec_equiv)

subsection \<open>Unwinding Conditions\<close>

definition observed_consistentC :: "bool" where
 "observed_consistentC \<equiv> (\<forall> s t u. ((s \<sim> u \<sim> t) \<longrightarrow> s \<guillemotright> u  = t \<guillemotright> u))"

definition local_respectC :: "bool" where
  "local_respectC \<equiv> \<forall>a u C. (reachablec0 C) \<longrightarrow> ((domain a) \<setminus>\<leadsto> u) \<longrightarrow> 
                              (\<forall> C'. (C'\<in>nextC C a) \<longrightarrow> (C \<sim>.u.\<sim> C'))"


definition weak_step_consistentC :: "bool" where
  "weak_step_consistentC \<equiv> \<forall>a u C1 C2. (reachablec0 C1) \<and> (reachablec0 C2) \<longrightarrow>  (C1 \<sim>.u.\<sim> C2) 
                         \<and> ( ((domain a) \<leadsto> u) \<longrightarrow> (C1 \<sim>.(domain a).\<sim> C2) ) \<longrightarrow> 
                         (\<forall> C1' C2'. (C1'\<in>nextC C1 a) \<and> (C2'\<in>nextC C2 a) \<longrightarrow> (C1' \<sim>.u.\<sim> C2'))"

lemma PiCore_obs_consistent : "observed_consistentC \<Longrightarrow> observed_consistent "
  by (simp add: obsC_def observed_consistentC_def observed_consistent_def vpeqC_def)

lemma local_respectC_equiv : "local_respectC \<longleftrightarrow> local_respect"
proof
  assume  "local_respectC"
  then show "local_respect"
    apply (simp add: local_respectC_def local_respect_def, clarify)
    apply (drule_tac a = a and b = d and c = aa and d = ab and e = b in all5_imp2D)
      apply (simp add: reachable0_equiv)
     apply (simp add:  noninterf_def)
    by (simp add:  nextC_def)
next
  assume "local_respect"
  then show "local_respectC"
    apply (simp add: local_respectC_def local_respect_def, clarify)
    apply (drule_tac a = a and b = u and c = aa and d = ab and e = b in all5_impD)
    using reachable0_equiv apply auto[1]
    by (simp add: nextC_def noninterf_def)
qed

lemma weak_step_consistentC_equiv : "weak_step_consistentC \<longleftrightarrow> weak_step_consistent"
proof
  assume "weak_step_consistentC"
  then show "weak_step_consistent"
    apply (simp add: weak_step_consistentC_def weak_step_consistent_def, clarify)
    apply (drule_tac a= a and b = d and c = aa and d = ab in all4D)
    apply (drule_tac a = b and b = ac and c = ad and d = ba in all4_imp2D)
    using reachable0_equiv apply presburger
    apply force
    by (simp add:  nextC_def)
next
  assume "weak_step_consistent "
  then show "weak_step_consistentC"
    apply (simp add: weak_step_consistentC_def weak_step_consistent_def, clarify)
    apply (drule_tac a= a and b = u and c = aa and d = ab in all4D)
    apply (drule_tac a = b and b = ac and c = ad and d = ba in all4_imp2D)
    using reachable0_equiv apply blast
    apply force
    using nextC_def by force
qed


subsection \<open>Unwinding Theorem\<close>

theorem PiCore_nonleakage:
    assumes p1: observed_consistentC
    and     p2: weak_step_consistentC 
  shows "nonleakage"
  using PiCore_obs_consistent UnwindingTheorem_nonleakage p1 p2 weak_step_consistentC_equiv by blast

theorem PiCore_noninfluence0:
    assumes p1: observed_consistentC
    and     p2: local_respectC
    and     p3: weak_step_consistentC
  shows "noninfluence0"
  using PiCore_obs_consistent UnwindingTheorem_noninfluence0 local_respectC_equiv p1 p2 p3 weak_step_consistentC_equiv by fastforce

end
end
