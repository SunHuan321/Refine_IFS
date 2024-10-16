section \<open>Integrating the SIMP language into Picore\<close>

theory picore_SIMP
  imports "RG_Tran" "../PiCore/PiCore_Hoare"
begin

abbreviation ptranI :: "'Env \<Rightarrow> ('a conf \<times> 'a conf) set"
where "ptranI \<Gamma> \<equiv> ctran"

abbreviation petranI :: "'Env \<Rightarrow> 'a conf \<Rightarrow> 'a conf \<Rightarrow> bool"
where "petranI \<Gamma> \<equiv> etran'"

abbreviation cpts_pI :: "'Env \<Rightarrow> 'a confs set"
where "cpts_pI \<Gamma> \<equiv> cptn"

abbreviation cpts_of_pI :: "'Env \<Rightarrow> ('a com) option \<Rightarrow> 'a \<Rightarrow> ('a confs) set" where
  "cpts_of_pI \<Gamma> \<equiv> cp" 

lemma cpts_pI_ne_empty: "[] \<notin> cpts_pI \<Gamma>"
  using cptn.cases by blast

lemma petran_simpsI:
"petranI \<Gamma> (a, b) (c, d) \<Longrightarrow> a = c" 
  by(simp add: etran.simps)

lemma none_no_tranI': "((Q, s),(P,t)) \<in> ptranI \<Gamma> \<Longrightarrow> Q \<noteq> None"
  apply (simp) apply(rule ctran.cases)
  by simp+

lemma none_no_tranI: "((None, s),(P,t)) \<notin> ptranI \<Gamma>"
  using none_no_tranI' 
  by fast

lemma ptran_neqI: "((P, s),(P,t)) \<notin> ptranI \<Gamma>"
  by (simp)

interpretation event ptranI petranI None
  using petran_simpsI none_no_tranI ptran_neqI 
        event.intro[of petranI None ptranI] by auto

lemma cpts_p_simpsI:
  "((\<exists>P s. aa = [(P, s)]) \<or>
   (\<exists>P t xs s. aa = (P, s) # (P, t) # xs \<and> (P, t) # xs \<in> cpts_pI \<Gamma>) \<or>
   (\<exists>P s Q t xs. aa = (P, s) # (Q, t) # xs \<and> ptran' \<Gamma> (P, s) (Q, t) \<and> (Q, t) # xs \<in> cpts_pI \<Gamma>))
  \<Longrightarrow> (aa \<in> cpts_pI \<Gamma>)"
  apply(simp add: ptran'_def) using cptn.simps[of aa] by blast

(*lemma cpts_of_p_defI: "cpts_of_pI \<Gamma> P s \<equiv> {l. l!0=(P,s) \<and> l \<in> cpts_pI \<Gamma>}" 
  by(simp add:cpts_pI_def cpts_of_pI_def cpts_of_p_def)*)
lemma cpts_of_p_defI: "l!0=(P,s) \<and> l \<in> cpts_pI \<Gamma> \<Longrightarrow> l \<in> cpts_of_pI \<Gamma> P s" 
  by(simp add: cp_def)

interpretation event_comp ptranI petranI None cpts_pI cpts_of_pI
  using cpts_pI_ne_empty cpts_p_simpsI cpts_of_p_defI petran_simpsI none_no_tranI ptran_neqI 
        event_comp.intro[of ptranI petranI None cpts_pI cpts_of_pI] event.intro[of petranI None ptranI] 
        event_comp_axioms.intro[of cpts_pI ptranI cpts_of_pI]
  apply(simp add: ptran'_def) by blast





end