theory PiCore_Anno_SIMP
  imports Anno_SIMP_Hoare_Plus "../PiCore/PiCore_Hoare"
begin

abbreviation ptranI :: "'Env \<Rightarrow> ('s conf \<times> 's conf) set"
where "ptranI \<Gamma> \<equiv> ptran"

abbreviation petranI :: "'Env \<Rightarrow> 's conf \<Rightarrow> 's conf \<Rightarrow> bool"
where "petranI \<Gamma> \<equiv> petran'"

abbreviation cpts_pI :: "'Env \<Rightarrow> 's confs set"
where "cpts_pI \<Gamma> \<equiv> cpts_p"

abbreviation cpts_of_pI :: "'Env \<Rightarrow> ('s ann_prog) option \<Rightarrow> 's \<Rightarrow> ('s confs) set" where
  "cpts_of_pI \<Gamma> \<equiv> cpts_of_p" 

abbreviation prog_validityI :: "'Env \<Rightarrow> ('s ann_prog) option \<Rightarrow> 's set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> 's set \<Rightarrow> bool"
where "prog_validityI \<Gamma> P \<equiv> prog_validity P"

abbreviation assume_pI :: "'Env \<Rightarrow> ('s set \<times> ('s \<times> 's) set) \<Rightarrow> ('s confs) set" 
where "assume_pI \<Gamma> \<equiv> assume_p"

abbreviation commit_pI :: "'Env \<Rightarrow> (('s \<times> 's) set \<times> 's set) \<Rightarrow> ('s confs) set" 
  where "commit_pI \<Gamma> \<equiv> commit_p"

abbreviation rghoare_pI :: "'Env \<Rightarrow> [('s ann_prog) option, 's set, ('s \<times> 's) set, ('s \<times> 's) set, 's set] \<Rightarrow> bool"
("_ \<turnstile>\<^sub>I _ sat\<^sub>p [_, _, _, _]" [60,0,0,0,0] 45)
where "rghoare_pI \<Gamma> \<equiv> rghoare_p"

lemma cpts_pI_ne_empty: "[] \<notin> cpts_pI \<Gamma>"
  by (simp)

lemma petran_simpsI:
"petranI \<Gamma> (a, b) (c, d) \<Longrightarrow> a = c" 
  by(simp add: petran.simps)

lemma none_no_tranI': "((Q, s),(P,t)) \<in> ptranI \<Gamma> \<Longrightarrow> Q \<noteq> None"
  apply (simp) apply(rule ptran.cases)
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
  apply(simp add: ptran'_def) 
  by (meson cpts_p.CptsPComp cpts_p.CptsPEnv cpts_p.CptsPOne)

(*lemma cpts_of_p_defI: "cpts_of_pI \<Gamma> P s \<equiv> {l. l!0=(P,s) \<and> l \<in> cpts_pI \<Gamma>}" 
  by(simp add:cpts_pI_def cpts_of_pI_def cpts_of_p_def)*)
lemma cpts_of_p_defI: "l!0=(P,s) \<and> l \<in> cpts_pI \<Gamma> \<Longrightarrow> l \<in> cpts_of_pI \<Gamma> P s" 
  by(simp add: cpts_of_p_def)

interpretation event_comp ptranI petranI None cpts_pI cpts_of_pI
  using cpts_pI_ne_empty cpts_p_simpsI cpts_of_p_defI petran_simpsI none_no_tranI ptran_neqI 
        event_comp.intro[of ptranI petranI None cpts_pI cpts_of_pI] event.intro[of petranI None ptranI] 
        event_comp_axioms.intro[of cpts_pI ptranI cpts_of_pI]
  apply(simp add: ptran'_def) by blast

lemma prog_validity_defI: "prog_validityI \<Gamma> P pre rely guar post \<Longrightarrow> 
   \<forall>s. cpts_of_pI \<Gamma> P s \<inter> assume_pI \<Gamma> (pre, rely) \<subseteq> commit_pI \<Gamma> (guar, post) \<inter> preserves_p"
  by (simp add: prog_validity_def)

lemma assume_p_defI: "snd (c!0) \<in> pre \<and> (\<forall>i. Suc i<length c \<longrightarrow> 
               petranI \<Gamma> (c!i) (c!(Suc i)) \<longrightarrow> (snd (c!i), snd (c!Suc i))\<in> rely) \<Longrightarrow> c\<in> assume_pI \<Gamma> (pre, rely)"
  by (simp add: assume_p_def PiCore_Semantics.gets_p_def Anno_SIMP_Tran.gets_p_def)

lemma commit_p_defI: "c \<in> commit_pI \<Gamma> (guar, post) \<Longrightarrow> (\<forall>i. Suc i<length c \<longrightarrow> 
               (c!i,c!(Suc i)) \<in> ptranI \<Gamma>  \<longrightarrow> (snd (c!i), snd (c!Suc i)) \<in> guar) \<and>
               (fst (last c) = None \<longrightarrow> snd (last c) \<in> post)"
  apply (simp add: commit_p_def PiCore_Semantics.getspc_p_def PiCore_Semantics.gets_p_def)
  by (simp add: Anno_SIMP_Tran.gets_p_def Anno_SIMP_Tran.getspc_p_def)

lemma rgsound_pI: "rghoare_pI \<Gamma> P pre rely guar post \<Longrightarrow> prog_validityI \<Gamma> P pre rely guar post"
  using rgsound_p by blast

print_locale event_hoare

interpretation event_hoare ptranI petranI None cpts_pI cpts_of_pI prog_validityI ann_preserves_p 
                           assume_pI commit_pI preserves_p rghoare_pI
proof
  show "\<And>\<Gamma> P pre rely guar post. \<Turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post] \<Longrightarrow> 
        \<forall>s. cpts_of_p P s \<inter> assume_p (pre, rely) \<subseteq> commit_p (guar, post) \<inter> preserves_p"
    by (simp add: Anno_SIMP_Hoare_Plus.prog_validity_def)
  show "\<And>c pre \<Gamma> rely. PiCore_Semantics.gets_p (c ! 0) \<in> pre \<and> (\<forall>i. Suc i < length c \<longrightarrow> 
         c ! i -pe\<rightarrow> c ! Suc i \<longrightarrow> (PiCore_Semantics.gets_p (c ! i), PiCore_Semantics.gets_p (c ! Suc i)) \<in> rely) \<Longrightarrow>
       c \<in> assume_p (pre, rely)"
    by (simp add: PiCore_Semantics.gets_p_def assume_p_defI)
  show "\<And>c \<Gamma> guar post. c \<in> commit_p (guar, post) \<Longrightarrow> (\<forall>i. Suc i < length c \<longrightarrow> 
        PiCore_Anno_SIMP.ptran' \<Gamma> (c ! i) (c ! Suc i) \<longrightarrow> (PiCore_Semantics.gets_p (c ! i), 
        PiCore_Semantics.gets_p (c ! Suc i)) \<in> guar) \<and>
       (PiCore_Semantics.getspc_p (last c) = None \<longrightarrow> PiCore_Semantics.gets_p (last c) \<in> post)"
    by (simp add: PiCore_Semantics.gets_p_def PiCore_Semantics.getspc_p_def commit_p_defI ptran'_def)
  show "\<And>c. c \<in> preserves_p \<Longrightarrow> \<forall>i<length c. ann_preserves_p (PiCore_Semantics.getspc_p (c ! i)) (PiCore_Semantics.gets_p (c ! i))"
    by (simp add: Anno_SIMP_Tran.gets_p_def Anno_SIMP_Tran.getspc_p_def PiCore_Semantics.gets_p_def 
        PiCore_Semantics.getspc_p_def preserves_p_def)
  show "\<And>s. ann_preserves_p None s = True" by simp
  show "\<And>\<Gamma> P pre rely guar post. \<turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post] \<longrightarrow> \<Turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post] "
    by (simp add: Anno_SIMP_Hoare_Plus.rgsound_p)
qed


abbreviation simp_rghoare_e :: "'Env \<Rightarrow> ('l, 'k, 's, 's ann_prog option) event \<Rightarrow> 's set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> 's set \<Rightarrow> bool" 
("_ \<turnstile> _ sat\<^sub>e [_, _, _, _]" [60,60,0,0,0,0] 45)
  where "simp_rghoare_e \<equiv> rghoare_e"

abbreviation simp_rghoare_es :: "'Env \<Rightarrow> ('l, 'k, 's, 's ann_prog option) rgformula_ess \<Rightarrow> 's set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> 's set \<Rightarrow> bool" 
("_ \<turnstile> _ sat\<^sub>s [_, _, _, _]" [60,60,0,0,0,0] 45)
where "simp_rghoare_es \<equiv> rghoare_es"

abbreviation simp_pestran :: "'Env \<Rightarrow> ('l,'k,'s, 's ann_prog option) pesconf \<Rightarrow> ('l,'k,'s,'s ann_prog option ) actk 
                            \<Rightarrow> ('l,'k,'s,'s ann_prog option) pesconf \<Rightarrow> bool"  ("_ \<turnstile> _ -pes-_\<rightarrow> _" [70,70] 60)
  where "simp_pestran \<equiv> pestran"

thm ptran_def
end




