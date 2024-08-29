theory PiCore_Sim
  imports PiCore_Refine
begin


definition related_transitions:: "('s\<^sub>c \<times> 's\<^sub>c) set \<Rightarrow> ('s\<^sub>a \<times> 's\<^sub>a) set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>a) set \<Rightarrow> 
                                  (('s\<^sub>c \<times> 's\<^sub>c) \<times> ('s\<^sub>a \<times> 's\<^sub>a)) set" ("'(_, _')\<^sub>_" )
  where "related_transitions R R' \<alpha> = {((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')). (\<sigma>,\<sigma>')\<in> R \<and> (\<Sigma>,\<Sigma>')\<in>R' 
                                      \<and>(\<sigma>, \<Sigma>) \<in> \<alpha> \<and> (\<sigma>', \<Sigma>') \<in> \<alpha>}"

definition Stable :: "('s\<^sub>c \<times> 's\<^sub>a) set \<Rightarrow> (('s\<^sub>c \<times> 's\<^sub>c) \<times> ('s\<^sub>a \<times> 's\<^sub>a)) set \<Rightarrow> bool" 
  where "Stable \<zeta> \<Delta> = (\<forall>\<sigma> \<sigma>' \<Sigma> \<Sigma>'. (\<sigma>, \<Sigma>) \<in> \<zeta> \<longrightarrow> ((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')) \<in> \<Delta> \<longrightarrow> (\<sigma>', \<Sigma>') \<in> \<zeta> )"

definition rel_guard_eq :: "'s\<^sub>c set \<Rightarrow> 's\<^sub>a set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>a) set" ("_ \<rightleftharpoons>\<^sub>r _" [70, 70] 60)
  where "rel_guard_eq g\<^sub>c g\<^sub>a = {(\<sigma>, \<Sigma>). (\<sigma> \<in> g\<^sub>c) = (\<Sigma> \<in> g\<^sub>a)}"

definition rel_guard_and :: "'s\<^sub>c set \<Rightarrow> 's\<^sub>a set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>a) set" ("_\<and>\<^sub>r_" [70, 70] 60) 
  where "rel_guard_and g\<^sub>c g\<^sub>a = {(\<sigma>, \<Sigma>). \<sigma> \<in> g\<^sub>c \<and> \<Sigma> \<in> g\<^sub>a}"

locale PiCore_Sim =
  Event\<^sub>c: event ptran\<^sub>c petran\<^sub>c fin_com\<^sub>c +
  Event\<^sub>a: event ptran\<^sub>a petran\<^sub>a fin_com\<^sub>a
  for ptran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> (('prog\<^sub>c \<times> 's\<^sub>c) \<times> 'prog\<^sub>c \<times> 's\<^sub>c) set" 
  and petran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> 'prog\<^sub>c \<times> 's\<^sub>c \<Rightarrow> 'prog\<^sub>c \<times> 's\<^sub>c \<Rightarrow> bool" 
  and fin_com\<^sub>c :: "'prog\<^sub>c"
  and ptran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> (('prog\<^sub>a \<times> 's\<^sub>a) \<times> 'prog\<^sub>a \<times> 's\<^sub>a) set"
  and petran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> 'prog\<^sub>a \<times> 's\<^sub>a \<Rightarrow> 'prog\<^sub>a \<times> 's\<^sub>a \<Rightarrow> bool" 
  and fin_com\<^sub>a :: "'prog\<^sub>a" +
fixes
      prog_sim :: "['Env\<^sub>c, ('s\<^sub>c,'prog\<^sub>c) pconf, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
                  ('s\<^sub>c \<times> 's\<^sub>a) set, 'prog\<^sub>c \<Rightarrow> 'prog\<^sub>a option, ('s\<^sub>c \<times> 's\<^sub>a) set,
                  'Env\<^sub>a, ('s\<^sub>a,'prog\<^sub>a) pconf, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool" 
  ("'(_,_,_,_')/ \<preceq>\<^sub>p \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>') /'(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81] 100)
  and prog_sim_pre :: "['Env\<^sub>c, 'prog\<^sub>c, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
                  ('s\<^sub>c \<times> 's\<^sub>a) set, 'prog\<^sub>c \<Rightarrow> 'prog\<^sub>a option, ('s\<^sub>c \<times> 's\<^sub>a) set, ('s\<^sub>c \<times> 's\<^sub>a) set,
                  'Env\<^sub>a, 'prog\<^sub>a, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool" 
  ("'(_,_,_,_')/ \<preceq>\<^sub>p \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>\<rhd>\<^sub>_\<^sub>')  /'(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81,81] 100)
assumes
  prog_sim_validity: "(\<Gamma>\<^sub>c, (P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a) \<Longrightarrow>
                            (s\<^sub>c, s\<^sub>a) \<in> \<alpha> \<and>

                            (\<forall>P\<^sub>c' s\<^sub>c'. ((P\<^sub>c, s\<^sub>c), (P\<^sub>c', s\<^sub>c')) \<in> ptran\<^sub>c \<Gamma>\<^sub>c \<and> \<zeta> P\<^sub>c = None \<longrightarrow> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> 
                            (\<Gamma>\<^sub>c, (P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)) \<and>

                            (\<forall>P\<^sub>c' s\<^sub>c'. ((P\<^sub>c, s\<^sub>c), (P\<^sub>c', s\<^sub>c')) \<in> ptran\<^sub>c \<Gamma>\<^sub>c \<and> \<zeta> P\<^sub>c \<noteq> None \<longrightarrow> 
                            (\<zeta> P\<^sub>c = Some P\<^sub>a \<and> (\<exists>P\<^sub>a' s\<^sub>a'. 
                            ((P\<^sub>a, s\<^sub>a), (P\<^sub>a', s\<^sub>a')) \<in> ptran\<^sub>a \<Gamma>\<^sub>a \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and>
                            (\<Gamma>\<^sub>c, (P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a', s\<^sub>a'), R\<^sub>a, G\<^sub>a)))) \<and>
                      
                            (P\<^sub>c = fin_com\<^sub>c \<longrightarrow> P\<^sub>a = fin_com\<^sub>a \<and> (s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<and> \<gamma> \<subseteq> \<alpha>) \<and> 

                            (\<forall>s\<^sub>c' s\<^sub>a'. ((s\<^sub>c, s\<^sub>c'), (s\<^sub>a, s\<^sub>a')) \<in> ((R\<^sub>c, R\<^sub>a \<union> Id)\<^sub>\<alpha>) \<longrightarrow> 
                            (\<Gamma>\<^sub>c, (P\<^sub>c, s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a'), R\<^sub>a, G\<^sub>a))" and
  prog_sim_pre_validity: " \<lbrakk>(\<Gamma>\<^sub>c, P\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>)  (\<Gamma>\<^sub>a, P\<^sub>a, R\<^sub>a, G\<^sub>a); (s\<^sub>c, s\<^sub>a) \<in> \<xi>\<rbrakk> \<Longrightarrow>  
                           (\<Gamma>\<^sub>c, (P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)"
begin


lemma prog_sim_pre_implies_inv : "(\<Gamma>\<^sub>c,P\<^sub>c,R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>)  (\<Gamma>\<^sub>a,P\<^sub>a,R\<^sub>a,G\<^sub>a) \<Longrightarrow> \<xi> \<subseteq> \<alpha>"
  by (meson prog_sim_pre_validity prog_sim_validity subrelI)

abbreviation ptran\<^sub>c' :: "'Env\<^sub>c \<Rightarrow> ('s\<^sub>c,'prog\<^sub>c) pconf \<Rightarrow> ('s\<^sub>c,'prog\<^sub>c) pconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ -c\<rightarrow> _" [81,81] 80)
  where "ptran\<^sub>c' \<equiv> Event\<^sub>c.ptran'"

abbreviation ptrans\<^sub>c :: "'Env\<^sub>c \<Rightarrow> ('s\<^sub>c,'prog\<^sub>c) pconf \<Rightarrow> ('s\<^sub>c,'prog\<^sub>c) pconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ c*\<rightarrow> _" [81,81] 80)
  where "ptrans\<^sub>c \<equiv>  Event\<^sub>c.ptrans"

abbreviation etran\<^sub>c ::  "'Env\<^sub>c \<Rightarrow> ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) econf \<Rightarrow> ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) actk \<Rightarrow> 
                        ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) econf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ -et-_\<rightarrow> _" [81,81,81] 80)
  where "etran\<^sub>c \<equiv>  Event\<^sub>c.etran"


abbreviation estran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) esconf \<Rightarrow> ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) actk \<Rightarrow> 
                        ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) esconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ -es-_\<rightarrow> _" [81,81] 80)
  where "estran\<^sub>c \<equiv>  Event\<^sub>c.estran"

abbreviation pestran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) pesconf \<Rightarrow> ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) actk \<Rightarrow> 
                        ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) pesconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ -pes-_\<rightarrow> _" [70,70] 60)
  where "pestran\<^sub>c \<equiv>  Event\<^sub>c.pestran"


abbreviation ptran\<^sub>a' :: "'Env\<^sub>a \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ -c\<rightarrow> _" [81,81] 80)
  where "ptran\<^sub>a' \<equiv>  Event\<^sub>a.ptran'"

abbreviation ptrans\<^sub>a :: "'Env\<^sub>a \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ c*\<rightarrow> _" [81,81] 80)
  where "ptrans\<^sub>a \<equiv> Event\<^sub>a.ptrans"

abbreviation etran\<^sub>a ::  "'Env\<^sub>a \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) econf \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) actk \<Rightarrow> 
                        ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) econf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ -et-_\<rightarrow> _" [81,81,81] 80)
  where "etran\<^sub>a \<equiv> Event\<^sub>a.etran"


abbreviation estran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) esconf \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) actk \<Rightarrow> 
                        ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) esconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ -es-_\<rightarrow> _" [81,81] 80)
  where "estran\<^sub>a \<equiv> Event\<^sub>a.estran"

abbreviation pestran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) pesconf \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) actk \<Rightarrow> 
                        ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) pesconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ -pes-_\<rightarrow> _" [70,70] 60)
  where "pestran\<^sub>a \<equiv> Event\<^sub>a.pestran"

coinductive e_sim :: "['Env\<^sub>c, ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) econf, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
                  ('s\<^sub>c \<times> 's\<^sub>a) set, 'prog\<^sub>c \<Rightarrow> 'prog\<^sub>a option, ('s\<^sub>c \<times> 's\<^sub>a) set,
                  'Env\<^sub>a, ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) econf, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool" 
  ("'(_,_,_,_')/ \<preceq>\<^sub>e \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>') /'(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81] 100)
  where rgsim : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<alpha>; 
                  
                  (\<forall>ec e\<^sub>c' x\<^sub>c' k. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-((EvtEnt ec)\<sharp>k)\<rightarrow> (e\<^sub>c', s\<^sub>c, x\<^sub>c')) \<longrightarrow> (\<exists>ea e\<^sub>a' x\<^sub>a'.
                   (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) -et-((EvtEnt ea)\<sharp>k)\<rightarrow> (e\<^sub>a', s\<^sub>a, x\<^sub>a')) \<and>
                   (\<Gamma>\<^sub>c, (e\<^sub>c', s\<^sub>c, x\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a', s\<^sub>a, x\<^sub>a'), R\<^sub>a, G\<^sub>a))) ;

                   (\<forall>Pc e\<^sub>c' s\<^sub>c' k. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-((Cmd Pc)\<sharp>k)\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c)) \<and> \<zeta> Pc = None \<longrightarrow> 
                   (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (\<Gamma>\<^sub>c, (e\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)) ;

                  (\<forall>Pc e\<^sub>c' s\<^sub>c' k Pa. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-((Cmd Pc)\<sharp>k)\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c)) \<and> \<zeta> Pc = Some Pa \<longrightarrow> 
                   (\<exists>e\<^sub>a' s\<^sub>a'. 
                   (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) -et-((Cmd Pa)\<sharp>k)\<rightarrow> (e\<^sub>a', s\<^sub>a', x\<^sub>a)) \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> 
                   (\<Gamma>\<^sub>c, (e\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a', s\<^sub>a', x\<^sub>a), R\<^sub>a, G\<^sub>a))) ;


                   (e\<^sub>c = AnonyEvent fin_com\<^sub>c \<longrightarrow> e\<^sub>a = AnonyEvent fin_com\<^sub>a \<and> (s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<and> \<gamma> \<subseteq> \<alpha>) ; 

                   (\<forall>s\<^sub>c' s\<^sub>a'. ((s\<^sub>c, s\<^sub>c'), (s\<^sub>a, s\<^sub>a')) \<in> ((R\<^sub>c, R\<^sub>a \<union> Id)\<^sub>\<alpha>) \<longrightarrow> 
                     (\<Gamma>\<^sub>c, (e\<^sub>c, s\<^sub>c', x\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a, s\<^sub>a', x\<^sub>a'), R\<^sub>a, G\<^sub>a))      
                  \<rbrakk> \<Longrightarrow> (\<Gamma>\<^sub>c, (e\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)"

definition e_sim_pre :: "['Env\<^sub>c, ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) event, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
                  ('s\<^sub>c \<times> 's\<^sub>a) set, 'prog\<^sub>c \<Rightarrow> 'prog\<^sub>a option, ('s\<^sub>c \<times> 's\<^sub>a) set, ('s\<^sub>c \<times> 's\<^sub>a) set,
                  'Env\<^sub>a, ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) event, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool" 
  ("'(_,_,_,_')/ \<preceq>\<^sub>e \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>\<rhd>\<^sub>_\<^sub>') /'(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81] 100)
  where "(\<Gamma>\<^sub>c, e\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>)  (\<Gamma>\<^sub>a, e\<^sub>a, R\<^sub>a, G\<^sub>a) = (\<forall>s\<^sub>c s\<^sub>a x\<^sub>c x\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<longrightarrow> 
         (\<Gamma>\<^sub>c, (e\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a))"

lemma e_sim_init :"(\<Gamma>\<^sub>c,(e\<^sub>c, s\<^sub>c, x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(e\<^sub>a, s\<^sub>a, x\<^sub>a),R\<^sub>a,G\<^sub>a) \<Longrightarrow> (s\<^sub>c, s\<^sub>a) \<in> \<alpha>"
  by (erule e_sim.cases, simp_all)

lemma e_sim_pre_implies_inv : "(\<Gamma>\<^sub>c, e\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>)  (\<Gamma>\<^sub>a, e\<^sub>a, R\<^sub>a, G\<^sub>a) \<Longrightarrow> \<xi> \<subseteq> \<alpha>"
  by (meson e_sim_pre_def PiCore_Sim_axioms e_sim_init subrelI)

lemma AnonyEvt_Sound_help1: "\<lbrakk>(\<Gamma>\<^sub>c,(P\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(P\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a); 
      \<Gamma>\<^sub>c \<turnstile>\<^sub>c (AnonyEvent P\<^sub>c, s\<^sub>c, x\<^sub>c) -et-Cmd Pc\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c); \<zeta> Pc = None\<rbrakk> 
      \<Longrightarrow> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (\<exists>P\<^sub>c'. e\<^sub>c' = AnonyEvent P\<^sub>c' \<and> (\<Gamma>\<^sub>c,(P\<^sub>c', s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(P\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a))"
proof-
  assume a0: "(\<Gamma>\<^sub>c,(P\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(P\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a)"
     and a1: "\<Gamma>\<^sub>c \<turnstile>\<^sub>c (AnonyEvent P\<^sub>c, s\<^sub>c, x\<^sub>c) -et-Cmd Pc\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c)"
     and a2: "\<zeta> Pc = None"
  from a1 have "(Pc = P\<^sub>c) \<and> (\<exists>P\<^sub>c'. \<Gamma>\<^sub>c \<turnstile>\<^sub>c (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c') \<and> e\<^sub>c' = AnonyEvent P\<^sub>c')"
    apply (rule Event\<^sub>c.etran.cases, simp_all)
    by (metis act.inject(1) actk.ext_inject get_actk_def)
  then obtain P\<^sub>c' where a3: "Pc = P\<^sub>c \<and> \<Gamma>\<^sub>c \<turnstile>\<^sub>c (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c') \<and> e\<^sub>c' = AnonyEvent P\<^sub>c'" by auto
  with a0 a2 have "(s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (\<Gamma>\<^sub>c, (P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)"
    by (meson Event\<^sub>c.ptran'_def prog_sim_validity)
  then show ?thesis
    by (simp add: a3)
qed

lemma AnonyEvt_Sound_help2: "\<lbrakk>(\<Gamma>\<^sub>c,(P\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(P\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a); 
      \<Gamma>\<^sub>c \<turnstile>\<^sub>c (AnonyEvent P\<^sub>c, s\<^sub>c, x\<^sub>c) -et-Cmd Pc\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c); \<zeta> Pc = Some Pa\<rbrakk> 
      \<Longrightarrow> \<exists>e\<^sub>a' s\<^sub>a'. \<Gamma>\<^sub>a \<turnstile>\<^sub>a (AnonyEvent P\<^sub>a, s\<^sub>a, x\<^sub>a) -et-Cmd Pa\<sharp>k\<rightarrow> (e\<^sub>a', s\<^sub>a', x\<^sub>a) \<and>
          (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> (\<exists>P\<^sub>c. e\<^sub>c' = AnonyEvent P\<^sub>c \<and> (\<exists>P\<^sub>a'. e\<^sub>a' = AnonyEvent P\<^sub>a'
          \<and> (\<Gamma>\<^sub>c,(P\<^sub>c, s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(P\<^sub>a', s\<^sub>a'),R\<^sub>a,G\<^sub>a)))"
proof-
  assume a0: "(\<Gamma>\<^sub>c,(P\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(P\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a)"
     and a1: "\<Gamma>\<^sub>c \<turnstile>\<^sub>c (AnonyEvent P\<^sub>c, s\<^sub>c, x\<^sub>c) -et-Cmd Pc\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c)"
     and a2: "\<zeta> Pc = Some Pa"  
  from a1 have "Pc = P\<^sub>c \<and> (\<exists>P\<^sub>c'. \<Gamma>\<^sub>c \<turnstile>\<^sub>c (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c') \<and> e\<^sub>c' = AnonyEvent P\<^sub>c')"
    apply (rule Event\<^sub>c.etran.cases, simp_all)
    by (metis act.inject(1) actk.ext_inject get_actk_def)
  then obtain P\<^sub>c' where a3: "Pc = P\<^sub>c \<and> \<Gamma>\<^sub>c \<turnstile>\<^sub>c (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c') \<and> e\<^sub>c' = AnonyEvent P\<^sub>c'" by auto
  with a0 have "\<zeta> P\<^sub>c = Some P\<^sub>a \<and> (\<exists>P\<^sub>a' s\<^sub>a'. \<Gamma>\<^sub>a \<turnstile>\<^sub>a (P\<^sub>a, s\<^sub>a) -c\<rightarrow> (P\<^sub>a', s\<^sub>a')
  \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> (\<Gamma>\<^sub>c, (P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a', s\<^sub>a'), R\<^sub>a, G\<^sub>a))"
    by (smt (verit, best) Event\<^sub>a.ptran'_def Event\<^sub>c.ptran'_def a2 option.distinct(1) prog_sim_validity)
  then obtain P\<^sub>a' s\<^sub>a' where a4: "\<zeta> P\<^sub>c = Some P\<^sub>a \<and> \<Gamma>\<^sub>a \<turnstile>\<^sub>a (P\<^sub>a, s\<^sub>a) -c\<rightarrow> (P\<^sub>a', s\<^sub>a')\<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c 
  \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> (\<Gamma>\<^sub>c, (P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a', s\<^sub>a'), R\<^sub>a, G\<^sub>a)" by auto
  with a2 a3 show ?thesis by (metis Event\<^sub>a.AnonyEvent option.inject)
qed

lemma AnonyEvt_Sound_lemma : "(\<Gamma>\<^sub>c, (P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)  \<Longrightarrow>
       (\<Gamma>\<^sub>c, (AnonyEvent P\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (AnonyEvent P\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduction arbitrary: P\<^sub>c s\<^sub>c x\<^sub>c P\<^sub>a s\<^sub>a x\<^sub>a, clarsimp)
  apply (rule conjI)
  using prog_sim_validity apply blast
  apply (rule conjI)
   apply (metis Event\<^sub>c.EvtSeq1 Event\<^sub>c.EvtSeq2 Event\<^sub>c.ent_spec1 Event\<^sub>c.evtent_is_basicevt event.distinct(1))
  apply (rule conjI, clarsimp)
  apply (simp add: AnonyEvt_Sound_help1)
  apply (rule conjI, clarsimp)
  using AnonyEvt_Sound_help2 apply fastforce
  apply (rule conjI)
  using prog_sim_validity apply blast
  using prog_sim_validity by blast

theorem AnonyEvent_Sound : "(\<Gamma>\<^sub>c, P\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>)  (\<Gamma>\<^sub>a, P\<^sub>a, R\<^sub>a, G\<^sub>a) \<Longrightarrow>  
                            (\<Gamma>\<^sub>c, AnonyEvent P\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>)  (\<Gamma>\<^sub>a, AnonyEvent P\<^sub>a, R\<^sub>a, G\<^sub>a)"
  by (simp add: AnonyEvt_Sound_lemma e_sim_pre_def prog_sim_pre_validity)

lemma BasicEvent_Sound_lemma : "\<lbrakk>(\<Gamma>\<^sub>c,P\<^sub>c,R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<eta>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>)  (\<Gamma>\<^sub>a,P\<^sub>a,R\<^sub>a,G\<^sub>a); \<xi> \<subseteq> g\<^sub>c \<rightleftharpoons>\<^sub>r g\<^sub>a; (s\<^sub>c, s\<^sub>a) \<in> \<xi>;
       \<eta> = \<xi> \<inter> (g\<^sub>c\<and>\<^sub>rg\<^sub>a); \<Gamma>\<^sub>c \<turnstile>\<^sub>c (BasicEvent (l\<^sub>c, g\<^sub>c, P\<^sub>c), s\<^sub>c, x\<^sub>c) -et-EvtEnt ec\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c, x\<^sub>c'); P\<^sub>a \<noteq> fin_com\<^sub>a \<rbrakk> \<Longrightarrow> 
       \<exists>ea e\<^sub>a' x\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (BasicEvent (l\<^sub>a, g\<^sub>a, P\<^sub>a), s\<^sub>a, x\<^sub>a) -et-EvtEnt ea\<sharp>k\<rightarrow> (e\<^sub>a', s\<^sub>a, x\<^sub>a')) \<and>
       (\<Gamma>\<^sub>c,(e\<^sub>c', s\<^sub>c, x\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(e\<^sub>a', s\<^sub>a, x\<^sub>a'),R\<^sub>a,G\<^sub>a)"
proof-
  assume a0: "(\<Gamma>\<^sub>c,P\<^sub>c,R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<eta>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>)  (\<Gamma>\<^sub>a,P\<^sub>a,R\<^sub>a,G\<^sub>a)"
     and a1: "\<xi> \<subseteq> g\<^sub>c \<rightleftharpoons>\<^sub>r g\<^sub>a"
     and a2: "(s\<^sub>c, s\<^sub>a) \<in> \<xi>"
     and a3: "\<eta> = \<xi> \<inter> (g\<^sub>c\<and>\<^sub>rg\<^sub>a)"
     and a4: "\<Gamma>\<^sub>c \<turnstile>\<^sub>c (BasicEvent (l\<^sub>c, g\<^sub>c, P\<^sub>c), s\<^sub>c, x\<^sub>c) -et-EvtEnt ec\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c, x\<^sub>c')"
     and a5: "P\<^sub>a \<noteq> fin_com\<^sub>a"
  from a4 have a6: "s\<^sub>c \<in> g\<^sub>c \<and> e\<^sub>c' = AnonyEvent P\<^sub>c " 
    apply (rule Event\<^sub>c.etran.cases, simp_all)
    using guard_def body_def by (metis fstI sndI)
  with a1 a2 have a7 : "s\<^sub>a \<in> g\<^sub>a" 
    by (smt (verit, ccfv_SIG) CollectD case_prodE fst_conv rel_guard_eq_def snd_conv subsetD)
  with a5 have a8: "\<Gamma>\<^sub>a \<turnstile>\<^sub>a (BasicEvent (l\<^sub>a, g\<^sub>a, P\<^sub>a), s\<^sub>a, x\<^sub>a) -et-EvtEnt (BasicEvent (l\<^sub>a, g\<^sub>a, P\<^sub>a))\<sharp>k\<rightarrow> 
                   (AnonyEvent P\<^sub>a, s\<^sub>a, x\<^sub>a(k := BasicEvent (l\<^sub>a, g\<^sub>a, P\<^sub>a)))"
    by (rule_tac Event\<^sub>a.EventEntry, simp_all add: body_def guard_def)
  from a2 a3 a6 a7 have "(s\<^sub>c, s\<^sub>a) \<in> \<eta>"
    by (simp add: rel_guard_and_def)
  with a0 have "(\<Gamma>\<^sub>c, (P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>)  (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)"
    by (rule_tac \<xi> = \<eta> in prog_sim_pre_validity, simp_all)
  then have "(\<Gamma>\<^sub>c, (AnonyEvent P\<^sub>c, s\<^sub>c, x\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>)  (\<Gamma>\<^sub>a, (AnonyEvent P\<^sub>a, s\<^sub>a, x\<^sub>a(k := BasicEvent (l\<^sub>a, g\<^sub>a, P\<^sub>a))), R\<^sub>a, G\<^sub>a)"
    by (simp add: AnonyEvt_Sound_lemma)
  then show ?thesis
    using a6 a8 by blast
qed

theorem BasicEvent_Sound : "\<lbrakk>(\<Gamma>\<^sub>c, P\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<eta>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>)  (\<Gamma>\<^sub>a, P\<^sub>a, R\<^sub>a, G\<^sub>a); \<xi> \<subseteq> g\<^sub>c \<rightleftharpoons>\<^sub>r g\<^sub>a; P\<^sub>a \<noteq> fin_com\<^sub>a; 
      \<eta> = \<xi> \<inter> (g\<^sub>c \<and>\<^sub>r g\<^sub>a); Stable \<eta> ((R\<^sub>c, R\<^sub>a \<union> Id)\<^sub>\<alpha>); Stable \<xi> ((R\<^sub>c, R\<^sub>a \<union> Id)\<^sub>\<alpha>); \<xi> \<subseteq> \<alpha> \<rbrakk> \<Longrightarrow>
      (\<Gamma>\<^sub>c, BasicEvent (l\<^sub>c, g\<^sub>c, P\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>)  (\<Gamma>\<^sub>a, BasicEvent (l\<^sub>a, g\<^sub>a, P\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (simp add: e_sim_pre_def, clarify)
  apply (coinduction arbitrary: P\<^sub>c P\<^sub>a, clarsimp)
  apply (rule conjI)
   apply blast
  apply (rule conjI, clarsimp)
   apply (meson BasicEvent_Sound_lemma)
  apply (rule conjI, clarsimp)
   apply (meson Event\<^sub>c.noevtent_notran0 act.distinct(1))
  apply (rule conjI, clarsimp)
   apply (meson Event\<^sub>c.noevtent_notran0 act.distinct(1))
  by (meson Stable_def)

coinductive es_sim :: "['Env\<^sub>c, ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) esconf, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
                  ('s\<^sub>c \<times> 's\<^sub>a) set, 
                  ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) event \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) event, 
                  ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) event \<Rightarrow> 'prog\<^sub>c \<Rightarrow> 'prog\<^sub>a option,
                  'Env\<^sub>a, ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) esconf, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool" 
  ("'(_,_,_,_')/ \<preceq>\<^sub>e\<^sub>s \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>') /'(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81] 100)
  where rgsim : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<alpha>; 
                  
                  (\<forall>k.

                  (\<forall>ec es\<^sub>c' x\<^sub>c'. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (es\<^sub>c, s\<^sub>c, x\<^sub>c) -es-((EvtEnt ec)\<sharp>k)\<rightarrow> (es\<^sub>c', s\<^sub>c, x\<^sub>c')) \<longrightarrow>(\<exists>ea es\<^sub>a' x\<^sub>a'. 
                   (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (es\<^sub>a, s\<^sub>a, x\<^sub>a) -es-((EvtEnt ea)\<sharp>k)\<rightarrow> (es\<^sub>a', s\<^sub>a, x\<^sub>a')) \<and> \<zeta> ec = ea \<and> 
                    (\<Gamma>\<^sub>c, (es\<^sub>c', s\<^sub>c, x\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a', s\<^sub>a, x\<^sub>a'), R\<^sub>a, G\<^sub>a))) \<and>

                  (\<forall>Pc es\<^sub>c' s\<^sub>c'. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (es\<^sub>c, s\<^sub>c, x\<^sub>c) -es-((Cmd Pc)\<sharp>k)\<rightarrow> (es\<^sub>c', s\<^sub>c, x\<^sub>c')) \<and> \<gamma> (x\<^sub>c k) Pc = None \<longrightarrow>
                  (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (\<Gamma>\<^sub>c, (es\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)) \<and>
                  
                  (\<forall>Pc es\<^sub>c' s\<^sub>c'. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (es\<^sub>c, s\<^sub>c, x\<^sub>c) -es-((Cmd Pc)\<sharp>k)\<rightarrow> (es\<^sub>c', s\<^sub>c, x\<^sub>c')) \<and> \<gamma> (x\<^sub>c k) Pc = Some Pa \<longrightarrow>
                  (\<exists>es\<^sub>a' s\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (es\<^sub>a, s\<^sub>a, x\<^sub>a) -es-((Cmd Pa)\<sharp>k)\<rightarrow> (es\<^sub>a', s\<^sub>a', x\<^sub>a)) \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a
                  \<and> (\<Gamma>\<^sub>c, (es\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a, s\<^sub>a', x\<^sub>a), R\<^sub>a, G\<^sub>a)))

                  ) ;

                   (\<forall>s\<^sub>c' s\<^sub>a'. ((s\<^sub>c, s\<^sub>c'), (s\<^sub>a, s\<^sub>a')) \<in> ((R\<^sub>c, R\<^sub>a \<union> Id)\<^sub>\<alpha>) \<longrightarrow> 
                     (\<Gamma>\<^sub>c, (es\<^sub>c, s\<^sub>c', x\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a, s\<^sub>a', x\<^sub>a'), R\<^sub>a, G\<^sub>a))      
                  \<rbrakk> \<Longrightarrow> (\<Gamma>\<^sub>c, (es\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)"

inductive pes_sim :: "['Env\<^sub>c, ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) pesconf, 
                  ('s\<^sub>c \<times> 's\<^sub>a) set, 
                  ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) event \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) event, 
                  ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) event \<Rightarrow> 'prog\<^sub>c \<Rightarrow> 'prog\<^sub>a option,
                  'Env\<^sub>a, ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) pesconf] \<Rightarrow> bool" 
  ("'(_,_')/ \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>') /'(_,_')" [81,81,81,81,81,81,81] 100)
  where rgsim : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<alpha>; 
                  
                  (\<forall>ec pes\<^sub>c' x\<^sub>c' k. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c, s\<^sub>c, x\<^sub>c) -pes-((EvtEnt ec)\<sharp>k)\<rightarrow> (pes\<^sub>c', s\<^sub>c, x\<^sub>c')) \<longrightarrow>(\<exists>ea pes\<^sub>a' x\<^sub>a'. 
                  (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a, s\<^sub>a, x\<^sub>a) -pes-((EvtEnt ea)\<sharp>k)\<rightarrow> (pes\<^sub>a', s\<^sub>a, x\<^sub>a')) \<and> \<eta> ec = ea \<and> 
                  (\<Gamma>\<^sub>c, (pes\<^sub>c', s\<^sub>c, x\<^sub>c')) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<kappa>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a', s\<^sub>a, x\<^sub>a'))));

                  (\<forall>Pc pes\<^sub>c' s\<^sub>c' k. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c, s\<^sub>c, x\<^sub>c) -pes-((Cmd Pc)\<sharp>k)\<rightarrow> (pes\<^sub>c', s\<^sub>c', x\<^sub>c)) \<and> \<kappa> (x\<^sub>c k) Pc = None \<longrightarrow>
                  (\<Gamma>\<^sub>c, (pes\<^sub>c', s\<^sub>c', x\<^sub>c)) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<kappa>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a, s\<^sub>a, x\<^sub>a)));

                  (\<forall>Pc pes\<^sub>c' s\<^sub>c' k Pa. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c, s\<^sub>c, x\<^sub>c) -pes-((Cmd Pc)\<sharp>k)\<rightarrow> (pes\<^sub>c', s\<^sub>c', x\<^sub>c)) \<and> \<kappa> (x\<^sub>c k) Pc = Some Pa \<longrightarrow>
                  (\<exists>pes\<^sub>a' s\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a, s\<^sub>a, x\<^sub>a) -pes-((Cmd Pa)\<sharp>k)\<rightarrow> (pes\<^sub>a', s\<^sub>a', x\<^sub>a)) \<and> \<eta> (x\<^sub>c k) = (x\<^sub>a k)
                  \<and> (\<Gamma>\<^sub>c, (pes\<^sub>c', s\<^sub>c', x\<^sub>c)) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<kappa>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a', s\<^sub>a', x\<^sub>a)))) 
     
                  \<rbrakk> \<Longrightarrow> (\<Gamma>\<^sub>c, (pes\<^sub>c, s\<^sub>c, x\<^sub>c)) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<kappa>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a, s\<^sub>a, x\<^sub>a))"



lemma KKV: "\<lbrakk>\<forall>k. (\<Gamma>\<^sub>c, (pes\<^sub>c k, s\<^sub>c, x\<^sub>c), (R\<^sub>c k), (G\<^sub>c k)) \<preceq>\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<kappa>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a k, s\<^sub>a, x\<^sub>a), (R\<^sub>a k), (G\<^sub>a k));
             \<forall>i j. i \<noteq> j \<longrightarrow> G\<^sub>c i \<subseteq> R\<^sub>c j \<and> G\<^sub>a i \<subseteq> R\<^sub>a j\<rbrakk> \<Longrightarrow> (\<Gamma>\<^sub>c, (pes\<^sub>c, s\<^sub>c, x\<^sub>c)) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<kappa>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a, s\<^sub>a, x\<^sub>a))"
(*
inductive None_event :: "('l\<^sub>c, 'k, 's\<^sub>c, 'prog\<^sub>c) event \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>a) set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>a) set \<Rightarrow> bool"
  where "None_event e \<xi> \<gamma> = (\<forall>s\<^sub>c s\<^sub>a. 
         )"
*)
end
 

locale PiCore_RGSim = 
       Sim: PiCore_Sim ptran\<^sub>c petran\<^sub>c fin_com\<^sub>c ptran\<^sub>a petran\<^sub>a fin_com\<^sub>a +
       InfoFlow\<^sub>c: InfoFlow ptran\<^sub>c petran\<^sub>c fin_com\<^sub>c \<Gamma>\<^sub>c C0\<^sub>c step\<^sub>c interference\<^sub>c vpeq\<^sub>c obs\<^sub>c dome\<^sub>c +
       InfoFlow\<^sub>a: InfoFlow ptran\<^sub>a petran\<^sub>a fin_com\<^sub>a \<Gamma>\<^sub>a C0\<^sub>a step\<^sub>a interference\<^sub>a vpeq\<^sub>a obs\<^sub>a dome\<^sub>a
  for ptran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> (('prog\<^sub>c \<times> 's\<^sub>c) \<times> 'prog\<^sub>c \<times> 's\<^sub>c) set" 
  and petran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> 'prog\<^sub>c \<times> 's\<^sub>c \<Rightarrow> 'prog\<^sub>c \<times> 's\<^sub>c \<Rightarrow> bool" 
  and fin_com\<^sub>c :: "'prog\<^sub>c"
  and \<Gamma>\<^sub>c :: "'Env\<^sub>c"
  and C0\<^sub>c  :: "('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) pesconf"
  and step\<^sub>c :: "('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c, 'd) action \<Rightarrow> (('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) pesconf \<times> ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) pesconf) set"
  and interference\<^sub>c :: "'d \<Rightarrow> 'd \<Rightarrow> bool" 
  and vpeq\<^sub>c :: "'s\<^sub>c \<Rightarrow> 'd \<Rightarrow> 's\<^sub>c \<Rightarrow> bool" ("(_ \<sim>\<^sub>c_\<sim>\<^sub>c _)" [70,69,70] 60)
  and obs\<^sub>c :: "'s\<^sub>c \<Rightarrow> 'd \<Rightarrow> 'o\<^sub>c" 
  and dome\<^sub>c :: "'s\<^sub>c \<Rightarrow> ('l\<^sub>c, 'k, 's\<^sub>c, 'prog\<^sub>c) event \<Rightarrow> 'd"
  and ptran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> (('prog\<^sub>a \<times> 's\<^sub>a) \<times> 'prog\<^sub>a \<times> 's\<^sub>a) set"
  and petran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> 'prog\<^sub>a \<times> 's\<^sub>a \<Rightarrow> 'prog\<^sub>a \<times> 's\<^sub>a \<Rightarrow> bool" 
  and fin_com\<^sub>a :: "'prog\<^sub>a"
  and \<Gamma>\<^sub>a :: "'Env\<^sub>a"
  and C0\<^sub>a :: "('l\<^sub>a, 'k, 's\<^sub>a, 'prog\<^sub>a) pesconf"
  and step\<^sub>a :: "('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a, 'd) action \<Rightarrow> (('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) pesconf \<times> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) pesconf) set" 
  and interference\<^sub>a :: "'d \<Rightarrow> 'd \<Rightarrow> bool" 
  and vpeq\<^sub>a ::  "'s\<^sub>a \<Rightarrow> 'd \<Rightarrow> 's\<^sub>a \<Rightarrow> bool" ("(_ \<sim>\<^sub>a_\<sim>\<^sub>a _)" [70,69,70] 60)
  and obs\<^sub>a :: "'s\<^sub>a \<Rightarrow> 'd \<Rightarrow> 'o\<^sub>a" 
  and dome\<^sub>a :: "'s\<^sub>a \<Rightarrow> ('l\<^sub>a, 'k, 's\<^sub>a, 'prog\<^sub>a) event \<Rightarrow> 'd" +
fixes \<alpha> :: "('s\<^sub>c \<times> 's\<^sub>a) set"
  and \<eta> :: "('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) event \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) event"
  and \<kappa> :: "('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) event \<Rightarrow> 'prog\<^sub>c \<Rightarrow> 'prog\<^sub>a option"
assumes
  init_sim : "(\<Gamma>\<^sub>c, C0\<^sub>c) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<kappa>\<^sub>) (\<Gamma>\<^sub>a, C0\<^sub>a)" and
  dom_sim : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<alpha>; \<eta> e\<^sub>c = e\<^sub>a \<rbrakk> \<Longrightarrow> dome\<^sub>c s\<^sub>c e\<^sub>c = dome\<^sub>a s\<^sub>a e\<^sub>a" and
  intefere_same : "interference\<^sub>c  = interference\<^sub>a" and
  sim_state_ifs : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<alpha>; (t\<^sub>c, t\<^sub>a) \<in> \<alpha>\<rbrakk> \<Longrightarrow> s\<^sub>a \<sim>\<^sub>a d \<sim>\<^sub>a t\<^sub>a = s\<^sub>c \<sim>\<^sub>c d \<sim>\<^sub>c t\<^sub>c"
begin

definition sim_s :: "('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) pesconf \<Rightarrow> ('l\<^sub>a, 'k, 's\<^sub>a, 'prog\<^sub>a) pesconf \<Rightarrow> bool" ("(_ \<sim> _)" [70,70] 60)
  where "C\<^sub>c \<sim> C\<^sub>a = (\<Gamma>\<^sub>c, C\<^sub>c) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<kappa>\<^sub>) (\<Gamma>\<^sub>a, C\<^sub>a)"

fun sim_a :: "('l\<^sub>c, 'k, 's\<^sub>c, 'prog\<^sub>c, 'd) action \<Rightarrow> ('l\<^sub>a, 'k, 's\<^sub>a, 'prog\<^sub>a, 'd) action option"
  where "sim_a \<lparr>actk = \<lparr>Act = Cmd P\<^sub>c, K = k\<rparr>, eventof = e\<^sub>c, domain = d\<rparr> = 
         (if (\<kappa> e\<^sub>c P\<^sub>c = None) then None 
         else Some (let e\<^sub>a = \<eta> e\<^sub>c; P\<^sub>a = the (\<kappa> e\<^sub>c P\<^sub>c) in 
              \<lparr>actk = \<lparr>Act = Cmd P\<^sub>a, K = k\<rparr>, eventof = e\<^sub>a, domain = d\<rparr>))" |
        "sim_a \<lparr>actk = \<lparr>Act = EvtEnt e\<^sub>c, K = k\<rparr>, eventof = ec, domain = d\<rparr> = 
         Some \<lparr>actk = \<lparr>Act = EvtEnt (\<eta> e\<^sub>c), K = k\<rparr>, eventof = \<eta> e\<^sub>c, domain = d\<rparr>"

lemma dom_refine : "sim_a a\<^sub>c = Some a\<^sub>a \<Longrightarrow> domain a\<^sub>c = domain a\<^sub>a"
  apply (case_tac a\<^sub>c, case_tac actk, case_tac Act, simp_all)
   apply (metis action.select_convs(3) option.discI option.inject)
  by (metis action.select_convs(3))

lemma none_refine: "\<lbrakk>sim_a a\<^sub>c = None; C\<^sub>c \<sim> C\<^sub>a; (C\<^sub>c, C\<^sub>c') \<in> step\<^sub>c a\<^sub>c\<rbrakk> \<Longrightarrow> C\<^sub>c' \<sim> C\<^sub>a"
proof-
  assume a0: "sim_a a\<^sub>c = None"
     and a1: "C\<^sub>c \<sim> C\<^sub>a"
     and a2: "(C\<^sub>c, C\<^sub>c') \<in> step\<^sub>c a\<^sub>c"

  from a0 have "is_Cmd_act (Act (actk a\<^sub>c))"
    by (metis act.exhaust action.surjective actk.surjective is_Cmd_act.simps(1) old.unit.exhaust option.distinct(1) sim_a.simps(2))
  then obtain P\<^sub>c k e\<^sub>c d where a3: "a\<^sub>c = \<lparr>actk = \<lparr>Act = Cmd P\<^sub>c, K = k\<rparr>, eventof = e\<^sub>c, domain = d\<rparr>"
    by (metis act.exhaust action.surjective actk.surjective is_Cmd_act.simps(2) old.unit.exhaust)
  with a0 have a4: "\<kappa> e\<^sub>c P\<^sub>c = None"
    by (metis option.discI sim_a.simps(1))

  obtain pes\<^sub>c s\<^sub>c x\<^sub>c pes\<^sub>c' s\<^sub>c' x\<^sub>c' where a5: "C\<^sub>c = (pes\<^sub>c ,s\<^sub>c ,x\<^sub>c) \<and> C\<^sub>c' = (pes\<^sub>c', s\<^sub>c', x\<^sub>c')" 
    by (meson Sim.Event\<^sub>c.pesconf_trip)
  with a2 a3 have a6: "(\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c ,s\<^sub>c ,x\<^sub>c) -pes-(Cmd P\<^sub>c)\<sharp>k \<rightarrow> (pes\<^sub>c', s\<^sub>c', x\<^sub>c')) \<and> (x\<^sub>c k = e\<^sub>c)"
    by (simp add: InfoFlow\<^sub>c.step_def get_actk_def getx_def)
  then have a7: "x\<^sub>c = x\<^sub>c'"
    by (meson Sim.Event\<^sub>c.act_in_pes_notchgstate)

  with a1 a4 a5 a6 show ?thesis
    apply (simp add: sim_s_def)
    apply (erule Sim.pes_sim.cases, simp)
    by (metis Sim.Event\<^sub>c.pesconf_trip snd_conv)
qed

lemma action_refine: "\<lbrakk>sim_a a\<^sub>c = Some a\<^sub>a; C\<^sub>c \<sim> C\<^sub>a; (C\<^sub>c, C\<^sub>c') \<in> step\<^sub>c a\<^sub>c\<rbrakk> \<Longrightarrow> \<exists>C\<^sub>a'. C\<^sub>c' \<sim> C\<^sub>a' \<and> (C\<^sub>a, C\<^sub>a') \<in> step\<^sub>a a\<^sub>a"
proof-
  assume a0: "sim_a a\<^sub>c = Some a\<^sub>a"
     and a1: "C\<^sub>c \<sim> C\<^sub>a"
     and a2: "(C\<^sub>c, C\<^sub>c') \<in> step\<^sub>c a\<^sub>c"
  then have "\<exists>C\<^sub>a'. C\<^sub>c' \<sim> C\<^sub>a' \<and> (C\<^sub>a, C\<^sub>a') \<in> step\<^sub>a a\<^sub>a"
  proof(case_tac "Act (actk a\<^sub>c)")
    fix P\<^sub>c
    assume "Act (actk a\<^sub>c) = Cmd P\<^sub>c"
    then obtain k e\<^sub>c d where b0: "a\<^sub>c = \<lparr>actk = \<lparr>Act = Cmd P\<^sub>c, K = k\<rparr>, eventof = e\<^sub>c, domain = d\<rparr>"
      by (metis action.surjective actk.surjective old.unit.exhaust)
    with a0 have "\<exists>P\<^sub>a. \<kappa> e\<^sub>c P\<^sub>c = Some P\<^sub>a"
      by (metis option.discI option.exhaust_sel sim_a.simps(1))
    then obtain P\<^sub>a where b1: "\<kappa> e\<^sub>c P\<^sub>c = Some P\<^sub>a" by auto
    with a0 b0 have b2: "a\<^sub>a = \<lparr>actk = \<lparr>Act = Cmd P\<^sub>a, K = k\<rparr>, eventof = \<eta> e\<^sub>c, domain = d\<rparr>" by auto

    obtain pes\<^sub>c s\<^sub>c x\<^sub>c pes\<^sub>c' s\<^sub>c' x\<^sub>c' where b3: "C\<^sub>c = (pes\<^sub>c ,s\<^sub>c ,x\<^sub>c) \<and> C\<^sub>c' = (pes\<^sub>c', s\<^sub>c', x\<^sub>c')" 
      by (meson Sim.Event\<^sub>c.pesconf_trip)
    with a2 b0 have b4: "(\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c ,s\<^sub>c ,x\<^sub>c) -pes-(Cmd P\<^sub>c)\<sharp>k \<rightarrow> (pes\<^sub>c', s\<^sub>c', x\<^sub>c')) \<and> (x\<^sub>c k = e\<^sub>c) \<and> (dome\<^sub>c s\<^sub>c e\<^sub>c = d)"
      apply (simp add: InfoFlow\<^sub>c.step_def get_actk_def gets_def getx_def)
      by blast
    obtain pes\<^sub>a s\<^sub>a x\<^sub>a where b5: "C\<^sub>a = (pes\<^sub>a, s\<^sub>a, x\<^sub>a)" by (meson Sim.Event\<^sub>c.pesconf_trip)
    with a1 b1 b3 b4 have "\<exists>pes\<^sub>a' s\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a, s\<^sub>a, x\<^sub>a) -pes-((Cmd P\<^sub>a)\<sharp>k)\<rightarrow> (pes\<^sub>a', s\<^sub>a', x\<^sub>a))
    \<and> \<eta> (x\<^sub>c k) = (x\<^sub>a k) \<and> (\<Gamma>\<^sub>c, (pes\<^sub>c', s\<^sub>c', x\<^sub>c)) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<kappa>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a', s\<^sub>a', x\<^sub>a))"
      apply (simp add: sim_s_def)
      apply (erule Sim.pes_sim.cases, simp)
      by (metis Sim.Event\<^sub>c.act_in_pes_notchgstate)
    then obtain pes\<^sub>a' s\<^sub>a' where b6: "(\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a, s\<^sub>a, x\<^sub>a) -pes-((Cmd P\<^sub>a)\<sharp>k)\<rightarrow> (pes\<^sub>a', s\<^sub>a', x\<^sub>a))
    \<and> \<eta> (x\<^sub>c k) = (x\<^sub>a k) \<and> (\<Gamma>\<^sub>c, (pes\<^sub>c', s\<^sub>c', x\<^sub>c)) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<kappa>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a', s\<^sub>a', x\<^sub>a))" by auto

    from a1 b3 b5 have "(s\<^sub>c, s\<^sub>a) \<in> \<alpha>"
      by (simp add: Sim.pes_sim_init sim_s_def)      
    with b2 b3 b4 b5 b6 have "dome\<^sub>a (gets C\<^sub>a) (eventof a\<^sub>a) = domain a\<^sub>a"
      apply (simp add: gets_def)
      apply (rule_tac s = "dome\<^sub>c s\<^sub>c e\<^sub>c" in trans)
      using dom_sim apply auto[1]
      using b5 by auto
    with b2 b4 b5 b6 have "actk a\<^sub>a = ((Cmd P\<^sub>a)\<sharp>k) \<and> eventof a\<^sub>a = (getx C\<^sub>a) k \<and> dome\<^sub>a (gets C\<^sub>a) (eventof a\<^sub>a) = domain a\<^sub>a"
      by (metis Sim.Event\<^sub>a.act_in_pes_notchgstate Sim.Event\<^sub>a.event_axioms action.select_convs(1) 
         action.select_convs(2)  event.pesconf_trip get_actk_def)
    with b5 b6 have "(C\<^sub>a, (pes\<^sub>a', s\<^sub>a', x\<^sub>a)) \<in> step\<^sub>a a\<^sub>a"
      using InfoFlow\<^sub>a.step_def by fastforce
    with b3 b4 b6 show ?thesis
      by (metis Sim.Event\<^sub>c.event_axioms event.act_in_pes_notchgstate sim_s_def)
  next
    fix e\<^sub>c
    assume "Act (actk a\<^sub>c) = EvtEnt e\<^sub>c"
    then obtain k ec d where b0: "a\<^sub>c = \<lparr>actk = \<lparr>Act = EvtEnt e\<^sub>c, K = k\<rparr>, eventof = ec, domain = d\<rparr>"
      by (metis action.surjective actk.surjective old.unit.exhaust)
    with a0 have b1: "a\<^sub>a = \<lparr>actk = \<lparr>Act = EvtEnt (\<eta> e\<^sub>c), K = k\<rparr>, eventof = \<eta> e\<^sub>c, domain = d\<rparr>"
      by force
    obtain pes\<^sub>c s\<^sub>c x\<^sub>c pes\<^sub>c' s\<^sub>c' x\<^sub>c' where b3: "C\<^sub>c = (pes\<^sub>c ,s\<^sub>c ,x\<^sub>c) \<and> C\<^sub>c' = (pes\<^sub>c', s\<^sub>c', x\<^sub>c')" 
      by (meson Sim.Event\<^sub>c.pesconf_trip)
    with b0 a2 have b4: "(\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c ,s\<^sub>c ,x\<^sub>c) -pes-(EvtEnt e\<^sub>c)\<sharp>k \<rightarrow> (pes\<^sub>c', s\<^sub>c', x\<^sub>c')) \<and> ec = e\<^sub>c \<and> dome\<^sub>c s\<^sub>c e\<^sub>c = d"
      by (simp add: InfoFlow\<^sub>c.step_def get_actk_def gets_def getx_def)
    then have b5: "s\<^sub>c = s\<^sub>c'"
      by (metis Sim.Event\<^sub>c.evtent_in_pes_notchgstate)
    obtain pes\<^sub>a s\<^sub>a x\<^sub>a where b6: "C\<^sub>a = (pes\<^sub>a, s\<^sub>a, x\<^sub>a)" by (meson Sim.Event\<^sub>c.pesconf_trip)
    with a1 b3 b4 have "\<exists>e\<^sub>a pes\<^sub>a' x\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a, s\<^sub>a, x\<^sub>a) -pes-((EvtEnt e\<^sub>a)\<sharp>k)\<rightarrow> (pes\<^sub>a', s\<^sub>a, x\<^sub>a'))
    \<and> \<eta> e\<^sub>c = e\<^sub>a \<and> (\<Gamma>\<^sub>c, (pes\<^sub>c', s\<^sub>c, x\<^sub>c')) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<kappa>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a', s\<^sub>a, x\<^sub>a'))"
      apply (simp add: sim_s_def)
      apply (erule Sim.pes_sim.cases, simp)
      by (metis Sim.Event\<^sub>c.evtent_in_pes_notchgstate)
    then obtain pes\<^sub>a' x\<^sub>a' where b7: "(\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a, s\<^sub>a, x\<^sub>a) -pes-((EvtEnt (\<eta> e\<^sub>c))\<sharp>k)\<rightarrow> (pes\<^sub>a', s\<^sub>a, x\<^sub>a'))
     \<and> (\<Gamma>\<^sub>c, (pes\<^sub>c', s\<^sub>c, x\<^sub>c')) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<kappa>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a', s\<^sub>a, x\<^sub>a'))" by auto

    then have "(s\<^sub>c, s\<^sub>a) \<in> \<alpha>"
      using Sim.pes_sim_init by blast
    with b1 b4 b6 have "dome\<^sub>a (gets C\<^sub>a) (\<eta> e\<^sub>c) = domain a\<^sub>a"
      by (metis action.select_convs(3) dom_sim fst_conv gets_def snd_conv)
    with b1 have "actk a\<^sub>a = (EvtEnt (\<eta> e\<^sub>c))\<sharp>k \<and> eventof a\<^sub>a = \<eta> e\<^sub>c \<and> dome\<^sub>a (gets C\<^sub>a) (\<eta> e\<^sub>c) = domain a\<^sub>a"
      by (simp add: get_actk_def)
    with b6 b7 have "(C\<^sub>a, (pes\<^sub>a', s\<^sub>a, x\<^sub>a')) \<in> step\<^sub>a a\<^sub>a"
      using InfoFlow\<^sub>a.step_def by auto
    with b3 b5 b7 show ?thesis
      using  sim_s_def by blast
  qed

  then show ?thesis by auto
qed   

lemma sim_ifs : "\<lbrakk>C\<^sub>c \<sim> C\<^sub>a; T\<^sub>c \<sim> T\<^sub>a\<rbrakk> \<Longrightarrow>  (gets C\<^sub>a) \<sim>\<^sub>a d \<sim>\<^sub>a (gets T\<^sub>a) = (gets C\<^sub>c) \<sim>\<^sub>c d \<sim>\<^sub>c (gets T\<^sub>c)"
  by (metis (mono_tags, lifting) Sim.Event\<^sub>c.pesconf_trip Sim.pes_sim_init sim_s_def sim_state_ifs)

interpretation PiCore_Refine ptran\<^sub>c petran\<^sub>c fin_com\<^sub>c \<Gamma>\<^sub>c C0\<^sub>c step\<^sub>c interference\<^sub>c vpeq\<^sub>c obs\<^sub>c dome\<^sub>c
                             ptran\<^sub>a petran\<^sub>a fin_com\<^sub>a \<Gamma>\<^sub>a C0\<^sub>a step\<^sub>a interference\<^sub>a vpeq\<^sub>a obs\<^sub>a dome\<^sub>a
                             sim_s sim_a
proof
  show "C0\<^sub>c \<sim> C0\<^sub>a"
    by (simp add: init_sim sim_s_def)
  show "\<And>a\<^sub>c a\<^sub>a C\<^sub>c C\<^sub>a C\<^sub>c'. sim_a a\<^sub>c = Some a\<^sub>a \<Longrightarrow> InfoFlow\<^sub>c.reachablec0 C\<^sub>c \<Longrightarrow> C\<^sub>c \<sim> C\<^sub>a \<Longrightarrow> 
        (C\<^sub>c, C\<^sub>c') \<in> step\<^sub>c a\<^sub>c \<Longrightarrow> \<exists>C\<^sub>a'. C\<^sub>c' \<sim> C\<^sub>a' \<and> (C\<^sub>a, C\<^sub>a') \<in> step\<^sub>a a\<^sub>a"
    using action_refine by auto
  show "\<And>a\<^sub>c C\<^sub>c C\<^sub>a C\<^sub>c'. sim_a a\<^sub>c = None \<Longrightarrow> InfoFlow\<^sub>c.reachablec0 C\<^sub>c \<Longrightarrow> C\<^sub>c \<sim> C\<^sub>a \<Longrightarrow> (C\<^sub>c, C\<^sub>c') \<in> step\<^sub>c a\<^sub>c 
        \<Longrightarrow> C\<^sub>c' \<sim> C\<^sub>a"
    using none_refine by blast
  show "interference\<^sub>c = interference\<^sub>a"
    by (simp add: intefere_same)
  show "\<And>a\<^sub>c a\<^sub>a. sim_a a\<^sub>c = Some a\<^sub>a \<longrightarrow> domain a\<^sub>c = domain a\<^sub>a"
    using dom_refine by presburger
  show "\<And>C\<^sub>c C\<^sub>a T\<^sub>c T\<^sub>a d. C\<^sub>c \<sim> C\<^sub>a \<Longrightarrow> T\<^sub>c \<sim> T\<^sub>a \<Longrightarrow> gets C\<^sub>a \<sim>\<^sub>ad\<sim>\<^sub>a gets T\<^sub>a = gets C\<^sub>c \<sim>\<^sub>cd\<sim>\<^sub>c gets T\<^sub>c "
    by (simp add: sim_ifs)
qed

end

end


