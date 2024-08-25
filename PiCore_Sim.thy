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
  InfoFlow\<^sub>c: InfoFlow ptran\<^sub>c petran\<^sub>c fin_com\<^sub>c C0\<^sub>c step\<^sub>c interference\<^sub>c vpeq\<^sub>c obs\<^sub>c dome\<^sub>c +
  InfoFlow\<^sub>a: InfoFlow ptran\<^sub>a petran\<^sub>a fin_com\<^sub>a C0\<^sub>a step\<^sub>a interference\<^sub>a vpeq\<^sub>a obs\<^sub>a dome\<^sub>a
  for ptran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> (('prog\<^sub>c \<times> 's\<^sub>c) \<times> 'prog\<^sub>c \<times> 's\<^sub>c) set" 
  and petran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> 'prog\<^sub>c \<times> 's\<^sub>c \<Rightarrow> 'prog\<^sub>c \<times> 's\<^sub>c \<Rightarrow> bool" 
  and fin_com\<^sub>c :: "'prog\<^sub>c"
  and C0\<^sub>c  :: "('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) pesconf"
  and step\<^sub>c :: "('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c, 'd) action \<Rightarrow> (('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) pesconf \<times> ('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) pesconf) set"
  and interference\<^sub>c :: "'d \<Rightarrow> 'd \<Rightarrow> bool" 
  and vpeq\<^sub>c :: "'s\<^sub>c \<Rightarrow> 'd \<Rightarrow> 's\<^sub>c \<Rightarrow> bool" ("(_ \<sim>\<^sub>c_\<sim>\<^sub>c _)" [70,69,70] 60)
  and obs\<^sub>c :: "'s\<^sub>c \<Rightarrow> 'd \<Rightarrow> 'o\<^sub>c" 
  and dome\<^sub>c :: "'s\<^sub>c \<Rightarrow> ('l\<^sub>c, 'k\<^sub>c, 's\<^sub>c, 'prog\<^sub>c) event \<Rightarrow> 'd"
  and ptran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> (('prog\<^sub>a \<times> 's\<^sub>a) \<times> 'prog\<^sub>a \<times> 's\<^sub>a) set"
  and petran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> 'prog\<^sub>a \<times> 's\<^sub>a \<Rightarrow> 'prog\<^sub>a \<times> 's\<^sub>a \<Rightarrow> bool" 
  and fin_com\<^sub>a :: "'prog\<^sub>a"
  and C0\<^sub>a :: "('l\<^sub>a, 'k\<^sub>a, 's\<^sub>a, 'prog\<^sub>a) pesconf"
  and step\<^sub>a :: "('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a, 'd) action \<Rightarrow> (('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) pesconf \<times> ('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) pesconf) set" 
  and interference\<^sub>a :: "'d \<Rightarrow> 'd \<Rightarrow> bool" 
  and vpeq\<^sub>a ::  "'s\<^sub>a \<Rightarrow> 'd \<Rightarrow> 's\<^sub>a \<Rightarrow> bool" ("(_ \<sim>\<^sub>a_\<sim>\<^sub>a _)" [70,69,70] 60)
  and obs\<^sub>a :: "'s\<^sub>a \<Rightarrow> 'd \<Rightarrow> 'o\<^sub>a" 
  and dome\<^sub>a :: "'s\<^sub>a \<Rightarrow> ('l\<^sub>a, 'k\<^sub>a, 's\<^sub>a, 'prog\<^sub>a) event \<Rightarrow> 'd" +
fixes 
      sim_e :: "('l\<^sub>c, 'k\<^sub>c, 's\<^sub>c, 'prog\<^sub>c) event \<Rightarrow> ('l\<^sub>a, 'k\<^sub>a, 's\<^sub>a, 'prog\<^sub>a) event option"
  and prog_sim :: "['Env\<^sub>c, ('s\<^sub>c,'prog\<^sub>c) pconf, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
                  ('s\<^sub>c \<times> 's\<^sub>a) set, 'prog\<^sub>c \<Rightarrow> 'prog\<^sub>a option, ('s\<^sub>c \<times> 's\<^sub>a) set,
                  'Env\<^sub>a, ('s\<^sub>a,'prog\<^sub>a) pconf, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool" 
  ("'(_,_,_,_')/ \<preceq>\<^sub>p \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>') /'(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81] 100)
  and prog_sim_pre :: "['Env\<^sub>c, 'prog\<^sub>c, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
                  ('s\<^sub>c \<times> 's\<^sub>a) set, 'prog\<^sub>c \<Rightarrow> 'prog\<^sub>a option, ('s\<^sub>c \<times> 's\<^sub>a) set, ('s\<^sub>c \<times> 's\<^sub>a) set,
                  'Env\<^sub>a, 'prog\<^sub>a, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool" 
  ("'(_,_,_,_')/ \<preceq>\<^sub>p \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>\<rhd>\<^sub>_\<^sub>')  /'(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81,81] 100)
assumes
  all_evts_are_basic: "(\<forall>e \<in> all_evts (getspc C0\<^sub>c). is_basicevt e) \<and> 
                       (\<forall>e \<in> all_evts (getspc C0\<^sub>a). is_basicevt e)" and
  intefere_same : "interference\<^sub>c  = interference\<^sub>a" and 
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
  where "ptran\<^sub>c' \<equiv> InfoFlow\<^sub>c.ptran'"

abbreviation ptrans\<^sub>c :: "'Env\<^sub>c \<Rightarrow> ('s\<^sub>c,'prog\<^sub>c) pconf \<Rightarrow> ('s\<^sub>c,'prog\<^sub>c) pconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ c*\<rightarrow> _" [81,81] 80)
  where "ptrans\<^sub>c \<equiv> InfoFlow\<^sub>c.ptrans"

abbreviation etran\<^sub>c ::  "'Env\<^sub>c \<Rightarrow> ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) econf \<Rightarrow> ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) actk \<Rightarrow> 
                        ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) econf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ -et-_\<rightarrow> _" [81,81,81] 80)
  where "etran\<^sub>c \<equiv> InfoFlow\<^sub>c.etran"


abbreviation estran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) esconf \<Rightarrow> ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) actk \<Rightarrow> 
                        ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) esconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ -es-_\<rightarrow> _" [81,81] 80)
  where "estran\<^sub>c \<equiv> InfoFlow\<^sub>c.estran"

abbreviation pestran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) pesconf \<Rightarrow> ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) actk \<Rightarrow> 
                        ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) pesconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ -pes-_\<rightarrow> _" [70,70] 60)
  where "pestran\<^sub>c \<equiv> InfoFlow\<^sub>c.pestran"


abbreviation ptran\<^sub>a' :: "'Env\<^sub>a \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ -c\<rightarrow> _" [81,81] 80)
  where "ptran\<^sub>a' \<equiv> InfoFlow\<^sub>a.ptran'"

abbreviation ptrans\<^sub>a :: "'Env\<^sub>a \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ c*\<rightarrow> _" [81,81] 80)
  where "ptrans\<^sub>a \<equiv> InfoFlow\<^sub>a.ptrans"

abbreviation etran\<^sub>a ::  "'Env\<^sub>a \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) econf \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) actk \<Rightarrow> 
                        ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) econf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ -et-_\<rightarrow> _" [81,81,81] 80)
  where "etran\<^sub>a \<equiv> InfoFlow\<^sub>a.etran"


abbreviation estran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) esconf \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) actk \<Rightarrow> 
                        ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) esconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ -es-_\<rightarrow> _" [81,81] 80)
  where "estran\<^sub>a \<equiv> InfoFlow\<^sub>a.estran"

abbreviation pestran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) pesconf \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) actk \<Rightarrow> 
                        ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) pesconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ -pes-_\<rightarrow> _" [70,70] 60)
  where "pestran\<^sub>a \<equiv> InfoFlow\<^sub>a.pestran"

coinductive e_sim :: "['Env\<^sub>c, ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) econf, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
                  ('s\<^sub>c \<times> 's\<^sub>a) set, 'prog\<^sub>c \<Rightarrow> 'prog\<^sub>a option, ('s\<^sub>c \<times> 's\<^sub>a) set,
                  'Env\<^sub>a, ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) econf, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool" 
  ("'(_,_,_,_')/ \<preceq>\<^sub>e \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>') /'(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81] 100)
  where rgsim : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<alpha>; 
                  
                  (\<forall>ec e\<^sub>c' x\<^sub>c' k. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-((EvtEnt ec)\<sharp>k)\<rightarrow> (e\<^sub>c', s\<^sub>c, x\<^sub>c')) \<longrightarrow> (\<exists>ea e\<^sub>a' x\<^sub>a'.
                   (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) -et-((EvtEnt ea)\<sharp>k)\<rightarrow> (e\<^sub>a', s\<^sub>a, x\<^sub>a')) \<and>
                   (\<Gamma>\<^sub>c, (e\<^sub>c', s\<^sub>c, x\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a', s\<^sub>a, x\<^sub>a'), R\<^sub>a, G\<^sub>a))) \<and>

                   (\<forall>Pc e\<^sub>c' s\<^sub>c' k. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-((Cmd Pc)\<sharp>k)\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c)) \<and> \<zeta> Pc = None \<longrightarrow> 
                   (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (\<Gamma>\<^sub>c, (e\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)) \<and>

                  (\<forall>Pc e\<^sub>c' s\<^sub>c' k Pa. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-((Cmd Pc)\<sharp>k)\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c)) \<and> \<zeta> Pc = Some Pa \<longrightarrow> 
                   (\<exists>e\<^sub>a' s\<^sub>a'. 
                   (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) -et-((Cmd Pa)\<sharp>k)\<rightarrow> (e\<^sub>a', s\<^sub>a', x\<^sub>a)) \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> 
                   (\<Gamma>\<^sub>c, (e\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a', s\<^sub>a', x\<^sub>a), R\<^sub>a, G\<^sub>a))) \<and>


                   (e\<^sub>c = AnonyEvent fin_com\<^sub>c \<longrightarrow> e\<^sub>a = AnonyEvent fin_com\<^sub>a \<and> (s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<and> \<gamma> \<subseteq> \<alpha>) \<and> 

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
    apply (rule InfoFlow\<^sub>c.etran.cases, simp_all)
    by (metis act.inject(1) actk.ext_inject get_actk_def)
  then obtain P\<^sub>c' where a3: "Pc = P\<^sub>c \<and> \<Gamma>\<^sub>c \<turnstile>\<^sub>c (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c') \<and> e\<^sub>c' = AnonyEvent P\<^sub>c'" by auto
  with a0 a2 have "(s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (\<Gamma>\<^sub>c, (P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)"
    by (meson InfoFlow\<^sub>c.ptran'_def prog_sim_validity)
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
    apply (rule InfoFlow\<^sub>c.etran.cases, simp_all)
    by (metis act.inject(1) actk.ext_inject get_actk_def)
  then obtain P\<^sub>c' where a3: "Pc = P\<^sub>c \<and> \<Gamma>\<^sub>c \<turnstile>\<^sub>c (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c') \<and> e\<^sub>c' = AnonyEvent P\<^sub>c'" by auto
  with a0 have "\<zeta> P\<^sub>c = Some P\<^sub>a \<and> (\<exists>P\<^sub>a' s\<^sub>a'. \<Gamma>\<^sub>a \<turnstile>\<^sub>a (P\<^sub>a, s\<^sub>a) -c\<rightarrow> (P\<^sub>a', s\<^sub>a')
  \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> (\<Gamma>\<^sub>c, (P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a', s\<^sub>a'), R\<^sub>a, G\<^sub>a))"
    by (smt (verit, best) InfoFlow\<^sub>a.ptran'_def InfoFlow\<^sub>c.ptran'_def a2 option.distinct(1) prog_sim_validity)
  then obtain P\<^sub>a' s\<^sub>a' where a4: "\<zeta> P\<^sub>c = Some P\<^sub>a \<and> \<Gamma>\<^sub>a \<turnstile>\<^sub>a (P\<^sub>a, s\<^sub>a) -c\<rightarrow> (P\<^sub>a', s\<^sub>a')\<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c 
  \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> (\<Gamma>\<^sub>c, (P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a', s\<^sub>a'), R\<^sub>a, G\<^sub>a)" by auto
  with a2 a3 show ?thesis by (metis InfoFlow\<^sub>a.AnonyEvent option.inject)
qed

lemma AnonyEvt_Sound_lemma : "(\<Gamma>\<^sub>c, (P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)  \<Longrightarrow>
       (\<Gamma>\<^sub>c, (AnonyEvent P\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (AnonyEvent P\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduction arbitrary: P\<^sub>c s\<^sub>c x\<^sub>c P\<^sub>a s\<^sub>a x\<^sub>a, clarsimp)
  apply (rule conjI)
  using prog_sim_validity apply blast
  apply (rule conjI)
   apply (metis InfoFlow\<^sub>c.EvtSeq1 InfoFlow\<^sub>c.EvtSeq2 InfoFlow\<^sub>c.ent_spec1 InfoFlow\<^sub>c.evtent_is_basicevt event.distinct(1))
  apply (rule conjI, clarsimp)
  apply (simp add: AnonyEvt_Sound_help1)
  apply (rule conjI, clarsimp)
  using AnonyEvt_Sound_help2 apply fastforce
  apply (rule conjI)
  using prog_sim_validity apply blast
  using prog_sim_validity by blast


thm prog_sim_pre_validity

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
    apply (rule InfoFlow\<^sub>c.etran.cases, simp_all)
    using guard_def body_def by (metis fstI sndI)
  with a1 a2 have a7 : "s\<^sub>a \<in> g\<^sub>a" 
    by (smt (verit, ccfv_SIG) CollectD case_prodE fst_conv rel_guard_eq_def snd_conv subsetD)
  with a5 have a8: "\<Gamma>\<^sub>a \<turnstile>\<^sub>a (BasicEvent (l\<^sub>a, g\<^sub>a, P\<^sub>a), s\<^sub>a, x\<^sub>a) -et-EvtEnt (BasicEvent (l\<^sub>a, g\<^sub>a, P\<^sub>a))\<sharp>k\<rightarrow> 
                   (AnonyEvent P\<^sub>a, s\<^sub>a, x\<^sub>a(k := BasicEvent (l\<^sub>a, g\<^sub>a, P\<^sub>a)))"
    by (rule_tac InfoFlow\<^sub>a.EventEntry, simp_all add: body_def guard_def)
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
   apply (meson InfoFlow\<^sub>c.noevtent_notran0 act.distinct(1))
  apply (rule conjI, clarsimp)
   apply (meson InfoFlow\<^sub>c.noevtent_notran0 act.distinct(1))
  by (meson Stable_def)



end


