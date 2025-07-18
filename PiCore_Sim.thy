theory PiCore_Sim
  imports PiCore_Refine
begin


definition related_transitions_e:: "('s\<^sub>c \<times> 's\<^sub>c) set \<Rightarrow> ('s\<^sub>a \<times> 's\<^sub>a) set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>a) set \<Rightarrow> 
                                  (('s\<^sub>c \<times> 's\<^sub>c) \<times> ('s\<^sub>a \<times> 's\<^sub>a)) set" ("'(_, _')\<^sub>e\<^sub>_" )
  where "related_transitions_e R R' \<alpha> = {((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')). (\<sigma>,\<sigma>')\<in> R \<and> (\<Sigma>,\<Sigma>')\<in>R' 
                                      \<and>(\<sigma>, \<Sigma>) \<in> \<alpha> \<and> (\<sigma>', \<Sigma>') \<in> \<alpha>}"

definition Stable_e :: "('s\<^sub>c \<times> 's\<^sub>a) set \<Rightarrow> (('s\<^sub>c \<times> 's\<^sub>c) \<times> ('s\<^sub>a \<times> 's\<^sub>a)) set \<Rightarrow> bool" 
  where "Stable_e \<zeta> \<Delta> = (\<forall>\<sigma> \<sigma>' \<Sigma> \<Sigma>'. (\<sigma>, \<Sigma>) \<in> \<zeta> \<longrightarrow> ((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')) \<in> \<Delta> \<longrightarrow> (\<sigma>', \<Sigma>') \<in> \<zeta> )"

lemma stable_e_alpha: "Stable_e \<alpha> (related_transitions_e R R' \<alpha>)"
  by (simp add: Stable_e_def related_transitions_e_def)

lemma stable_e_conj: "\<lbrakk>Stable_e \<zeta>1 \<Delta>; Stable_e \<zeta>2 \<Delta>\<rbrakk> \<Longrightarrow> Stable_e (\<zeta>1 \<inter> \<zeta>2) \<Delta>"
  apply (simp add: Stable_e_def)
  by blast

definition rel_guard_eq :: "'s\<^sub>c set \<Rightarrow> 's\<^sub>a set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>a) set" ("_ \<rightleftharpoons>\<^sub>g _" [70, 70] 60)
  where "rel_guard_eq g\<^sub>c g\<^sub>a = {(\<sigma>, \<Sigma>). (\<sigma> \<in> g\<^sub>c) = (\<Sigma> \<in> g\<^sub>a)}"

definition rel_guard_and :: "'s\<^sub>c set \<Rightarrow> 's\<^sub>a set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>a) set" ("_\<and>\<^sub>g_" [70, 70] 60) 
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
                  ('s\<^sub>c \<times> 's\<^sub>a) set, 'prog\<^sub>c \<rightharpoonup> 'prog\<^sub>a, ('s\<^sub>c \<times> 's\<^sub>a) set,
                  'Env\<^sub>a, ('s\<^sub>a,'prog\<^sub>a) pconf, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool" 
  ("'(_,_,_,_')/ \<preceq>\<^sub>p \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>') /'(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81] 100)
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

                            (\<forall>s\<^sub>c' s\<^sub>a'. ((s\<^sub>c, s\<^sub>c'),(s\<^sub>a, s\<^sub>a')) \<in> ((R\<^sub>c \<union> Id, R\<^sub>a \<union> Id)\<^sub>e\<^sub>\<alpha>) \<longrightarrow> 
                            (\<Gamma>\<^sub>c, (P\<^sub>c, s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a'), R\<^sub>a, G\<^sub>a))" 
(*                          (P\<^sub>c \<noteq> fin_com\<^sub>c \<longrightarrow> P\<^sub>a \<noteq> fin_com\<^sub>a) \<and>   *)
begin

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
                  ('s\<^sub>c \<times> 's\<^sub>a) set, 'prog\<^sub>c \<rightharpoonup> 'prog\<^sub>a, ('s\<^sub>c \<times> 's\<^sub>a) set,
                  'Env\<^sub>a, ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) econf, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool" 
  ("'(_,_,_,_')/ \<preceq>\<^sub>e \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>') /'(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81] 100)
  where rgsim : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<alpha>; 
                  
                  \<forall>ec e\<^sub>c' x\<^sub>c' k. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-((EvtEnt ec)\<sharp>k)\<rightarrow> (e\<^sub>c', s\<^sub>c, x\<^sub>c')) \<longrightarrow> (\<exists>e\<^sub>a' x\<^sub>a' ea.
                  (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) -et-((EvtEnt ea)\<sharp>k)\<rightarrow> (e\<^sub>a', s\<^sub>a, x\<^sub>a')) \<and>
                  (\<Gamma>\<^sub>c, (e\<^sub>c', s\<^sub>c, x\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a', s\<^sub>a, x\<^sub>a'), R\<^sub>a, G\<^sub>a));

                  \<forall>Pc e\<^sub>c' s\<^sub>c' k. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-((Cmd Pc)\<sharp>k)\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c)) \<and> \<zeta> Pc = None \<longrightarrow> 
                  (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (\<Gamma>\<^sub>c, (e\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a) ;

                  \<forall>Pc e\<^sub>c' s\<^sub>c' Pa k. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-((Cmd Pc)\<sharp>k)\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c)) \<and> \<zeta> Pc = Some Pa \<longrightarrow> 
                  (\<exists>e\<^sub>a' s\<^sub>a'. 
                  (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) -et-((Cmd Pa)\<sharp>k)\<rightarrow> (e\<^sub>a', s\<^sub>a', x\<^sub>a)) \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> 
                  (\<Gamma>\<^sub>c, (e\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a', s\<^sub>a', x\<^sub>a), R\<^sub>a, G\<^sub>a));


                   e\<^sub>c = AnonyEvent fin_com\<^sub>c \<longrightarrow> e\<^sub>a = AnonyEvent fin_com\<^sub>a \<and> (s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<and> \<gamma> \<subseteq> \<alpha>;

                   \<forall>s\<^sub>c' s\<^sub>a' x\<^sub>c' x\<^sub>a'. ((s\<^sub>c, s\<^sub>c'),(s\<^sub>a, s\<^sub>a')) \<in> ((R\<^sub>c \<union> Id, R\<^sub>a \<union> Id)\<^sub>e\<^sub>\<alpha>) \<longrightarrow>
                   (\<Gamma>\<^sub>c, (e\<^sub>c, s\<^sub>c', x\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a, s\<^sub>a', x\<^sub>a'), R\<^sub>a, G\<^sub>a)      
                  \<rbrakk> \<Longrightarrow> (\<Gamma>\<^sub>c, (e\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)"

lemma e_sim_init :"(\<Gamma>\<^sub>c,(e\<^sub>c, s\<^sub>c, x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(e\<^sub>a, s\<^sub>a, x\<^sub>a),R\<^sub>a,G\<^sub>a) \<Longrightarrow> (s\<^sub>c, s\<^sub>a) \<in> \<alpha>"
  by (erule e_sim.cases, simp)

lemma e_sim_new_evt_occur_help : "(\<Gamma>\<^sub>c,(e\<^sub>c, s\<^sub>c, x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(e\<^sub>a, s\<^sub>a, x\<^sub>a),R\<^sub>a,G\<^sub>a) \<Longrightarrow> 
      \<forall>ec e\<^sub>c' x\<^sub>c' k. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-((EvtEnt ec)\<sharp>k)\<rightarrow> (e\<^sub>c', s\<^sub>c, x\<^sub>c')) \<longrightarrow> (\<exists>e\<^sub>a' x\<^sub>a' ea.
      (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) -et-((EvtEnt ea)\<sharp>k)\<rightarrow> (e\<^sub>a', s\<^sub>a, x\<^sub>a')) \<and>
      (\<Gamma>\<^sub>c, (e\<^sub>c', s\<^sub>c, x\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a', s\<^sub>a, x\<^sub>a'), R\<^sub>a, G\<^sub>a))"
  by (erule e_sim.cases, simp)

lemma e_sim_new_evt_occur: "\<lbrakk>(\<Gamma>\<^sub>c,(e\<^sub>c, s\<^sub>c, x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(\<eta> e\<^sub>c, s\<^sub>a, x\<^sub>a),R\<^sub>a,G\<^sub>a);
                             \<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-EvtEnt ec\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c, x\<^sub>c')\<rbrakk> \<Longrightarrow> 
                            \<exists>e\<^sub>a' x\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (\<eta> e\<^sub>c, s\<^sub>a, x\<^sub>a) -et-EvtEnt (\<eta> ec)\<sharp>k\<rightarrow> (e\<^sub>a', s\<^sub>a, x\<^sub>a')) 
       \<and> (\<Gamma>\<^sub>c,(e\<^sub>c', s\<^sub>c, x\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(e\<^sub>a', s\<^sub>a, x\<^sub>a'),R\<^sub>a,G\<^sub>a)"
proof-
  assume a0: "(\<Gamma>\<^sub>c,(e\<^sub>c, s\<^sub>c, x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(\<eta> e\<^sub>c, s\<^sub>a, x\<^sub>a),R\<^sub>a,G\<^sub>a)"
     and a1: "\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-EvtEnt ec\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c, x\<^sub>c')"
  then have "\<exists>e\<^sub>a' x\<^sub>a' ea. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (\<eta> e\<^sub>c, s\<^sub>a, x\<^sub>a) -et-((EvtEnt ea)\<sharp>k)\<rightarrow> (e\<^sub>a', s\<^sub>a, x\<^sub>a')) \<and>
            (\<Gamma>\<^sub>c, (e\<^sub>c', s\<^sub>c, x\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a', s\<^sub>a, x\<^sub>a'), R\<^sub>a, G\<^sub>a)"
    using e_sim_new_evt_occur_help by fastforce
  then obtain e\<^sub>a' x\<^sub>a' ea where a3: "(\<Gamma>\<^sub>a \<turnstile>\<^sub>a (\<eta> e\<^sub>c, s\<^sub>a, x\<^sub>a) -et-((EvtEnt ea)\<sharp>k)\<rightarrow> (e\<^sub>a', s\<^sub>a, x\<^sub>a')) \<and>
            (\<Gamma>\<^sub>c, (e\<^sub>c', s\<^sub>c, x\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a', s\<^sub>a, x\<^sub>a'), R\<^sub>a, G\<^sub>a)" by auto
  with a1 show ?thesis
    by (metis Event\<^sub>a.ent_spec1 Event\<^sub>c.ent_spec1)
qed

lemma e_sim_stutter_step: "\<lbrakk>\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-((Cmd Pc)\<sharp>k)\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c); \<zeta> Pc = None; 
       (\<Gamma>\<^sub>c,(e\<^sub>c, s\<^sub>c, x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(e\<^sub>a, s\<^sub>a, x\<^sub>a),R\<^sub>a,G\<^sub>a)\<rbrakk> \<Longrightarrow> 
       (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (\<Gamma>\<^sub>c, (e\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (erule e_sim.cases, simp)
  by metis

lemma e_sim_finish: "\<lbrakk>(\<Gamma>\<^sub>c,(e\<^sub>c, s\<^sub>c, x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(e\<^sub>a, s\<^sub>a, x\<^sub>a),R\<^sub>a,G\<^sub>a);
       e\<^sub>c = AnonyEvent fin_com\<^sub>c\<rbrakk> \<Longrightarrow> e\<^sub>a = AnonyEvent fin_com\<^sub>a  \<and> (s\<^sub>c, s\<^sub>a) \<in> \<gamma>"
  by (erule e_sim.cases, simp)

lemma e_sim_stutter_step_finish: "\<lbrakk>\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-((Cmd Pc)\<sharp>k)\<rightarrow> (AnonyEvent fin_com\<^sub>c, s\<^sub>c', x\<^sub>c); \<zeta> Pc = None; 
       (\<Gamma>\<^sub>c,(e\<^sub>c, s\<^sub>c, x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(e\<^sub>a, s\<^sub>a, x\<^sub>a),R\<^sub>a,G\<^sub>a)\<rbrakk> \<Longrightarrow> 
       e\<^sub>a = AnonyEvent fin_com\<^sub>a"
  apply (erule e_sim.cases, clarsimp)
  by (meson e_sim_finish)

lemma e_sim_corresponding_step: "\<lbrakk>\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-((Cmd Pc)\<sharp>k)\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c); \<zeta> Pc =  Some Pa; 
       (\<Gamma>\<^sub>c,(e\<^sub>c, s\<^sub>c, x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(e\<^sub>a, s\<^sub>a, x\<^sub>a),R\<^sub>a,G\<^sub>a)\<rbrakk> \<Longrightarrow> 
       (\<exists>e\<^sub>a' s\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) -et-((Cmd Pa)\<sharp>k)\<rightarrow> (e\<^sub>a', s\<^sub>a', x\<^sub>a)) \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> 
       (\<Gamma>\<^sub>c, (e\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a', s\<^sub>a', x\<^sub>a), R\<^sub>a, G\<^sub>a))"
  by (erule e_sim.cases, simp)

lemma e_sim_env_interf: "\<lbrakk>(\<Gamma>\<^sub>c,(e\<^sub>c, s\<^sub>c, x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(e\<^sub>a, s\<^sub>a, x\<^sub>a),R\<^sub>a,G\<^sub>a); 
      ((s\<^sub>c, s\<^sub>c'),(s\<^sub>a, s\<^sub>a')) \<in> (R\<^sub>c \<union> Id, R\<^sub>a \<union> Id)\<^sub>e\<^sub>\<alpha>\<rbrakk> \<Longrightarrow> 
      (\<Gamma>\<^sub>c, (e\<^sub>c, s\<^sub>c', x\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a, s\<^sub>a', x\<^sub>a'), R\<^sub>a, G\<^sub>a)"
  by (erule e_sim.cases, simp)

lemma AnonyEvt_Stutter_Step: "\<lbrakk>(\<Gamma>\<^sub>c,(P\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(P\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a); 
      \<Gamma>\<^sub>c \<turnstile>\<^sub>c (AnonyEvent P\<^sub>c, s\<^sub>c, x\<^sub>c) -et-Cmd Pc\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c); \<zeta> Pc = None\<rbrakk> 
      \<Longrightarrow> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (\<exists>P\<^sub>c'. e\<^sub>c' = AnonyEvent P\<^sub>c' \<and> (\<Gamma>\<^sub>c,(P\<^sub>c', s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(P\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a))"
proof-
  assume a0: "(\<Gamma>\<^sub>c,(P\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(P\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a)"
     and a1: "\<Gamma>\<^sub>c \<turnstile>\<^sub>c (AnonyEvent P\<^sub>c, s\<^sub>c, x\<^sub>c) -et-Cmd Pc\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c)"
     and a2: "\<zeta> Pc = None"
  from a1 have "(Pc = P\<^sub>c) \<and> (\<exists>P\<^sub>c'. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c')) \<and> e\<^sub>c' = AnonyEvent P\<^sub>c')"
    apply (rule Event\<^sub>c.etran.cases, simp_all)
    by (metis act.inject(1) actk.ext_inject get_actk_def)
  then obtain P\<^sub>c' where a3: "Pc = P\<^sub>c \<and> (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c')) \<and> e\<^sub>c' = AnonyEvent P\<^sub>c'" by auto
  with a0 a2 have "(s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (\<Gamma>\<^sub>c, (P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)"
    by (meson Event\<^sub>c.ptran'_def prog_sim_validity)
  then show ?thesis
    by (simp add: a3)
qed

lemma AnonyEvt_Corresponding_Step: "\<lbrakk>(\<Gamma>\<^sub>c,(P\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(P\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a); 
      \<Gamma>\<^sub>c \<turnstile>\<^sub>c (AnonyEvent P\<^sub>c, s\<^sub>c, x\<^sub>c) -et-Cmd Pc\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c); \<zeta> Pc = Some Pa\<rbrakk> 
      \<Longrightarrow> \<exists>e\<^sub>a' s\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (AnonyEvent P\<^sub>a, s\<^sub>a, x\<^sub>a) -et-Cmd Pa\<sharp>k\<rightarrow> (e\<^sub>a', s\<^sub>a', x\<^sub>a)) \<and>
          (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> (\<exists>P\<^sub>c. e\<^sub>c' = AnonyEvent P\<^sub>c \<and> (\<exists>P\<^sub>a'. e\<^sub>a' = AnonyEvent P\<^sub>a'
          \<and> (\<Gamma>\<^sub>c,(P\<^sub>c, s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(P\<^sub>a', s\<^sub>a'),R\<^sub>a,G\<^sub>a)))"
proof-
  assume a0: "(\<Gamma>\<^sub>c,(P\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(P\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a)"
     and a1: "\<Gamma>\<^sub>c \<turnstile>\<^sub>c (AnonyEvent P\<^sub>c, s\<^sub>c, x\<^sub>c) -et-Cmd Pc\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c)"
     and a2: "\<zeta> Pc = Some Pa"  
  from a1 have "Pc = P\<^sub>c \<and> (\<exists>P\<^sub>c'. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c')) \<and> e\<^sub>c' = AnonyEvent P\<^sub>c')"
    apply (rule Event\<^sub>c.etran.cases, simp_all)
    by (metis act.inject(1) actk.ext_inject get_actk_def)
  then obtain P\<^sub>c' where a3: "Pc = P\<^sub>c \<and> (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c')) \<and> e\<^sub>c' = AnonyEvent P\<^sub>c'" by auto
  with a0 have "\<zeta> P\<^sub>c = Some P\<^sub>a \<and> (\<exists>P\<^sub>a' s\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (P\<^sub>a, s\<^sub>a) -c\<rightarrow> (P\<^sub>a', s\<^sub>a'))
  \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> (\<Gamma>\<^sub>c, (P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a', s\<^sub>a'), R\<^sub>a, G\<^sub>a))"
    by (smt (verit, best) Event\<^sub>a.ptran'_def Event\<^sub>c.ptran'_def a2 option.distinct(1) prog_sim_validity)
  then obtain P\<^sub>a' s\<^sub>a' where a4: "\<zeta> P\<^sub>c = Some P\<^sub>a \<and> (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (P\<^sub>a, s\<^sub>a) -c\<rightarrow> (P\<^sub>a', s\<^sub>a')) \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c 
  \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> (\<Gamma>\<^sub>c, (P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a', s\<^sub>a'), R\<^sub>a, G\<^sub>a)" by auto
  with a2 a3 show ?thesis by (metis Event\<^sub>a.AnonyEvent option.inject)
qed

lemma AnonyEvt_None_lemma: "\<lbrakk>(\<Gamma>\<^sub>c, (e\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (AnonyEvent fin_com\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a);
                              \<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-act\<sharp>k \<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c') \<rbrakk> 
                             \<Longrightarrow> \<exists>P\<^sub>c. e\<^sub>c = AnonyEvent P\<^sub>c \<and> act = Cmd P\<^sub>c \<and> \<zeta>  P\<^sub>c = None"
  apply (erule Event\<^sub>c.etran.cases, simp add: get_actk_def)
   apply (case_tac "\<zeta> P", simp)
   apply (erule e_sim.cases, clarsimp)
   apply (drule_tac a = P and b = "AnonyEvent Q" and c = s\<^sub>c' and d = a and e = k in all5_impD)
    apply (simp add: Event\<^sub>c.AnonyEvent, clarify)
  using Event\<^sub>a.none_no_trane apply blast
  apply (erule e_sim.cases, clarsimp)
  by (meson Event\<^sub>a.none_no_trane Event\<^sub>c.EventEntry)

lemma AnonyEvt_Rule : "\<lbrakk>(\<Gamma>\<^sub>c, (P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)\<rbrakk>  \<Longrightarrow> 
       (\<Gamma>\<^sub>c, (AnonyEvent P\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (AnonyEvent P\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduction arbitrary: P\<^sub>c s\<^sub>c x\<^sub>c P\<^sub>a s\<^sub>a x\<^sub>a, clarsimp)
  apply (rule conjI)
  using prog_sim_validity apply blast
  apply (rule conjI)
   apply (metis Event\<^sub>c.EvtSeq1 Event\<^sub>c.EvtSeq2 Event\<^sub>c.ent_spec1 Event\<^sub>c.evtent_is_basicevt event.distinct(1))
  apply (rule conjI, clarsimp)
  apply (simp add: AnonyEvt_Stutter_Step)
  apply (rule conjI, clarsimp)
  using AnonyEvt_Corresponding_Step apply fastforce
  apply (rule conjI)
  using prog_sim_validity apply blast
  using prog_sim_validity by blast

(*
theorem BasicEvt_Rule: "\<lbrakk>\<xi> \<subseteq> g\<^sub>c \<rightleftharpoons>\<^sub>g g\<^sub>a; \<xi> \<subseteq> \<alpha>; Stable \<xi> ((R\<^sub>c \<union> Id, R\<^sub>a \<union> Id)\<^sub>\<alpha>); (s\<^sub>c, s\<^sub>a) \<in> \<xi>;
     P\<^sub>a \<noteq> fin_com\<^sub>a;
    \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<inter> (g\<^sub>c \<and>\<^sub>g g\<^sub>a) \<longrightarrow> (\<Gamma>\<^sub>c, (P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)\<rbrakk> \<Longrightarrow>
    (\<Gamma>\<^sub>c, (BasicEvent (l\<^sub>c, g\<^sub>c, P\<^sub>c), s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>)
    (\<Gamma>\<^sub>a, (BasicEvent (l\<^sub>a, g\<^sub>a, P\<^sub>a),s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduction arbitrary: P\<^sub>c s\<^sub>c x\<^sub>c P\<^sub>a s\<^sub>a x\<^sub>a, clarsimp)
  apply (rule conjI)
   apply blast
  apply (rule conjI, clarsimp)
   apply (erule Event\<^sub>c.etran.cases, simp_all, simp add: body_def  guard_def)
   apply auto[1]
   apply (rule_tac x = "AnonyEvent P\<^sub>a" and y = "x\<^sub>a(k := BasicEvent (l\<^sub>a, g\<^sub>a, P\<^sub>a))" in ex2I)
   apply (drule_tac a = s\<^sub>c and b = s\<^sub>a in all2_impD, simp add: rel_guard_and_def rel_guard_eq_def)
    apply blast
   apply (rule conjI)
    apply (rule_tac x = "BasicEvent (l\<^sub>a, g\<^sub>a, P\<^sub>a)" in exI)
    apply (smt (verit, best) CollectD Event\<^sub>a.basicevt_tran case_prodD rel_guard_eq_def subsetD)
   apply (rule AnonyEvt_Rule, simp_all)
  apply (rule conjI)
   apply (metis Event\<^sub>c.noevtent_notran0 act.simps(4))
  apply (rule conjI)
   apply (meson Event\<^sub>c.noevtent_notran0 act.distinct(1))
  by (meson Stable_def)
*)

theorem BasicEvt_Rule': "\<lbrakk>\<xi> \<subseteq> g\<^sub>c \<rightleftharpoons>\<^sub>g g\<^sub>a; \<xi> \<subseteq> \<alpha>; Stable_e \<xi> ((R\<^sub>c \<union> Id, R\<^sub>a \<union> Id)\<^sub>e\<^sub>\<alpha>); (s\<^sub>c, s\<^sub>a) \<in> \<xi>;
     P\<^sub>a \<noteq> fin_com\<^sub>a;
    \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<inter> (g\<^sub>c \<and>\<^sub>g g\<^sub>a) \<longrightarrow> (\<Gamma>\<^sub>c, (P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)\<rbrakk> \<Longrightarrow>
    (\<Gamma>\<^sub>c, (BasicEvent (l\<^sub>c, g\<^sub>c, P\<^sub>c), s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>)
    (\<Gamma>\<^sub>a, (BasicEvent (l\<^sub>a, g\<^sub>a, P\<^sub>a),s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduction arbitrary: P\<^sub>c s\<^sub>c x\<^sub>c P\<^sub>a s\<^sub>a x\<^sub>a, clarsimp)
  apply (rule conjI)
   apply blast
  apply (rule conjI, clarsimp)
   apply (erule Event\<^sub>c.etran.cases, simp_all, simp add: body_def  guard_def)
   apply auto[1]
   apply (rule_tac x = "AnonyEvent P\<^sub>a" and y = "x\<^sub>a(k := BasicEvent (l\<^sub>a, g\<^sub>a, P\<^sub>a))" in ex2I)
   apply (drule_tac a = s\<^sub>c and b = s\<^sub>a in all2_impD, simp add: rel_guard_and_def rel_guard_eq_def)
    apply blast
   apply (rule conjI)
    apply (rule_tac x = "BasicEvent (l\<^sub>a, g\<^sub>a, P\<^sub>a)" in exI)
    apply (smt (verit, best) CollectD Event\<^sub>a.basicevt_tran case_prodD rel_guard_eq_def subsetD)
   apply (rule AnonyEvt_Rule, simp_all)
  apply (rule conjI)
   apply (metis Event\<^sub>c.noevtent_notran0 act.simps(4))
  apply (rule conjI)
   apply (meson Event\<^sub>c.noevtent_notran0 act.distinct(1))
  by (meson Stable_e_def)

theorem BasicEvt_Rule: "\<lbrakk>Stable_e (g\<^sub>c \<rightleftharpoons>\<^sub>g g\<^sub>a) ((R\<^sub>c \<union> Id, R\<^sub>a \<union> Id)\<^sub>e\<^sub>\<alpha>); (s\<^sub>c, s\<^sub>a) \<in> ((g\<^sub>c \<rightleftharpoons>\<^sub>g g\<^sub>a) \<inter> \<alpha>);
     P\<^sub>a \<noteq> fin_com\<^sub>a;
    \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> (\<alpha> \<inter> (g\<^sub>c \<and>\<^sub>g g\<^sub>a)) \<longrightarrow> (\<Gamma>\<^sub>c, (P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)\<rbrakk> \<Longrightarrow>
    (\<Gamma>\<^sub>c, (BasicEvent (l\<^sub>c, g\<^sub>c, P\<^sub>c), s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>)
    (\<Gamma>\<^sub>a, (BasicEvent (l\<^sub>a, g\<^sub>a, P\<^sub>a),s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)"
  by (metis BasicEvt_Rule' Int_iff Int_lower1 Int_lower2 stable_e_alpha stable_e_conj)

coinductive es_sim :: "['Env\<^sub>c, ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) esconf, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
                  'k, ('s\<^sub>c \<times> 's\<^sub>a) set, 
                  ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) event \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) event, 
                  ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) event \<Rightarrow> 'prog\<^sub>c \<rightharpoonup> 'prog\<^sub>a,
                  'Env\<^sub>a, ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) esconf, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool" 
  ("'(_,_,_,_')/ \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>_ \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>') /'(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81,81] 100)
  where rgsim : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<alpha>;
                       
                  \<forall>e\<^sub>c es\<^sub>c' x\<^sub>c'. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (es\<^sub>c, s\<^sub>c, x\<^sub>c) -es-((EvtEnt e\<^sub>c)\<sharp>k)\<rightarrow> (es\<^sub>c', s\<^sub>c, x\<^sub>c')) \<longrightarrow>(\<exists> es\<^sub>a' x\<^sub>a'. 
                  (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (es\<^sub>a, s\<^sub>a, x\<^sub>a) -es-((EvtEnt (\<eta> e\<^sub>c))\<sharp>k)\<rightarrow> (es\<^sub>a', s\<^sub>a, x\<^sub>a')) \<and> 
                  (\<Gamma>\<^sub>c, (es\<^sub>c', s\<^sub>c, x\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a', s\<^sub>a, x\<^sub>a'), R\<^sub>a, G\<^sub>a));

                  \<forall>Pc es\<^sub>c' s\<^sub>c'. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (es\<^sub>c, s\<^sub>c, x\<^sub>c) -es-((Cmd Pc)\<sharp>k)\<rightarrow> (es\<^sub>c', s\<^sub>c', x\<^sub>c)) \<and> \<zeta> (x\<^sub>c k) Pc = None \<longrightarrow>
                  (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (\<Gamma>\<^sub>c, (es\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a);

                  \<forall>Pc es\<^sub>c' s\<^sub>c' Pa. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (es\<^sub>c, s\<^sub>c, x\<^sub>c) -es-((Cmd Pc)\<sharp>k)\<rightarrow> (es\<^sub>c', s\<^sub>c', x\<^sub>c)) \<and> \<zeta> (x\<^sub>c k) Pc = Some Pa \<longrightarrow>
                  \<eta> (x\<^sub>c k) = x\<^sub>a k \<and>
                  (\<exists>es\<^sub>a' s\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (es\<^sub>a, s\<^sub>a, x\<^sub>a) -es-((Cmd Pa)\<sharp>k)\<rightarrow> (es\<^sub>a', s\<^sub>a', x\<^sub>a)) \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a
                  \<and> (\<Gamma>\<^sub>c, (es\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a', s\<^sub>a', x\<^sub>a), R\<^sub>a, G\<^sub>a));

                 \<forall>s\<^sub>c' s\<^sub>a' x\<^sub>c' x\<^sub>a'. ((s\<^sub>c, s\<^sub>c'),(s\<^sub>a, s\<^sub>a')) \<in> ((R\<^sub>c \<union> Id, R\<^sub>a \<union> Id)\<^sub>e\<^sub>\<alpha>) \<longrightarrow>(x\<^sub>c' k = x\<^sub>c k \<and> x\<^sub>a' k = x\<^sub>a k)
                   \<longrightarrow> (\<Gamma>\<^sub>c, (es\<^sub>c, s\<^sub>c', x\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a, s\<^sub>a', x\<^sub>a'), R\<^sub>a, G\<^sub>a)\<rbrakk> 
        \<Longrightarrow> (\<Gamma>\<^sub>c, (es\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)"

lemma es_sim_init :"(\<Gamma>\<^sub>c, (es\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a) \<Longrightarrow> (s\<^sub>c, s\<^sub>a) \<in> \<alpha>"
  by (erule es_sim.cases, simp)

lemma es_new_evt_occur: "\<lbrakk>(\<Gamma>\<^sub>c, (es\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a);
       \<Gamma>\<^sub>c \<turnstile>\<^sub>c (es\<^sub>c, s\<^sub>c, x\<^sub>c) -es-((EvtEnt e\<^sub>c)\<sharp>k)\<rightarrow> (es\<^sub>c', s\<^sub>c, x\<^sub>c')\<rbrakk> \<Longrightarrow> \<exists> es\<^sub>a' x\<^sub>a'. 
                   (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (es\<^sub>a, s\<^sub>a, x\<^sub>a) -es-((EvtEnt (\<eta> e\<^sub>c))\<sharp>k)\<rightarrow> (es\<^sub>a', s\<^sub>a, x\<^sub>a')) \<and> 
                    (\<Gamma>\<^sub>c, (es\<^sub>c', s\<^sub>c, x\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a', s\<^sub>a, x\<^sub>a'), R\<^sub>a, G\<^sub>a)"
  by (erule es_sim.cases, simp)

lemma es_stutter_step: "\<lbrakk>(\<Gamma>\<^sub>c, (es\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a);
      (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (es\<^sub>c, s\<^sub>c, x\<^sub>c) -es-((Cmd Pc)\<sharp>k)\<rightarrow> (es\<^sub>c', s\<^sub>c', x\<^sub>c)) \<and> \<zeta> (x\<^sub>c k) Pc = None\<rbrakk> \<Longrightarrow>
      (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (\<Gamma>\<^sub>c, (es\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)"
  by (erule es_sim.cases, simp)

lemma es_corresponding_step: "\<lbrakk>(\<Gamma>\<^sub>c, (es\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a);
      (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (es\<^sub>c, s\<^sub>c, x\<^sub>c) -es-((Cmd Pc)\<sharp>k)\<rightarrow> (es\<^sub>c', s\<^sub>c', x\<^sub>c)) \<and> \<zeta> (x\<^sub>c k) Pc = Some Pa\<rbrakk> \<Longrightarrow>
      \<eta> (x\<^sub>c k) = x\<^sub>a k \<and>(\<exists>es\<^sub>a' s\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (es\<^sub>a, s\<^sub>a, x\<^sub>a) -es-((Cmd Pa)\<sharp>k)\<rightarrow> (es\<^sub>a', s\<^sub>a', x\<^sub>a)) \<and> 
      (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> (\<Gamma>\<^sub>c, (es\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a', s\<^sub>a', x\<^sub>a), R\<^sub>a, G\<^sub>a))"
  by (erule es_sim.cases, simp)

lemma es_env_interf: "\<lbrakk>(\<Gamma>\<^sub>c, (es\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a);
      ((s\<^sub>c, s\<^sub>c'),(s\<^sub>a, s\<^sub>a')) \<in> (R\<^sub>c \<union> Id, R\<^sub>a \<union> Id)\<^sub>e\<^sub>\<alpha>; x\<^sub>c' k = x\<^sub>c k \<and> x\<^sub>a' k = x\<^sub>a k\<rbrakk> \<Longrightarrow>
      (\<Gamma>\<^sub>c, (es\<^sub>c, s\<^sub>c', x\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a, s\<^sub>a', x\<^sub>a'), R\<^sub>a, G\<^sub>a)"
  by (erule es_sim.cases, simp)

lemma EvtSeq_None: "\<lbrakk>(\<Gamma>\<^sub>c, (e\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<sigma>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (AnonyEvent fin_com\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a);
      \<forall>s\<^sub>c s\<^sub>a x\<^sub>c x\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<longrightarrow> (\<Gamma>\<^sub>c, (es\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c)\<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a);
      \<zeta> (x\<^sub>c k) = \<sigma>\<rbrakk>  
      \<Longrightarrow> (\<Gamma>\<^sub>c, (EvtSeq e\<^sub>c es\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduction arbitrary: e\<^sub>c s\<^sub>c x\<^sub>c s\<^sub>a x\<^sub>a, clarsimp)
  apply (rule conjI, simp add: e_sim_init)
  apply (rule conjI, clarsimp)
   apply (erule Event\<^sub>c.estran.cases, simp)
    apply (metis Event\<^sub>a.none_no_trane e_sim_new_evt_occur_help esys.inject(1) prod.inject)
   apply (metis Event\<^sub>c.basicevt_not_tran_fin Event\<^sub>c.ent_spec1 snd_conv)
  apply (rule conjI, clarsimp)
   apply (erule Event\<^sub>c.estran.cases, simp)
    apply (metis AnonyEvt_None_lemma Pair_inject e_sim_stutter_step esys.inject(1))
  apply (metis AnonyEvt_None_lemma Pair_inject e_sim_finish e_sim_stutter_step esys.inject(1))
  apply (rule conjI, clarsimp)
   apply (erule Event\<^sub>c.estran.cases, simp)
    apply (metis Event\<^sub>a.none_no_trane Pair_inject Pair_inject e_sim_corresponding_step esys.inject(1))
   apply (metis Event\<^sub>a.none_no_trane Pair_inject Pair_inject e_sim_corresponding_step esys.inject(1))
  by (meson e_sim_env_interf)

lemma EvtSeq_AnonyEvt_Corresponding_Step: "\<lbrakk>(\<Gamma>\<^sub>c,(e\<^sub>c, s\<^sub>c, x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<sigma>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(e\<^sub>a, s\<^sub>a, x\<^sub>a),R\<^sub>a,G\<^sub>a);
      \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<longrightarrow> (\<forall>x\<^sub>c x\<^sub>a. (\<Gamma>\<^sub>c,(es\<^sub>c, s\<^sub>c, x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,(es\<^sub>a, s\<^sub>a, x\<^sub>a),R\<^sub>a,G\<^sub>a));
      \<zeta> (x\<^sub>c k) Pc = Some Pa; \<zeta> (x\<^sub>c k) = \<sigma>; e\<^sub>c' \<noteq> AnonyEvent fin_com\<^sub>c;
      \<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et- Cmd Pc\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c); e\<^sub>c' \<noteq> AnonyEvent fin_com\<^sub>c \<rbrakk> \<Longrightarrow>  
      \<exists>es\<^sub>a' s\<^sub>a'.
      \<Gamma>\<^sub>a \<turnstile>\<^sub>a (EvtSeq e\<^sub>a es\<^sub>a, s\<^sub>a, x\<^sub>a) -es-Cmd Pa\<sharp>k\<rightarrow> (es\<^sub>a', s\<^sub>a', x\<^sub>a) \<and>
      (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and>

      ((\<exists>e\<^sub>a. es\<^sub>a' = EvtSeq e\<^sub>a es\<^sub>a \<and> e\<^sub>a \<noteq> AnonyEvent fin_com\<^sub>a \<and> 
      (\<Gamma>\<^sub>c,(e\<^sub>c', s\<^sub>c', x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<sigma>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(e\<^sub>a, s\<^sub>a', x\<^sub>a),R\<^sub>a,G\<^sub>a)) 

      \<or> (\<Gamma>\<^sub>c,(EvtSeq e\<^sub>c' es\<^sub>c, s\<^sub>c', x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,(es\<^sub>a', s\<^sub>a', x\<^sub>a),R\<^sub>a,G\<^sub>a))"
proof-
  assume a0: "(\<Gamma>\<^sub>c,(e\<^sub>c, s\<^sub>c, x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<sigma>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(e\<^sub>a, s\<^sub>a, x\<^sub>a),R\<^sub>a,G\<^sub>a)"
     and a1: "\<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<longrightarrow> (\<forall>x\<^sub>c x\<^sub>a. (\<Gamma>\<^sub>c,(es\<^sub>c, s\<^sub>c, x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,(es\<^sub>a, s\<^sub>a, x\<^sub>a),R\<^sub>a,G\<^sub>a))"
     and a2: "\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et- Cmd Pc\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c)"
     and a3: "e\<^sub>c' \<noteq> AnonyEvent fin_com\<^sub>c"
     and a4: "\<zeta> (x\<^sub>c k) Pc = Some Pa"
     and a5: "\<zeta> (x\<^sub>c k) = \<sigma>"
  from a0 a2 a4 a5 have "(\<exists>e\<^sub>a' s\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) -et-((Cmd Pa)\<sharp>k)\<rightarrow> (e\<^sub>a', s\<^sub>a', x\<^sub>a)) 
                  \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> 
                  (\<Gamma>\<^sub>c, (e\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<sigma>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a', s\<^sub>a', x\<^sub>a), R\<^sub>a, G\<^sub>a))"
    by (simp add: e_sim_corresponding_step)
    
  then obtain e\<^sub>a' s\<^sub>a' where a6: "(\<Gamma>\<^sub>a \<turnstile>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) -et-((Cmd Pa)\<sharp>k)\<rightarrow> (e\<^sub>a', s\<^sub>a', x\<^sub>a)) 
                  \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> 
                  (\<Gamma>\<^sub>c, (e\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<sigma>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a', s\<^sub>a', x\<^sub>a), R\<^sub>a, G\<^sub>a)"
    by auto
  then show ?thesis
  proof(cases "e\<^sub>a' = AnonyEvent fin_com\<^sub>a")
    assume b0: "e\<^sub>a' = AnonyEvent fin_com\<^sub>a"
    with a6 have b1: "\<Gamma>\<^sub>a \<turnstile>\<^sub>a (EvtSeq e\<^sub>a es\<^sub>a, s\<^sub>a, x\<^sub>a) -es-Cmd Pa\<sharp>k\<rightarrow> (es\<^sub>a, s\<^sub>a', x\<^sub>a)"
      by (meson Event\<^sub>a.EvtSeq2)
    with a6 b0 have b2: "(\<Gamma>\<^sub>c, (e\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<sigma>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (AnonyEvent fin_com\<^sub>a, s\<^sub>a', x\<^sub>a), R\<^sub>a, G\<^sub>a)"
      by fastforce
    with a1 a5 have "(\<Gamma>\<^sub>c,(EvtSeq e\<^sub>c' es\<^sub>c, s\<^sub>c', x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,(es\<^sub>a, s\<^sub>a', x\<^sub>a),R\<^sub>a,G\<^sub>a)"
      by (simp add: EvtSeq_None)
    with a6 b1 show ?thesis by blast
  next
    assume c0: "e\<^sub>a' \<noteq> AnonyEvent fin_com\<^sub>a"
    with a6 have c1: "\<Gamma>\<^sub>a \<turnstile>\<^sub>a (EvtSeq e\<^sub>a es\<^sub>a, s\<^sub>a, x\<^sub>a) -es-Cmd Pa\<sharp>k\<rightarrow> (EvtSeq e\<^sub>a' es\<^sub>a, s\<^sub>a', x\<^sub>a)"
      by (simp add: Event\<^sub>a.EvtSeq1)
    with a6 c0 show ?thesis by blast
  qed
qed
     
lemma EvtSeq_AnonyEvt: "\<lbrakk>e\<^sub>a \<noteq> AnonyEvent fin_com\<^sub>a; is_anonyevt e\<^sub>c; \<zeta> (x\<^sub>c k) = \<sigma>; \<eta> (x\<^sub>c k) = x\<^sub>a k;
     (\<Gamma>\<^sub>c, (e\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<sigma>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a); 
      \<forall>s\<^sub>c s\<^sub>a x\<^sub>c x\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<longrightarrow> (\<Gamma>\<^sub>c, (es\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c)\<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)\<rbrakk> 
       \<Longrightarrow> (\<Gamma>\<^sub>c, (EvtSeq e\<^sub>c es\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (EvtSeq e\<^sub>a es\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduction arbitrary: e\<^sub>c s\<^sub>c x\<^sub>c e\<^sub>a s\<^sub>a x\<^sub>a, clarsimp)
  apply (rule conjI, simp add: e_sim_init)
  apply (rule conjI, clarsimp)
   apply (meson Event\<^sub>c.evtseq_no_evtent)
  apply (rule conjI, clarsimp)
   apply (erule Event\<^sub>c.estran.cases, simp, clarsimp)
    apply (metis Event\<^sub>c.no_tran2basic e_sim_stutter_step event.exhaust is_anonyevt.simps(1))
   apply (metis e_sim_stutter_step_finish esys.inject(1) fst_conv snd_conv)
  apply (rule conjI, clarsimp)
   apply (erule Event\<^sub>c.estran.cases, simp, clarsimp)
    apply (drule_tac s\<^sub>c' = s\<^sub>c' in EvtSeq_AnonyEvt_Corresponding_Step, simp_all)
     apply presburger
    apply (metis Event\<^sub>c.no_tran2basic event.exhaust is_anonyevt.simps(1))
   apply (metis (no_types, lifting) Event\<^sub>a.event_axioms e_sim_corresponding_step e_sim_finish event.EvtSeq2)
  by (meson e_sim_env_interf)

lemma EvtSeq_New_Evt_Occur: "\<lbrakk>(\<Gamma>\<^sub>c,(e\<^sub>c, s\<^sub>c, x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<sigma>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(\<eta> e\<^sub>c, s\<^sub>a, x\<^sub>a),R\<^sub>a,G\<^sub>a); 
      \<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-EvtEnt ec\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c, x\<^sub>c'); 
      \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<longrightarrow> (\<forall>x\<^sub>c x\<^sub>a. (\<Gamma>\<^sub>c,(es\<^sub>c, s\<^sub>c, x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,(es\<^sub>a, s\<^sub>a, x\<^sub>a),R\<^sub>a,G\<^sub>a));
      \<eta> e\<^sub>c = e\<^sub>a; \<zeta> e\<^sub>c = \<sigma>\<rbrakk> \<Longrightarrow> 
      \<exists>e\<^sub>a' x\<^sub>a'. 
      \<Gamma>\<^sub>a \<turnstile>\<^sub>a (EvtSeq (\<eta> e\<^sub>c) es\<^sub>a, s\<^sub>a, x\<^sub>a) -es-EvtEnt (\<eta> ec)\<sharp>k\<rightarrow> (EvtSeq e\<^sub>a' es\<^sub>a, s\<^sub>a, x\<^sub>a') \<and>
      (\<Gamma>\<^sub>c, (EvtSeq e\<^sub>c' es\<^sub>c, s\<^sub>c, x\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,(EvtSeq e\<^sub>a' es\<^sub>a, s\<^sub>a, x\<^sub>a'),R\<^sub>a,G\<^sub>a)"
proof-
  assume a0: "(\<Gamma>\<^sub>c,(e\<^sub>c, s\<^sub>c, x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<sigma>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(\<eta> e\<^sub>c, s\<^sub>a, x\<^sub>a),R\<^sub>a,G\<^sub>a)"
     and a1: "\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-EvtEnt ec\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c, x\<^sub>c')"
     and a2: "\<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<longrightarrow> (\<forall>x\<^sub>c x\<^sub>a. (\<Gamma>\<^sub>c,(es\<^sub>c, s\<^sub>c, x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,(es\<^sub>a, s\<^sub>a, x\<^sub>a),R\<^sub>a,G\<^sub>a))"
     and a3: "\<eta> e\<^sub>c = e\<^sub>a"
     and a4: "\<zeta> e\<^sub>c = \<sigma>"
  then have "\<exists>e\<^sub>a' x\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a ((\<eta> e\<^sub>c), s\<^sub>a, x\<^sub>a) -et-EvtEnt (\<eta> ec)\<sharp>k\<rightarrow> (e\<^sub>a', s\<^sub>a, x\<^sub>a')) \<and> 
            (\<Gamma>\<^sub>c,(e\<^sub>c', s\<^sub>c, x\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<sigma>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(e\<^sub>a', s\<^sub>a, x\<^sub>a'),R\<^sub>a,G\<^sub>a)"
    by (meson e_sim_new_evt_occur)
  then obtain e\<^sub>a' x\<^sub>a' where a5: " \<Gamma>\<^sub>a \<turnstile>\<^sub>a ((\<eta> e\<^sub>c), s\<^sub>a, x\<^sub>a) -et-EvtEnt (\<eta> ec)\<sharp>k\<rightarrow> (e\<^sub>a', s\<^sub>a, x\<^sub>a') \<and> 
            (\<Gamma>\<^sub>c,(e\<^sub>c', s\<^sub>c, x\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<sigma>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(e\<^sub>a', s\<^sub>a, x\<^sub>a'),R\<^sub>a,G\<^sub>a)" by auto
  then have a6: "e\<^sub>a' \<noteq> AnonyEvent fin_com\<^sub>a" 
    by (metis Event\<^sub>a.basicevt_not_tran_fin Event\<^sub>a.ent_spec1)
  from a1 have a7: "is_anonyevt e\<^sub>c'"
    by (metis Event\<^sub>c.no_tran2basic event.exhaust is_anonyevt.simps(1))
  from a1 have a80: "x\<^sub>c' k = e\<^sub>c"
    by (metis Event\<^sub>c.ent_spec1 Event\<^sub>c.entevt_ines_chg_selfx Event\<^sub>c.event_axioms event.EvtSeq1 event.basicevt_not_tran_fin)
  from a5 have a81: "x\<^sub>a' k = e\<^sub>a"
    by (metis Event\<^sub>a.ent_spec1 Event\<^sub>a.entevt_ines_chg_selfx Event\<^sub>a.event_axioms a3 a6 event.EvtSeq1)
  with a3 a4 a80 have a8: "\<zeta> (x\<^sub>c' k) = \<sigma> \<and> \<eta> (x\<^sub>c' k) = x\<^sub>a' k" by simp
  with a0 a2 a5 a6 a7 have "(\<Gamma>\<^sub>c, (EvtSeq e\<^sub>c' es\<^sub>c, s\<^sub>c, x\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,(EvtSeq e\<^sub>a' es\<^sub>a, s\<^sub>a, x\<^sub>a'),R\<^sub>a,G\<^sub>a)"
    by (meson EvtSeq_AnonyEvt)
  with a5 a6 show ?thesis
    by (meson Event\<^sub>a.EvtSeq1)
qed
    
theorem EvtSeq_rule: "\<lbrakk>(\<Gamma>\<^sub>c, (e\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<sigma>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a); is_basicevt e\<^sub>c;
                       \<forall>s\<^sub>c s\<^sub>a x\<^sub>c x\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<longrightarrow> (\<Gamma>\<^sub>c, (es\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c)\<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a);
                       \<eta> e\<^sub>c = e\<^sub>a; \<zeta> e\<^sub>c = \<sigma>\<rbrakk> \<Longrightarrow> (\<Gamma>\<^sub>c, (EvtSeq e\<^sub>c es\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (EvtSeq e\<^sub>a es\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduction arbitrary: e\<^sub>c s\<^sub>c x\<^sub>c e\<^sub>a s\<^sub>a x\<^sub>a, clarsimp)
  apply (rule conjI, simp add: e_sim_init)
  apply (rule conjI, clarsimp)
   apply (erule Event\<^sub>c.estran.cases, clarsimp)
    apply (drule_tac ec = e\<^sub>c' in EvtSeq_New_Evt_Occur, simp_all)
    apply blast
  apply (metis Event\<^sub>c.basicevt_not_tran_fin Event\<^sub>c.ent_spec1)
  apply (rule conjI)
   apply (metis Event\<^sub>c.evtseq_cmd_tran_anonyevt esys.inject(1) is_basicevt.simps(1))
  apply (rule conjI)
   apply (metis Event\<^sub>c.evtseq_cmd_tran_anonyevt esys.inject(1) is_basicevt.simps(1))
  by (meson e_sim_env_interf)

definition coPre :: "[('s\<^sub>c \<times> 's\<^sub>a) set, 'Env\<^sub>c, ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) event set, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
                  'k, ('s\<^sub>c \<times> 's\<^sub>a) set, 
                  ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) event \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) event, 
                  ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) event \<Rightarrow> 'prog\<^sub>c \<Rightarrow> 'prog\<^sub>a option,
                  'Env\<^sub>a, ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) event set, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set,
                  'Env\<^sub>c, ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) esconf, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set,
                  'k, ('s\<^sub>c \<times> 's\<^sub>a) set, 
                  ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) event \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) event, 
                  ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) event \<Rightarrow> 'prog\<^sub>c \<rightharpoonup> 'prog\<^sub>a,
                  'Env\<^sub>a, ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) esconf, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool"
  where "coPre \<gamma> \<Gamma>\<^sub>c es\<^sub>c R\<^sub>c G\<^sub>c k \<alpha> \<eta> \<zeta> \<Gamma>\<^sub>a es\<^sub>a R\<^sub>a G\<^sub>a \<Gamma>\<^sub>c' esconf\<^sub>c' R\<^sub>c' G\<^sub>c' k' \<alpha>' \<eta>' \<zeta>' \<Gamma>\<^sub>a' esconf\<^sub>a' R\<^sub>a' G\<^sub>a' \<equiv> 
         \<exists>s\<^sub>c s\<^sub>a x\<^sub>c x\<^sub>a e\<^sub>c e\<^sub>a.
         \<Gamma>\<^sub>c' = \<Gamma>\<^sub>c \<and> R\<^sub>c' = R\<^sub>c \<and> G\<^sub>c' = G\<^sub>c \<and> k' = k \<and> \<alpha>' = \<alpha> \<and> \<eta>' = \<eta> \<and> \<zeta>' = \<zeta> \<and> \<Gamma>\<^sub>a' = \<Gamma>\<^sub>a \<and> R\<^sub>a' = R\<^sub>a \<and> G\<^sub>a' = G\<^sub>a \<and>

         ((esconf\<^sub>c' = (EvtSeq e\<^sub>c (EvtSys es\<^sub>c), s\<^sub>c, x\<^sub>c) \<and> esconf\<^sub>a' = (EvtSeq e\<^sub>a (EvtSys es\<^sub>a), s\<^sub>a, x\<^sub>a) \<and>
          \<eta> (x\<^sub>c k) = x\<^sub>a k \<and> e\<^sub>a \<noteq> AnonyEvent fin_com\<^sub>a \<and> is_anonyevt e\<^sub>c \<and> is_anonyevt e\<^sub>a \<and>
          e_sim \<Gamma>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) R\<^sub>c G\<^sub>c \<alpha> (\<zeta> (x\<^sub>c k)) \<gamma> \<Gamma>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) R\<^sub>a G\<^sub>a) \<or>

          (esconf\<^sub>c' = (EvtSeq e\<^sub>c (EvtSys es\<^sub>c), s\<^sub>c, x\<^sub>c) \<and> esconf\<^sub>a' = ((EvtSys es\<^sub>a), s\<^sub>a, x\<^sub>a) \<and>
          is_anonyevt e\<^sub>c \<and>
          e_sim \<Gamma>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) R\<^sub>c G\<^sub>c \<alpha> (\<zeta> (x\<^sub>c k)) \<gamma> \<Gamma>\<^sub>a (AnonyEvent fin_com\<^sub>a, s\<^sub>a, x\<^sub>a) R\<^sub>a G\<^sub>a) \<or>

          (esconf\<^sub>c' = (EvtSys es\<^sub>c, s\<^sub>c, x\<^sub>c) \<and> esconf\<^sub>a' = (EvtSys es\<^sub>a, s\<^sub>a, x\<^sub>a) \<and> (s\<^sub>c, s\<^sub>a) \<in> \<gamma>)
         )
         "

lemma EvtSys_Sound_New_Evt_Occur: "\<lbrakk>\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-EvtEnt e\<^sub>c\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c, x\<^sub>c'); \<eta> e\<^sub>c \<in> es\<^sub>a;
          e_sim \<Gamma>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) R\<^sub>c G\<^sub>c \<alpha> (\<zeta> e\<^sub>c) \<gamma> \<Gamma>\<^sub>a (\<eta> e\<^sub>c, s\<^sub>a, x\<^sub>a) R\<^sub>a G\<^sub>a\<rbrakk> \<Longrightarrow> 
          \<exists>e\<^sub>a' x\<^sub>a'.
          \<Gamma>\<^sub>a \<turnstile>\<^sub>a (EvtSys es\<^sub>a, s\<^sub>a, x\<^sub>a) -es-EvtEnt (\<eta> e\<^sub>c)\<sharp>k\<rightarrow> (EvtSeq e\<^sub>a' (EvtSys es\<^sub>a), s\<^sub>a, x\<^sub>a') \<and>
          \<eta> (x\<^sub>c' k) = x\<^sub>a' k \<and> is_anonyevt e\<^sub>c' \<and> is_anonyevt e\<^sub>a' \<and> e\<^sub>a' \<noteq> AnonyEvent fin_com\<^sub>a \<and>
          e_sim \<Gamma>\<^sub>c (e\<^sub>c', s\<^sub>c, x\<^sub>c') R\<^sub>c G\<^sub>c \<alpha> (\<zeta> (x\<^sub>c' k)) \<gamma> \<Gamma>\<^sub>a (e\<^sub>a', s\<^sub>a, x\<^sub>a') R\<^sub>a G\<^sub>a"
proof-
  assume a0: "\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-EvtEnt e\<^sub>c\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c, x\<^sub>c')"
     and a1: "\<eta> e\<^sub>c \<in> es\<^sub>a"
     and a2: "e_sim \<Gamma>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) R\<^sub>c G\<^sub>c \<alpha> (\<zeta> e\<^sub>c) \<gamma> \<Gamma>\<^sub>a (\<eta> e\<^sub>c, s\<^sub>a, x\<^sub>a) R\<^sub>a G\<^sub>a"
  then have  "\<exists>e\<^sub>a' x\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (\<eta> e\<^sub>c, s\<^sub>a, x\<^sub>a) -et-EvtEnt (\<eta> e\<^sub>c)\<sharp>k\<rightarrow> (e\<^sub>a', s\<^sub>a, x\<^sub>a')) 
             \<and> (\<Gamma>\<^sub>c,(e\<^sub>c', s\<^sub>c, x\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta> e\<^sub>c\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(e\<^sub>a', s\<^sub>a, x\<^sub>a'),R\<^sub>a,G\<^sub>a)"
    by (simp add: e_sim_new_evt_occur)
  then obtain e\<^sub>a' x\<^sub>a' where a3: "(\<Gamma>\<^sub>a \<turnstile>\<^sub>a (\<eta> e\<^sub>c, s\<^sub>a, x\<^sub>a) -et-EvtEnt (\<eta> e\<^sub>c)\<sharp>k\<rightarrow> (e\<^sub>a', s\<^sub>a, x\<^sub>a')) 
             \<and> (\<Gamma>\<^sub>c,(e\<^sub>c', s\<^sub>c, x\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta> e\<^sub>c\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(e\<^sub>a', s\<^sub>a, x\<^sub>a'),R\<^sub>a,G\<^sub>a)"
    by auto
  then have a4: "e\<^sub>a' \<noteq> AnonyEvent fin_com\<^sub>a"
    by (metis Event\<^sub>a.basicevt_not_tran_fin Event\<^sub>a.ent_spec1)
  with a1 a3 have a5: "\<Gamma>\<^sub>a \<turnstile>\<^sub>a (EvtSys es\<^sub>a, s\<^sub>a, x\<^sub>a) -es-EvtEnt (\<eta> e\<^sub>c)\<sharp>k\<rightarrow> (EvtSeq e\<^sub>a' (EvtSys es\<^sub>a), s\<^sub>a, x\<^sub>a')"
    by (metis Event\<^sub>a.EvtOccur Event\<^sub>a.ent_spec1)
  from a0 a3 have a6: "is_anonyevt e\<^sub>c' \<and> is_anonyevt e\<^sub>a'"
    by (metis Event\<^sub>a.event_axioms Event\<^sub>c.event_axioms event.exhaust event.no_tran2basic0 is_anonyevt.simps(1))
  from a0 have a70: "x\<^sub>c' k = e\<^sub>c"
    by (metis Event\<^sub>c.EvtSeq1 Event\<^sub>c.basicevt_not_tran_fin Event\<^sub>c.entevt_ines_chg_selfx)
  from a5 have a71: "x\<^sub>a' k = \<eta> e\<^sub>c"
    by (simp add: Event\<^sub>a.entevt_ines_chg_selfx)
  with a70 have a7: "\<eta> (x\<^sub>c' k) = x\<^sub>a' k" by simp
  with a3 a4 a5 a6 a70 show ?thesis by blast
qed

lemma EvtSys_Sound_Not_Stutter: "\<lbrakk>e_sim \<Gamma>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) R\<^sub>c G\<^sub>c \<alpha> (\<zeta> (x\<^sub>c k)) \<gamma> \<Gamma>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) R\<^sub>a G\<^sub>a;
      \<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-Cmd Pc\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c); \<zeta> (x\<^sub>c k) Pc = Some Pa; \<eta> (x\<^sub>c k) = x\<^sub>a k\<rbrakk> \<Longrightarrow>
      
      \<exists>es\<^sub>a' s\<^sub>a'.

      \<Gamma>\<^sub>a \<turnstile>\<^sub>a (EvtSeq e\<^sub>a (EvtSys es\<^sub>a), s\<^sub>a, x\<^sub>a) -es-Cmd Pa\<sharp>k\<rightarrow> (es\<^sub>a', s\<^sub>a', x\<^sub>a) \<and> 
      (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> 

      ((\<exists>e\<^sub>a'. es\<^sub>a' = EvtSeq e\<^sub>a' (EvtSys es\<^sub>a) \<and> (\<eta> (x\<^sub>c k) = x\<^sub>a k \<and> e\<^sub>a' \<noteq> AnonyEvent fin_com\<^sub>a
      \<and> is_anonyevt e\<^sub>c' \<and> is_anonyevt e\<^sub>a'
      \<and> e_sim \<Gamma>\<^sub>c (e\<^sub>c', s\<^sub>c', x\<^sub>c) R\<^sub>c G\<^sub>c \<alpha> (\<zeta> (x\<^sub>c k)) \<gamma> \<Gamma>\<^sub>a (e\<^sub>a', s\<^sub>a', x\<^sub>a) R\<^sub>a G\<^sub>a)) \<or>

      (es\<^sub>a' =  EvtSys es\<^sub>a \<and> is_anonyevt e\<^sub>c' \<and> 
      e_sim \<Gamma>\<^sub>c (e\<^sub>c', s\<^sub>c', x\<^sub>c) R\<^sub>c G\<^sub>c \<alpha> (\<zeta> (x\<^sub>c k)) \<gamma> \<Gamma>\<^sub>a (AnonyEvent fin_com\<^sub>a, s\<^sub>a', x\<^sub>a) R\<^sub>a G\<^sub>a))"
proof-
  assume a0: "e_sim \<Gamma>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) R\<^sub>c G\<^sub>c \<alpha> (\<zeta> (x\<^sub>c k)) \<gamma> \<Gamma>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) R\<^sub>a G\<^sub>a"
     and a1: "\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-Cmd Pc\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c)"
     and a2: "\<zeta> (x\<^sub>c k) Pc = Some Pa"
     and a3: "\<eta> (x\<^sub>c k) = x\<^sub>a k"
  then have  "\<exists>e\<^sub>a' s\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) -et-Cmd Pa\<sharp>k\<rightarrow> (e\<^sub>a', s\<^sub>a', x\<^sub>a)) \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a
              \<and> e_sim \<Gamma>\<^sub>c (e\<^sub>c', s\<^sub>c', x\<^sub>c) R\<^sub>c G\<^sub>c \<alpha> (\<zeta> (x\<^sub>c k)) \<gamma>  \<Gamma>\<^sub>a (e\<^sub>a', s\<^sub>a', x\<^sub>a) R\<^sub>a G\<^sub>a"
    by (simp add: e_sim_corresponding_step)
  then obtain e\<^sub>a' s\<^sub>a' where a4: "(\<Gamma>\<^sub>a \<turnstile>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) -et-Cmd Pa\<sharp>k\<rightarrow> (e\<^sub>a', s\<^sub>a', x\<^sub>a)) \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a
                                 \<and> e_sim \<Gamma>\<^sub>c (e\<^sub>c', s\<^sub>c', x\<^sub>c) R\<^sub>c G\<^sub>c \<alpha> (\<zeta> (x\<^sub>c k)) \<gamma>  \<Gamma>\<^sub>a (e\<^sub>a', s\<^sub>a', x\<^sub>a) R\<^sub>a G\<^sub>a"
    by auto
  with a1 have a5: "is_anonyevt e\<^sub>c' \<and> is_anonyevt e\<^sub>a'"
    by (metis Event\<^sub>a.no_tran2basic Event\<^sub>c.no_tran2basic event.exhaust is_anonyevt.simps(1))
  then show ?thesis
  proof(cases "e\<^sub>a' = AnonyEvent fin_com\<^sub>a")
    assume b0: "e\<^sub>a' = AnonyEvent fin_com\<^sub>a"
    with a4 have b1: "\<Gamma>\<^sub>a \<turnstile>\<^sub>a (EvtSeq e\<^sub>a (EvtSys es\<^sub>a), s\<^sub>a, x\<^sub>a) -es-Cmd Pa\<sharp>k\<rightarrow> (EvtSys es\<^sub>a, s\<^sub>a', x\<^sub>a)"
      by (metis Event\<^sub>a.EvtSeq2)
    with a4 a5 b0 show ?thesis by blast
  next
    assume c0: "e\<^sub>a' \<noteq> AnonyEvent fin_com\<^sub>a"
    with a4 have c1: "\<Gamma>\<^sub>a \<turnstile>\<^sub>a (EvtSeq e\<^sub>a (EvtSys es\<^sub>a), s\<^sub>a, x\<^sub>a) -es-Cmd Pa\<sharp>k\<rightarrow> (EvtSeq e\<^sub>a' (EvtSys es\<^sub>a), s\<^sub>a', x\<^sub>a)"
      by (simp add: Event\<^sub>a.EvtSeq1 a3)
    with a3 a4 a5 c0 show ?thesis by blast
  qed
qed

lemma EvtSys_Sound_Not_Stutter_Finish: "\<lbrakk>e_sim \<Gamma>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) R\<^sub>c G\<^sub>c \<alpha> (\<zeta> (x\<^sub>c k)) \<gamma> \<Gamma>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) R\<^sub>a G\<^sub>a;
      \<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-Cmd Pc\<sharp>k\<rightarrow> (AnonyEvent fin_com\<^sub>c, s\<^sub>c', x\<^sub>c); \<zeta> (x\<^sub>c k) Pc = Some Pa\<rbrakk> \<Longrightarrow>
      
      \<exists>s\<^sub>a'.

      \<Gamma>\<^sub>a \<turnstile>\<^sub>a (EvtSeq e\<^sub>a (EvtSys es\<^sub>a), s\<^sub>a, x\<^sub>a) -es-Cmd Pa\<sharp>k\<rightarrow> (EvtSys es\<^sub>a, s\<^sub>a', x\<^sub>a) \<and> 
      (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and>  (s\<^sub>c', s\<^sub>a') \<in> \<gamma>"
proof-
  assume a0: "e_sim \<Gamma>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) R\<^sub>c G\<^sub>c \<alpha> (\<zeta> (x\<^sub>c k)) \<gamma> \<Gamma>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) R\<^sub>a G\<^sub>a"
     and a1: "\<zeta> (x\<^sub>c k) Pc = Some Pa"
     and a2: "\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-Cmd Pc\<sharp>k\<rightarrow> (AnonyEvent fin_com\<^sub>c, s\<^sub>c', x\<^sub>c)"
  then have  "\<exists>e\<^sub>a' s\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) -et-Cmd Pa\<sharp>k\<rightarrow> (e\<^sub>a', s\<^sub>a', x\<^sub>a)) \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a
              \<and> e_sim \<Gamma>\<^sub>c (AnonyEvent fin_com\<^sub>c, s\<^sub>c', x\<^sub>c) R\<^sub>c G\<^sub>c \<alpha> (\<zeta> (x\<^sub>c k)) \<gamma> \<Gamma>\<^sub>a (e\<^sub>a', s\<^sub>a', x\<^sub>a) R\<^sub>a G\<^sub>a"
    by (simp add: e_sim_corresponding_step)
  then obtain e\<^sub>a' s\<^sub>a' where a3: "(\<Gamma>\<^sub>a \<turnstile>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) -et-Cmd Pa\<sharp>k\<rightarrow> (e\<^sub>a', s\<^sub>a', x\<^sub>a)) \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a
              \<and> e_sim \<Gamma>\<^sub>c (AnonyEvent fin_com\<^sub>c, s\<^sub>c', x\<^sub>c) R\<^sub>c G\<^sub>c \<alpha> (\<zeta> (x\<^sub>c k)) \<gamma> \<Gamma>\<^sub>a (e\<^sub>a', s\<^sub>a', x\<^sub>a) R\<^sub>a G\<^sub>a"
    by auto
  then have a4: "e\<^sub>a' = AnonyEvent fin_com\<^sub>a \<and> (s\<^sub>c', s\<^sub>a') \<in> \<gamma>"
    using e_sim_finish by blast
  with a3 show ?thesis
    by (metis Event\<^sub>a.EvtSeq2)
qed

theorem EvtSys_rule: "\<lbrakk>\<forall>e\<^sub>c \<in> es\<^sub>c. is_basicevt e\<^sub>c;  \<forall>e\<^sub>c \<in> es\<^sub>c. \<eta> e\<^sub>c \<in> es\<^sub>a;
                      \<forall>s\<^sub>c s\<^sub>a x\<^sub>c x\<^sub>a e\<^sub>c. e\<^sub>c \<in> es\<^sub>c \<longrightarrow>(s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<longrightarrow>
                      e_sim \<Gamma>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) R\<^sub>c G\<^sub>c \<alpha> (\<zeta> e\<^sub>c) \<gamma> \<Gamma>\<^sub>a (\<eta> e\<^sub>c, s\<^sub>a, x\<^sub>a) R\<^sub>a G\<^sub>a;
                      (s\<^sub>c, s\<^sub>a) \<in> \<gamma>; \<gamma> \<subseteq> \<alpha>; Stable_e \<gamma> ((R\<^sub>c \<union> Id, R\<^sub>a \<union> Id)\<^sub>e\<^sub>\<alpha>)\<rbrakk> \<Longrightarrow> 
       (\<Gamma>\<^sub>c, (EvtSys es\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (EvtSys es\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduct taking: "coPre \<gamma> \<Gamma>\<^sub>c es\<^sub>c R\<^sub>c G\<^sub>c k \<alpha> \<eta> \<zeta> \<Gamma>\<^sub>a es\<^sub>a R\<^sub>a G\<^sub>a" rule:es_sim.coinduct)
   apply (simp add: coPre_def, clarsimp)
(* initial state *)
  apply (rule conjI, simp add: coPre_def, clarsimp)
   apply (meson e_sim_init subsetD)
  apply (rule conjI, clarsimp)
(* New event Occur *)
   apply (erule Event\<^sub>c.estran.cases, simp_all add: coPre_def)
(* EvtSys es\<^sub>c *)
     apply clarsimp
     apply (drule_tac e\<^sub>c = evt and es\<^sub>a = es\<^sub>a and R\<^sub>c = R\<^sub>c and G\<^sub>c = G\<^sub>c 
            and \<alpha> = \<alpha> and \<eta> = \<eta> and \<gamma> = \<gamma> and \<zeta> = \<zeta> and \<Gamma>\<^sub>a = \<Gamma>\<^sub>a and s\<^sub>a = ac and x\<^sub>a = ba and R\<^sub>a = R\<^sub>a 
            and G\<^sub>a = G\<^sub>a in EvtSys_Sound_New_Evt_Occur, simp_all)
      apply (simp add: get_actk_def, drule_tac a = aa and b = ac and c = x\<^sub>c and d = ba 
             and e = evt in all5_imp2D, simp_all)
     apply blast
(* EvtSys e\<^sub>c es\<^sub>c, impossible because is_anonyevt e\<^sub>c*)
    apply (metis Event\<^sub>c.EvtSeq1 Event\<^sub>c.evtseq_no_evtent)
   apply (metis Event\<^sub>c.basicevt_not_tran_fin Event\<^sub>c.ent_spec1)
  apply (rule conjI, clarsimp)
(* Stutter Steps *)
   apply (erule Event\<^sub>c.estran.cases, simp_all add: coPre_def)
(* EvtSys es\<^sub>c, impossible because e\<^sub>c \<in> es\<^sub>c \<longrightarrow> is_basicevt e\<^sub>c *)
     apply (metis Event\<^sub>c.cmd_enable_impl_notesys Event\<^sub>c.event_axioms event.EvtOccur)
(* EvtSys e\<^sub>c es\<^sub>c,  \<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-Cmd Pc\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c) \<and> e\<^sub>c' \<noteq> AnonyEvent fin_com\<^sub>c *)
    apply (rule conjI)
     apply (metis e_sim_stutter_step)
    apply auto[1]
       apply (metis Event\<^sub>c.no_tran2basic event.exhaust is_anonyevt.simps(1))
      apply (metis e_sim_stutter_step)
     apply (metis Event\<^sub>c.no_tran2basic event.exhaust is_anonyevt.simps(1))
    apply (metis e_sim_stutter_step)
(* EvtSys e\<^sub>c es\<^sub>c,  \<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-Cmd Pc\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c) \<and> e\<^sub>c' = AnonyEvent fin_com\<^sub>c *)
   apply (rule conjI)
    apply (metis e_sim_stutter_step)
   apply auto[1]
    apply (metis e_sim_stutter_step_finish)
   apply (metis e_sim_finish e_sim_stutter_step)
  apply (rule conjI, clarsimp)
(* Corresponding Steps *)
   apply (erule Event\<^sub>c.estran.cases, simp_all add: coPre_def)
    (* EvtSys es\<^sub>c, impossible because e\<^sub>c \<in> es\<^sub>c \<longrightarrow> is_basicevt e\<^sub>c *)
     apply (metis Event\<^sub>c.ev_tran_cmd_anony is_basicevt.simps(1))
    (* EvtSys e\<^sub>c es\<^sub>c,  \<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-Cmd Pc\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c) \<and> e\<^sub>c' \<noteq> AnonyEvent fin_com\<^sub>c *)
    apply (rule conjI)
     apply (metis Event\<^sub>a.none_no_trane e_sim_corresponding_step)
    apply auto[1]
     (* (\<Gamma>\<^sub>c,(e\<^sub>c, s\<^sub>c', x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(e\<^sub>a, s\<^sub>a', x\<^sub>a),R\<^sub>a,G\<^sub>a) *)
     apply (drule_tac Pc = Pc and e\<^sub>c' = e' and s\<^sub>c' = s\<^sub>c'' and Pa = Pa and es\<^sub>a = es\<^sub>a 
            in EvtSys_Sound_Not_Stutter, simp_all)
     apply blast
    (* (\<Gamma>\<^sub>c,(e\<^sub>c, s\<^sub>c', x\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>e\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(AnonyEvent fin_com\<^sub>a, s\<^sub>a', x\<^sub>a),R\<^sub>a,G\<^sub>a) *)
    apply (metis Event\<^sub>a.none_no_trane e_sim_corresponding_step)
    (* EvtSys e\<^sub>c es\<^sub>c,  \<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-Cmd Pc\<sharp>k\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c) \<and> e\<^sub>c' = AnonyEvent fin_com\<^sub>c *)
   apply (rule conjI)
    apply (metis Event\<^sub>a.none_no_trane e_sim_corresponding_step)
   apply auto[1]
    apply (metis EvtSys_Sound_Not_Stutter_Finish)
  apply (metis Event\<^sub>a.none_no_trane e_sim_corresponding_step)
(* Environmental Interference *)
   apply auto
    apply (meson e_sim_env_interf)
   apply (metis e_sim_env_interf)
  by (metis Stable_e_def)

coinductive pes_sim :: "['Env\<^sub>c, ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) pesconf, 
                  ('s\<^sub>c \<times> 's\<^sub>a) set, 
                  ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) event \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) event, 
                  ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) event \<Rightarrow> 'prog\<^sub>c \<rightharpoonup> 'prog\<^sub>a,
                  'Env\<^sub>a, ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) pesconf] \<Rightarrow> bool" 
  ("'(_,_')/ \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>') /'(_,_')" [81,81,81,81,81,81,81] 100)
  where rgsim : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<alpha>; 
                  
                  \<forall>ec pes\<^sub>c' x\<^sub>c' k. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c, s\<^sub>c, x\<^sub>c) -pes-((EvtEnt ec)\<sharp>k)\<rightarrow> (pes\<^sub>c', s\<^sub>c, x\<^sub>c')) \<longrightarrow>(\<exists>pes\<^sub>a' x\<^sub>a'. 
                  (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a, s\<^sub>a, x\<^sub>a) -pes-((EvtEnt (\<eta> ec))\<sharp>k)\<rightarrow> (pes\<^sub>a', s\<^sub>a, x\<^sub>a')) \<and> 
                  (\<Gamma>\<^sub>c, (pes\<^sub>c', s\<^sub>c, x\<^sub>c')) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a', s\<^sub>a, x\<^sub>a')));

                  \<forall>Pc pes\<^sub>c' s\<^sub>c' k. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c, s\<^sub>c, x\<^sub>c) -pes-((Cmd Pc)\<sharp>k)\<rightarrow> (pes\<^sub>c', s\<^sub>c', x\<^sub>c)) \<and> \<zeta> (x\<^sub>c k) Pc = None \<longrightarrow>
                  (\<Gamma>\<^sub>c, (pes\<^sub>c', s\<^sub>c', x\<^sub>c)) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a, s\<^sub>a, x\<^sub>a));

                  \<forall>Pc pes\<^sub>c' s\<^sub>c' k Pa. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c, s\<^sub>c, x\<^sub>c) -pes-((Cmd Pc)\<sharp>k)\<rightarrow> (pes\<^sub>c', s\<^sub>c', x\<^sub>c)) \<and> \<zeta> (x\<^sub>c k) Pc = Some Pa \<longrightarrow>
                  (\<exists>pes\<^sub>a' s\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a, s\<^sub>a, x\<^sub>a) -pes-((Cmd Pa)\<sharp>k)\<rightarrow> (pes\<^sub>a', s\<^sub>a', x\<^sub>a)) \<and> \<eta> (x\<^sub>c k) = (x\<^sub>a k)
                  \<and> (\<Gamma>\<^sub>c, (pes\<^sub>c', s\<^sub>c', x\<^sub>c)) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a', s\<^sub>a', x\<^sub>a))) 
     
                  \<rbrakk> \<Longrightarrow> (\<Gamma>\<^sub>c, (pes\<^sub>c, s\<^sub>c, x\<^sub>c)) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a, s\<^sub>a, x\<^sub>a))"

lemma pes_sim_init :"(\<Gamma>\<^sub>c, (pes\<^sub>c, s\<^sub>c, x\<^sub>c)) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a, s\<^sub>a, x\<^sub>a)) \<Longrightarrow> (s\<^sub>c, s\<^sub>a) \<in> \<alpha>"
  by (erule pes_sim.cases, simp)

lemma Pes_Sound_New_Evt_Occur: " \<lbrakk>\<forall>k. (\<Gamma>\<^sub>c,(pes\<^sub>c k, s\<^sub>c, x\<^sub>c),R\<^sub>c k,G\<^sub>c k) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,(pes\<^sub>a k, s\<^sub>a, x\<^sub>a),R\<^sub>a k,G\<^sub>a k);
      \<forall>i j. i \<noteq> j \<longrightarrow> G\<^sub>c i \<subseteq> R\<^sub>c j \<and> G\<^sub>a i \<subseteq> R\<^sub>a j; \<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c, s\<^sub>c, x\<^sub>c) -pes-EvtEnt e\<^sub>c\<sharp>k\<rightarrow> (pes\<^sub>c', s\<^sub>c, x\<^sub>c')\<rbrakk>
       \<Longrightarrow> \<exists>pes\<^sub>a' x\<^sub>a'.
            (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a, s\<^sub>a, x\<^sub>a) -pes-EvtEnt (\<eta> e\<^sub>c)\<sharp>k\<rightarrow> (pes\<^sub>a', s\<^sub>a, x\<^sub>a')) \<and>
            (\<forall>k. (\<Gamma>\<^sub>c,(pes\<^sub>c' k, s\<^sub>c, x\<^sub>c'),R\<^sub>c k,G\<^sub>c k) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,(pes\<^sub>a' k, s\<^sub>a, x\<^sub>a'),R\<^sub>a k,G\<^sub>a k))"
proof-
  assume a0: "\<forall>k. (\<Gamma>\<^sub>c,(pes\<^sub>c k, s\<^sub>c, x\<^sub>c),R\<^sub>c k,G\<^sub>c k) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,(pes\<^sub>a k, s\<^sub>a, x\<^sub>a),R\<^sub>a k,G\<^sub>a k)"
     and a1: "\<forall>i j. i \<noteq> j \<longrightarrow> G\<^sub>c i \<subseteq> R\<^sub>c j \<and> G\<^sub>a i \<subseteq> R\<^sub>a j"
     and a2: "\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c, s\<^sub>c, x\<^sub>c) -pes-EvtEnt e\<^sub>c\<sharp>k\<rightarrow> (pes\<^sub>c', s\<^sub>c, x\<^sub>c')"

  from a2 have "\<exists>es\<^sub>c'. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c k, s\<^sub>c, x\<^sub>c) -es-(EvtEnt e\<^sub>c\<sharp>k)\<rightarrow> (es\<^sub>c', s\<^sub>c, x\<^sub>c'))\<and> pes\<^sub>c' = (pes\<^sub>c(k := es\<^sub>c'))"
    by (simp add: Event\<^sub>c.pestran_estran)
  then obtain es\<^sub>c' where a3:"(\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c k, s\<^sub>c, x\<^sub>c) -es-(EvtEnt e\<^sub>c\<sharp>k)\<rightarrow> (es\<^sub>c', s\<^sub>c, x\<^sub>c'))\<and> pes\<^sub>c' = (pes\<^sub>c(k := es\<^sub>c'))"
    by blast
  then have a4: "\<forall>k'. k' \<noteq> k \<longrightarrow> x\<^sub>c k' = x\<^sub>c' k'"
    by (meson Event\<^sub>c.entevt_ines_notchg_otherx)
  from a0 a3 have "\<exists>es\<^sub>a' x\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a k, s\<^sub>a, x\<^sub>a) -es-(EvtEnt (\<eta> e\<^sub>c)\<sharp>k)\<rightarrow> (es\<^sub>a', s\<^sub>a, x\<^sub>a')) 
                    \<and> (\<Gamma>\<^sub>c, (es\<^sub>c', s\<^sub>c, x\<^sub>c'), R\<^sub>c k, G\<^sub>c k) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a', s\<^sub>a, x\<^sub>a'), R\<^sub>a k, G\<^sub>a k)"
    by (meson es_new_evt_occur)
  then obtain es\<^sub>a' x\<^sub>a' where a5: "(\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a k, s\<^sub>a, x\<^sub>a) -es-(EvtEnt (\<eta> e\<^sub>c)\<sharp>k)\<rightarrow> (es\<^sub>a', s\<^sub>a, x\<^sub>a'))
  \<and> (\<Gamma>\<^sub>c, (es\<^sub>c', s\<^sub>c, x\<^sub>c'), R\<^sub>c k, G\<^sub>c k) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a', s\<^sub>a, x\<^sub>a'), R\<^sub>a k, G\<^sub>a k)" by blast
  then have a6: "\<forall>k'. k' \<noteq> k \<longrightarrow> x\<^sub>a k' = x\<^sub>a' k'"
    by (meson Event\<^sub>a.entevt_ines_notchg_otherx)
  from a5 have a7: "\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a, s\<^sub>a, x\<^sub>a) -pes-EvtEnt (\<eta> e\<^sub>c)\<sharp>k\<rightarrow> (pes\<^sub>a(k := es\<^sub>a'), s\<^sub>a, x\<^sub>a')"
    by (meson Event\<^sub>a.pestran.intros a4)
  have "\<forall>j. (\<Gamma>\<^sub>c,(pes\<^sub>c' j, s\<^sub>c, x\<^sub>c'),R\<^sub>c j,G\<^sub>c j) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>j \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, ((pes\<^sub>a(k := es\<^sub>a')) j, s\<^sub>a, x\<^sub>a'),R\<^sub>a j,G\<^sub>a j)"
  proof-
    {
      fix j
      have "(\<Gamma>\<^sub>c,(pes\<^sub>c' j, s\<^sub>c, x\<^sub>c'),R\<^sub>c j,G\<^sub>c j) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>j \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, ((pes\<^sub>a(k := es\<^sub>a')) j, s\<^sub>a, x\<^sub>a'),R\<^sub>a j,G\<^sub>a j)"
      proof(case_tac "j = k")
        assume "j = k"
        with a3 a5 show ?thesis by simp
      next
        assume b0: "j \<noteq> k"
        with a0 a3 a4 have b1: "(\<Gamma>\<^sub>c,(pes\<^sub>c' j, s\<^sub>c, x\<^sub>c),R\<^sub>c j,G\<^sub>c j) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>j \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,((pes\<^sub>a(k := es\<^sub>a')) j, s\<^sub>a, x\<^sub>a),R\<^sub>a j,G\<^sub>a j)"
          by simp
        from b1 have "(s\<^sub>c, s\<^sub>a) \<in> \<alpha>"
          by (simp add: es_sim_init)
        then have b2: "((s\<^sub>c, s\<^sub>c),(s\<^sub>a, s\<^sub>a)) \<in> (R\<^sub>c j \<union> Id, R\<^sub>a j \<union> Id)\<^sub>e\<^sub>\<alpha>"
          by (simp add: related_transitions_e_def)
        from b0 a4 a6 have "x\<^sub>c j = x\<^sub>c' j \<and> x\<^sub>a j = x\<^sub>a' j" by auto
        with b1 b2 show ?thesis 
          by (metis es_env_interf)     
      qed 
    }
    then show ?thesis by auto
  qed

  with a7 show ?thesis by blast
qed

lemma Pes_Sound_Stutter_Step: "\<lbrakk>\<forall>k. (\<Gamma>\<^sub>c,(pes\<^sub>c k, s\<^sub>c, x\<^sub>c),R\<^sub>c k,G\<^sub>c k) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,(pes\<^sub>a k, s\<^sub>a, x\<^sub>a),R\<^sub>a k,G\<^sub>a k);
      \<forall>i j. i \<noteq> j \<longrightarrow> G\<^sub>c i \<subseteq> R\<^sub>c j \<and> G\<^sub>a i \<subseteq> R\<^sub>a j; \<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c, s\<^sub>c, x\<^sub>c) -pes-Cmd Pc\<sharp>k\<rightarrow> (pes\<^sub>c', s\<^sub>c', x\<^sub>c);
      \<zeta> (x\<^sub>c k) Pc = None\<rbrakk> \<Longrightarrow> \<forall>k. (\<Gamma>\<^sub>c,(pes\<^sub>c' k, s\<^sub>c', x\<^sub>c),R\<^sub>c k,G\<^sub>c k) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,(pes\<^sub>a k, s\<^sub>a, x\<^sub>a),R\<^sub>a k,G\<^sub>a k)"
proof-
  assume a0: "\<forall>k. (\<Gamma>\<^sub>c,(pes\<^sub>c k, s\<^sub>c, x\<^sub>c),R\<^sub>c k,G\<^sub>c k) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,(pes\<^sub>a k, s\<^sub>a, x\<^sub>a),R\<^sub>a k,G\<^sub>a k)"
     and a1: "\<forall>i j. i \<noteq> j \<longrightarrow> G\<^sub>c i \<subseteq> R\<^sub>c j \<and> G\<^sub>a i \<subseteq> R\<^sub>a j"
     and a2: "\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c, s\<^sub>c, x\<^sub>c) -pes-Cmd Pc\<sharp>k\<rightarrow> (pes\<^sub>c', s\<^sub>c', x\<^sub>c)"
     and a3: "\<zeta> (x\<^sub>c k) Pc = None"

  from a2 have "\<exists>es\<^sub>c'. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c k, s\<^sub>c, x\<^sub>c) -es-Cmd Pc\<sharp>k\<rightarrow> (pes\<^sub>c' k, s\<^sub>c', x\<^sub>c)) \<and> pes\<^sub>c' = pes\<^sub>c(k :=es\<^sub>c')"
    using Event\<^sub>c.pestran_estran by fastforce
  then obtain es\<^sub>c' where a4: "(\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c k, s\<^sub>c, x\<^sub>c) -es-Cmd Pc\<sharp>k\<rightarrow> (pes\<^sub>c' k, s\<^sub>c', x\<^sub>c)) \<and> pes\<^sub>c' = pes\<^sub>c(k :=es\<^sub>c')"
    by auto
  with a0 a3 have a5: "(s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c k \<and> (\<Gamma>\<^sub>c, (es\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c k, G\<^sub>c k) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a k, s\<^sub>a, x\<^sub>a), R\<^sub>a k, G\<^sub>a k)"
    by (metis es_stutter_step fun_upd_same)
  show ?thesis
  proof-
    {
      fix j
      have "(\<Gamma>\<^sub>c,(pes\<^sub>c' j, s\<^sub>c', x\<^sub>c),R\<^sub>c j,G\<^sub>c j) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>j \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,(pes\<^sub>a j, s\<^sub>a, x\<^sub>a),R\<^sub>a j,G\<^sub>a j)"
      proof(case_tac "j = k")
        assume "j = k"
        with a4 a5 show ?thesis by force
      next
        assume b0: "j \<noteq> k"
        with a0 a2 have b1: "(\<Gamma>\<^sub>c,(pes\<^sub>c' j, s\<^sub>c, x\<^sub>c),R\<^sub>c j,G\<^sub>c j) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>j \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,(pes\<^sub>a j, s\<^sub>a, x\<^sub>a),R\<^sub>a j,G\<^sub>a j)"
          using Event\<^sub>c.pestran_estran by fastforce
        from b1 have "(s\<^sub>c, s\<^sub>a) \<in> \<alpha>"
          by (simp add: es_sim_init)
        with a1 a5 b0 have b2: "((s\<^sub>c, s\<^sub>c'),(s\<^sub>a, s\<^sub>a)) \<in> (R\<^sub>c j \<union> Id, R\<^sub>a j \<union> Id)\<^sub>e\<^sub>\<alpha>"
          apply (simp add: related_transitions_e_def)
          by (metis es_sim_init subsetD)
        with b1 show ?thesis 
          using es_env_interf by fastforce
      qed
    }
    then show ?thesis by auto
  qed
qed

lemma Pes_Sound_Corresponding_Step: "\<lbrakk>\<forall>k. (\<Gamma>\<^sub>c,(pes\<^sub>c k, s\<^sub>c, x\<^sub>c),R\<^sub>c k,G\<^sub>c k) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,(pes\<^sub>a k, s\<^sub>a, x\<^sub>a),R\<^sub>a k,G\<^sub>a k);
       \<forall>i j. i \<noteq> j \<longrightarrow> G\<^sub>c i \<subseteq> R\<^sub>c j \<and> G\<^sub>a i \<subseteq> R\<^sub>a j;\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c, s\<^sub>c, x\<^sub>c) -pes-Cmd Pc\<sharp>k\<rightarrow> (pes\<^sub>c', s\<^sub>c', x\<^sub>c);
        \<zeta> (x\<^sub>c k) Pc = Some Pa\<rbrakk> \<Longrightarrow>
        \<exists>pes\<^sub>a' s\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a, s\<^sub>a, x\<^sub>a) -pes-Cmd Pa\<sharp>k\<rightarrow> (pes\<^sub>a', s\<^sub>a', x\<^sub>a)) \<and> \<eta> (x\<^sub>c k) = x\<^sub>a k \<and>
        (\<forall>k. (\<Gamma>\<^sub>c,(pes\<^sub>c' k, s\<^sub>c', x\<^sub>c),R\<^sub>c k,G\<^sub>c k) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,(pes\<^sub>a' k, s\<^sub>a', x\<^sub>a),R\<^sub>a k,G\<^sub>a k))"
proof-
  assume a0: "\<forall>k. (\<Gamma>\<^sub>c,(pes\<^sub>c k, s\<^sub>c, x\<^sub>c),R\<^sub>c k,G\<^sub>c k) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,(pes\<^sub>a k, s\<^sub>a, x\<^sub>a),R\<^sub>a k,G\<^sub>a k)"
     and a1: "\<forall>i j. i \<noteq> j \<longrightarrow> G\<^sub>c i \<subseteq> R\<^sub>c j \<and> G\<^sub>a i \<subseteq> R\<^sub>a j"
     and a2: "\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c, s\<^sub>c, x\<^sub>c) -pes-Cmd Pc\<sharp>k\<rightarrow> (pes\<^sub>c', s\<^sub>c', x\<^sub>c)"
     and a3: "\<zeta> (x\<^sub>c k) Pc = Some Pa"

  from a2 have "\<exists>es\<^sub>c'. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c k, s\<^sub>c, x\<^sub>c) -es-Cmd Pc\<sharp>k\<rightarrow> (pes\<^sub>c' k, s\<^sub>c', x\<^sub>c)) \<and> pes\<^sub>c' = pes\<^sub>c(k :=es\<^sub>c')"
    by (metis Event\<^sub>c.pestran_estran fun_upd_same)
  then obtain es\<^sub>c' where a4: "(\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c k, s\<^sub>c, x\<^sub>c) -es-Cmd Pc\<sharp>k\<rightarrow> (pes\<^sub>c' k, s\<^sub>c', x\<^sub>c)) \<and> pes\<^sub>c' = pes\<^sub>c(k :=es\<^sub>c')"
    by auto
  with a0 a3 have "  \<eta> (x\<^sub>c k) = x\<^sub>a k \<and> (\<exists>es\<^sub>a' s\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a k, s\<^sub>a, x\<^sub>a) -es-((Cmd Pa)\<sharp>k)\<rightarrow> (es\<^sub>a', s\<^sub>a', x\<^sub>a)) 
                     \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c k \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a k 
                     \<and> (\<Gamma>\<^sub>c, (es\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c k, G\<^sub>c k) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a', s\<^sub>a', x\<^sub>a), R\<^sub>a k, G\<^sub>a k))"
    using es_corresponding_step by fastforce
  then obtain es\<^sub>a' s\<^sub>a' where a5: "(\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a k, s\<^sub>a, x\<^sub>a) -es-((Cmd Pa)\<sharp>k)\<rightarrow> (es\<^sub>a', s\<^sub>a', x\<^sub>a)) 
                      \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c k \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a k \<and> \<eta> (x\<^sub>c k) = x\<^sub>a k \<and> 
                      (\<Gamma>\<^sub>c, (es\<^sub>c', s\<^sub>c', x\<^sub>c), R\<^sub>c k, G\<^sub>c k) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (es\<^sub>a', s\<^sub>a', x\<^sub>a), R\<^sub>a k, G\<^sub>a k)"
    by auto
  then have a6: "(\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a, s\<^sub>a, x\<^sub>a) -pes-((Cmd Pa)\<sharp>k)\<rightarrow> (pes\<^sub>a (k :=es\<^sub>a'), s\<^sub>a', x\<^sub>a))"
    by (simp add: Event\<^sub>a.pestran.intros)
  show ?thesis
  proof-
    {
      fix j
      have "(\<Gamma>\<^sub>c,(pes\<^sub>c' j, s\<^sub>c', x\<^sub>c),R\<^sub>c j,G\<^sub>c j) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>j \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,((pes\<^sub>a (k :=es\<^sub>a')) j, s\<^sub>a', x\<^sub>a),R\<^sub>a j,G\<^sub>a j)"
      proof(case_tac "j = k")
        assume "j = k"
        with a4 a5 show ?thesis by simp
      next
        assume b0: "j \<noteq> k"
        with a0 a2 have b1: "(\<Gamma>\<^sub>c,(pes\<^sub>c j, s\<^sub>c, x\<^sub>c),R\<^sub>c j,G\<^sub>c j) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>j \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a,((pes\<^sub>a (k :=es\<^sub>a')) j, s\<^sub>a, x\<^sub>a),R\<^sub>a j,G\<^sub>a j)"
          by simp
        from b1 have "(s\<^sub>c, s\<^sub>a) \<in> \<alpha>"
          by (simp add: es_sim_init)
        from a1 a5 b0 have b2: "((s\<^sub>c, s\<^sub>c'), (s\<^sub>a, s\<^sub>a')) \<in> (R\<^sub>c j \<union> Id, R\<^sub>a j \<union> Id)\<^sub>e\<^sub>\<alpha>"
          apply (simp add: related_transitions_e_def)
          by (metis (no_types, lifting) \<open>(s\<^sub>c, s\<^sub>a) \<in> \<alpha>\<close> es_sim_init subsetD)
        with a4 b0 b1 show ?thesis
          by (simp add: es_env_interf)
      qed
    }
    with a5 a6 show ?thesis  by blast
  qed
qed

theorem Pes_rule : "\<lbrakk>\<forall>k. (\<Gamma>\<^sub>c, (pes\<^sub>c k, s\<^sub>c, x\<^sub>c), (R\<^sub>c k), (G\<^sub>c k)) \<preceq>\<^sub>e\<^sub>s\<^sub>@\<^sub>k \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a k, s\<^sub>a, x\<^sub>a), (R\<^sub>a k), (G\<^sub>a k));
             \<forall>i j. i \<noteq> j \<longrightarrow> G\<^sub>c i \<subseteq> R\<^sub>c j \<and> G\<^sub>a i \<subseteq> R\<^sub>a j\<rbrakk> \<Longrightarrow> (\<Gamma>\<^sub>c, (pes\<^sub>c, s\<^sub>c, x\<^sub>c)) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a, s\<^sub>a, x\<^sub>a))"
  apply (coinduction arbitrary: pes\<^sub>c s\<^sub>c x\<^sub>c pes\<^sub>a s\<^sub>a x\<^sub>a, clarsimp)
  apply (rule conjI)
   apply (meson es_sim_init)
  apply (rule conjI)
  apply (metis Pes_Sound_New_Evt_Occur)
  apply (rule conjI)
   apply (metis Pes_Sound_Stutter_Step)
  apply clarsimp
  apply (drule_tac Pc = Pc  and pes\<^sub>c' = pes\<^sub>c' and s\<^sub>c' = s\<^sub>c' and Pa = Pa in Pes_Sound_Corresponding_Step)
     apply meson
    apply blast
   apply blast
  by blast

end
 
locale PiCore_Sim_IFS = 
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
  and \<zeta> :: "('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) event \<Rightarrow> 'prog\<^sub>c \<Rightarrow> 'prog\<^sub>a option"
assumes
  init_sim : "(\<Gamma>\<^sub>c, C0\<^sub>c) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, C0\<^sub>a)" and
  dom_sim : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<alpha>; \<eta> e\<^sub>c = e\<^sub>a \<rbrakk> \<Longrightarrow> dome\<^sub>c s\<^sub>c e\<^sub>c = dome\<^sub>a s\<^sub>a e\<^sub>a" and
  intefere_refine : "interference\<^sub>a \<preceq>\<^sub>p interference\<^sub>c" and
  sim_state_ifs : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<alpha>; (t\<^sub>c, t\<^sub>a) \<in> \<alpha>\<rbrakk> \<Longrightarrow> s\<^sub>a \<sim>\<^sub>a d \<sim>\<^sub>a t\<^sub>a = s\<^sub>c \<sim>\<^sub>c d \<sim>\<^sub>c t\<^sub>c"
begin

definition sim_s :: "('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) pesconf \<Rightarrow> ('l\<^sub>a, 'k, 's\<^sub>a, 'prog\<^sub>a) pesconf \<Rightarrow> bool" ("(_ \<sim> _)" [70,70] 60)
  where "C\<^sub>c \<sim> C\<^sub>a = (\<Gamma>\<^sub>c, C\<^sub>c) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, C\<^sub>a)"

fun sim_a :: "('l\<^sub>c, 'k, 's\<^sub>c, 'prog\<^sub>c, 'd) action \<Rightarrow> ('l\<^sub>a, 'k, 's\<^sub>a, 'prog\<^sub>a, 'd) action option"
  where "sim_a \<lparr>actk = \<lparr>Act = Cmd P\<^sub>c, K = k\<rparr>, eventof = e\<^sub>c, domain = d\<rparr> = 
         (if (\<zeta> e\<^sub>c P\<^sub>c = None) then None 
         else Some (let e\<^sub>a = \<eta> e\<^sub>c; P\<^sub>a = the (\<zeta> e\<^sub>c P\<^sub>c) in 
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
  with a0 have a4: "\<zeta> e\<^sub>c P\<^sub>c = None"
    by (metis option.discI sim_a.simps(1))

  obtain pes\<^sub>c s\<^sub>c x\<^sub>c pes\<^sub>c' s\<^sub>c' x\<^sub>c' where a5: "C\<^sub>c = (pes\<^sub>c ,s\<^sub>c ,x\<^sub>c) \<and> C\<^sub>c' = (pes\<^sub>c', s\<^sub>c', x\<^sub>c')" 
    by (meson Sim.Event\<^sub>c.pesconf_trip)
  with a2 a3 have a6: "(\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c ,s\<^sub>c ,x\<^sub>c) -pes-(Cmd P\<^sub>c)\<sharp>k \<rightarrow> (pes\<^sub>c', s\<^sub>c', x\<^sub>c')) \<and> (x\<^sub>c k = e\<^sub>c)"
    by (simp add: InfoFlow\<^sub>c.info_step_def get_actk_def getx_def)
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
    with a0 have "\<exists>P\<^sub>a. \<zeta> e\<^sub>c P\<^sub>c = Some P\<^sub>a"
      by (metis option.discI option.exhaust_sel sim_a.simps(1))
    then obtain P\<^sub>a where b1: "\<zeta> e\<^sub>c P\<^sub>c = Some P\<^sub>a" by auto
    with a0 b0 have b2: "a\<^sub>a = \<lparr>actk = \<lparr>Act = Cmd P\<^sub>a, K = k\<rparr>, eventof = \<eta> e\<^sub>c, domain = d\<rparr>" by auto

    obtain pes\<^sub>c s\<^sub>c x\<^sub>c pes\<^sub>c' s\<^sub>c' x\<^sub>c' where b3: "C\<^sub>c = (pes\<^sub>c ,s\<^sub>c ,x\<^sub>c) \<and> C\<^sub>c' = (pes\<^sub>c', s\<^sub>c', x\<^sub>c')" 
      by (meson Sim.Event\<^sub>c.pesconf_trip)
    with a2 b0 have b4: "(\<Gamma>\<^sub>c \<turnstile>\<^sub>c (pes\<^sub>c ,s\<^sub>c ,x\<^sub>c) -pes-(Cmd P\<^sub>c)\<sharp>k \<rightarrow> (pes\<^sub>c', s\<^sub>c', x\<^sub>c')) \<and> (x\<^sub>c k = e\<^sub>c) \<and> (dome\<^sub>c s\<^sub>c e\<^sub>c = d)"
      apply (simp add: InfoFlow\<^sub>c.info_step_def get_actk_def gets_def getx_def)
      by blast
    obtain pes\<^sub>a s\<^sub>a x\<^sub>a where b5: "C\<^sub>a = (pes\<^sub>a, s\<^sub>a, x\<^sub>a)" by (meson Sim.Event\<^sub>c.pesconf_trip)
    with a1 b1 b3 b4 have "\<exists>pes\<^sub>a' s\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a, s\<^sub>a, x\<^sub>a) -pes-((Cmd P\<^sub>a)\<sharp>k)\<rightarrow> (pes\<^sub>a', s\<^sub>a', x\<^sub>a))
    \<and> \<eta> (x\<^sub>c k) = (x\<^sub>a k) \<and> (\<Gamma>\<^sub>c, (pes\<^sub>c', s\<^sub>c', x\<^sub>c)) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a', s\<^sub>a', x\<^sub>a))"
      apply (simp add: sim_s_def)
      apply (erule Sim.pes_sim.cases, simp)
      by (metis Sim.Event\<^sub>c.act_in_pes_notchgstate)
    then obtain pes\<^sub>a' s\<^sub>a' where b6: "(\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a, s\<^sub>a, x\<^sub>a) -pes-((Cmd P\<^sub>a)\<sharp>k)\<rightarrow> (pes\<^sub>a', s\<^sub>a', x\<^sub>a))
    \<and> \<eta> (x\<^sub>c k) = (x\<^sub>a k) \<and> (\<Gamma>\<^sub>c, (pes\<^sub>c', s\<^sub>c', x\<^sub>c)) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a', s\<^sub>a', x\<^sub>a))" by auto

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
      using InfoFlow\<^sub>a.info_step_def by fastforce
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
      by (simp add: InfoFlow\<^sub>c.info_step_def get_actk_def gets_def getx_def)
    then have b5: "s\<^sub>c = s\<^sub>c'"
      by (metis Sim.Event\<^sub>c.evtent_in_pes_notchgstate)
    obtain pes\<^sub>a s\<^sub>a x\<^sub>a where b6: "C\<^sub>a = (pes\<^sub>a, s\<^sub>a, x\<^sub>a)" by (meson Sim.Event\<^sub>c.pesconf_trip)
    with a1 b3 b4 have "\<exists>e\<^sub>a pes\<^sub>a' x\<^sub>a'. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a, s\<^sub>a, x\<^sub>a) -pes-((EvtEnt e\<^sub>a)\<sharp>k)\<rightarrow> (pes\<^sub>a', s\<^sub>a, x\<^sub>a'))
    \<and> \<eta> e\<^sub>c = e\<^sub>a \<and> (\<Gamma>\<^sub>c, (pes\<^sub>c', s\<^sub>c, x\<^sub>c')) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a', s\<^sub>a, x\<^sub>a'))"
      apply (simp add: sim_s_def)
      apply (erule Sim.pes_sim.cases, simp)
      by (metis Sim.Event\<^sub>c.evtent_in_pes_notchgstate)
    then obtain pes\<^sub>a' x\<^sub>a' where b7: "(\<Gamma>\<^sub>a \<turnstile>\<^sub>a (pes\<^sub>a, s\<^sub>a, x\<^sub>a) -pes-((EvtEnt (\<eta> e\<^sub>c))\<sharp>k)\<rightarrow> (pes\<^sub>a', s\<^sub>a, x\<^sub>a'))
     \<and> (\<Gamma>\<^sub>c, (pes\<^sub>c', s\<^sub>c, x\<^sub>c')) \<preceq>\<^sub>p\<^sub>e\<^sub>s \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<eta>\<^sub>;\<^sub>\<zeta>\<^sub>) (\<Gamma>\<^sub>a, (pes\<^sub>a', s\<^sub>a, x\<^sub>a'))" by auto

    then have "(s\<^sub>c, s\<^sub>a) \<in> \<alpha>"
      using Sim.pes_sim_init by blast
    with b1 b4 b6 have "dome\<^sub>a (gets C\<^sub>a) (\<eta> e\<^sub>c) = domain a\<^sub>a"
      by (metis action.select_convs(3) dom_sim fst_conv gets_def snd_conv)
    with b1 have "actk a\<^sub>a = (EvtEnt (\<eta> e\<^sub>c))\<sharp>k \<and> eventof a\<^sub>a = \<eta> e\<^sub>c \<and> dome\<^sub>a (gets C\<^sub>a) (\<eta> e\<^sub>c) = domain a\<^sub>a"
      by (simp add: get_actk_def)
    with b6 b7 have "(C\<^sub>a, (pes\<^sub>a', s\<^sub>a, x\<^sub>a')) \<in> step\<^sub>a a\<^sub>a"
      using InfoFlow\<^sub>a.info_step_def by auto
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
  show "\<And>a\<^sub>c a\<^sub>a C\<^sub>c C\<^sub>a C\<^sub>c'. sim_a a\<^sub>c = Some a\<^sub>a \<Longrightarrow> C\<^sub>c \<sim> C\<^sub>a \<Longrightarrow> (C\<^sub>c, C\<^sub>c') \<in> step\<^sub>c a\<^sub>c \<Longrightarrow> \<exists>C\<^sub>a'. C\<^sub>c' \<sim> C\<^sub>a' \<and> (C\<^sub>a, C\<^sub>a') \<in> step\<^sub>a a\<^sub>a"
    using action_refine by auto
  show "\<And>a\<^sub>c C\<^sub>c C\<^sub>a C\<^sub>c'. sim_a a\<^sub>c = None \<Longrightarrow> C\<^sub>c \<sim> C\<^sub>a \<Longrightarrow> (C\<^sub>c, C\<^sub>c') \<in> step\<^sub>c a\<^sub>c \<Longrightarrow> C\<^sub>c' \<sim> C\<^sub>a"
    using none_refine by blast
  show "interference\<^sub>a \<preceq>\<^sub>p interference\<^sub>c"
    by (simp add: intefere_refine)
  show "\<And>a\<^sub>c a\<^sub>a. sim_a a\<^sub>c = Some a\<^sub>a \<longrightarrow> domain a\<^sub>c = domain a\<^sub>a"
    using dom_refine by presburger
  show "\<And>C\<^sub>c C\<^sub>a T\<^sub>c T\<^sub>a d. C\<^sub>c \<sim> C\<^sub>a \<Longrightarrow> T\<^sub>c \<sim> T\<^sub>a \<Longrightarrow> gets C\<^sub>a \<sim>\<^sub>ad\<sim>\<^sub>a gets T\<^sub>a = gets C\<^sub>c \<sim>\<^sub>cd\<sim>\<^sub>c gets T\<^sub>c "
    by (simp add: sim_ifs)
qed

theorem PiCore_abs_lr_imp: "InfoFlow\<^sub>a.local_respectC \<Longrightarrow> InfoFlow\<^sub>c.local_respectC"
  using PiCore_abs_lr_imp by force

theorem PiCore_abs_wsc_imp: "InfoFlow\<^sub>a.weak_step_consistentC \<Longrightarrow> InfoFlow\<^sub>c.weak_step_consistentC"
  using PiCore_abs_wsc_imp by auto

end

end


