theory PiCore_Sim
  imports PiCore_Refine
begin


definition related_transitions:: "('s\<^sub>c \<times> 's\<^sub>c) set \<Rightarrow> ('s\<^sub>a \<times> 's\<^sub>a) set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>a) set \<Rightarrow> 
                                  (('s\<^sub>c \<times> 's\<^sub>c) \<times> ('s\<^sub>a \<times> 's\<^sub>a)) set" ("'(_, _')\<^sub>_")
  where "related_transitions R R' \<alpha> = {((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')). (\<sigma>,\<sigma>')\<in> R \<and> (\<Sigma>,\<Sigma>')\<in>R' 
                                      \<and>(\<sigma>, \<Sigma>) \<in> \<alpha> \<and> (\<sigma>', \<Sigma>') \<in> \<alpha>}"

thm related_transitions_def
locale event_sim_validity = 
   event\<^sub>c: event ptran\<^sub>c petran\<^sub>c fin_com\<^sub>c + 
   event\<^sub>a: event ptran\<^sub>a petran\<^sub>a fin_com\<^sub>a
for ptran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> (('s\<^sub>c,'prog\<^sub>c) pconf \<times> ('s\<^sub>c,'prog\<^sub>c) pconf) set" 
and petran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> ('s\<^sub>c,'prog\<^sub>c) pconf \<Rightarrow> ('s\<^sub>c,'prog\<^sub>c) pconf \<Rightarrow> bool"
and fin_com\<^sub>c :: "'prog\<^sub>c"
and ptran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> (('s\<^sub>a,'prog\<^sub>a) pconf \<times> ('s\<^sub>a,'prog\<^sub>a) pconf) set" 
and petran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> bool"
and fin_com\<^sub>a :: "'prog\<^sub>a" +
fixes prog_sim :: "['Env\<^sub>c, ('s\<^sub>c,'prog\<^sub>c) pconf, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
                  ('s\<^sub>c \<times> 's\<^sub>a) set, 'prog\<^sub>c \<Rightarrow> 'prog\<^sub>a option, ('s\<^sub>c \<times> 's\<^sub>a) set,
                  'Env\<^sub>a, ('s\<^sub>a,'prog\<^sub>a) pconf, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool" 
  ("'(_,_,_,_')/ \<preceq>\<^sub>p \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>') /'(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81] 100)
assumes prog_sim_validity: "(\<Gamma>\<^sub>c, (P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a) \<Longrightarrow>
                            (s\<^sub>c, s\<^sub>a) \<in> \<alpha> \<and>

                            (((P\<^sub>c, s\<^sub>c), (P\<^sub>c', s\<^sub>c')) \<in> ptran\<^sub>c \<Gamma>\<^sub>c \<and> \<zeta> P\<^sub>c = None \<longrightarrow> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> 
                            (\<Gamma>\<^sub>c, (P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)) \<and>

                            (((P\<^sub>c, s\<^sub>c), (P\<^sub>c', s\<^sub>c')) \<in> ptran\<^sub>c \<Gamma>\<^sub>c \<and> \<zeta> P\<^sub>c = Some P\<^sub>a \<longrightarrow> (\<exists>P\<^sub>a' s\<^sub>a'. 
                            ((P\<^sub>a, s\<^sub>a), (P\<^sub>a', s\<^sub>a')) \<in> ptran\<^sub>a \<Gamma>\<^sub>a \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and>
                            (\<Gamma>\<^sub>c, (P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a', s\<^sub>a'), R\<^sub>a, G\<^sub>a))) \<and>
                      
                            (P\<^sub>c = fin_com\<^sub>c \<longrightarrow> P\<^sub>a = fin_com\<^sub>a \<and> (s\<^sub>c, s\<^sub>a) \<in> \<gamma>) \<and> 

                            (((s\<^sub>c, s\<^sub>c'), (s\<^sub>a, s\<^sub>a')) \<in> (R\<^sub>c, R\<^sub>a \<union> Id)\<^sub>\<alpha> \<longrightarrow> 
                            (\<Gamma>\<^sub>c, (P\<^sub>c, s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a'), R\<^sub>a, G\<^sub>a))"
begin


abbreviation ptran\<^sub>c' :: "'Env\<^sub>c \<Rightarrow> ('s\<^sub>c,'prog\<^sub>c) pconf \<Rightarrow> ('s\<^sub>c,'prog\<^sub>c) pconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ -c\<rightarrow> _" [81,81] 80)
  where "ptran\<^sub>c' \<equiv> event\<^sub>c.ptran'"

abbreviation ptrans\<^sub>c :: "'Env\<^sub>c \<Rightarrow> ('s\<^sub>c,'prog\<^sub>c) pconf \<Rightarrow> ('s\<^sub>c,'prog\<^sub>c) pconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ c*\<rightarrow> _" [81,81] 80)
  where "ptrans\<^sub>c \<equiv> event\<^sub>c.ptrans"

abbreviation etran\<^sub>c ::  "'Env\<^sub>c \<Rightarrow> ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) econf \<Rightarrow> ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) actk \<Rightarrow> 
                        ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) econf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ -et-_\<rightarrow> _" [81,81,81] 80)
  where "etran\<^sub>c \<equiv> event\<^sub>c.etran"


abbreviation estran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) esconf \<Rightarrow> ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) actk \<Rightarrow> 
                        ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) esconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ -es-_\<rightarrow> _" [81,81] 80)
  where "estran\<^sub>c \<equiv> event\<^sub>c.estran"

abbreviation pestran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) pesconf \<Rightarrow> ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) actk \<Rightarrow> 
                        ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) pesconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ -pes-_\<rightarrow> _" [70,70] 60)
  where "pestran\<^sub>c \<equiv> event\<^sub>c.pestran"


abbreviation ptran\<^sub>a' :: "'Env\<^sub>a \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ -c\<rightarrow> _" [81,81] 80)
  where "ptran\<^sub>a' \<equiv> event\<^sub>a.ptran'"

abbreviation ptrans\<^sub>a :: "'Env\<^sub>a \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ c*\<rightarrow> _" [81,81] 80)
  where "ptrans\<^sub>a \<equiv> event\<^sub>a.ptrans"

abbreviation etran\<^sub>a ::  "'Env\<^sub>a \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) econf \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) actk \<Rightarrow> 
                        ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) econf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ -et-_\<rightarrow> _" [81,81,81] 80)
  where "etran\<^sub>a \<equiv> event\<^sub>a.etran"


abbreviation estran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) esconf \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) actk \<Rightarrow> 
                        ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) esconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ -es-_\<rightarrow> _" [81,81] 80)
  where "estran\<^sub>a \<equiv> event\<^sub>a.estran"

abbreviation pestran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) pesconf \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) actk \<Rightarrow> 
                        ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) pesconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ -pes-_\<rightarrow> _" [70,70] 60)
  where "pestran\<^sub>a \<equiv> event\<^sub>a.pestran"

inductive e_sim_validity :: "['Env\<^sub>c, ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) econf, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
                  ('s\<^sub>c \<times> 's\<^sub>a) set, ('l\<^sub>c,'k,'s\<^sub>c,'prog\<^sub>c) act \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) act option, ('s\<^sub>c \<times> 's\<^sub>a) set,
                  'Env\<^sub>a, ('l\<^sub>a,'k,'s\<^sub>a,'prog\<^sub>a) econf, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool" 
  ("'(_,_,_,_')/ \<preceq>\<^sub>e \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>') /'(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81] 100)
  where rgsim : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<alpha>; 
                  
                  ((\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-(a\<^sub>c\<sharp>k)\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c')) \<and> \<zeta> a\<^sub>c = None \<longrightarrow> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and>
                   (\<Gamma>\<^sub>c, (e\<^sub>c', s\<^sub>c', x\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)) \<and>

                  ((\<Gamma>\<^sub>c \<turnstile>\<^sub>c (e\<^sub>c, s\<^sub>c, x\<^sub>c) -et-(a\<^sub>c\<sharp>k)\<rightarrow> (e\<^sub>c', s\<^sub>c', x\<^sub>c')) \<and> \<zeta> a\<^sub>c = Some a\<^sub>a \<longrightarrow> (\<exists>e\<^sub>a s\<^sub>a x\<^sub>a. 
                   (\<Gamma>\<^sub>a \<turnstile>\<^sub>a (e\<^sub>a, s\<^sub>a, x\<^sub>a) -et-(a\<^sub>a\<sharp>k)\<rightarrow> (e\<^sub>a', s\<^sub>a', x\<^sub>a')) \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> 
                   (\<Gamma>\<^sub>c, (e\<^sub>c', s\<^sub>c', x\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a', s\<^sub>a', x\<^sub>a'), R\<^sub>a, G\<^sub>a))) \<and>

                   (e\<^sub>c = AnonyEvent fin_com\<^sub>c \<longrightarrow> e\<^sub>a = AnonyEvent fin_com\<^sub>a \<and> (s\<^sub>c, s\<^sub>a) \<in> \<gamma>) \<and> 

                   (((s\<^sub>c, s\<^sub>c'), (s\<^sub>a, s\<^sub>a')) \<in> (R\<^sub>c, R\<^sub>a \<union> Id)\<^sub>\<alpha> \<longrightarrow> 
                     (\<Gamma>\<^sub>c, (e\<^sub>c, s\<^sub>c', x\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a, s\<^sub>a', x\<^sub>a'), R\<^sub>a, G\<^sub>a))      
                  \<rbrakk> \<Longrightarrow> (\<Gamma>\<^sub>c, (e\<^sub>c, s\<^sub>c, x\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (e\<^sub>a, s\<^sub>a, x\<^sub>a), R\<^sub>a, G\<^sub>a)"





