theory PiCore_SIMP_Ref
  imports "../PiCore_Sim" Ref_SIMP
begin

typedecl SIMP_Env\<^sub>c
typedecl SIMP_Env\<^sub>a
type_synonym 'a prog = "('a com) option"

abbreviation ptranI\<^sub>c :: "SIMP_Env\<^sub>c \<Rightarrow> ('s\<^sub>c conf \<times> 's\<^sub>c conf) set"
  where "ptranI\<^sub>c \<Gamma>\<^sub>c \<equiv> ctran"

abbreviation petranI\<^sub>c :: "SIMP_Env\<^sub>c \<Rightarrow> 's\<^sub>c conf \<Rightarrow> 's\<^sub>c conf \<Rightarrow> bool "
  where "petranI\<^sub>c \<Gamma>\<^sub>c \<equiv> etran'"

abbreviation ptranI\<^sub>a :: "SIMP_Env\<^sub>a \<Rightarrow> ('s\<^sub>a conf \<times> 's\<^sub>a conf) set"
  where "ptranI\<^sub>a \<Gamma>\<^sub>a \<equiv> ctran"

abbreviation petranI\<^sub>a :: "SIMP_Env\<^sub>a \<Rightarrow> 's\<^sub>a conf \<Rightarrow> 's\<^sub>a conf \<Rightarrow> bool "
  where "petranI\<^sub>a \<Gamma>\<^sub>a \<equiv> etran'"

coinductive prog_simI :: "[SIMP_Env\<^sub>c, 's\<^sub>c conf, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
                  ('s\<^sub>c \<times> 's\<^sub>a) set, 's\<^sub>c prog \<rightharpoonup> 's\<^sub>a prog, ('s\<^sub>c \<times> 's\<^sub>a) set,
                  SIMP_Env\<^sub>a, 's\<^sub>a conf, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool" 
  ("'(_,_,_,_')/ \<preceq>\<^sub>p\<^sub>I \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>') /'(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81] 100) 
  where rgsim : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<alpha>;

                 (\<forall>P\<^sub>c' s\<^sub>c'. (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c') \<and> \<zeta> P\<^sub>c = None \<longrightarrow> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> 
                 (\<Gamma>\<^sub>c, (P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p\<^sub>I \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a));

                 (\<forall>P\<^sub>c' s\<^sub>c'. (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c') \<and> \<zeta> P\<^sub>c \<noteq> None \<longrightarrow> 
                 (\<zeta> P\<^sub>c = Some P\<^sub>a \<and> (\<exists>P\<^sub>a' s\<^sub>a'. 
                 (P\<^sub>a, s\<^sub>a) -c\<rightarrow> (P\<^sub>a', s\<^sub>a') \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and>
                 (\<Gamma>\<^sub>c, (P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p\<^sub>I \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a', s\<^sub>a'), R\<^sub>a, G\<^sub>a))));

                  (P\<^sub>c = None \<longrightarrow> P\<^sub>a = None \<and> (s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<and> \<gamma> \<subseteq> \<alpha>); 

                  (\<forall>s\<^sub>c' s\<^sub>a'. ((s\<^sub>c, s\<^sub>c'),(s\<^sub>a, s\<^sub>a')) \<in> ((R\<^sub>c \<union> Id, R\<^sub>a \<union> Id)\<^sub>\<alpha>) \<longrightarrow> 
                  (\<Gamma>\<^sub>c, (P\<^sub>c, s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p\<^sub>I \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a'), R\<^sub>a, G\<^sub>a))
                                   
                  \<rbrakk> \<Longrightarrow> (\<Gamma>\<^sub>c, (P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p\<^sub>I \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)"


fun zetaI :: "('s\<^sub>c com \<rightharpoonup> 's\<^sub>a com) \<Rightarrow> ('s\<^sub>c prog \<rightharpoonup> 's\<^sub>a prog)"
  where "zetaI \<zeta> None = None"
  | "zetaI \<zeta> (Some C\<^sub>c) = (if (\<zeta> C\<^sub>c) = None then None else Some (\<zeta> C\<^sub>c))"

lemma zetaI_None: "zetaI \<zeta> (Some C\<^sub>c) = None \<Longrightarrow> \<zeta> C\<^sub>c = None"
  by (metis option.distinct(1) zetaI.simps(2))

lemma zetaI_Some: "zetaI \<zeta> (Some C\<^sub>c) = Some (Some C\<^sub>a) \<Longrightarrow> \<zeta> C\<^sub>c = Some C\<^sub>a"
  by (metis option.discI option.sel zetaI.simps(2))

theorem sim_implies_simI: "\<lbrakk>((P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a); \<zeta>\<^sub>1 = zetaI \<zeta> \<rbrakk> 
            \<Longrightarrow> (\<Gamma>\<^sub>c, (P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p\<^sub>I \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduction arbitrary: P\<^sub>c P\<^sub>a s\<^sub>c s\<^sub>a, clarsimp)
  apply (rule conjI, simp add: prog_sim_init)
  apply (rule conjI)
   apply (case_tac "P\<^sub>c")
  using non_no_tran apply fastforce
   apply (metis option.sel prog_sim_sttuter_step zetaI_None)
  apply (rule conjI)
   apply (case_tac "P\<^sub>c", simp)
   apply (metis (full_types) option.discI option.sel prog_sim_corresponding_step zetaI.simps(2))
  apply (rule conjI, simp add: prog_sim_finish)
  by (metis prog_env_interf)

lemma prog_simI_sound: "\<lbrakk>(\<Gamma>\<^sub>c, (P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p\<^sub>I \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)\<rbrakk> \<Longrightarrow> 
      (s\<^sub>c, s\<^sub>a) \<in> \<alpha> \<and>

      (\<forall>P\<^sub>c' s\<^sub>c'. (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c') \<and> \<zeta> P\<^sub>c = None \<longrightarrow> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> 
                 (\<Gamma>\<^sub>c, (P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p\<^sub>I \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)) \<and>

      (\<forall>P\<^sub>c' s\<^sub>c'. (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c') \<and> \<zeta> P\<^sub>c \<noteq> None \<longrightarrow> 
                 (\<zeta> P\<^sub>c = Some P\<^sub>a \<and> (\<exists>P\<^sub>a' s\<^sub>a'. 
                 (P\<^sub>a, s\<^sub>a) -c\<rightarrow> (P\<^sub>a', s\<^sub>a') \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and>
                 (\<Gamma>\<^sub>c, (P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p\<^sub>I \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a, (P\<^sub>a', s\<^sub>a'), R\<^sub>a, G\<^sub>a)))) \<and>

      (P\<^sub>c = None \<longrightarrow> P\<^sub>a = None \<and> (s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<and> \<gamma> \<subseteq> \<alpha>) \<and> 

      (\<forall>s\<^sub>c' s\<^sub>a'. ((s\<^sub>c, s\<^sub>c'), s\<^sub>a, s\<^sub>a') \<in> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>e\<^sub>\<alpha> \<longrightarrow> (\<Gamma>\<^sub>c,(P\<^sub>c, s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p\<^sub>I \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(P\<^sub>a, s\<^sub>a'),R\<^sub>a,G\<^sub>a))"
  apply (rule conjI)
   apply (erule prog_simI.cases, simp)
  apply (rule conjI)
   apply (erule prog_simI.cases, simp)
   apply force
  apply (rule conjI)
   apply (erule prog_simI.cases, simp)
   apply force
  apply (rule conjI)
   apply (erule prog_simI.cases, simp)
  apply (erule prog_simI.cases, simp)
  by (simp add: related_transitions_def related_transitions_e_def)

interpretation PiCore_SIMP_Refine: PiCore_Sim ptranI\<^sub>c petranI\<^sub>c None ptranI\<^sub>a petranI\<^sub>a None prog_simI
proof
  show "\<And>\<Gamma> a b c d. (a, b) -e\<rightarrow> (c, d) \<Longrightarrow> a = c"
    by (simp add: etran.simps)
  show "\<And>s P t \<Gamma>. ((None, s), P, t) \<notin> ctran"
    by (meson non_no_tran)
  show "\<And>P s t \<Gamma>. ((P, s), P, t) \<notin> ctran"
    by simp
  show "\<And>\<Gamma> a b c d. (a, b) -e\<rightarrow> (c, d) \<Longrightarrow> a = c"
    by (simp add: etran.simps)
  show " \<And>s P t \<Gamma>. ((None, s), P, t) \<notin> ctran"
    by (meson non_no_tran)
  show "\<And>P s t \<Gamma>. ((P, s), P, t) \<notin> ctran"
    by simp
  show "\<And>\<Gamma>\<^sub>c P\<^sub>c s\<^sub>c R\<^sub>c G\<^sub>c \<alpha> \<zeta> \<gamma> \<Gamma>\<^sub>a P\<^sub>a s\<^sub>a R\<^sub>a G\<^sub>a.
       (\<Gamma>\<^sub>c,(P\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p\<^sub>I \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(P\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a) \<Longrightarrow>
       (s\<^sub>c, s\<^sub>a) \<in> \<alpha> \<and>
       (\<forall>P\<^sub>c' s\<^sub>c'. (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c') \<and> \<zeta> P\<^sub>c = None \<longrightarrow> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> 
        (\<Gamma>\<^sub>c,(P\<^sub>c', s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p\<^sub>I \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(P\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a)) \<and>
       (\<forall>P\<^sub>c' s\<^sub>c'. (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c') \<and> \<zeta> P\<^sub>c \<noteq> None \<longrightarrow> \<zeta> P\<^sub>c = Some P\<^sub>a \<and> 
        (\<exists>P\<^sub>a' s\<^sub>a'. (P\<^sub>a, s\<^sub>a) -c\<rightarrow> (P\<^sub>a', s\<^sub>a') \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> 
       (\<Gamma>\<^sub>c,(P\<^sub>c', s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p\<^sub>I \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(P\<^sub>a', s\<^sub>a'),R\<^sub>a,G\<^sub>a))) \<and>
       (P\<^sub>c = None \<longrightarrow> P\<^sub>a = None \<and> (s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<and> \<gamma> \<subseteq> \<alpha>) \<and> 
       (\<forall>s\<^sub>c' s\<^sub>a'. ((s\<^sub>c, s\<^sub>c'), s\<^sub>a, s\<^sub>a') \<in> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>e\<^sub>\<alpha> \<longrightarrow> (\<Gamma>\<^sub>c,(P\<^sub>c, s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p\<^sub>I \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) (\<Gamma>\<^sub>a,(P\<^sub>a, s\<^sub>a'),R\<^sub>a,G\<^sub>a))"
    by (rule prog_simI_sound, simp)
qed

abbreviation pestran\<^sub>a :: "SIMP_Env\<^sub>a \<Rightarrow> ('l,'k,'s,'s prog) pesconf \<Rightarrow> ('l,'k,'s,'s prog) actk \<Rightarrow> 
                        ('l,'k,'s,'s prog) pesconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ -pes-_\<rightarrow> _" [70,70] 60)
  where "pestran\<^sub>a \<equiv> PiCore_SIMP_Refine.pestran\<^sub>a"

abbreviation pestran\<^sub>c :: "SIMP_Env\<^sub>c \<Rightarrow> ('l,'k,'s,'s prog) pesconf \<Rightarrow> ('l,'k,'s,'s prog) actk \<Rightarrow> 
                        ('l,'k,'s,'s prog) pesconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ -pes-_\<rightarrow> _" [70,70] 60)
  where "pestran\<^sub>c \<equiv> PiCore_SIMP_Refine.pestran\<^sub>c"

abbreviation e_sim :: "[SIMP_Env\<^sub>c, ('l\<^sub>c,'k,'s\<^sub>c, 's\<^sub>c prog) econf, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set,
                  ('s\<^sub>c \<times> 's\<^sub>a) set, 's\<^sub>c prog \<rightharpoonup> 's\<^sub>a prog, ('s\<^sub>c \<times> 's\<^sub>a) set,
                  SIMP_Env\<^sub>a, ('l\<^sub>a,'k,'s\<^sub>a,'s\<^sub>a prog) econf, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool"
  where "e_sim \<equiv> PiCore_SIMP_Refine.e_sim"

abbreviation es_sim :: "[SIMP_Env\<^sub>c, ('l\<^sub>c,'k,'s\<^sub>c, 's\<^sub>c prog) esconf, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
                  'k, ('s\<^sub>c \<times> 's\<^sub>a) set, 
                  ('l\<^sub>c,'k,'s\<^sub>c,'s\<^sub>c prog) event \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'s\<^sub>a prog) event, 
                  ('l\<^sub>c,'k,'s\<^sub>c,'s\<^sub>c prog) event \<Rightarrow> 's\<^sub>c prog \<rightharpoonup> 's\<^sub>a prog,
                  SIMP_Env\<^sub>a, ('l\<^sub>a,'k,'s\<^sub>a,'s\<^sub>a prog) esconf, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool"
  where "es_sim \<equiv> PiCore_SIMP_Refine.es_sim"

abbreviation pes_sim :: "[SIMP_Env\<^sub>c, ('l\<^sub>c,'k,'s\<^sub>c,'s\<^sub>c prog) pesconf, 
                  ('s\<^sub>c \<times> 's\<^sub>a) set, 
                  ('l\<^sub>c,'k,'s\<^sub>c,'s\<^sub>c prog) event \<Rightarrow> ('l\<^sub>a,'k,'s\<^sub>a,'s\<^sub>a prog) event, 
                  ('l\<^sub>c,'k,'s\<^sub>c,'s\<^sub>c prog) event \<Rightarrow> 's\<^sub>c prog \<rightharpoonup> 's\<^sub>a prog,
                  SIMP_Env\<^sub>a, ('l\<^sub>a,'k,'s\<^sub>a,'s\<^sub>a prog) pesconf] \<Rightarrow> bool"
  where "pes_sim \<equiv> PiCore_SIMP_Refine.pes_sim"


end

