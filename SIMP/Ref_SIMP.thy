theory Ref_SIMP
  imports RG_Tran RG_Hoare "../VHelper"
begin

definition related_transitions:: "('s\<^sub>c \<times> 's\<^sub>c) set \<Rightarrow> ('s\<^sub>a \<times> 's\<^sub>a) set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>a) set \<Rightarrow> 
                                  (('s\<^sub>c \<times> 's\<^sub>c) \<times> ('s\<^sub>a \<times> 's\<^sub>a)) set" ("'(_, _')\<^sub>_" ) 
  where "related_transitions R R' \<alpha> = {((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')). (\<sigma>,\<sigma>')\<in> R \<and> (\<Sigma>,\<Sigma>')\<in>R' 
                                      \<and>(\<sigma>, \<Sigma>) \<in> \<alpha> \<and> (\<sigma>', \<Sigma>') \<in> \<alpha>}"

definition rel_guard_eq :: "'s\<^sub>c set \<Rightarrow> 's\<^sub>a set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>a) set" ("_ \<rightleftharpoons>\<^sub>r _" [70, 70] 60)
  where "rel_guard_eq g\<^sub>c g\<^sub>a = {(\<sigma>, \<Sigma>). (\<sigma> \<in> g\<^sub>c) = (\<Sigma> \<in> g\<^sub>a)}"

definition rel_guard_and :: "'s\<^sub>c set \<Rightarrow> 's\<^sub>a set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>a) set" ("_\<and>\<^sub>r_" [70, 70] 60) 
  where "rel_guard_and g\<^sub>c g\<^sub>a = {(\<sigma>, \<Sigma>). \<sigma> \<in> g\<^sub>c \<and> \<Sigma> \<in> g\<^sub>a}"

lemma rel_guard_eq_true : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<xi>; s\<^sub>c \<in> g\<^sub>c;  \<xi> \<subseteq> g\<^sub>c \<rightleftharpoons>\<^sub>r g\<^sub>a\<rbrakk> \<Longrightarrow> s\<^sub>a \<in> g\<^sub>a"
  apply (simp add: rel_guard_eq_def)
  by blast

lemma rel_guard_eq_false : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<xi>; s\<^sub>c \<notin> g\<^sub>c;  \<xi> \<subseteq> g\<^sub>c \<rightleftharpoons>\<^sub>r g\<^sub>a\<rbrakk> \<Longrightarrow> s\<^sub>a \<notin> g\<^sub>a"
  apply (simp add: rel_guard_eq_def)
  by blast

definition Stable :: "('s\<^sub>c \<times> 's\<^sub>a) set \<Rightarrow> (('s\<^sub>c \<times> 's\<^sub>c) \<times> ('s\<^sub>a \<times> 's\<^sub>a)) set \<Rightarrow> bool" 
  where "Stable \<zeta> \<Delta> = (\<forall>\<sigma> \<sigma>' \<Sigma> \<Sigma>'. (\<sigma>, \<Sigma>) \<in> \<zeta> \<longrightarrow> ((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')) \<in> \<Delta> \<longrightarrow> (\<sigma>', \<Sigma>') \<in> \<zeta> )"

coinductive prog_sim :: "['s\<^sub>c conf, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
                  ('s\<^sub>c \<times> 's\<^sub>a) set, 's\<^sub>c com \<rightharpoonup> 's\<^sub>a com, ('s\<^sub>c \<times> 's\<^sub>a) set,
                  's\<^sub>a conf, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool" 
  ("'(_,_,_')/ \<preceq>\<^sub>p \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>') /'(_,_,_')" [81,81,81,81,81,81,81,81,81] 100) 
  where rgsim : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<alpha>;

                 (\<forall>P\<^sub>c' s\<^sub>c'. (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c') \<and> \<zeta> (the P\<^sub>c) = None \<longrightarrow> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> 
                 ((P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a));

                 (\<forall>P\<^sub>c' s\<^sub>c'. (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c') \<and> \<zeta> (the P\<^sub>c) \<noteq> None \<longrightarrow> 
                 (\<zeta> (the P\<^sub>c) = P\<^sub>a \<and> (\<exists>P\<^sub>a' s\<^sub>a'. 
                 (P\<^sub>a, s\<^sub>a) -c\<rightarrow> (P\<^sub>a', s\<^sub>a') \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and>
                 ((P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a', s\<^sub>a'), R\<^sub>a, G\<^sub>a))));

                  (P\<^sub>c = None \<longrightarrow> P\<^sub>a = None \<and> (s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<and> \<gamma> \<subseteq> \<alpha>); 

                  (\<forall>s\<^sub>c' s\<^sub>a'. ((s\<^sub>c, s\<^sub>c'),(s\<^sub>a, s\<^sub>a')) \<in> ((R\<^sub>c \<union> Id, R\<^sub>a \<union> Id)\<^sub>\<alpha>) \<longrightarrow> 
                  ((P\<^sub>c, s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a'), R\<^sub>a, G\<^sub>a))
                                   
                  \<rbrakk> \<Longrightarrow> ((P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)"


definition prog_sim_pre :: "[('s\<^sub>c com) option, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
                  ('s\<^sub>c \<times> 's\<^sub>a) set, 's\<^sub>c com \<Rightarrow> ('s\<^sub>a com) option, ('s\<^sub>c \<times> 's\<^sub>a) set,('s\<^sub>c \<times> 's\<^sub>a) set,
                  ('s\<^sub>a com) option, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool" 
  ("'(_,_,_')/ \<preceq>\<^sub>p \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>\<rhd>\<^sub>_\<^sub>') /'(_,_,_')" [81,81,81,81,81,81,81,81,81,81] 100)
  where " (P\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (P\<^sub>a, R\<^sub>a, G\<^sub>a) \<equiv> 
          (\<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<longrightarrow> ((P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a))"


lemma prog_sim_init: "((P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a) \<Longrightarrow> (s\<^sub>c, s\<^sub>a) \<in> \<alpha>"
  by (erule prog_sim.cases, simp)

lemma prog_sim_pre_implies_inv : "(P\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (P\<^sub>a, R\<^sub>a, G\<^sub>a) \<Longrightarrow> \<xi> \<subseteq> \<alpha>"
  by (meson prog_sim_init prog_sim_pre_def subrelI)

lemma prog_sim_sttuter_step: "\<lbrakk>((P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a); \<zeta> (the P\<^sub>c) = None;
      (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c')\<rbrakk> \<Longrightarrow> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> ((P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)"
  by (erule prog_sim.cases, simp)

lemma prog_sim_finish: "\<lbrakk>((P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a); P\<^sub>c = None\<rbrakk> \<Longrightarrow> P\<^sub>a = None \<and> (s\<^sub>c, s\<^sub>a) \<in> \<gamma>"
  by (erule prog_sim.cases, simp)

lemma prog_sim_sttuter_step_finish: "\<lbrakk>((P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a); \<zeta> (the P\<^sub>c) = None;
                                      (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (None, s\<^sub>c')\<rbrakk> \<Longrightarrow> P\<^sub>a = None \<and> (s\<^sub>c', s\<^sub>a) \<in> \<gamma>"
  apply (erule prog_sim.cases, simp)
  by (meson prog_sim_finish)

lemma prog_sim_corresponding_step: "\<lbrakk>((P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a); 
      (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c'); \<zeta> (the P\<^sub>c) \<noteq> None \<rbrakk> \<Longrightarrow> \<zeta> (the P\<^sub>c) = P\<^sub>a \<and> (\<exists>P\<^sub>a' s\<^sub>a'. 
                 (P\<^sub>a, s\<^sub>a) -c\<rightarrow> (P\<^sub>a', s\<^sub>a') \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and>
                 ((P\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a', s\<^sub>a'), R\<^sub>a, G\<^sub>a))"
  by (erule prog_sim.cases, simp)

lemma prog_sim_guar: "\<lbrakk>((P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a); (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c')\<rbrakk> 
                      \<Longrightarrow> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c"
  apply (erule prog_sim.cases, simp)
  by (metis option.collapse)

lemma prog_env_interf: "\<lbrakk>((P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a); ((s\<^sub>c, s\<^sub>c'),(s\<^sub>a, s\<^sub>a')) \<in> ((R\<^sub>c \<union> Id, R\<^sub>a \<union> Id)\<^sub>\<alpha>)\<rbrakk> 
                        \<Longrightarrow> ((P\<^sub>c, s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a'), R\<^sub>a, G\<^sub>a)"
  by (erule prog_sim.cases, simp)

lemma related_conseq: "\<lbrakk>R\<^sub>c' \<subseteq> R\<^sub>c; R\<^sub>a' \<subseteq> R\<^sub>a\<rbrakk> \<Longrightarrow> (R\<^sub>c', R\<^sub>a')\<^sub>\<alpha> \<subseteq> (R\<^sub>c, R\<^sub>a)\<^sub>\<alpha>"
  apply (simp add: related_transitions_def)
  by auto

lemma related_conseq_Id: "\<lbrakk>R\<^sub>c' \<subseteq> R\<^sub>c; R\<^sub>a' \<subseteq> R\<^sub>a\<rbrakk> \<Longrightarrow> (R\<^sub>c'\<^sup>=, R\<^sub>a'\<^sup>=)\<^sub>\<alpha> \<subseteq> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>"
  apply (rule related_conseq)
   apply blast
  by blast

lemma Conseq_Sim: "\<lbrakk>((P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a); (s\<^sub>c, s\<^sub>a) \<in> \<alpha>;
                    \<gamma> \<subseteq> \<gamma>\<^sub>' \<and> \<gamma>\<^sub>' \<subseteq> \<alpha>; R\<^sub>c' \<subseteq> R\<^sub>c; R\<^sub>a' \<subseteq> R\<^sub>a; G\<^sub>c \<subseteq> G\<^sub>c'; G\<^sub>a \<subseteq> G\<^sub>a'\<rbrakk> 
                    \<Longrightarrow> ((P\<^sub>c, s\<^sub>c), R\<^sub>c', G\<^sub>c') \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>'\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a', G\<^sub>a')"
  apply (coinduction arbitrary: P\<^sub>c s\<^sub>c P\<^sub>a s\<^sub>a, clarsimp)
  apply (rule conjI)
   apply (erule prog_sim.cases)
   apply (metis (no_types, lifting) Pair_inject prog_sim_init subsetD)
  apply (rule conjI)
  apply (erule prog_sim.cases)
  using prog_sim_init apply fastforce
  apply (rule conjI)
   apply (erule prog_sim.cases)
   apply blast
  apply (erule prog_sim.cases, clarify)
  apply (rule conjI)
   apply (meson related_conseq_Id subset_iff)
  by (simp add: related_transitions_def)

lemma Conseq_Sim': "\<lbrakk>((P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a); (s\<^sub>c, s\<^sub>a) \<in> \<alpha>;
                    R\<^sub>c' \<subseteq> R\<^sub>c; R\<^sub>a' \<subseteq> R\<^sub>a; G\<^sub>c \<subseteq> G\<^sub>c'; G\<^sub>a \<subseteq> G\<^sub>a'\<rbrakk> 
                    \<Longrightarrow> ((P\<^sub>c, s\<^sub>c), R\<^sub>c', G\<^sub>c') \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a', G\<^sub>a')"
  apply (coinduction arbitrary: P\<^sub>c s\<^sub>c P\<^sub>a s\<^sub>a, clarsimp)
  apply (rule conjI)
   apply (erule prog_sim.cases)
   apply (metis (no_types, lifting) Pair_inject prog_sim_init subsetD)
  apply (rule conjI)
  apply (erule prog_sim.cases)
  using prog_sim_init apply fastforce
  apply (rule conjI)
   apply (erule prog_sim.cases)
   apply blast
  apply (erule prog_sim.cases, clarify)
  apply (rule conjI)
   apply (meson related_conseq_Id subset_iff)
  by (simp add: related_transitions_def)

theorem Conseq_Sound: "\<lbrakk>(P\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (P\<^sub>a, R\<^sub>a, G\<^sub>a); \<xi>\<^sub>' \<subseteq> \<xi>; \<gamma> \<subseteq> \<gamma>\<^sub>' \<and> \<gamma>\<^sub>' \<subseteq> \<alpha>; 
      R\<^sub>c' \<subseteq> R\<^sub>c; R\<^sub>a' \<subseteq> R\<^sub>a; G\<^sub>c \<subseteq> G\<^sub>c'; G\<^sub>a \<subseteq> G\<^sub>a'\<rbrakk> \<Longrightarrow> (P\<^sub>c, R\<^sub>c', G\<^sub>c') \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (P\<^sub>a, R\<^sub>a', G\<^sub>a')"
  apply (simp add: prog_sim_pre_def)
  by (meson Conseq_Sim order_refl order_trans prog_sim_init)

lemma None_Sim : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<xi>; \<xi> \<subseteq> \<alpha>; Stable \<xi> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>\<rbrakk> \<Longrightarrow> ((None, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>) ((None, s\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduction arbitrary: s\<^sub>c s\<^sub>a, clarsimp)
  apply (rule conjI)
   apply blast
  apply (rule conjI, clarsimp)
   apply (erule ctran.cases, simp_all)
  apply (rule conjI, clarsimp)
   apply (erule ctran.cases, simp_all)
  apply (simp add: related_transitions_def, clarify)
  by (simp add: Pair_inject Stable_def)


theorem None_Sound : "\<lbrakk> \<xi> \<subseteq> \<alpha>; Stable \<xi> (R\<^sub>c \<union> Id, R\<^sub>a \<union> Id)\<^sub>\<alpha>\<rbrakk> \<Longrightarrow> (None, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<xi>\<^sub>) (None, R\<^sub>a, G\<^sub>a)"
  by (simp add: prog_sim_pre_def None_Sim)

lemma Basic_None_Sim: "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<xi>; \<xi> \<subseteq> \<alpha>; \<gamma> \<subseteq> \<alpha>; \<zeta> (Basic f\<^sub>c) = None; 
                        Stable \<xi> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>;
                        \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<longrightarrow> (s\<^sub>c, f\<^sub>c s\<^sub>c) \<in> G\<^sub>c \<and> (f\<^sub>c s\<^sub>c, s\<^sub>a) \<in> \<gamma>\<rbrakk> 
                      \<Longrightarrow> ((Some (Basic f\<^sub>c), s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((None, s\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduction arbitrary: s\<^sub>c s\<^sub>a, clarsimp)
  apply (rule conjI)
   apply blast
  apply (rule conjI, clarsimp)
   apply (erule ctran.cases, simp_all)
   apply (rule None_Sim, simp_all)
  by (simp add: related_transitions_def Stable_def)

theorem Basic_None_Sound: "\<lbrakk>\<xi> \<subseteq> \<alpha>; \<gamma> \<subseteq> \<alpha>; Stable \<xi> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>;
        \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<longrightarrow> (s\<^sub>c, f\<^sub>c s\<^sub>c) \<in> G\<^sub>c \<and> (f\<^sub>c s\<^sub>c, s\<^sub>a) \<in> \<gamma>; \<zeta> (Basic f\<^sub>c) = None\<rbrakk>
                    \<Longrightarrow> (Some (Basic f\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (None, R\<^sub>a, G\<^sub>a)"
  apply (simp add: prog_sim_pre_def)
  by (simp add: Basic_None_Sim)
  
lemma Basic_Sim: "\<lbrakk>\<xi> \<subseteq> \<alpha>; \<gamma> \<subseteq> \<alpha>; \<zeta> (Basic f\<^sub>c) = Some (Basic f\<^sub>a); (s\<^sub>c, s\<^sub>a) \<in> \<xi>; 
                   Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; Stable \<xi> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>;
                   \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<longrightarrow> (s\<^sub>c, f\<^sub>c s\<^sub>c) \<in> G\<^sub>c \<and> (s\<^sub>a, f\<^sub>a s\<^sub>a) \<in> G\<^sub>a \<and> (f\<^sub>c s\<^sub>c, f\<^sub>a s\<^sub>a) \<in> \<gamma>\<rbrakk> 
                  \<Longrightarrow> ((Some (Basic f\<^sub>c), s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some (Basic f\<^sub>a), s\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduction arbitrary: s\<^sub>c s\<^sub>a, clarsimp)
  apply (rule conjI)
   apply blast
  apply (rule conjI, clarsimp)
   apply (erule ctran.cases, simp_all)
   apply (rule_tac x = None and y = "f\<^sub>a s\<^sub>a" in ex2I, simp add: ctran.Basic)
   apply (rule None_Sim, simp_all)
  by (simp add: related_transitions_def Stable_def)

theorem Basic_Sound: "\<lbrakk>\<xi> \<subseteq> \<alpha>; \<gamma> \<subseteq> \<alpha>; Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; Stable \<xi> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; \<zeta> (Basic f\<^sub>c) = Some (Basic f\<^sub>a);
                      \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<longrightarrow> (s\<^sub>c, f\<^sub>c s\<^sub>c) \<in> G\<^sub>c \<and> (s\<^sub>a, f\<^sub>a s\<^sub>a) \<in> G\<^sub>a \<and> (f\<^sub>c s\<^sub>c, f\<^sub>a s\<^sub>a) \<in> \<gamma>\<rbrakk> 
                      \<Longrightarrow> (Some (Basic f\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (Some (Basic f\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (simp add: prog_sim_pre_def)
  by (simp add: Basic_Sim)

lemma Seq_None_Sim: "\<lbrakk> \<forall>C\<^sub>c. \<zeta>\<^sub>1 C\<^sub>c = None \<longrightarrow> \<zeta> (Seq C\<^sub>c C2\<^sub>c) = None; (s\<^sub>c, s\<^sub>a) \<in> \<alpha>;
                     ((Some C1\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((None, s\<^sub>a), R\<^sub>a, G\<^sub>a);
                     \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<gamma>\<^sub>1 \<longrightarrow> ((Some C2\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some C\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)\<rbrakk> \<Longrightarrow> 
                     ((Some (Seq C1\<^sub>c C2\<^sub>c), s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some C\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduction arbitrary: C1\<^sub>c s\<^sub>c s\<^sub>a, clarsimp)
  apply (rule conjI, clarsimp)
(* stutter step *)
   apply (erule ctran.cases, simp_all)
    apply (rule conjI, simp add: prog_sim_guar)
    apply (meson prog_sim_corresponding_step prog_sim_sttuter_step_finish)
   apply (metis prog_sim_corresponding_step prog_sim_init prog_sim_sttuter_step)
  apply (rule conjI, clarsimp)
(* corresponding step, impossible as refine by None means all step is sttuter *)
   apply (drule_tac a = C1\<^sub>c in allD)
  apply (erule ctran.cases, simp_all)
  using prog_sim_corresponding_step apply fastforce
   apply (metis option.distinct(1) option.sel prog_sim_corresponding_step)
(* environmental interference *)
  by (meson prog_env_interf prog_sim_init)

theorem Seq_None_Sound: "\<lbrakk> \<xi> \<subseteq> \<alpha>; \<forall>C\<^sub>c. \<zeta>\<^sub>1 C\<^sub>c = None \<longrightarrow> \<zeta> (Seq C\<^sub>c C2\<^sub>c) = None;
                          (Some C1\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>1\<^sub>) (None, R\<^sub>a, G\<^sub>a);
                          (Some C2\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (Some C\<^sub>a, R\<^sub>a, G\<^sub>a)\<rbrakk> 
                      \<Longrightarrow> (Some (Seq C1\<^sub>c C2\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (Some C\<^sub>a, R\<^sub>a, G\<^sub>a)"
  apply (simp add: prog_sim_pre_def, clarify)
  by (metis Seq_None_Sim prog_sim_init)

lemma Seq_Sim_Corresponding_Finish: "\<lbrakk>((Some C\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some C\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a);
      (Some C\<^sub>c, s\<^sub>c) -c\<rightarrow> (None, s\<^sub>c'); \<zeta> C\<^sub>c \<noteq> None\<rbrakk> \<Longrightarrow> 
      \<exists>s\<^sub>a'. (Some (Seq C\<^sub>a C2\<^sub>a), s\<^sub>a) -c\<rightarrow> (Some C2\<^sub>a, s\<^sub>a') \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> 
      (s\<^sub>c', s\<^sub>a') \<in> \<gamma>"
proof-
  assume a0: "((Some C\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some C\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a)"
     and a1: "(Some C\<^sub>c, s\<^sub>c) -c\<rightarrow> (None, s\<^sub>c')"
     and a2: " \<zeta> C\<^sub>c \<noteq> None"
  then have " \<exists>C\<^sub>a' s\<^sub>a'. (Some C\<^sub>a, s\<^sub>a) -c\<rightarrow> (C\<^sub>a', s\<^sub>a') \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and>
                 ((None, s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((C\<^sub>a', s\<^sub>a'), R\<^sub>a, G\<^sub>a)"
    by (simp add: prog_sim_corresponding_step)
  then obtain C\<^sub>a' s\<^sub>a' where a3: "(Some C\<^sub>a, s\<^sub>a) -c\<rightarrow> (C\<^sub>a', s\<^sub>a') \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and>
                                ((None, s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((C\<^sub>a', s\<^sub>a'), R\<^sub>a, G\<^sub>a)" by auto
  then have a4: "C\<^sub>a' = None \<and> (s\<^sub>c', s\<^sub>a') \<in> \<gamma>"
    by (meson prog_sim_finish)
  with a3 show ?thesis
    by (metis ctran.Seq1)
qed

lemma Seq_Sim_Corresponding_Not_Finish: "\<lbrakk>((Some C1\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((Some C1\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a);
      (Some C1\<^sub>c, s\<^sub>c) -c\<rightarrow> (Some C1\<^sub>c', s\<^sub>c'); \<zeta>\<^sub>1 C1\<^sub>c \<noteq> None;  \<forall>C\<^sub>c. \<zeta>\<^sub>1 C\<^sub>c = None \<longrightarrow> \<zeta> (Seq C\<^sub>c C2\<^sub>c) = None;
      \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<gamma>\<^sub>1 \<longrightarrow> ((Some C2\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some C2\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)\<rbrakk> \<Longrightarrow> 
      \<exists>C\<^sub>a' s\<^sub>a'.
      (Some (Seq C1\<^sub>a C2\<^sub>a), s\<^sub>a) -c\<rightarrow> (C\<^sub>a', s\<^sub>a') \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> 

      (
      (\<exists>C1\<^sub>a'. C\<^sub>a' = Some (Seq C1\<^sub>a' C2\<^sub>a) \<and> (s\<^sub>c', s\<^sub>a') \<in> \<alpha> \<and> ((Some C1\<^sub>c', s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((Some C1\<^sub>a', s\<^sub>a'),R\<^sub>a,G\<^sub>a)) 
      \<or> ((Some (Seq C1\<^sub>c' C2\<^sub>c), s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((C\<^sub>a', s\<^sub>a'),R\<^sub>a,G\<^sub>a))"
proof-
  assume a0: "((Some C1\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((Some C1\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a)"
     and a1: "(Some C1\<^sub>c, s\<^sub>c) -c\<rightarrow> (Some C1\<^sub>c', s\<^sub>c')"
     and a2: "\<zeta>\<^sub>1 C1\<^sub>c \<noteq> None"
     and a3: " \<forall>C\<^sub>c. \<zeta>\<^sub>1 C\<^sub>c = None \<longrightarrow> \<zeta> (Seq C\<^sub>c C2\<^sub>c) = None"
     and a4: "\<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<gamma>\<^sub>1 \<longrightarrow> ((Some C2\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some C2\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)"
  then have "\<exists>CO1\<^sub>a' s\<^sub>a'. (Some C1\<^sub>a, s\<^sub>a) -c\<rightarrow> (CO1\<^sub>a', s\<^sub>a') \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and>
             ((Some C1\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((CO1\<^sub>a', s\<^sub>a'), R\<^sub>a, G\<^sub>a)"
    by (simp add: prog_sim_corresponding_step)
  then obtain CO1\<^sub>a' s\<^sub>a' where a5: "(Some C1\<^sub>a, s\<^sub>a) -c\<rightarrow> (CO1\<^sub>a', s\<^sub>a') \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and>
             ((Some C1\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((CO1\<^sub>a', s\<^sub>a'), R\<^sub>a, G\<^sub>a)"
    by blast
  then show ?thesis
  proof(cases CO1\<^sub>a')
    case None
    assume b0: "CO1\<^sub>a' = None"
    with a5 have b1: "(Some (Seq C1\<^sub>a C2\<^sub>a), s\<^sub>a) -c\<rightarrow> (Some C2\<^sub>a, s\<^sub>a')"
      by (metis ctran.Seq1)
    from a5 b0 have b2: "((Some C1\<^sub>c', s\<^sub>c'), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((None, s\<^sub>a'), R\<^sub>a, G\<^sub>a)"
      by simp
    with a3 a4 have "((Some (Seq C1\<^sub>c' C2\<^sub>c), s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some C2\<^sub>a, s\<^sub>a'),R\<^sub>a,G\<^sub>a)"
      by (metis Seq_None_Sim prog_sim_init)
    with a5 b1 show ?thesis by metis
  next
    case (Some C1\<^sub>a')
    assume c0: "CO1\<^sub>a' = Some C1\<^sub>a'"
    with a5 have c2: "(Some (Seq C1\<^sub>a C2\<^sub>a), s\<^sub>a) -c\<rightarrow> (Some (Seq C1\<^sub>a' C2\<^sub>a), s\<^sub>a')" 
      by (metis a5 ctran.Seq2)
    with a5 c0 show ?thesis 
      by (metis  prog_sim_init)
  qed
qed

lemma Seq_Sim: "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<alpha>; \<forall>C\<^sub>c.  \<zeta> (Seq C\<^sub>c C2\<^sub>c) = None \<longrightarrow> \<zeta>\<^sub>1 C\<^sub>c = None ; 
                 \<forall>C\<^sub>c. \<zeta> (Seq C\<^sub>c C2\<^sub>c) \<noteq> None \<longrightarrow> (\<exists>C\<^sub>a. \<zeta>\<^sub>1 C\<^sub>c = Some C\<^sub>a \<and> \<zeta> (Seq C\<^sub>c C2\<^sub>c) = Some (Seq C\<^sub>a C2\<^sub>a)) ;
                 ((Some C1\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((Some C1\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a);
                 \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<gamma>\<^sub>1 \<longrightarrow> ((Some C2\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some C2\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)\<rbrakk> \<Longrightarrow> 
                 ((Some (Seq C1\<^sub>c C2\<^sub>c), s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some (Seq C1\<^sub>a C2\<^sub>a), s\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduction arbitrary: C1\<^sub>c C1\<^sub>a s\<^sub>c s\<^sub>a, clarsimp)
  apply (rule conjI, clarsimp)
(* stutter step *)
   apply (erule ctran.cases, simp_all)
    apply (rule conjI, simp add: prog_sim_guar)
    apply (metis option.discI option.sel prog_sim_sttuter_step_finish)
   apply (metis option.sel prog_sim_init prog_sim_sttuter_step)
  apply (rule conjI, clarsimp)
(* corresponding step *)
   apply (erule ctran.cases, simp_all)
    (* C1\<^sub>c finishes executing, it implies C1\<^sub>a finishes too *)
    apply (rule conjI)
     apply (metis option.distinct(1) option.sel prog_sim_corresponding_step)
    apply (drule_tac C2\<^sub>a = C2\<^sub>a in Seq_Sim_Corresponding_Finish, simp_all)
     apply blast
    apply meson
    (* C1\<^sub>c does not finish, C1\<^sub>a can either finish or not *)
   apply (rule conjI)
    apply (metis option.distinct(1) option.sel prog_sim_corresponding_step)
   apply (drule Seq_Sim_Corresponding_Not_Finish, simp_all)
     apply blast
    apply (metis not_Some_eq)
(* environmental interference *)
  by (meson prog_env_interf prog_sim_init)

theorem Seq_Sound: "\<lbrakk>(Some C1\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>1\<^sub>) (Some C1\<^sub>a, R\<^sub>a, G\<^sub>a); (Some C2\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (Some C2\<^sub>a, R\<^sub>a, G\<^sub>a);
       \<xi> \<subseteq> \<alpha>; \<forall>C\<^sub>c.  \<zeta> (Seq C\<^sub>c C2\<^sub>c) = None \<longrightarrow> \<zeta>\<^sub>1 C\<^sub>c = None; 
       \<forall>C\<^sub>c. \<zeta> (Seq C\<^sub>c C2\<^sub>c) \<noteq> None \<longrightarrow> (\<exists>C\<^sub>a. \<zeta>\<^sub>1 C\<^sub>c = Some C\<^sub>a \<and> \<zeta> (Seq C\<^sub>c C2\<^sub>c) = Some (Seq C\<^sub>a C2\<^sub>a))\<rbrakk> 
       \<Longrightarrow> (Some (Seq C1\<^sub>c C2\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (Some (Seq C1\<^sub>a C2\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (simp add: prog_sim_pre_def, clarify)
  apply (rule Seq_Sim, simp_all)
   apply blast
  by blast


lemma If_None_Sim: "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<xi>; \<xi> \<subseteq> \<alpha>; \<zeta> (Cond b\<^sub>c C1\<^sub>c C2\<^sub>c) = None;  Stable \<xi> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>;
                     \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<and> s\<^sub>c \<in> b\<^sub>c \<longrightarrow> ((Some C1\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((None, s\<^sub>a), R\<^sub>a, G\<^sub>a);
                     \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<and> s\<^sub>c \<notin> b\<^sub>c \<longrightarrow> ((Some C2\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((None, s\<^sub>a), R\<^sub>a, G\<^sub>a)
                     \<rbrakk> \<Longrightarrow> ((Some (Cond b\<^sub>c C1\<^sub>c C2\<^sub>c), s\<^sub>c), R\<^sub>c, (G\<^sub>c \<union> Id)) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((None, s\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduction arbitrary: s\<^sub>c s\<^sub>a, clarsimp)
  apply (rule conjI)
(* initial state *)
   apply blast
  apply (rule conjI, clarsimp)
(* stutter step *)
   apply (erule ctran.cases, simp_all)
  apply (meson Conseq_Sim' order_refl prog_sim_init sup.cobounded1)
   apply (meson Conseq_Sim' order_refl prog_sim_init sup.cobounded1)
  by (simp add: Stable_def)

theorem If_None_Sound: "\<lbrakk>\<xi> \<subseteq> \<alpha>; \<zeta> (Cond b\<^sub>c C1\<^sub>c C2\<^sub>c) = None;  Stable \<xi> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>;
        (Some C1\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (None, R\<^sub>a, G\<^sub>a); (Some C2\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>2\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (None, R\<^sub>a, G\<^sub>a);
        \<xi>\<^sub>1 = \<xi> \<inter> {(s\<^sub>c, s\<^sub>a).  s\<^sub>c \<in> b\<^sub>c}; \<xi>\<^sub>2 = \<xi> \<inter> {(s\<^sub>c, s\<^sub>a).  s\<^sub>c \<notin> b\<^sub>c}\<rbrakk> 
        \<Longrightarrow> (Some (Cond b\<^sub>c C1\<^sub>c C2\<^sub>c), R\<^sub>c, (G\<^sub>c \<union> Id)) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (None, R\<^sub>a, G\<^sub>a)"
  by (simp add: prog_sim_pre_def, simp add: If_None_Sim)

lemma If_Sim: "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<xi>; \<xi> \<subseteq> \<alpha> \<inter> (b\<^sub>c \<rightleftharpoons>\<^sub>r b\<^sub>a); \<zeta> (Cond b\<^sub>c C1\<^sub>c C2\<^sub>c) = Some (Cond b\<^sub>a C1\<^sub>a C2\<^sub>a); Stable \<xi> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; 
      \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<inter> (b\<^sub>c \<and>\<^sub>r b\<^sub>a) \<longrightarrow> ((Some C1\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some C1\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a);
      \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<inter> (- b\<^sub>c \<and>\<^sub>r - b\<^sub>a) \<longrightarrow> ((Some C2\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some C2\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)
     \<rbrakk> \<Longrightarrow> ((Some (Cond b\<^sub>c C1\<^sub>c C2\<^sub>c), s\<^sub>c), R\<^sub>c, (G\<^sub>c \<union> Id)) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some (Cond b\<^sub>a C1\<^sub>a C2\<^sub>a), s\<^sub>a), R\<^sub>a, (G\<^sub>a \<union> Id))"
  apply (coinduction arbitrary: s\<^sub>c s\<^sub>a, clarsimp)
  apply (rule conjI)
(* initial state *)
   apply blast
  apply (rule conjI, clarsimp)
(* corresponding step *)
  apply (simp add: rel_guard_and_def rel_guard_eq_def)
   apply (erule ctran.cases, simp_all)
    apply (rule_tac x = "Some C1\<^sub>a" and y = s\<^sub>a in ex2I, simp_all)
    apply (rule conjI, simp add: ctran.CondT subset_iff)
    apply (smt (verit, best) Conseq_Sim' case_prod_conv mem_Collect_eq subsetD sup.orderI sup_assoc sup_commute sup_idem)
   apply (rule_tac x = "Some C2\<^sub>a" and y = s\<^sub>a in ex2I, simp_all)
   apply (rule conjI, simp add: ctran.CondF subset_iff)
   apply (smt (verit, best) Conseq_Sim' case_prod_conv mem_Collect_eq subsetD sup.orderI sup_assoc sup_commute sup_idem)
  by (simp add: Stable_def)

theorem If_Sound: "\<lbrakk>\<xi> \<subseteq> \<alpha> \<inter> (b\<^sub>c \<rightleftharpoons>\<^sub>r b\<^sub>a); \<zeta> (Cond b\<^sub>c C1\<^sub>c C2\<^sub>c) = Some (Cond b\<^sub>a C1\<^sub>a C2\<^sub>a);  Stable \<xi> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>;
        (Some C1\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (Some C1\<^sub>a, R\<^sub>a, G\<^sub>a); (Some C2\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>2\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (Some C2\<^sub>a, R\<^sub>a, G\<^sub>a);
        \<xi>\<^sub>1 = \<xi> \<inter> (b\<^sub>c \<and>\<^sub>r b\<^sub>a); \<xi>\<^sub>2 = \<xi> \<inter> (- b\<^sub>c \<and>\<^sub>r - b\<^sub>a)\<rbrakk> 
        \<Longrightarrow> (Some (Cond b\<^sub>c C1\<^sub>c C2\<^sub>c), R\<^sub>c, (G\<^sub>c \<union> Id)) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (Some (Cond b\<^sub>a C1\<^sub>a C2\<^sub>a), R\<^sub>a, (G\<^sub>a \<union> Id))"
  by (simp add: prog_sim_pre_def, simp add: If_Sim)

lemma Await_implies: "\<lbrakk> (Some (Await b\<^sub>c C\<^sub>c), s) -c\<rightarrow> (P', s'); \<turnstile> Await b\<^sub>c C\<^sub>c sat [P, R, G, Q]; s \<in> P\<rbrakk> 
                       \<Longrightarrow> (s, s') \<in> G \<and> s' \<in> Q"
proof-
  assume a0: "\<turnstile> Await b\<^sub>c C\<^sub>c sat [P, R, G, Q]"
     and a1: "s \<in> P"
     and a2: "(Some (Await b\<^sub>c C\<^sub>c), s) -c\<rightarrow> (P', s')"
  from a0 have "\<Turnstile> Await b\<^sub>c C\<^sub>c sat [P, R, G, Q]" by (simp add: rgsound)
  then have a3: "cp (Some (Await b\<^sub>c C\<^sub>c)) s \<inter> assum(P, R) \<subseteq> comm(G, Q)"
    by (simp add: com_validity_def)
  from a2 have a4: "(Some (Await b\<^sub>c C\<^sub>c), s) -c\<rightarrow> (None, s')"
    by (rule ctran.cases, simp_all)
  then have a5: "[(Some (Await b\<^sub>c C\<^sub>c), s), (None, s')] \<in> cp (Some (Await b\<^sub>c C\<^sub>c)) s"
    by (simp add: cp_def cptn.CptnComp cptn.CptnOne)
  from a1 have a6: "[(Some (Await b\<^sub>c C\<^sub>c), s), (None, s')] \<in> assum(P, R)"
    by (simp add: assum_def etran.simps)
  with a3 a5 have "[(Some (Await b\<^sub>c C\<^sub>c), s), (None, s')] \<in> comm(G, Q)" by auto
  with a4 show ?thesis by (simp add: comm_def)
qed

lemma Await_None_Sim_stutter_step: "\<lbrakk>(Some (Await b\<^sub>c C\<^sub>c), s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c'); (s\<^sub>c, s\<^sub>a) \<in> \<xi>;
        Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; \<gamma> \<subseteq> \<alpha>;
        \<forall>s\<^sub>c s\<^sub>a. \<turnstile> Await b\<^sub>c C\<^sub>c sat [{s\<^sub>c. (s\<^sub>c, s\<^sub>a) \<in> \<xi>} \<inter> b\<^sub>c \<inter> {s\<^sub>c}, Id, G\<^sub>c, {s\<^sub>c'. (s\<^sub>c', s\<^sub>a) \<in> \<gamma>}] \<rbrakk>
        \<Longrightarrow> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> ((P\<^sub>c', s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((None, s\<^sub>a),R\<^sub>a,G\<^sub>a)"
proof-
  assume a0: "(Some (Await b\<^sub>c C\<^sub>c), s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c')"
     and a1: "\<forall>s\<^sub>c s\<^sub>a. \<turnstile> Await b\<^sub>c C\<^sub>c sat [{s\<^sub>c. (s\<^sub>c, s\<^sub>a) \<in> \<xi>} \<inter> b\<^sub>c \<inter> {s\<^sub>c}, Id, G\<^sub>c, {s\<^sub>c'. (s\<^sub>c', s\<^sub>a) \<in> \<gamma>}]"
     and a2: "(s\<^sub>c, s\<^sub>a) \<in> \<xi>"
     and a3: "Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>"
     and a4: "\<gamma> \<subseteq> \<alpha>"

  from a0 have b0: "P\<^sub>c' = None \<and> s\<^sub>c \<in> b\<^sub>c"
    by (rule ctran.cases, simp_all)
  from a1 a2 have "\<turnstile> Await b\<^sub>c C\<^sub>c sat [{s\<^sub>c. (s\<^sub>c, s\<^sub>a) \<in> \<xi>} \<inter> b\<^sub>c \<inter> {s\<^sub>c}, Id, G\<^sub>c, {s\<^sub>c'. (s\<^sub>c', s\<^sub>a) \<in> \<gamma>}]"
    by blast
  with a0 a2 b0 have b1: "(s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>c', s\<^sub>a) \<in> \<gamma>"
    using Await_implies a2 by fastforce
  with a3 a4 have "((None, s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((None, s\<^sub>a),R\<^sub>a,G\<^sub>a)"
    by (simp add: None_Sim)
  with b0 b1 show ?thesis by blast
qed
    
    
lemma Await_None_Sim: "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<xi>; \<xi> \<subseteq> \<alpha>; \<zeta> (Await b\<^sub>c C\<^sub>c) = None; 
      Stable \<xi> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; \<gamma> \<subseteq> \<alpha>;
      \<forall>s\<^sub>c s\<^sub>a. \<turnstile> Await b\<^sub>c C\<^sub>c sat [{s\<^sub>c. (s\<^sub>c, s\<^sub>a) \<in> \<xi>} \<inter> b\<^sub>c \<inter> {s\<^sub>c}, Id, G\<^sub>c, {s\<^sub>c'. (s\<^sub>c', s\<^sub>a) \<in> \<gamma>}]\<rbrakk> 
      \<Longrightarrow> ((Some (Await b\<^sub>c C\<^sub>c), s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((None, s\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduction arbitrary: s\<^sub>c s\<^sub>a, clarsimp)
  apply (rule conjI)
(* initial state *)
   apply blast
  apply (rule conjI, clarsimp)
(* stutter step *)
   apply (subgoal_tac "(s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> ((P\<^sub>c', s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((None, s\<^sub>a),R\<^sub>a,G\<^sub>a)")
    apply blast
   apply (rule Await_None_Sim_stutter_step, simp_all)
  by (meson Stable_def)

theorem Await_None_Sound: "\<lbrakk>\<xi> \<subseteq> \<alpha>; \<zeta> (Await b\<^sub>c C\<^sub>c) = None;
    Stable \<xi> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; \<gamma> \<subseteq> \<alpha>;
    \<forall>s\<^sub>c s\<^sub>a. \<turnstile> Await b\<^sub>c C\<^sub>c sat [{s\<^sub>c. (s\<^sub>c, s\<^sub>a) \<in> \<xi>} \<inter> b\<^sub>c \<inter> {s\<^sub>c}, Id, G\<^sub>c, {s\<^sub>c'. (s\<^sub>c', s\<^sub>a) \<in> \<gamma>}]\<rbrakk> 
    \<Longrightarrow> (Some (Await b\<^sub>c C\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (None, R\<^sub>a, G\<^sub>a)"
  by (simp add: prog_sim_pre_def Await_None_Sim)

definition not_stuck :: "'s set \<Rightarrow> 's com \<Rightarrow> bool"
  where "not_stuck b C = (\<forall>s. s \<in> b \<longrightarrow> (\<exists>t. (Some C, s) -c*\<rightarrow> (None, t)))"

lemma Await_Await_corresponding_step: "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<xi>; \<xi> \<subseteq> b\<^sub>c \<rightleftharpoons>\<^sub>r b\<^sub>a; (Some (Await b\<^sub>c C\<^sub>c), s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c');
      \<forall>s\<^sub>a. s\<^sub>a \<in> b\<^sub>a \<longrightarrow> (\<exists>t\<^sub>a. (Some C\<^sub>a, s\<^sub>a) -c*\<rightarrow> (None, t\<^sub>a)); Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; \<gamma> \<subseteq> \<alpha>;
      \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<longrightarrow> (\<exists>Q\<^sub>c. \<turnstile> Await b\<^sub>c C\<^sub>c sat [b\<^sub>c \<inter> {s\<^sub>c}, Id, G\<^sub>c, Q\<^sub>c] \<and> 
       (\<exists>Q\<^sub>a. \<turnstile> Await b\<^sub>a C\<^sub>a sat [b\<^sub>a \<inter> {s\<^sub>a}, Id, G\<^sub>a, Q\<^sub>a] \<and> (\<forall>s\<^sub>c s\<^sub>a. s\<^sub>c \<in> Q\<^sub>c \<and> s\<^sub>a \<in> Q\<^sub>a \<longrightarrow> (s\<^sub>c, s\<^sub>a) \<in> \<gamma>)))\<rbrakk> 
      \<Longrightarrow> \<exists>P\<^sub>a' s\<^sub>a'. (Some (Await b\<^sub>a C\<^sub>a), s\<^sub>a) -c\<rightarrow> (P\<^sub>a', s\<^sub>a') \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> 
          ((P\<^sub>c', s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a', s\<^sub>a'),R\<^sub>a,G\<^sub>a)"
proof-
  assume a0: "(s\<^sub>c, s\<^sub>a) \<in> \<xi>"
     and a1: "\<xi> \<subseteq> b\<^sub>c \<rightleftharpoons>\<^sub>r b\<^sub>a"
     and a2: "(Some (Await b\<^sub>c C\<^sub>c), s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c')"
     and a3: "\<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<longrightarrow> (\<exists>Q\<^sub>c. \<turnstile> Await b\<^sub>c C\<^sub>c sat [b\<^sub>c \<inter> {s\<^sub>c}, Id, G\<^sub>c, Q\<^sub>c] \<and> 
       (\<exists>Q\<^sub>a. \<turnstile> Await b\<^sub>a C\<^sub>a sat [b\<^sub>a \<inter> {s\<^sub>a}, Id, G\<^sub>a, Q\<^sub>a] \<and> (\<forall>s\<^sub>c s\<^sub>a. s\<^sub>c \<in> Q\<^sub>c \<and> s\<^sub>a \<in> Q\<^sub>a \<longrightarrow> (s\<^sub>c, s\<^sub>a) \<in> \<gamma>)))"
     and a4: " \<forall>s\<^sub>a. s\<^sub>a \<in> b\<^sub>a \<longrightarrow> (\<exists>t\<^sub>a. (Some C\<^sub>a, s\<^sub>a) -c*\<rightarrow> (None, t\<^sub>a))"
     and a5: "Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>"
     and a6: "\<gamma> \<subseteq> \<alpha>"

  from a2 have b0 : "P\<^sub>c' = None \<and> s\<^sub>c \<in> b\<^sub>c"
    by (rule ctran.cases, simp_all)
  with a0 a1 have b1: "s\<^sub>a \<in> b\<^sub>a"
    by (metis rel_guard_eq_true)
  with a4 have "\<exists>s\<^sub>a'. (Some C\<^sub>a, s\<^sub>a) -c*\<rightarrow> (None, s\<^sub>a')" by blast
  then obtain s\<^sub>a' where "(Some C\<^sub>a, s\<^sub>a) -c*\<rightarrow> (None, s\<^sub>a')" by blast
  with b1 have b2: "(Some (Await b\<^sub>a C\<^sub>a), s\<^sub>a) -c\<rightarrow> (None, s\<^sub>a')"
    by (simp add: ctran.Await)
  from a0 a3 have "\<exists>Q\<^sub>c. \<turnstile> Await b\<^sub>c C\<^sub>c sat [b\<^sub>c \<inter> {s\<^sub>c}, Id, G\<^sub>c, Q\<^sub>c] \<and> 
                  (\<exists>Q\<^sub>a. \<turnstile> Await b\<^sub>a C\<^sub>a sat [b\<^sub>a \<inter> {s\<^sub>a}, Id, G\<^sub>a, Q\<^sub>a] \<and> 
                  (\<forall>s\<^sub>c s\<^sub>a. s\<^sub>c \<in> Q\<^sub>c \<and> s\<^sub>a \<in> Q\<^sub>a \<longrightarrow> (s\<^sub>c, s\<^sub>a) \<in> \<gamma>))"
    by blast
  then obtain Q\<^sub>c Q\<^sub>a where b3: "\<turnstile> Await b\<^sub>c C\<^sub>c sat [b\<^sub>c \<inter> {s\<^sub>c}, Id, G\<^sub>c, Q\<^sub>c] \<and> \<turnstile> Await b\<^sub>a C\<^sub>a sat [b\<^sub>a \<inter> {s\<^sub>a}, Id, G\<^sub>a, Q\<^sub>a]
                          \<and> (\<forall>s\<^sub>c s\<^sub>a. s\<^sub>c \<in> Q\<^sub>c \<and> s\<^sub>a \<in> Q\<^sub>a \<longrightarrow> (s\<^sub>c, s\<^sub>a) \<in> \<gamma>)"
    by blast
  with a2 b0 b1 b2 have b4: "(s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> s\<^sub>c' \<in> Q\<^sub>c \<and> s\<^sub>a' \<in> Q\<^sub>a"
    by (meson Await_implies IntI insertI1)
  with b3 have b5: "(s\<^sub>c', s\<^sub>a') \<in> \<gamma>" by blast
  with a5 a6 have b6: "((None, s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((None, s\<^sub>a'),R\<^sub>a,G\<^sub>a)"
    by (simp add: None_Sim)
  with b0 b2 b4 b5 show ?thesis by blast
qed

lemma Await_Await_Sim: "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<xi>; \<xi> \<subseteq> \<alpha> \<inter> ( b\<^sub>c \<rightleftharpoons>\<^sub>r b\<^sub>a); \<zeta> (Await b\<^sub>c C\<^sub>c) = Some (Await b\<^sub>a C\<^sub>a);
      Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; \<gamma> \<subseteq> \<alpha>; Stable \<xi> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>;
      \<forall>s\<^sub>a. s\<^sub>a \<in> b\<^sub>a \<longrightarrow> (\<exists>t\<^sub>a. (Some C\<^sub>a, s\<^sub>a) -c*\<rightarrow> (None, t\<^sub>a));
      \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<longrightarrow> (\<exists>Q\<^sub>c Q\<^sub>a. \<turnstile> Await b\<^sub>c C\<^sub>c sat [b\<^sub>c \<inter> {s\<^sub>c}, Id, G\<^sub>c, Q\<^sub>c] \<and> \<turnstile> Await b\<^sub>a C\<^sub>a sat [b\<^sub>a \<inter> {s\<^sub>a}, Id, G\<^sub>a, Q\<^sub>a]
      \<and> (\<forall>s\<^sub>c s\<^sub>a. s\<^sub>c \<in> Q\<^sub>c \<and> s\<^sub>a \<in> Q\<^sub>a \<longrightarrow> (s\<^sub>c, s\<^sub>a) \<in> \<gamma>)) \<rbrakk> 
      \<Longrightarrow> ((Some (Await b\<^sub>c C\<^sub>c), s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some (Await b\<^sub>a C\<^sub>a), s\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduction arbitrary: s\<^sub>c s\<^sub>a, clarsimp)
  apply (rule conjI)
(* initial state *)
   apply blast
  apply (rule conjI, clarsimp)
   apply (drule_tac \<zeta> = \<zeta> in Await_Await_corresponding_step, simp_all)
   apply blast
  by (metis Stable_def)

theorem Await_Await_Sound: "\<lbrakk>\<xi> \<subseteq> \<alpha> \<inter> ( b\<^sub>c \<rightleftharpoons>\<^sub>r b\<^sub>a); \<zeta> (Await b\<^sub>c C\<^sub>c) = Some (Await b\<^sub>a C\<^sub>a); 
   Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; \<gamma> \<subseteq> \<alpha>; Stable \<xi> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>;  not_stuck b\<^sub>a C\<^sub>a;
   \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<longrightarrow> (\<exists>Q\<^sub>c Q\<^sub>a. \<turnstile> Await b\<^sub>c C\<^sub>c sat [b\<^sub>c \<inter> {s\<^sub>c}, Id, G\<^sub>c, Q\<^sub>c] \<and> \<turnstile> Await b\<^sub>a C\<^sub>a sat [b\<^sub>a \<inter> {s\<^sub>a}, Id, G\<^sub>a, Q\<^sub>a]
  \<and> (\<forall>s\<^sub>c s\<^sub>a. s\<^sub>c \<in> Q\<^sub>c \<and> s\<^sub>a \<in> Q\<^sub>a \<longrightarrow> (s\<^sub>c, s\<^sub>a) \<in> \<gamma>)) \<rbrakk> \<Longrightarrow> (Some (Await b\<^sub>c C\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (Some (Await b\<^sub>a C\<^sub>a), R\<^sub>a, G\<^sub>a)"
  by (simp add: prog_sim_pre_def Await_Await_Sim not_stuck_def)

lemma Basic_Await_corresponding_step: "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<xi>; \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<longrightarrow> s\<^sub>a \<in> b\<^sub>a \<and> (s\<^sub>c, f s\<^sub>c) \<in> G\<^sub>c; 
      \<forall>s\<^sub>a. s\<^sub>a \<in> b\<^sub>a \<longrightarrow> (\<exists>t\<^sub>a. (Some C\<^sub>a, s\<^sub>a) -c*\<rightarrow> (None, t\<^sub>a));
      \<forall>s\<^sub>c. \<turnstile> Await b\<^sub>a C\<^sub>a sat [{s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi>} \<inter> b\<^sub>a \<inter> {s\<^sub>a}, Id, G\<^sub>a, {s\<^sub>a'. (f s\<^sub>c, s\<^sub>a') \<in> \<gamma>}];
      Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; \<gamma> \<subseteq> \<alpha>\<rbrakk> 
     \<Longrightarrow> \<exists>P\<^sub>a' s\<^sub>a'. (Some (Await b\<^sub>a C\<^sub>a), s\<^sub>a) -c\<rightarrow> (P\<^sub>a', s\<^sub>a') \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> ((None, f s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a', s\<^sub>a'),R\<^sub>a,G\<^sub>a)"
proof-
  assume a0: "(s\<^sub>c, s\<^sub>a) \<in> \<xi>"
     and a1: "\<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<longrightarrow> s\<^sub>a \<in> b\<^sub>a \<and> (s\<^sub>c, f s\<^sub>c) \<in> G\<^sub>c"
     and a2: "\<forall>s\<^sub>a. s\<^sub>a \<in> b\<^sub>a \<longrightarrow> (\<exists>t\<^sub>a. (Some C\<^sub>a, s\<^sub>a) -c*\<rightarrow> (None, t\<^sub>a))"
     and a3: "\<forall>s\<^sub>c. \<turnstile> Await b\<^sub>a C\<^sub>a sat [{s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi>} \<inter> b\<^sub>a \<inter> {s\<^sub>a}, Id, G\<^sub>a, {s\<^sub>a'. (f s\<^sub>c, s\<^sub>a') \<in> \<gamma>}]"
     and a4: "Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>"
     and a5: "\<gamma> \<subseteq> \<alpha>"

  then have "\<exists>s\<^sub>a'. (Some C\<^sub>a, s\<^sub>a) -c*\<rightarrow> (None, s\<^sub>a')" by blast
  then obtain s\<^sub>a' where b0: "(Some C\<^sub>a, s\<^sub>a) -c*\<rightarrow> (None, s\<^sub>a')" by blast
  from a0 a1 have b1: "s\<^sub>a \<in> b\<^sub>a" by blast
  with b0 have b2: "(Some (Await b\<^sub>a C\<^sub>a), s\<^sub>a) -c\<rightarrow> (None, s\<^sub>a')"
    by (simp add: ctran.Await)

  from a3 have b30: "\<turnstile> Await b\<^sub>a C\<^sub>a sat [{s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi>} \<inter> b\<^sub>a \<inter> {s\<^sub>a}, Id, G\<^sub>a, {s\<^sub>a'. (f s\<^sub>c, s\<^sub>a') \<in> \<gamma>}]"
    by auto
  from a0 b1 have b31: "s\<^sub>a \<in> {s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi>} \<inter> b\<^sub>a \<inter> {s\<^sub>a}" by blast
  with b30 b2 have b3: "(s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> (f s\<^sub>c, s\<^sub>a') \<in> \<gamma>"
    by (metis Await_implies CollectD)
  with a4 a5 have b4: "((None, f s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((None, s\<^sub>a'),R\<^sub>a,G\<^sub>a)"
    by (simp add: None_Sim)
  with b2 b3 show ?thesis by blast
qed
    
lemma Basic_Await_Sim: "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<xi>; \<xi> \<subseteq> \<alpha>;  Stable \<xi> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; \<zeta> (Basic f\<^sub>c) = Some (Await b\<^sub>a C\<^sub>a);
      Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; \<gamma> \<subseteq> \<alpha>;
      \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<longrightarrow> s\<^sub>a \<in> b\<^sub>a \<and> (s\<^sub>c, f\<^sub>c s\<^sub>c) \<in> G\<^sub>c;
      \<forall>s\<^sub>a. s\<^sub>a \<in> b\<^sub>a \<longrightarrow> (\<exists>t\<^sub>a. (Some C\<^sub>a, s\<^sub>a) -c*\<rightarrow> (None, t\<^sub>a)); 
      \<forall>s\<^sub>c s\<^sub>a.  \<turnstile> Await b\<^sub>a C\<^sub>a sat [{s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi>} \<inter> b\<^sub>a \<inter> {s\<^sub>a}, Id, G\<^sub>a, {s\<^sub>a'. (f\<^sub>c s\<^sub>c, s\<^sub>a') \<in> \<gamma>}]\<rbrakk> 
      \<Longrightarrow> ((Some (Basic f\<^sub>c), s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some (Await b\<^sub>a C\<^sub>a), s\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduction arbitrary: s\<^sub>c s\<^sub>a, clarsimp)
  apply (rule conjI)
(* initial state *)
   apply blast
  apply (rule conjI, clarsimp)
   apply (erule ctran.cases, simp_all)
   apply (drule Basic_Await_corresponding_step, simp_all)
  by (meson Stable_def)

theorem Basic_Await_Sound: "\<lbrakk>\<xi> \<subseteq> \<alpha>;  Stable \<xi> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; \<zeta> (Basic f\<^sub>c) = Some (Await b\<^sub>a C\<^sub>a);
      Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; \<gamma> \<subseteq> \<alpha>; not_stuck b\<^sub>a C\<^sub>a;
      \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<longrightarrow> s\<^sub>a \<in> b\<^sub>a \<and> (s\<^sub>c, f\<^sub>c s\<^sub>c) \<in> G\<^sub>c;
      \<forall>s\<^sub>c s\<^sub>a.  \<turnstile> Await b\<^sub>a C\<^sub>a sat [{s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi>} \<inter> b\<^sub>a \<inter> {s\<^sub>a}, Id, G\<^sub>a, {s\<^sub>a'. (f\<^sub>c s\<^sub>c, s\<^sub>a') \<in> \<gamma>}]\<rbrakk> \<Longrightarrow> (
      Some (Basic f\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (Some (Await b\<^sub>a C\<^sub>a), R\<^sub>a, G\<^sub>a)"
  by (simp add: not_stuck_def prog_sim_pre_def Basic_Await_Sim)








end


