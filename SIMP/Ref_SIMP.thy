theory Ref_SIMP
  imports RG_Tran RG_Hoare "../VHelper"
begin

definition related_transitions:: "('s\<^sub>c \<times> 's\<^sub>c) set \<Rightarrow> ('s\<^sub>a \<times> 's\<^sub>a) set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>a) set \<Rightarrow> 
                                  (('s\<^sub>c \<times> 's\<^sub>c) \<times> ('s\<^sub>a \<times> 's\<^sub>a)) set" ("'(_, _')\<^sub>_" ) 
  where "related_transitions R R' \<alpha> = {((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')). (\<sigma>,\<sigma>')\<in> R \<and> (\<Sigma>,\<Sigma>')\<in>R' 
                                      \<and>(\<sigma>, \<Sigma>) \<in> \<alpha> \<and> (\<sigma>', \<Sigma>') \<in> \<alpha>}"

definition rel_eq :: "'s\<^sub>c set \<Rightarrow> 's\<^sub>a set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>a) set" ("_ \<rightleftharpoons>\<^sub>r _" [70, 70] 60)
  where "rel_eq g\<^sub>c g\<^sub>a = {(\<sigma>, \<Sigma>). (\<sigma> \<in> g\<^sub>c) = (\<Sigma> \<in> g\<^sub>a)}"

definition rel_and :: "'s\<^sub>c set \<Rightarrow> 's\<^sub>a set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>a) set" ("_\<and>\<^sub>r_" [70, 70] 60) 
  where "rel_and g\<^sub>c g\<^sub>a = {(\<sigma>, \<Sigma>). \<sigma> \<in> g\<^sub>c \<and> \<Sigma> \<in> g\<^sub>a}"

definition rel_comp :: " ('s\<^sub>m \<times> 's\<^sub>a) set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>m) set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>a) set" ("_ \<bullet> _" [79, 70] 60)
  where "rel_comp \<beta> \<alpha> = {(\<sigma>, \<Sigma>). (\<exists>\<theta>. (\<sigma>, \<theta>) \<in> \<alpha> \<and> (\<theta>, \<Sigma>) \<in> \<beta>)}" 

lemma rel_eq_true : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<xi>; s\<^sub>c \<in> g\<^sub>c;  \<xi> \<subseteq> g\<^sub>c \<rightleftharpoons>\<^sub>r g\<^sub>a\<rbrakk> \<Longrightarrow> s\<^sub>a \<in> g\<^sub>a"
  apply (simp add: rel_eq_def)
  by blast

lemma rel_eq_false : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<xi>; s\<^sub>c \<notin> g\<^sub>c;  \<xi> \<subseteq> g\<^sub>c \<rightleftharpoons>\<^sub>r g\<^sub>a\<rbrakk> \<Longrightarrow> s\<^sub>a \<notin> g\<^sub>a"
  apply (simp add: rel_eq_def)
  by blast

definition Stable :: "('s\<^sub>c \<times> 's\<^sub>a) set \<Rightarrow> (('s\<^sub>c \<times> 's\<^sub>c) \<times> ('s\<^sub>a \<times> 's\<^sub>a)) set \<Rightarrow> bool" 
  where "Stable \<zeta> \<Delta> = (\<forall>\<sigma> \<sigma>' \<Sigma> \<Sigma>'. (\<sigma>, \<Sigma>) \<in> \<zeta> \<longrightarrow> ((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')) \<in> \<Delta> \<longrightarrow> (\<sigma>', \<Sigma>') \<in> \<zeta> )"

definition isMidof :: "('s\<^sub>m \<times> 's\<^sub>m) set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>m) set \<Rightarrow>('s\<^sub>m \<times> 's\<^sub>a) set \<Rightarrow> 
                       ('s\<^sub>c \<times> 's\<^sub>c) set \<Rightarrow> ('s\<^sub>a \<times> 's\<^sub>a) set \<Rightarrow> bool"
  where "isMidof R\<^sub>m \<alpha> \<beta> R\<^sub>c R\<^sub>a = (\<forall>s\<^sub>c s\<^sub>c' s\<^sub>a s\<^sub>a' s\<^sub>m. ((s\<^sub>c, s\<^sub>c'), (s\<^sub>a, s\<^sub>a')) \<in> related_transitions R\<^sub>c R\<^sub>a (\<beta> \<bullet> \<alpha>)
  \<longrightarrow> (s\<^sub>c, s\<^sub>m) \<in> \<alpha> \<and> (s\<^sub>m, s\<^sub>a) \<in> \<beta> \<longrightarrow> (\<exists>s\<^sub>m'. (((s\<^sub>c, s\<^sub>c'), (s\<^sub>m, s\<^sub>m')) \<in> related_transitions R\<^sub>c R\<^sub>m \<alpha>) \<and> 
                                            ((s\<^sub>m, s\<^sub>m'), (s\<^sub>a, s\<^sub>a')) \<in> related_transitions R\<^sub>m R\<^sub>a \<beta>))"

lemma non_no_tran: "(None, s) -c\<rightarrow> (P, t) \<Longrightarrow> False"
  by (erule ctran.cases, simp_all)

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

lemma prog_sim_finish: "\<lbrakk>((P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a); P\<^sub>c = None\<rbrakk> \<Longrightarrow> P\<^sub>a = None \<and> (s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<and> \<gamma> \<subseteq> \<alpha>"
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

(*
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
*)

lemma If_None_Sim: "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<xi>; \<xi> \<subseteq> \<alpha>; \<zeta> (Cond b\<^sub>c C1\<^sub>c C2\<^sub>c) = None;  Stable \<xi> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>;
                     \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<and> s\<^sub>c \<in> b\<^sub>c \<longrightarrow> ((Some C1\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((C\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a);
                     \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<and> s\<^sub>c \<notin> b\<^sub>c \<longrightarrow> ((Some C2\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((C\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)
                     \<rbrakk> \<Longrightarrow> ((Some (Cond b\<^sub>c C1\<^sub>c C2\<^sub>c), s\<^sub>c), R\<^sub>c, (G\<^sub>c \<union> Id)) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((C\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)"
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
        (Some C1\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (C\<^sub>a, R\<^sub>a, G\<^sub>a); (Some C2\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>2\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (C\<^sub>a, R\<^sub>a, G\<^sub>a);
        \<xi>\<^sub>1 = \<xi> \<inter> {(s\<^sub>c, s\<^sub>a).  s\<^sub>c \<in> b\<^sub>c}; \<xi>\<^sub>2 = \<xi> \<inter> {(s\<^sub>c, s\<^sub>a).  s\<^sub>c \<notin> b\<^sub>c}\<rbrakk> 
        \<Longrightarrow> (Some (Cond b\<^sub>c C1\<^sub>c C2\<^sub>c), R\<^sub>c, (G\<^sub>c \<union> Id)) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (C\<^sub>a, R\<^sub>a, G\<^sub>a)"
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
  apply (simp add: rel_and_def rel_eq_def)
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
    by (metis rel_eq_true)
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


definition coPre_None :: "[ 's\<^sub>c set, 's\<^sub>c com, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
    ('s\<^sub>c \<times> 's\<^sub>a) set, 's\<^sub>c com \<rightharpoonup> 's\<^sub>a com, 's\<^sub>c com \<rightharpoonup> 's\<^sub>a com, ('s\<^sub>c \<times> 's\<^sub>a) set, 
    ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set,

     's\<^sub>c conf, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
     ('s\<^sub>c \<times> 's\<^sub>a) set, 's\<^sub>c com \<rightharpoonup> 's\<^sub>a com, ('s\<^sub>c \<times> 's\<^sub>a) set,
     's\<^sub>a conf, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool"
  where "coPre_None b\<^sub>c C\<^sub>c R\<^sub>c G\<^sub>c \<alpha> \<zeta> \<zeta>\<^sub>1 \<gamma> R\<^sub>a G\<^sub>a conf\<^sub>c R\<^sub>c' G\<^sub>c' \<alpha>' \<zeta>' \<gamma>' conf\<^sub>a R\<^sub>a' G\<^sub>a' \<equiv>
        R\<^sub>c' = R\<^sub>c \<and> G\<^sub>c' = G\<^sub>c\<^sup>= \<and> R\<^sub>a' = R\<^sub>a \<and> G\<^sub>a' = G\<^sub>a \<and> \<alpha>' = \<alpha> \<and> \<zeta>' = \<zeta> \<and> \<gamma>' = \<gamma> \<and> 
        (\<exists>s\<^sub>c s\<^sub>a. 

        (conf\<^sub>c = (Some (While b\<^sub>c C\<^sub>c), s\<^sub>c) \<and> conf\<^sub>a = (None, s\<^sub>a) \<and> (s\<^sub>c, s\<^sub>a) \<in> \<gamma>) \<or>

        (\<exists>P\<^sub>c. conf\<^sub>c = (Some (Seq P\<^sub>c (While b\<^sub>c C\<^sub>c)), s\<^sub>c) \<and> conf\<^sub>a = (None, s\<^sub>a) \<and>
        ((Some P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>) ((None, s\<^sub>a), R\<^sub>a, G\<^sub>a)) \<or>
  
        (conf\<^sub>c = (None, s\<^sub>c) \<and> conf\<^sub>a = (None, s\<^sub>a) \<and> (s\<^sub>c, s\<^sub>a) \<in> \<gamma>)
        )"


lemma While_None_Sim: "\<lbrakk>\<zeta> (While b\<^sub>c C\<^sub>c) = None; (s\<^sub>c, s\<^sub>a) \<in> \<gamma>; \<gamma> \<subseteq> \<alpha>;  
      \<forall>P\<^sub>c. \<zeta>\<^sub>1 P\<^sub>c = None \<longrightarrow> \<zeta> (Seq P\<^sub>c (While b\<^sub>c C\<^sub>c)) = None;  Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>;
      \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<and> s\<^sub>c \<in> b\<^sub>c \<longrightarrow> ((Some C\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>) ((None, s\<^sub>a), R\<^sub>a, G\<^sub>a)\<rbrakk> 
                    \<Longrightarrow> ((Some (While b\<^sub>c C\<^sub>c), s\<^sub>c), R\<^sub>c, G\<^sub>c\<^sup>=) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((None, s\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduct taking: "coPre_None b\<^sub>c C\<^sub>c R\<^sub>c G\<^sub>c \<alpha> \<zeta> \<zeta>\<^sub>1 \<gamma> R\<^sub>a G\<^sub>a" rule:prog_sim.coinduct)
   apply (simp add: coPre_None_def, clarsimp)
  apply (rule conjI, simp add: coPre_None_def, clarify)
(* initial state *)
   apply (meson prog_sim_init subset_iff)
  apply (rule conjI, simp add: coPre_None_def, clarsimp)
(* stutter step *)
   apply (case_tac "a = None", simp)
    apply (meson non_no_tran)
   apply (case_tac "a = Some (While b\<^sub>c C\<^sub>c)", clarsimp)
    apply (erule ctran.cases, simp_all)
   apply (erule ctran.cases, simp_all)
  apply (meson prog_sim_corresponding_step prog_sim_guar prog_sim_sttuter_step_finish)
   apply (metis prog_sim_corresponding_step prog_sim_sttuter_step)
(* corresponding step, impossible *)
  apply (rule conjI, simp add: coPre_None_def, clarsimp)
   apply (metis (no_types, opaque_lifting) Seq_cases non_no_tran option.distinct(1) option.sel prog_sim_corresponding_step)
(* env interf *)
  apply (simp add: coPre_None_def)
  apply auto[1]
    apply (meson Stable_def)
   apply (meson prog_env_interf)
  by (meson Stable_def)


definition coPre :: "['s\<^sub>c set, 's\<^sub>c com, 's\<^sub>a set, 's\<^sub>a com, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
    ('s\<^sub>c \<times> 's\<^sub>a) set, 's\<^sub>c com \<rightharpoonup> 's\<^sub>a com, 's\<^sub>c com \<rightharpoonup> 's\<^sub>a com, ('s\<^sub>c \<times> 's\<^sub>a) set, 
    ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set,

     's\<^sub>c conf, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
     ('s\<^sub>c \<times> 's\<^sub>a) set, 's\<^sub>c com \<rightharpoonup> 's\<^sub>a com, ('s\<^sub>c \<times> 's\<^sub>a) set,
     's\<^sub>a conf, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool"
  where "coPre b\<^sub>c C\<^sub>c b\<^sub>a C\<^sub>a R\<^sub>c G\<^sub>c \<alpha> \<zeta> \<zeta>\<^sub>1 \<gamma> R\<^sub>a G\<^sub>a conf\<^sub>c R\<^sub>c' G\<^sub>c' \<alpha>' \<zeta>' \<gamma>' conf\<^sub>a R\<^sub>a' G\<^sub>a' \<equiv>
        R\<^sub>c' = R\<^sub>c \<and> G\<^sub>c' = G\<^sub>c\<^sup>= \<and> R\<^sub>a' = R\<^sub>a \<and> G\<^sub>a' = G\<^sub>a\<^sup>= \<and> \<alpha>' = \<alpha> \<and> \<zeta>' = \<zeta> \<and> \<gamma>' = \<gamma>  \<inter> (-b\<^sub>c \<and>\<^sub>r -b\<^sub>a) \<and> 
        (\<exists>s\<^sub>c s\<^sub>a. 

        (conf\<^sub>c = (Some (While b\<^sub>c C\<^sub>c), s\<^sub>c) \<and> conf\<^sub>a = (Some (While b\<^sub>a C\<^sub>a), s\<^sub>a) \<and> (s\<^sub>c, s\<^sub>a) \<in> \<gamma>) \<or>

        (\<exists>P\<^sub>c P\<^sub>a. conf\<^sub>c = (Some (Seq P\<^sub>c (While b\<^sub>c C\<^sub>c)), s\<^sub>c) \<and> conf\<^sub>a = (Some (Seq P\<^sub>a (While b\<^sub>a C\<^sub>a)), s\<^sub>a) \<and>
        ((Some P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)) \<or>

        (\<exists>P\<^sub>c. conf\<^sub>c = (Some (Seq P\<^sub>c (While b\<^sub>c C\<^sub>c)), s\<^sub>c) \<and> conf\<^sub>a = (Some (While b\<^sub>a C\<^sub>a), s\<^sub>a) \<and>
        ((Some P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>) ((None, s\<^sub>a), R\<^sub>a, G\<^sub>a)) \<or>
  
        (conf\<^sub>c = (None, s\<^sub>c) \<and> conf\<^sub>a = (None, s\<^sub>a) \<and> (s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<inter> (-b\<^sub>c \<and>\<^sub>r -b\<^sub>a))
        )"

thm prog_sim_corresponding_step

lemma While_While_corresponding_step: "\<lbrakk>((Some P\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some P\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a);
                                        (Some P\<^sub>c, s\<^sub>c) -c\<rightarrow> (Some P\<^sub>c', s\<^sub>c'); \<zeta>\<^sub>1 P\<^sub>c \<noteq> None \<rbrakk> \<Longrightarrow> 
          \<exists>C\<^sub>a' s\<^sub>a'.
          (Some (Seq P\<^sub>a (While b\<^sub>a C\<^sub>a)), s\<^sub>a) -c\<rightarrow> (C\<^sub>a', s\<^sub>a') \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> 

          (
          (\<exists>P\<^sub>a'. C\<^sub>a' = Some (Seq P\<^sub>a' (While b\<^sub>a C\<^sub>a)) \<and> ((Some P\<^sub>c', s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some P\<^sub>a', s\<^sub>a'),R\<^sub>a,G\<^sub>a)) \<or>

          (C\<^sub>a' = Some (While b\<^sub>a C\<^sub>a) \<and> ((Some P\<^sub>c', s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>) ((None, s\<^sub>a'),R\<^sub>a,G\<^sub>a))

          )"
proof-
  assume a0: "((Some P\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some P\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a)"
     and a1: "(Some P\<^sub>c, s\<^sub>c) -c\<rightarrow> (Some P\<^sub>c', s\<^sub>c')"
     and a2: " \<zeta>\<^sub>1 P\<^sub>c \<noteq> None"

  then have "\<zeta>\<^sub>1 P\<^sub>c = Some P\<^sub>a \<and> (\<exists>P\<^sub>a' s\<^sub>a'. (Some P\<^sub>a, s\<^sub>a) -c\<rightarrow> (P\<^sub>a', s\<^sub>a') \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a 
            \<and> ((Some P\<^sub>c', s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a', s\<^sub>a'),R\<^sub>a,G\<^sub>a))"
    using prog_sim_corresponding_step by fastforce
  then obtain P\<^sub>a' s\<^sub>a' where b0: "\<zeta>\<^sub>1 P\<^sub>c = Some P\<^sub>a \<and> (Some P\<^sub>a, s\<^sub>a) -c\<rightarrow> (P\<^sub>a', s\<^sub>a') \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c
   \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> ((Some P\<^sub>c', s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a', s\<^sub>a'),R\<^sub>a,G\<^sub>a)" by blast
  then show ?thesis
  proof(cases P\<^sub>a')
    assume c0: "P\<^sub>a' = None"
    with b0 have c1: "(Some (Seq P\<^sub>a (While b\<^sub>a C\<^sub>a)), s\<^sub>a) -c\<rightarrow> (Some (While b\<^sub>a C\<^sub>a), s\<^sub>a')"
      by (simp add: ctran.Seq1)
    with b0 c0 show ?thesis by metis
  next
    case (Some P)
    assume d0: "P\<^sub>a' = Some P"
    with b0 have d1: "(Some (Seq P\<^sub>a (While b\<^sub>a C\<^sub>a)), s\<^sub>a) -c\<rightarrow> (Some (Seq P (While b\<^sub>a C\<^sub>a)), s\<^sub>a')"
      by (simp add: ctran.Seq2)
    with b0 d0 show ?thesis by metis
  qed
qed


lemma While_While_Sim: "\<lbrakk>\<zeta> (While b\<^sub>c C\<^sub>c) = Some (While b\<^sub>a C\<^sub>a); \<gamma> \<subseteq> (b\<^sub>c \<rightleftharpoons>\<^sub>r b\<^sub>a); (s\<^sub>c, s\<^sub>a) \<in> \<gamma>; \<gamma> \<subseteq> \<alpha>;
      \<gamma>\<^sub>1 = \<gamma> \<inter> (-b\<^sub>c \<and>\<^sub>r -b\<^sub>a); Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; \<forall>P\<^sub>c. \<zeta> (Seq P\<^sub>c (While b\<^sub>c C\<^sub>c)) = None \<longrightarrow> \<zeta>\<^sub>1 P\<^sub>c = None; 
      Stable \<gamma>\<^sub>1 (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>;
      \<forall>P\<^sub>c. \<zeta> (Seq P\<^sub>c (While b\<^sub>c C\<^sub>c)) \<noteq> None \<longrightarrow> (\<exists>P\<^sub>a. \<zeta>\<^sub>1 P\<^sub>c = Some P\<^sub>a \<and> \<zeta> (Seq P\<^sub>c (While b\<^sub>c C\<^sub>c)) = Some (Seq P\<^sub>a (While b\<^sub>a C\<^sub>a)));
      \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<gamma> \<inter> (b\<^sub>c \<and>\<^sub>r b\<^sub>a) \<longrightarrow> ((Some C\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some C\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)\<rbrakk> 
                    \<Longrightarrow> ((Some (While b\<^sub>c C\<^sub>c), s\<^sub>c), R\<^sub>c, G\<^sub>c\<^sup>=) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((Some (While b\<^sub>a C\<^sub>a), s\<^sub>a), R\<^sub>a, G\<^sub>a\<^sup>=)"
  apply (coinduct taking: "coPre b\<^sub>c C\<^sub>c b\<^sub>a C\<^sub>a R\<^sub>c G\<^sub>c \<alpha> \<zeta> \<zeta>\<^sub>1 \<gamma> R\<^sub>a G\<^sub>a" rule:prog_sim.coinduct)
   apply (simp add: coPre_def, clarsimp)
  apply (rule conjI, simp add: coPre_def)
(* initial state *)
   apply (meson prog_sim_init subsetD)
  apply (rule conjI, simp add: coPre_def, clarify)
(* stutter step *)
   apply (case_tac "a = Some (While b\<^sub>c C\<^sub>c)", simp)
   apply (case_tac "a = None")
    apply (metis non_no_tran)
   apply (case_tac "\<exists>P\<^sub>c. a = Some (Seq P\<^sub>c (While b\<^sub>c C\<^sub>c)) \<and> b = s\<^sub>c' \<and> aa = Some (While b\<^sub>a C\<^sub>a) \<and> ba = s\<^sub>a'
          \<and> ((Some P\<^sub>c, s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>) ((None, s\<^sub>a'),R\<^sub>a,G\<^sub>a)")
    apply (erule ctran.cases, simp_all)
     apply (metis option.sel prog_sim_guar prog_sim_sttuter_step_finish)
    apply (metis option.sel prog_sim_sttuter_step)
   apply clarsimp
   apply (metis (no_types, lifting) Pair_inject Seq_cases option.distinct(1) option.sel 
          prog_sim_sttuter_step prog_sim_sttuter_step_finish)
  apply (rule conjI, simp add: coPre_def, clarify)
(* corresponding step *)
   apply (case_tac "\<exists>P\<^sub>c. a = Some (Seq P\<^sub>c (While b\<^sub>c C\<^sub>c)) \<and> b = s\<^sub>c' \<and> (\<exists>P\<^sub>a. aa = Some (Seq P\<^sub>a (While b\<^sub>a C\<^sub>a)) 
          \<and> ba = s\<^sub>a' \<and> ((Some P\<^sub>c, s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some P\<^sub>a, s\<^sub>a'),R\<^sub>a,G\<^sub>a))")
    apply clarsimp
    apply (rule conjI)
     apply (metis (no_types, opaque_lifting) Seq_cases option.distinct(1) option.sel prog_sim_corresponding_step)
    apply (erule ctran.cases, simp_all)
     apply (metis (no_types, opaque_lifting) Seq_Sim_Corresponding_Finish option.distinct(1))
    apply (drule_tac b\<^sub>a = b\<^sub>a and C\<^sub>a = C\<^sub>a in While_While_corresponding_step, simp_all)
     apply blast
    apply (metis (full_types))
   apply (case_tac "a = None")
  using non_no_tran apply fastforce
   apply (case_tac "\<exists>P\<^sub>c. a = Some (Seq P\<^sub>c (While b\<^sub>c C\<^sub>c)) \<and> b = s\<^sub>c' \<and> aa = Some (While b\<^sub>a C\<^sub>a) \<and> ba = s\<^sub>a'
          \<and> ((Some P\<^sub>c, s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>) ((None, s\<^sub>a'),R\<^sub>a,G\<^sub>a)")
    apply (metis (no_types, lifting) Seq_cases option.distinct(1) option.sel prog_sim_corresponding_step)
    apply (erule ctran.cases, simp_all)
     apply (case_tac "ba \<in> b\<^sub>a")
      apply (meson rel_eq_false)
     apply (rule_tac x = None and y = ba in ex2I, simp add: rel_and_def)
     apply (meson ctran.WhileF)
    apply (case_tac "ba \<in> b\<^sub>a")
     apply (rule_tac x = "Some (Seq C\<^sub>a (While b\<^sub>a C\<^sub>a))" and y = ba in ex2I, simp add: rel_and_def)
     apply (meson ctran.WhileT)
   apply (meson rel_eq_true)
(* env interf *)
  apply (simp add: coPre_def)
  apply auto[1]
      apply (meson Stable_def)
     apply (meson prog_env_interf)
    apply (meson prog_env_interf)
   apply (meson Stable_def)
  by (metis Int_iff Stable_def)

theorem While_While_Sound: "\<lbrakk>\<zeta> (While b\<^sub>c C\<^sub>c) = Some (While b\<^sub>a C\<^sub>a); \<gamma> \<subseteq> (b\<^sub>c \<rightleftharpoons>\<^sub>r b\<^sub>a); \<gamma> \<subseteq> \<alpha>; 
        Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; Stable \<gamma>\<^sub>2 (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>;
        \<forall>P\<^sub>c. \<zeta> (Seq P\<^sub>c (While b\<^sub>c C\<^sub>c)) = None \<longrightarrow> \<zeta>\<^sub>1 P\<^sub>c = None; \<forall>P\<^sub>c. \<zeta> (Seq P\<^sub>c (While b\<^sub>c C\<^sub>c)) \<noteq> None 
        \<longrightarrow> (\<exists>P\<^sub>a. \<zeta>\<^sub>1 P\<^sub>c = Some P\<^sub>a \<and> \<zeta> (Seq P\<^sub>c (While b\<^sub>c C\<^sub>c)) = Some (Seq P\<^sub>a (While b\<^sub>a C\<^sub>a)));    
        (Some C\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (Some C\<^sub>a, R\<^sub>a, G\<^sub>a); \<gamma>\<^sub>1 = \<gamma> \<inter> (b\<^sub>c \<and>\<^sub>r b\<^sub>a); \<gamma>\<^sub>2 = \<gamma> \<inter> (-b\<^sub>c \<and>\<^sub>r -b\<^sub>a)\<rbrakk> \<Longrightarrow> 
        (Some (While b\<^sub>c C\<^sub>c), R\<^sub>c, G\<^sub>c\<^sup>=) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>2\<^sub>) (Some (While b\<^sub>a C\<^sub>a), R\<^sub>a, G\<^sub>a\<^sup>=)"
  by (simp add: prog_sim_pre_def While_While_Sim)

lemma Trans_Sim_stutter_step: "\<lbrakk>((Some P\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>1\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((C\<^sub>m, s\<^sub>m),R\<^sub>m,G\<^sub>m);
      ((C\<^sub>m, s\<^sub>m),R\<^sub>m,G\<^sub>m) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>2\<^sub>;\<^sub>\<zeta>\<^sub>2\<^sub>;\<^sub>\<gamma>\<^sub>2\<^sub>) ((C\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a); (Some P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c');
      \<zeta>\<^sub>1 P\<^sub>c \<noteq> None; (\<zeta>\<^sub>2 \<circ>\<^sub>m \<zeta>\<^sub>1) P\<^sub>c = None\<rbrakk> \<Longrightarrow> 
      \<exists>s\<^sub>m' C\<^sub>m'. ((P\<^sub>c', s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>1\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((C\<^sub>m', s\<^sub>m'),R\<^sub>m,G\<^sub>m) \<and> ((C\<^sub>m', s\<^sub>m'),R\<^sub>m,G\<^sub>m) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>2\<^sub>;\<^sub>\<zeta>\<^sub>2\<^sub>;\<^sub>\<gamma>\<^sub>2\<^sub>) ((C\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a)"
proof-
  assume a0: "((Some P\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>1\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((C\<^sub>m, s\<^sub>m),R\<^sub>m,G\<^sub>m)"
     and a1: "((C\<^sub>m, s\<^sub>m),R\<^sub>m,G\<^sub>m) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>2\<^sub>;\<^sub>\<zeta>\<^sub>2\<^sub>;\<^sub>\<gamma>\<^sub>2\<^sub>) ((C\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a)"
     and a2: "(Some P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c')"
     and a3: "\<zeta>\<^sub>1 P\<^sub>c \<noteq> None"
     and a4: "(\<zeta>\<^sub>2 \<circ>\<^sub>m \<zeta>\<^sub>1) P\<^sub>c = None"

  from a0 a2 a3 have "\<zeta>\<^sub>1 P\<^sub>c = C\<^sub>m \<and> (\<exists>s\<^sub>m' C\<^sub>m'. (C\<^sub>m, s\<^sub>m) -c\<rightarrow> (C\<^sub>m', s\<^sub>m') \<and> ((P\<^sub>c', s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>1\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((C\<^sub>m', s\<^sub>m'),R\<^sub>m,G\<^sub>m))"
    using prog_sim_corresponding_step by fastforce
  then obtain s\<^sub>m' C\<^sub>m' where b0: "\<zeta>\<^sub>1 P\<^sub>c = C\<^sub>m \<and> (C\<^sub>m, s\<^sub>m) -c\<rightarrow> (C\<^sub>m', s\<^sub>m') \<and> ((P\<^sub>c', s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>1\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((C\<^sub>m', s\<^sub>m'),R\<^sub>m,G\<^sub>m)"
    by auto
  with a3 a4 have b1: "\<zeta>\<^sub>2 (the C\<^sub>m) = None" by force
  with a1 b0 have b2: "((C\<^sub>m', s\<^sub>m'),R\<^sub>m,G\<^sub>m) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>2\<^sub>;\<^sub>\<zeta>\<^sub>2\<^sub>;\<^sub>\<gamma>\<^sub>2\<^sub>) ((C\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a)"
    by (meson prog_sim_sttuter_step)
  with b0 show ?thesis by auto
qed

lemma Trans_Sim_coresponding_step: "\<lbrakk>((Some P\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>1\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((C\<^sub>m, s\<^sub>m),R\<^sub>m,G\<^sub>m);
      ((C\<^sub>m, s\<^sub>m),R\<^sub>m,G\<^sub>m) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>2\<^sub>;\<^sub>\<zeta>\<^sub>2\<^sub>;\<^sub>\<gamma>\<^sub>2\<^sub>) ((C\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a); (Some P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c');
      (\<zeta>\<^sub>2 \<circ>\<^sub>m \<zeta>\<^sub>1) P\<^sub>c \<noteq> None\<rbrakk> \<Longrightarrow> (\<zeta>\<^sub>2 \<circ>\<^sub>m \<zeta>\<^sub>1) P\<^sub>c = C\<^sub>a \<and> 
      (\<exists>C\<^sub>a' s\<^sub>a'. (C\<^sub>a, s\<^sub>a) -c\<rightarrow> (C\<^sub>a', s\<^sub>a') \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and>
      (\<exists>s\<^sub>m' C\<^sub>m'. ((P\<^sub>c', s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>1\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((C\<^sub>m', s\<^sub>m'),R\<^sub>m,G\<^sub>m) \<and> ((C\<^sub>m', s\<^sub>m'),R\<^sub>m,G\<^sub>m) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>2\<^sub>;\<^sub>\<zeta>\<^sub>2\<^sub>;\<^sub>\<gamma>\<^sub>2\<^sub>) ((C\<^sub>a', s\<^sub>a'),R\<^sub>a,G\<^sub>a)))"
proof-
  assume a0: "((Some P\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>1\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((C\<^sub>m, s\<^sub>m),R\<^sub>m,G\<^sub>m)"
     and a1: "((C\<^sub>m, s\<^sub>m),R\<^sub>m,G\<^sub>m) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>2\<^sub>;\<^sub>\<zeta>\<^sub>2\<^sub>;\<^sub>\<gamma>\<^sub>2\<^sub>) ((C\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a)"
     and a2: "(Some P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c')"
     and a3: "(\<zeta>\<^sub>2 \<circ>\<^sub>m \<zeta>\<^sub>1) P\<^sub>c \<noteq> None"

  from a3 have b0: "\<zeta>\<^sub>1 P\<^sub>c \<noteq> None"
    by (simp add: map_comp_None_iff)
  with a0 a2 have "\<zeta>\<^sub>1 P\<^sub>c = C\<^sub>m \<and> (\<exists>s\<^sub>m' C\<^sub>m'. (C\<^sub>m, s\<^sub>m) -c\<rightarrow> (C\<^sub>m', s\<^sub>m') \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> ((P\<^sub>c', s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>1\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((C\<^sub>m', s\<^sub>m'),R\<^sub>m,G\<^sub>m))"
    using prog_sim_corresponding_step by fastforce
  then obtain s\<^sub>m' C\<^sub>m' where b0: "\<zeta>\<^sub>1 P\<^sub>c = C\<^sub>m \<and> (C\<^sub>m, s\<^sub>m) -c\<rightarrow> (C\<^sub>m', s\<^sub>m') \<and> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c \<and> ((P\<^sub>c', s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>1\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((C\<^sub>m', s\<^sub>m'),R\<^sub>m,G\<^sub>m)"
    by auto
  with a3 have b1: "\<zeta>\<^sub>2 (the C\<^sub>m) \<noteq> None"
    by (metis map_comp_None_iff option.exhaust_sel)
  with b0 a1 have "\<zeta>\<^sub>2 (the C\<^sub>m) = C\<^sub>a \<and> (\<exists>C\<^sub>a' s\<^sub>a'. (C\<^sub>a, s\<^sub>a) -c\<rightarrow> (C\<^sub>a', s\<^sub>a') \<and>
            (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> ((C\<^sub>m', s\<^sub>m'),R\<^sub>m,G\<^sub>m) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>2\<^sub>;\<^sub>\<zeta>\<^sub>2\<^sub>;\<^sub>\<gamma>\<^sub>2\<^sub>) ((C\<^sub>a', s\<^sub>a'),R\<^sub>a,G\<^sub>a))"
    by (meson prog_sim_corresponding_step)
  then obtain C\<^sub>a' s\<^sub>a' where b2: "\<zeta>\<^sub>2 (the C\<^sub>m) = C\<^sub>a \<and> (C\<^sub>a, s\<^sub>a) -c\<rightarrow> (C\<^sub>a', s\<^sub>a') \<and> (s\<^sub>a, s\<^sub>a') \<in> G\<^sub>a \<and> ((C\<^sub>m', s\<^sub>m'),R\<^sub>m,G\<^sub>m) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>2\<^sub>;\<^sub>\<zeta>\<^sub>2\<^sub>;\<^sub>\<gamma>\<^sub>2\<^sub>) ((C\<^sub>a', s\<^sub>a'),R\<^sub>a,G\<^sub>a)"
    by auto
  with a3 b0 show ?thesis
    by (metis (mono_tags, lifting) map_comp_None_iff map_comp_simps(2) option.exhaust_sel) 
qed

lemma Trans_Sim_finish: "\<lbrakk>((None, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>1\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((C\<^sub>m, s\<^sub>m),R\<^sub>m,G\<^sub>m); 
      ((C\<^sub>m, s\<^sub>m),R\<^sub>m,G\<^sub>m) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>2\<^sub>;\<^sub>\<zeta>\<^sub>2\<^sub>;\<^sub>\<gamma>\<^sub>2\<^sub>) ((C\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a)\<rbrakk> \<Longrightarrow> C\<^sub>a = None \<and> (s\<^sub>c, s\<^sub>a) \<in> \<gamma>\<^sub>2 \<bullet> \<gamma>\<^sub>1 \<and> \<gamma>\<^sub>2 \<bullet> \<gamma>\<^sub>1 \<subseteq> \<alpha>\<^sub>2 \<bullet> \<alpha>\<^sub>1"
proof-
  assume a0: "((None, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>1\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((C\<^sub>m, s\<^sub>m),R\<^sub>m,G\<^sub>m)"
     and a1: "((C\<^sub>m, s\<^sub>m),R\<^sub>m,G\<^sub>m) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>2\<^sub>;\<^sub>\<zeta>\<^sub>2\<^sub>;\<^sub>\<gamma>\<^sub>2\<^sub>) ((C\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a)"

  from a0 have b0: "C\<^sub>m = None \<and> (s\<^sub>c, s\<^sub>m) \<in> \<gamma>\<^sub>1 \<and> \<gamma>\<^sub>1 \<subseteq> \<alpha>\<^sub>1"
    by (simp add: prog_sim_finish)
  with a1 have b1: "C\<^sub>a = None \<and> (s\<^sub>m, s\<^sub>a) \<in> \<gamma>\<^sub>2 \<and> \<gamma>\<^sub>2 \<subseteq> \<alpha>\<^sub>2"
    by (simp add: prog_sim_finish)
  with b0 show ?thesis
    using Product_Type.Collect_case_prodD case_prodI fst_conv rel_comp_def snd_conv by fastforce
qed

lemma Trans_Sim_env_interf: "\<lbrakk>((C\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>1\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((C\<^sub>m, s\<^sub>m),R\<^sub>m,G\<^sub>m); 
      ((s\<^sub>c, s\<^sub>c'), s\<^sub>a, s\<^sub>a') \<in> related_transitions (R\<^sub>c\<^sup>=) (R\<^sub>a\<^sup>=) (\<alpha>\<^sub>2 \<bullet> \<alpha>\<^sub>1);
      ((C\<^sub>m, s\<^sub>m),R\<^sub>m,G\<^sub>m) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>2\<^sub>;\<^sub>\<zeta>\<^sub>2\<^sub>;\<^sub>\<gamma>\<^sub>2\<^sub>) ((C\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a); isMidof (R\<^sub>m\<^sup>=) \<alpha>\<^sub>1 \<alpha>\<^sub>2 (R\<^sub>c\<^sup>=) (R\<^sub>a\<^sup>=)\<rbrakk> \<Longrightarrow>
      \<exists>s\<^sub>m'. ((C\<^sub>c, s\<^sub>c'),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>1\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((C\<^sub>m, s\<^sub>m'),R\<^sub>m,G\<^sub>m) \<and> ((C\<^sub>m, s\<^sub>m'),R\<^sub>m,G\<^sub>m) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>2\<^sub>;\<^sub>\<zeta>\<^sub>2\<^sub>;\<^sub>\<gamma>\<^sub>2\<^sub>) ((C\<^sub>a, s\<^sub>a'),R\<^sub>a,G\<^sub>a)"
proof-
  assume a0: "((C\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>1\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((C\<^sub>m, s\<^sub>m),R\<^sub>m,G\<^sub>m)"
     and a1: "((s\<^sub>c, s\<^sub>c'), s\<^sub>a, s\<^sub>a') \<in> related_transitions (R\<^sub>c\<^sup>=) (R\<^sub>a\<^sup>=) (\<alpha>\<^sub>2 \<bullet> \<alpha>\<^sub>1)"
     and a2: "((C\<^sub>m, s\<^sub>m),R\<^sub>m,G\<^sub>m) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>2\<^sub>;\<^sub>\<zeta>\<^sub>2\<^sub>;\<^sub>\<gamma>\<^sub>2\<^sub>) ((C\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a)"
     and a3: "isMidof (R\<^sub>m\<^sup>=) \<alpha>\<^sub>1 \<alpha>\<^sub>2 (R\<^sub>c\<^sup>=) (R\<^sub>a\<^sup>=)"

  from a0 a2 have b0: "(s\<^sub>c, s\<^sub>m) \<in> \<alpha>\<^sub>1 \<and> (s\<^sub>m, s\<^sub>a) \<in> \<alpha>\<^sub>2"
    by (simp add: prog_sim_init)
  with a1 a3 have  "\<exists>s\<^sub>m'. ((s\<^sub>c, s\<^sub>c'), (s\<^sub>m, s\<^sub>m')) \<in> ((R\<^sub>c\<^sup>=, R\<^sub>m\<^sup>=)\<^sub>\<alpha>\<^sub>1) \<and> ((s\<^sub>m, s\<^sub>m'), (s\<^sub>a, s\<^sub>a')) \<in> ((R\<^sub>m\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>\<^sub>2)"
    by (simp add: isMidof_def)
  then obtain s\<^sub>m' where b1: "((s\<^sub>c, s\<^sub>c'), (s\<^sub>m, s\<^sub>m')) \<in> ((R\<^sub>c\<^sup>=, R\<^sub>m\<^sup>=)\<^sub>\<alpha>\<^sub>1) \<and> ((s\<^sub>m, s\<^sub>m'), (s\<^sub>a, s\<^sub>a')) \<in> ((R\<^sub>m\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>\<^sub>2)"
    by auto
  with a0 a2 show ?thesis
    by (meson prog_env_interf)
qed

lemma Trans_Sim: "\<lbrakk>((C\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>1\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((C\<^sub>m, s\<^sub>m),R\<^sub>m,G\<^sub>m); ((C\<^sub>m, s\<^sub>m),R\<^sub>m,G\<^sub>m) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>2\<^sub>;\<^sub>\<zeta>\<^sub>2\<^sub>;\<^sub>\<gamma>\<^sub>2\<^sub>) ((C\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a);
                   \<alpha>\<^sub>3 = \<alpha>\<^sub>2 \<bullet> \<alpha>\<^sub>1; \<zeta>\<^sub>3 = \<zeta>\<^sub>2 \<circ>\<^sub>m \<zeta>\<^sub>1; \<gamma>\<^sub>3 = \<gamma>\<^sub>2 \<bullet> \<gamma>\<^sub>1; isMidof (R\<^sub>m\<^sup>=) \<alpha>\<^sub>1 \<alpha>\<^sub>2 (R\<^sub>c\<^sup>=) (R\<^sub>a\<^sup>=)\<rbrakk> \<Longrightarrow> 
                   ((C\<^sub>c, s\<^sub>c),R\<^sub>c,G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>3\<^sub>;\<^sub>\<zeta>\<^sub>3\<^sub>;\<^sub>\<gamma>\<^sub>3\<^sub>)  ((C\<^sub>a, s\<^sub>a),R\<^sub>a,G\<^sub>a)"
  apply (coinduction arbitrary: s\<^sub>c s\<^sub>a s\<^sub>m C\<^sub>c C\<^sub>a C\<^sub>m, clarsimp)
(* initial state *)
  apply (rule conjI, simp add: rel_comp_def)
  apply (meson prog_sim_init)
  apply (rule conjI, clarsimp)
(* stutter step *)
   apply (case_tac "C\<^sub>c")
    apply (metis non_no_tran)
   apply (case_tac "\<zeta>\<^sub>1 a", clarsimp)
    apply (metis option.sel prog_sim_sttuter_step)
   apply (rule conjI)
    apply (meson prog_sim_guar, clarsimp)
   apply (drule Trans_Sim_stutter_step, simp_all)
  apply (rule conjI)
(* corresponding step *)
   apply (case_tac "C\<^sub>c")
    apply (metis non_no_tran, clarsimp)
   apply (drule Trans_Sim_coresponding_step, simp_all)
    apply blast
   apply auto[1]
  apply (rule conjI, clarsimp)
(* finish *)
   apply (simp add: Trans_Sim_finish)
(* env_interf *)
  apply clarsimp
  apply (drule Trans_Sim_env_interf, simp_all)
  by blast

theorem Trans_Sound: "\<lbrakk>(C\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>1\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>1\<^sub>) (C\<^sub>m, R\<^sub>m, G\<^sub>m); (C\<^sub>m, R\<^sub>m, G\<^sub>m) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>2\<^sub>;\<^sub>\<zeta>\<^sub>2\<^sub>;\<^sub>\<xi>\<^sub>2\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>2\<^sub>) (C\<^sub>a, R\<^sub>a, G\<^sub>a);
        \<alpha>\<^sub>3 = \<alpha>\<^sub>2 \<bullet> \<alpha>\<^sub>1; \<zeta>\<^sub>3 = \<zeta>\<^sub>2 \<circ>\<^sub>m \<zeta>\<^sub>1; \<xi>\<^sub>3 = \<xi>\<^sub>2 \<bullet> \<xi>\<^sub>1; \<gamma>\<^sub>3 = \<gamma>\<^sub>2 \<bullet> \<gamma>\<^sub>1; isMidof (R\<^sub>m\<^sup>=) \<alpha>\<^sub>1 \<alpha>\<^sub>2 (R\<^sub>c\<^sup>=) (R\<^sub>a\<^sup>=)\<rbrakk>
                       \<Longrightarrow> (C\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>3\<^sub>;\<^sub>\<zeta>\<^sub>3\<^sub>;\<^sub>\<xi>\<^sub>3\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>3\<^sub>) (C\<^sub>a, R\<^sub>a, G\<^sub>a)"
  apply (simp add: prog_sim_pre_def, clarsimp)
  apply (subgoal_tac "\<exists>s\<^sub>m. (s\<^sub>c, s\<^sub>m) \<in> \<xi>\<^sub>1 \<and> (s\<^sub>m, s\<^sub>a) \<in> \<xi>\<^sub>2")
   apply (meson Trans_Sim)
  by (simp add: rel_comp_def)












end


