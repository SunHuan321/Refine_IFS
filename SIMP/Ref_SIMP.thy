theory Ref_SIMP
  imports RG_Tran "../VHelper"
begin

definition related_transitions:: "('s\<^sub>c \<times> 's\<^sub>c) set \<Rightarrow> ('s\<^sub>a \<times> 's\<^sub>a) set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>a) set \<Rightarrow> 
                                  (('s\<^sub>c \<times> 's\<^sub>c) \<times> ('s\<^sub>a \<times> 's\<^sub>a)) set" ("'(_, _')\<^sub>_" ) 
  where "related_transitions R R' \<alpha> = {((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')). (\<sigma>,\<sigma>')\<in> R \<and> (\<Sigma>,\<Sigma>')\<in>R' 
                                      \<and>(\<sigma>, \<Sigma>) \<in> \<alpha> \<and> (\<sigma>', \<Sigma>') \<in> \<alpha>}"

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

(*
definition prog_sim_pre :: "[('s\<^sub>c com) option, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
                  ('s\<^sub>c \<times> 's\<^sub>a) set, 's\<^sub>c com \<Rightarrow> ('s\<^sub>a com) option, ('s\<^sub>c \<times> 's\<^sub>a) set,('s\<^sub>c \<times> 's\<^sub>a) set,
                  ('s\<^sub>a com) option, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool" 
  ("'(_,_,_')/ \<preceq>\<^sub>p \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>\<rhd>\<^sub>_\<^sub>') /'(_,_,_')" [81,81,81,81,81,81,81,81,81,81] 100)
  where " (P\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (P\<^sub>a, R\<^sub>a, G\<^sub>a) \<equiv> 
          (\<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<longrightarrow> ((P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a))"
*)

definition prog_sim_pre :: "[('s\<^sub>c com) option, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
                  ('s\<^sub>c \<times> 's\<^sub>a) set, ('s\<^sub>c \<times> 's\<^sub>a) set,('s\<^sub>c \<times> 's\<^sub>a) set,
                  ('s\<^sub>a com) option, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool" 
  ("'(_,_,_')/ \<preceq>\<^sub>p \<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>\<rhd>\<^sub>_\<^sub>') /'(_,_,_')" [81,81,81,81,81,81,81,81,81] 100)
  where " (P\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (P\<^sub>a, R\<^sub>a, G\<^sub>a) \<equiv> \<exists>\<zeta>.
          (\<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<longrightarrow> ((P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a))"


lemma prog_sim_init: "((P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a) \<Longrightarrow> (s\<^sub>c, s\<^sub>a) \<in> \<alpha>"
  by (erule prog_sim.cases, simp_all)

lemma prog_sim_pre_implies_inv : "(P\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (P\<^sub>a, R\<^sub>a, G\<^sub>a) \<Longrightarrow> \<xi> \<subseteq> \<alpha>"
  by (meson prog_sim_init prog_sim_pre_def subrelI)



lemma prog_sim_guar: "\<lbrakk>((P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a); (P\<^sub>c, s\<^sub>c) -c\<rightarrow> (P\<^sub>c', s\<^sub>c')\<rbrakk> 
                      \<Longrightarrow> (s\<^sub>c, s\<^sub>c') \<in> G\<^sub>c"
  apply (erule prog_sim.cases, simp_all)
  by (metis option.collapse)

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

theorem Conseq_Sound: "\<lbrakk>(P\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (P\<^sub>a, R\<^sub>a, G\<^sub>a); \<xi>\<^sub>' \<subseteq> \<xi>; \<gamma> \<subseteq> \<gamma>\<^sub>' \<and> \<gamma>\<^sub>' \<subseteq> \<alpha>; 
      R\<^sub>c' \<subseteq> R\<^sub>c; R\<^sub>a' \<subseteq> R\<^sub>a; G\<^sub>c \<subseteq> G\<^sub>c'; G\<^sub>a \<subseteq> G\<^sub>a'\<rbrakk> \<Longrightarrow> (P\<^sub>c, R\<^sub>c', G\<^sub>c') \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>'\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>'\<^sub>) (P\<^sub>a, R\<^sub>a', G\<^sub>a')"
  apply (simp add: prog_sim_pre_def)
  by (meson Conseq_Sim prog_sim_init subsetD)

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


theorem None_Sound : "\<lbrakk> \<xi> \<subseteq> \<alpha>; Stable \<xi> (R\<^sub>c \<union> Id, R\<^sub>a \<union> Id)\<^sub>\<alpha>\<rbrakk> \<Longrightarrow> (None, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<xi>\<^sub>) (None, R\<^sub>a, G\<^sub>a)"
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
                      \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<longrightarrow> (s\<^sub>c, f\<^sub>c s\<^sub>c) \<in> G\<^sub>c \<and> (f\<^sub>c s\<^sub>c, s\<^sub>a) \<in> \<gamma>\<rbrakk>
                    \<Longrightarrow> (Some (Basic f\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (None, R\<^sub>a, G\<^sub>a)"
  apply (simp add: prog_sim_pre_def)
  apply (rule_tac x = "Map.empty" in exI)
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

theorem Basic_Sound: "\<lbrakk>\<xi> \<subseteq> \<alpha>; \<gamma> \<subseteq> \<alpha>; Stable \<gamma> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>; Stable \<xi> (R\<^sub>c\<^sup>=, R\<^sub>a\<^sup>=)\<^sub>\<alpha>;
                      \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<xi> \<longrightarrow> (s\<^sub>c, f\<^sub>c s\<^sub>c) \<in> G\<^sub>c \<and> (s\<^sub>a, f\<^sub>a s\<^sub>a) \<in> G\<^sub>a \<and> (f\<^sub>c s\<^sub>c, f\<^sub>a s\<^sub>a) \<in> \<gamma>\<rbrakk> 
                      \<Longrightarrow> (Some (Basic f\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (Some (Basic f\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (simp add: prog_sim_pre_def)
  apply (rule_tac x = "[Basic f\<^sub>c \<mapsto> Basic f\<^sub>a]" in exI)
  by (simp add: Basic_Sim)

definition lift_seq_map :: " 's\<^sub>a com \<Rightarrow> ('s\<^sub>a com \<rightharpoonup> 's\<^sub>a com)"
  where "lift_seq_map C2 C = Some (Seq C C2)"

definition seq_map :: "'s\<^sub>a com \<Rightarrow> ('s\<^sub>c com \<rightharpoonup> 's\<^sub>a com) \<Rightarrow> ('s\<^sub>c com \<rightharpoonup> 's\<^sub>a com)"
  where "seq_map C\<^sub>a \<zeta> = (lift_seq_map C\<^sub>a) \<circ>\<^sub>m \<zeta>"

definition seq_map_none :: "('s\<^sub>c com \<rightharpoonup> 's\<^sub>a com) \<Rightarrow> 's\<^sub>c com \<Rightarrow> ('s\<^sub>c com \<rightharpoonup> 's\<^sub>a com)"
  where "seq_map_none \<zeta> C2 C = (if (\<exists>C1. C = Seq C1 C2) then None else \<zeta> C)"

lemma " (Some C2, s) -c\<rightarrow> (Some C2', s') \<Longrightarrow> \<forall>C1. C2' \<noteq> Seq C1 C2"
  apply (induct C2, erule ctran.cases, simp_all)
     apply (erule ctran.cases, simp_all)
    apply (erule ctran.cases, simp_all)
   apply (erule ctran.cases, simp_all)

lemma Seq_None_Sim: "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> \<xi>; \<xi> \<subseteq> \<alpha>; 
                     ((Some C1\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((None, s\<^sub>a), R\<^sub>a, G\<^sub>a);
                     \<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<gamma>\<^sub>1 \<longrightarrow> ((Some C2\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>2\<^sub>;\<^sub>\<gamma>\<^sub>1\<^sub>) ((Some C\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)\<rbrakk> \<Longrightarrow> 
                     ((Some (Seq C1\<^sub>c C2\<^sub>c), s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<zeta>\<^sub>;\<^sub>\<gamma>\<^sub>) ((Some C\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a)"
  apply (coinduction arbitrary: C1\<^sub>c s\<^sub>c s\<^sub>a, clarsimp)
  apply (rule conjI)
   apply blast
  apply (rule conjI, clarsimp)
   apply (erule ctran.cases, simp_all)
    apply (rule conjI, simp add: prog_sim_guar)


theorem Seq_None_Sound: "\<lbrakk>(Some C1\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<xi>\<^sub>1\<^sub>) (None, R\<^sub>a, G\<^sub>a);
                          (Some C2\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (Some C\<^sub>a, R\<^sub>a, G\<^sub>a)\<rbrakk> 
                      \<Longrightarrow> (Some (Seq C1\<^sub>c C2\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p \<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>) (Some C\<^sub>a, R\<^sub>a, G\<^sub>a)"
  apply (simp add: prog_sim_pre_def, clarify)
  apply (rule_tac x = "(seq_map_none \<zeta>' C2\<^sub>c) ++ (seq_map C\<^sub>a \<zeta>)" in exI)


end


