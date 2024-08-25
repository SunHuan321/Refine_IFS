theory Refinement
  imports SecurityModel
begin

locale SM_Refine = 
  SM_IFS\<^sub>c: SM_IFS s0\<^sub>c step\<^sub>c domain\<^sub>c obs\<^sub>c vpeq\<^sub>c interference\<^sub>c +
  SM_IFS\<^sub>a: SM_IFS s0\<^sub>a step\<^sub>a domain\<^sub>a obs\<^sub>a vpeq\<^sub>a interference\<^sub>a
  for s0\<^sub>c :: "'s\<^sub>c"
  and step\<^sub>c :: "'a\<^sub>c \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>c) set"
  and domain\<^sub>c :: "'a\<^sub>c \<Rightarrow> 'd"
  and obs\<^sub>c :: "'s\<^sub>c \<Rightarrow> 'd \<Rightarrow> 'o\<^sub>c" (infixl "\<guillemotright>\<^sub>c"  55)
  and vpeq\<^sub>c :: "'s\<^sub>c \<Rightarrow> 'd \<Rightarrow> 's\<^sub>c \<Rightarrow> bool" ("(_ \<sim>\<^sub>c_\<sim>\<^sub>c _)" [70,69,70] 60)
  and interference\<^sub>c :: "'d \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<leadsto>\<^sub>c _)" [70,71] 60)
  and s0\<^sub>a :: "'s\<^sub>a"
  and step\<^sub>a :: "'a\<^sub>a \<Rightarrow> ('s\<^sub>a \<times> 's\<^sub>a) set"
  and domain\<^sub>a :: "'a\<^sub>a \<Rightarrow> 'd"
  and obs\<^sub>a :: "'s\<^sub>a \<Rightarrow> 'd \<Rightarrow> 'o\<^sub>a" (infixl "\<guillemotright>\<^sub>a"  55)
  and vpeq\<^sub>a :: "'s\<^sub>a \<Rightarrow> 'd \<Rightarrow> 's\<^sub>a \<Rightarrow> bool" ("(_ \<sim>\<^sub>a_\<sim>\<^sub>a _)" [70,69,70] 60)
  and interference\<^sub>a :: "'d \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<leadsto>\<^sub>a _)" [70,71] 60) + 
fixes sim_s :: "'s\<^sub>c \<Rightarrow> 's\<^sub>a \<Rightarrow> bool" ("(_ \<sim> _)" [70,70] 60)
  and sim_a :: "'a\<^sub>c \<Rightarrow> 'a\<^sub>a option"
assumes
  init_sim : " s0\<^sub>c \<sim> s0\<^sub>a" and
  action_refine : "\<lbrakk>sim_a a\<^sub>c = Some a\<^sub>a; SM_IFS\<^sub>c.reachable0 s\<^sub>c; s\<^sub>c \<sim> s\<^sub>a; (s\<^sub>c, t\<^sub>c) \<in> step\<^sub>c a\<^sub>c\<rbrakk> 
            \<Longrightarrow> \<exists>t\<^sub>a. t\<^sub>c \<sim> t\<^sub>a \<and> (s\<^sub>a, t\<^sub>a) \<in> step\<^sub>a a\<^sub>a" and
  none_refine : "\<lbrakk>sim_a a\<^sub>c = None; SM_IFS\<^sub>c.reachable0 s\<^sub>c; s\<^sub>c \<sim> s\<^sub>a; (s\<^sub>c, t\<^sub>c) \<in> step\<^sub>c a\<^sub>c\<rbrakk> \<Longrightarrow> t\<^sub>c \<sim> s\<^sub>a" and
  intefere_same : "interference\<^sub>c = interference\<^sub>a" and 
  dom_refine : "sim_a a\<^sub>c = Some a\<^sub>a \<longrightarrow> domain\<^sub>c a\<^sub>c = domain\<^sub>a a\<^sub>a" and 
  sim_ifs : " \<lbrakk>s\<^sub>c \<sim> s\<^sub>a; t\<^sub>c \<sim> t\<^sub>a\<rbrakk> \<Longrightarrow> s\<^sub>a \<sim>\<^sub>a d \<sim>\<^sub>a t\<^sub>a = s\<^sub>c \<sim>\<^sub>c d \<sim>\<^sub>c t\<^sub>c" 
begin 

abbreviation reachable0\<^sub>c :: "'s\<^sub>c \<Rightarrow> bool"
  where "reachable0\<^sub>c \<equiv> SM_IFS\<^sub>c.reachable0"

abbreviation reachable0\<^sub>a :: "'s\<^sub>a \<Rightarrow> bool"
  where "reachable0\<^sub>a \<equiv> SM_IFS\<^sub>a.reachable0"

abbreviation run\<^sub>c :: " 'a\<^sub>c list \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>c) set"
  where "run\<^sub>c \<equiv> SM_IFS\<^sub>c.run"

abbreviation execute\<^sub>c :: "'a\<^sub>c list \<Rightarrow> 's\<^sub>c \<Rightarrow> 's\<^sub>c set"
  where "execute\<^sub>c \<equiv> SM_IFS\<^sub>c.execute"

lemma reachR_reach1: "\<forall>s\<^sub>c as\<^sub>c t\<^sub>c s\<^sub>a. reachable0\<^sub>a s\<^sub>a \<and> reachable0\<^sub>c s\<^sub>c \<and> s\<^sub>c \<sim> s\<^sub>a \<and> t\<^sub>c \<in> execute\<^sub>c as\<^sub>c s\<^sub>c
                        \<longrightarrow> (\<exists>t\<^sub>a. t\<^sub>c \<sim> t\<^sub>a \<and> reachable0\<^sub>a t\<^sub>a)"
proof -
  {
    fix as\<^sub>c
    have "\<forall>s\<^sub>c t\<^sub>c s\<^sub>a. reachable0\<^sub>a s\<^sub>a \<and> reachable0\<^sub>c s\<^sub>c \<and> s\<^sub>c \<sim> s\<^sub>a \<and> t\<^sub>c \<in> execute\<^sub>c as\<^sub>c s\<^sub>c
                        \<longrightarrow> (\<exists>t\<^sub>a. t\<^sub>c \<sim> t\<^sub>a \<and> reachable0\<^sub>a t\<^sub>a)"
    proof(induct as\<^sub>c)
      case Nil show ?case 
        using SM_IFS\<^sub>c.execute_def by auto
    next
      case (Cons b\<^sub>c bs\<^sub>c)
      assume a0: "\<forall>s\<^sub>c t\<^sub>c s\<^sub>a. reachable0\<^sub>a s\<^sub>a \<and> reachable0\<^sub>c s\<^sub>c \<and> s\<^sub>c \<sim> s\<^sub>a \<and> t\<^sub>c \<in> execute\<^sub>c bs\<^sub>c s\<^sub>c 
                  \<longrightarrow> (\<exists>t\<^sub>a. t\<^sub>c \<sim> t\<^sub>a \<and> reachable0\<^sub>a t\<^sub>a)"
      show ?case
      proof -
        {
          fix s\<^sub>c t\<^sub>c s\<^sub>a
          assume b0: "reachable0\<^sub>a s\<^sub>a \<and> reachable0\<^sub>c s\<^sub>c \<and> s\<^sub>c \<sim> s\<^sub>a \<and> t\<^sub>c \<in> execute\<^sub>c (b\<^sub>c # bs\<^sub>c) s\<^sub>c"
          have b1: "\<forall>s\<^sub>c'. (s\<^sub>c, s\<^sub>c') \<in> step\<^sub>c b\<^sub>c \<longrightarrow> (\<exists>s\<^sub>a'. s\<^sub>c' \<sim> s\<^sub>a' \<and> reachable0\<^sub>a s\<^sub>a')"
          proof-
            {
              fix s\<^sub>c'
              assume c0: "(s\<^sub>c, s\<^sub>c') \<in> step\<^sub>c b\<^sub>c"
              have "\<exists>s\<^sub>a'. s\<^sub>c' \<sim> s\<^sub>a' \<and> reachable0\<^sub>a s\<^sub>a'"
              proof(cases "sim_a b\<^sub>c = None")
                assume d0: "sim_a b\<^sub>c = None"
                with b0 c0 have "s\<^sub>c' \<sim> s\<^sub>a"
                  using none_refine by blast
                then show ?thesis
                  using b0 by blast
              next
                assume e0: "sim_a b\<^sub>c \<noteq> None"
                then have "\<exists>b\<^sub>a. sim_a b\<^sub>c = Some b\<^sub>a" by simp
                then obtain b\<^sub>a where e1: "sim_a b\<^sub>c = Some b\<^sub>a" by auto
                then have "\<exists>s\<^sub>a'. s\<^sub>c' \<sim> s\<^sub>a' \<and> (s\<^sub>a, s\<^sub>a') \<in> step\<^sub>a b\<^sub>a"
                  using action_refine b0 c0 by blast
                then obtain s\<^sub>a' where e2: "s\<^sub>c' \<sim> s\<^sub>a' \<and> (s\<^sub>a, s\<^sub>a') \<in> step\<^sub>a b\<^sub>a" by auto
                then show ?thesis 
                  using SM_IFS\<^sub>a.reachableStep b0 by blast
              qed
            }          
            then show ?thesis by auto
          qed
          from b0 have "\<exists>s\<^sub>c'. (s\<^sub>c, s\<^sub>c') \<in> step\<^sub>c b\<^sub>c \<and> (s\<^sub>c', t\<^sub>c) \<in> run\<^sub>c bs\<^sub>c"
            using SM_IFS\<^sub>c.execute_def by auto
          then obtain s\<^sub>c' where b2: "(s\<^sub>c, s\<^sub>c') \<in> step\<^sub>c b\<^sub>c \<and> (s\<^sub>c', t\<^sub>c) \<in> run\<^sub>c bs\<^sub>c" by auto
          with b1 have "\<exists>s\<^sub>a'. s\<^sub>c' \<sim> s\<^sub>a' \<and> reachable0\<^sub>a s\<^sub>a'" by blast
          then obtain s\<^sub>a' where b3: " s\<^sub>c' \<sim> s\<^sub>a' \<and> reachable0\<^sub>a s\<^sub>a'" by auto
          have b4: "reachable0\<^sub>c s\<^sub>c'"
            using SM_IFS\<^sub>c.reachableStep b0 b2 by blast
          with a0 b2 b3 have "\<exists>t\<^sub>a. t\<^sub>c \<sim> t\<^sub>a \<and> reachable0\<^sub>a t\<^sub>a"
            using SM_IFS\<^sub>c.execute_def by auto
        }
        then show ?thesis by auto
      qed
    qed
  }
  then show ?thesis by auto
qed

lemma reachR_reach: "reachable0\<^sub>c s\<^sub>c \<Longrightarrow> \<exists>s\<^sub>a. s\<^sub>c \<sim> s\<^sub>a \<and> reachable0\<^sub>a s\<^sub>a"
  by (metis Image_singleton_iff SM_IFS.execute_def SM_IFS\<^sub>a.reachableC0 SM_IFS\<^sub>c.SM_IFS_axioms 
     SM_IFS\<^sub>c.reachable0_def SM_IFS\<^sub>c.reachableC0 SM_IFS\<^sub>c.reachable_def init_sim reachR_reach1)

theorem abs_lr_imp : "SM_IFS\<^sub>a.local_respect \<Longrightarrow> SM_IFS\<^sub>c.local_respect"
proof-
  assume a0: "SM_IFS\<^sub>a.local_respect"
  then have a1: "\<forall>aa d sa sa'. reachable0\<^sub>a sa \<longrightarrow> \<not> domain\<^sub>a aa \<leadsto>\<^sub>a d 
                 \<and> (sa, sa') \<in> step\<^sub>a aa \<longrightarrow> (sa \<sim>\<^sub>a d \<sim>\<^sub>a sa')"
    by (simp add: SM_IFS\<^sub>a.local_respect_def)
  have "\<forall>ac d sc sc'. reachable0\<^sub>c sc \<longrightarrow> \<not> domain\<^sub>c ac \<leadsto>\<^sub>a d \<and> (sc, sc') \<in> step\<^sub>c ac 
                      \<longrightarrow> (sc \<sim>\<^sub>c d \<sim>\<^sub>c sc')"
  proof-
    {
      fix ac d sc sc'
      assume b0: "reachable0\<^sub>c sc"
        and  b1: "\<not> domain\<^sub>c ac \<leadsto>\<^sub>a d"
        and  b2: "(sc, sc') \<in> step\<^sub>c ac "
      from b0 have  "\<exists>sa. sc \<sim> sa \<and> reachable0\<^sub>a sa" by (simp add: reachR_reach)
      then obtain sa where b3: "sc \<sim> sa \<and> reachable0\<^sub>a sa" by auto
      have "sc \<sim>\<^sub>c d \<sim>\<^sub>c sc'"
      proof(cases "sim_a ac = None")
        assume c0: "sim_a ac = None"
        with b0 b2 b3 have "sc' \<sim> sa"by (simp add: none_refine)
        then show ?thesis
          by (meson SM_IFS\<^sub>a.vpeq_reflexive SM_Refine.sim_ifs SM_Refine_axioms b3)
      next
        assume d0: "\<not> sim_a ac = None"
        then have  "\<exists>aa. sim_a ac = Some aa" by auto
        then obtain aa where d1: "sim_a ac = Some aa" by force
        then have d01: "domain\<^sub>c ac = domain\<^sub>a aa"
          by (simp add: dom_refine)
        with b1 have d2 :"\<not> domain\<^sub>c ac \<leadsto>\<^sub>a d"
          by (simp add: intefere_same)
        from b0 b2 b3 have "\<exists>sa'. sc' \<sim> sa' \<and> (sa, sa') \<in> step\<^sub>a aa"
          using SM_Refine.action_refine SM_Refine_axioms d1 by fastforce
        then obtain sa' where d3: "sc' \<sim> sa' \<and> (sa, sa') \<in> step\<^sub>a aa" by auto
        with a1 d2 d3 have " sa \<sim>\<^sub>a d \<sim>\<^sub>a sa'"
          using b3 d01 by auto
        then show ?thesis
          using b3 d3 sim_ifs by blast
      qed
    }
    then show ?thesis by auto
  qed
  then show ?thesis 
    using SM_IFS\<^sub>c.local_respect_def intefere_same by blast
qed


theorem abs_wsc_imp : "SM_IFS\<^sub>a.weak_step_consistent \<Longrightarrow> SM_IFS\<^sub>c.weak_step_consistent"
proof-
  assume a0: "SM_IFS\<^sub>a.weak_step_consistent"
  then have a1: "\<forall>aa d sa ta. reachable0\<^sub>a sa \<and> reachable0\<^sub>a ta \<longrightarrow> (sa \<sim>\<^sub>a d \<sim>\<^sub>a ta) \<and> 
                 (domain\<^sub>a aa \<leadsto>\<^sub>a d \<longrightarrow> sa \<sim>\<^sub>a domain\<^sub>a aa \<sim>\<^sub>a ta) 
                 \<longrightarrow> (\<forall>sa' ta'. (sa, sa') \<in> step\<^sub>a aa \<and> (ta, ta') \<in> step\<^sub>a aa \<longrightarrow> sa' \<sim>\<^sub>a d \<sim>\<^sub>a ta')"
    using SM_IFS\<^sub>a.weak_step_consistent_def by blast
  have "\<forall>ac d sc tc. reachable0\<^sub>c sc \<and> reachable0\<^sub>c tc \<longrightarrow> (sc \<sim>\<^sub>c d \<sim>\<^sub>c tc) \<and> 
                 (domain\<^sub>c ac \<leadsto>\<^sub>c d \<longrightarrow> sc \<sim>\<^sub>c domain\<^sub>c ac \<sim>\<^sub>c tc) 
                 \<longrightarrow> (\<forall>sc' tc'. (sc, sc') \<in> step\<^sub>c ac \<and> (tc, tc') \<in> step\<^sub>c ac \<longrightarrow> sc' \<sim>\<^sub>c d \<sim>\<^sub>c tc')"
  proof-
    {
      fix ac d sc tc
      assume b0: "reachable0\<^sub>c sc"
        and  b1: "reachable0\<^sub>c tc"
        and  b2: "sc \<sim>\<^sub>c d \<sim>\<^sub>c tc"
        and  b3: "domain\<^sub>c ac \<leadsto>\<^sub>c d \<longrightarrow> sc \<sim>\<^sub>c domain\<^sub>c ac \<sim>\<^sub>c tc"
      from b0 have "\<exists>sa. sc \<sim> sa \<and> reachable0\<^sub>a sa"
        using reachR_reach by blast
      then obtain sa where b4: "sc \<sim> sa \<and> reachable0\<^sub>a sa" by auto
      from b1 have "\<exists>ta. tc \<sim> ta \<and> reachable0\<^sub>a ta"
        using reachR_reach by blast
      then obtain ta where b5: "tc \<sim> ta \<and> reachable0\<^sub>a ta" by auto
      have "\<forall>sc' tc'. (sc, sc') \<in> step\<^sub>c ac \<and> (tc, tc') \<in> step\<^sub>c ac \<longrightarrow> sc' \<sim>\<^sub>c d \<sim>\<^sub>c tc'"
      proof-
        {
          fix sc' tc'
          assume c0: "(sc,sc') \<in> step\<^sub>c ac"
            and  c1: "(tc,tc') \<in> step\<^sub>c ac"
          have "sc' \<sim>\<^sub>c d \<sim>\<^sub>c tc'"
          proof(cases "sim_a ac = None")
            assume "sim_a ac = None"
            then have " sc' \<sim> sa \<and> tc' \<sim> ta"
              using b0 b1 b4 b5 c0 c1 none_refine by blast
            with b2 show ?thesis
              by (meson b4 b5 sim_ifs)
          next
            assume "\<not> sim_a ac = None"
            then have "\<exists>aa. sim_a ac = Some aa" by auto
            then obtain aa where d0: "sim_a ac = Some aa" by auto
            from b2 b4 b5 have d1: "sa \<sim>\<^sub>a d \<sim>\<^sub>a ta"
              using b4 b5 sim_ifs by blast
          from d0 have d2 : "domain\<^sub>c ac = domain\<^sub>a aa"
            using dom_refine by blast
          then have d3: " domain\<^sub>c ac \<leadsto>\<^sub>c d =  domain\<^sub>a aa \<leadsto>\<^sub>c d"
            by (simp add: intefere_same)
          from b2 b4 b5 have d4 : "sc \<sim>\<^sub>c domain\<^sub>c ac \<sim>\<^sub>c tc = sa \<sim>\<^sub>a domain\<^sub>a aa \<sim>\<^sub>a ta"
            using d2 sim_ifs by auto
          from b3 have d5: " domain\<^sub>a aa \<leadsto>\<^sub>a d \<longrightarrow> sa \<sim>\<^sub>a domain\<^sub>a aa \<sim>\<^sub>a ta"
            using d2 d4 intefere_same by fastforce
          have "\<exists>sa' ta'. sc' \<sim> sa' \<and> tc' \<sim> ta' \<and> (sa, sa') \<in> step\<^sub>a aa \<and> (ta, ta') \<in> step\<^sub>a aa"
            using action_refine b0 b1 b4 b5 c0 c1 d0 by blast
          then obtain sa' ta' where d6: "sc' \<sim> sa' \<and> tc' \<sim> ta' \<and> (sa, sa') \<in> step\<^sub>a aa \<and> (ta, ta') \<in> step\<^sub>a aa"
            by auto
          with a1 d1 d2 d3 d5 b4 b5 have "sa' \<sim>\<^sub>a d \<sim>\<^sub>a ta'" by blast
          then show ?thesis
            using d6 sim_ifs by blast
        qed
        }
        then show ?thesis by blast
      qed
    }
    then show ?thesis by blast
  qed
  then show ?thesis
    using SM_IFS\<^sub>c.weak_step_consistent_def by fastforce
qed

end

(*
locale SM_Refine = 
  SM_IFS\<^sub>c: SM_IFS s0\<^sub>c step\<^sub>c domain\<^sub>c obs\<^sub>c vpeq\<^sub>c interference\<^sub>c +
  SM_IFS\<^sub>a: SM_IFS s0\<^sub>a step\<^sub>a domain\<^sub>a obs\<^sub>a vpeq\<^sub>a interference\<^sub>a
  for s0\<^sub>c :: "'s\<^sub>c"
  and step\<^sub>c :: "'a\<^sub>c \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>c) set"
  and domain\<^sub>c :: "'a\<^sub>c \<Rightarrow> 'd"
  and obs\<^sub>c :: "'s\<^sub>c \<Rightarrow> 'd \<Rightarrow> 'o\<^sub>c" (infixl "\<guillemotright>\<^sub>c"  55)
  and vpeq\<^sub>c :: "'s\<^sub>c \<Rightarrow> 'd \<Rightarrow> 's\<^sub>c \<Rightarrow> bool" ("(_ \<sim>\<^sub>c_\<sim>\<^sub>c _)" [70,69,70] 60)
  and interference\<^sub>c :: "'d \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<leadsto>\<^sub>c _)" [70,71] 60)
  and s0\<^sub>a :: "'s\<^sub>a"
  and step\<^sub>a :: "'a\<^sub>a \<Rightarrow> ('s\<^sub>a \<times> 's\<^sub>a) set"
  and domain\<^sub>a :: "'a\<^sub>a \<Rightarrow> 'd"
  and obs\<^sub>a :: "'s\<^sub>a \<Rightarrow> 'd \<Rightarrow> 'o\<^sub>a" (infixl "\<guillemotright>\<^sub>a"  55)
  and vpeq\<^sub>a :: "'s\<^sub>a \<Rightarrow> 'd \<Rightarrow> 's\<^sub>a \<Rightarrow> bool" ("(_ \<sim>\<^sub>a_\<sim>\<^sub>a _)" [70,69,70] 60)
  and interference\<^sub>a :: "'d \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<leadsto>\<^sub>a _)" [70,71] 60) + 
fixes sim_s :: "'s\<^sub>c \<Rightarrow> 's\<^sub>a"
assumes
  init_sim : "sim_s s0\<^sub>c = s0\<^sub>a" and
  action_refine : "SM_IFS\<^sub>c.reachable0 s\<^sub>c  \<longrightarrow> (s\<^sub>c, t\<^sub>c) \<in> step\<^sub>c a\<^sub>c \<longrightarrow> 
                  (\<forall>sc sc'. (sc, sc') \<in> step\<^sub>c a\<^sub>c \<longrightarrow> sim_s sc = sim_s sc') \<or> 
                  (\<exists>a\<^sub>a. \<forall>sc sc'. ((sc, sc') \<in> step\<^sub>c a\<^sub>c \<longrightarrow> (sim_s sc, sim_s sc') \<in> step\<^sub>a a\<^sub>a) 
                  \<and> domain\<^sub>c a\<^sub>c = domain\<^sub>a a\<^sub>a)" and
  intefere_same : "interference\<^sub>c = interference\<^sub>a" and 
  sim_ifs : "  (sim_s s\<^sub>c) \<sim>\<^sub>a d \<sim>\<^sub>a (sim_s t\<^sub>c) = s\<^sub>c \<sim>\<^sub>c d \<sim>\<^sub>c t\<^sub>c" 
begin 


abbreviation reachable0\<^sub>c :: "'s\<^sub>c \<Rightarrow> bool"
  where "reachable0\<^sub>c \<equiv> SM_IFS\<^sub>c.reachable0"

abbreviation reachable0\<^sub>a :: "'s\<^sub>a \<Rightarrow> bool"
  where "reachable0\<^sub>a \<equiv> SM_IFS\<^sub>a.reachable0"

abbreviation run\<^sub>c :: " 'a\<^sub>c list \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>c) set"
  where "run\<^sub>c \<equiv> SM_IFS\<^sub>c.run"

abbreviation execute\<^sub>c :: "'a\<^sub>c list \<Rightarrow> 's\<^sub>c \<Rightarrow> 's\<^sub>c set"
  where "execute\<^sub>c \<equiv> SM_IFS\<^sub>c.execute"

lemma reachR_reach1: "\<forall>s as s'. reachable0\<^sub>a (sim_s s) \<and> reachable0\<^sub>c s \<and> s' \<in> execute\<^sub>c as s
                        \<longrightarrow> reachable0\<^sub>a  (sim_s s')"
proof -
  {
    fix as
    have "\<forall>s s'. reachable0\<^sub>a (sim_s s) \<and> reachable0\<^sub>c s \<and> s' \<in> execute\<^sub>c as s \<longrightarrow> reachable0\<^sub>a (sim_s s')"
    proof(induct as)
      case Nil show ?case 
        by (simp add: SM_IFS\<^sub>c.execute_def)
    next
      case (Cons b bs)
      assume a0: "\<forall>s s'. reachable0\<^sub>a (sim_s s) \<and> reachable0\<^sub>c s \<and> s' \<in> execute\<^sub>c bs s \<longrightarrow> reachable0\<^sub>a (sim_s s')"
      show ?case 
      proof -
        {
          fix s s'
          assume b0: "reachable0\<^sub>a (sim_s s) \<and> reachable0\<^sub>c  s \<and> s' \<in> execute\<^sub>c (b # bs) s"
          have b1: "\<forall>s1. (s, s1) \<in> step\<^sub>c b \<longrightarrow> reachable0\<^sub>a (sim_s s1)"
            by (metis SM_IFS\<^sub>a.reachableStep action_refine b0)
          from b0 have "\<exists>s1. (s,s1)\<in> step\<^sub>c b \<and>  (s1 , s') \<in> run\<^sub>c bs"   
            using SM_IFS\<^sub>c.execute_def by auto
          then obtain s1 where b2: "(s,s1)\<in> step\<^sub>c b \<and>  (s1 , s') \<in> run\<^sub>c bs" by auto
          with b1 have b3: "reachable0\<^sub>a (sim_s s1)" by simp
          have b4: "reachable0\<^sub>c s1" 
            using SM_IFS\<^sub>c.reachableStep b0 b2 by blast
          with a0 b2 b3 have "reachable0\<^sub>a (sim_s s')"
            by (metis Image_singleton_iff SM_IFS.execute_def SM_IFS\<^sub>c.SM_IFS_axioms)
        }
        then show ?thesis by auto
      qed
    qed
  }
  then show ?thesis by auto
qed

lemma reachR_reach: "reachable0\<^sub>c sc \<Longrightarrow> reachable0\<^sub>a (sim_s sc)"
  by (metis Image_singleton_iff SM_IFS.execute_def SM_IFS\<^sub>a.reachableC0 SM_IFS\<^sub>c.SM_IFS_axioms 
     SM_IFS\<^sub>c.reachable0_def SM_IFS\<^sub>c.reachableC0 SM_IFS\<^sub>c.reachable_def init_sim reachR_reach1)


theorem abs_lr_imp : "SM_IFS\<^sub>a.local_respect \<Longrightarrow> SM_IFS\<^sub>c.local_respect"
proof-
  assume a0: "SM_IFS\<^sub>a.local_respect"
  then have a1: "\<forall>aa d sa sa'. reachable0\<^sub>a sa \<longrightarrow> \<not> domain\<^sub>a aa \<leadsto>\<^sub>a d 
                 \<and> (sa, sa') \<in> step\<^sub>a aa \<longrightarrow> (sa \<sim>\<^sub>a d \<sim>\<^sub>a sa')"
    by (simp add: SM_IFS\<^sub>a.local_respect_def)
  have "\<forall>ac d sc sc'. reachable0\<^sub>c sc \<longrightarrow> \<not> domain\<^sub>c ac \<leadsto>\<^sub>a d \<and> (sc, sc') \<in> step\<^sub>c ac 
                      \<longrightarrow> (sc \<sim>\<^sub>c d \<sim>\<^sub>c sc')"
  proof-
    {
      fix ac d sc sc'
      assume b0: "reachable0\<^sub>c sc"
        and  b1: "\<not> domain\<^sub>c ac \<leadsto>\<^sub>a d"
        and  b2: "(sc, sc') \<in> step\<^sub>c ac "
      have "sc \<sim>\<^sub>c d \<sim>\<^sub>c sc'"
      proof(cases "\<forall>sc sc'. (sc, sc') \<in> step\<^sub>c ac \<longrightarrow> sim_s sc = sim_s sc'")
        assume  "\<forall>sc sc'. (sc, sc') \<in> step\<^sub>c ac \<longrightarrow> sim_s sc = sim_s sc'"
        then show ?thesis
          by (metis SM_IFS\<^sub>c.vpeq_reflexive b2 sim_ifs)
      next
        assume d0: "\<not> (\<forall>sc sc'. (sc, sc') \<in> step\<^sub>c ac \<longrightarrow> sim_s sc = sim_s sc')"
        then have "\<exists>aa. (sim_s sc, sim_s sc') \<in> step\<^sub>a aa \<and> domain\<^sub>c ac = domain\<^sub>a aa"
          using action_refine b0 b2 by blast
        then obtain aa where d1: "(sim_s sc, sim_s sc') \<in> step\<^sub>a aa \<and> domain\<^sub>c ac = domain\<^sub>a aa" by auto
        with b1 have d2: "\<not> domain\<^sub>a aa \<leadsto>\<^sub>a d" by simp
        from b0 have d3: "reachable0\<^sub>a (sim_s sc)" using reachR_reach by auto
        with a1 d1 d2 have "sim_s sc \<sim>\<^sub>a d \<sim>\<^sub>a sim_s sc'" by blast
        then show ?thesis by (simp add: sim_ifs)
      qed
    }
    then show ?thesis by auto
  qed
  then show ?thesis 
    using SM_IFS\<^sub>c.local_respect_def intefere_same by blast 
qed

theorem abs_wsc_imp : "SM_IFS\<^sub>a.weak_step_consistent \<Longrightarrow> SM_IFS\<^sub>c.weak_step_consistent"
proof-
  assume a0: "SM_IFS\<^sub>a.weak_step_consistent"
  then have a1: "\<forall>aa d sa ta. reachable0\<^sub>a sa \<and> reachable0\<^sub>a ta \<longrightarrow> (sa \<sim>\<^sub>a d \<sim>\<^sub>a ta) \<and> 
                 (domain\<^sub>a aa \<leadsto>\<^sub>a d \<longrightarrow> sa \<sim>\<^sub>a domain\<^sub>a aa \<sim>\<^sub>a ta) 
                 \<longrightarrow> (\<forall>sa' ta'. (sa, sa') \<in> step\<^sub>a aa \<and> (ta, ta') \<in> step\<^sub>a aa \<longrightarrow> sa' \<sim>\<^sub>a d \<sim>\<^sub>a ta')"
    using SM_IFS\<^sub>a.weak_step_consistent_def by blast
  have "\<forall>ac d sc tc. reachable0\<^sub>c sc \<and> reachable0\<^sub>c tc \<longrightarrow> (sc \<sim>\<^sub>c d \<sim>\<^sub>c tc) \<and> 
                 (domain\<^sub>c ac \<leadsto>\<^sub>c d \<longrightarrow> sc \<sim>\<^sub>c domain\<^sub>c ac \<sim>\<^sub>c tc) 
                 \<longrightarrow> (\<forall>sc' tc'. (sc, sc') \<in> step\<^sub>c ac \<and> (tc, tc') \<in> step\<^sub>c ac \<longrightarrow> sc' \<sim>\<^sub>c d \<sim>\<^sub>c tc')"
  proof-
    {
      fix ac d sc tc
      assume b0: "reachable0\<^sub>c sc"
        and  b1: "reachable0\<^sub>c tc"
        and  b2: "sc \<sim>\<^sub>c d \<sim>\<^sub>c tc"
        and  b3: "domain\<^sub>c ac \<leadsto>\<^sub>c d \<longrightarrow> sc \<sim>\<^sub>c domain\<^sub>c ac \<sim>\<^sub>c tc"
      have "\<forall>sc' tc'. (sc, sc') \<in> step\<^sub>c ac \<and> (tc, tc') \<in> step\<^sub>c ac \<longrightarrow> sc' \<sim>\<^sub>c d \<sim>\<^sub>c tc'"
      proof-
        {
          fix sc' tc'
          assume c0: "(sc,sc') \<in> step\<^sub>c ac"
            and  c1: "(tc,tc') \<in> step\<^sub>c ac"
          have "sc' \<sim>\<^sub>c d \<sim>\<^sub>c tc'"
          proof(cases "\<forall>sc sc'. (sc, sc') \<in> step\<^sub>c ac \<longrightarrow> sim_s sc = sim_s sc'")
            assume "\<forall>sc sc'. (sc, sc') \<in> step\<^sub>c ac \<longrightarrow> sim_s sc = sim_s sc'"
            then have "sim_s sc' = sim_s sc \<and> sim_s tc' = sim_s tc"
              using c0 c1  by force
            with b2 show ?thesis by (metis b2 sim_ifs)
          next
            assume "\<not> (\<forall>sc sc'. (sc, sc') \<in> step\<^sub>c ac \<longrightarrow> sim_s sc = sim_s sc')"
            then have "\<exists>aa. (sim_s sc, sim_s sc') \<in> step\<^sub>a aa \<and> (sim_s tc, sim_s tc') \<in> step\<^sub>a aa \<and> domain\<^sub>c ac = domain\<^sub>a aa" 
              by (meson action_refine b1 c0 c1)
            then obtain aa where d0: "(sim_s sc, sim_s sc') \<in> step\<^sub>a aa \<and> (sim_s tc, sim_s tc') \<in> step\<^sub>a aa \<and> domain\<^sub>c ac = domain\<^sub>a aa" by auto
            from b0 have d1: "reachable0\<^sub>a (sim_s sc)"
              by (simp add: reachR_reach)
            from b1 have d2: "reachable0\<^sub>a (sim_s tc)"
              by (simp add: reachR_reach)
            from b2 have d3: "sim_s sc \<sim>\<^sub>a d \<sim>\<^sub>a sim_s tc"
              using sim_ifs by blast
            from d0 have d5: " domain\<^sub>c ac \<leadsto>\<^sub>c d =  domain\<^sub>a aa \<leadsto>\<^sub>c d"
            by (simp add: intefere_same)
          from d0 have d6 : "sc \<sim>\<^sub>c domain\<^sub>c ac \<sim>\<^sub>c tc = sim_s sc \<sim>\<^sub>a domain\<^sub>a aa \<sim>\<^sub>a sim_s tc"
            using sim_ifs by auto
          with b3 d5 have d7: " domain\<^sub>a aa \<leadsto>\<^sub>a d \<longrightarrow> sim_s sc \<sim>\<^sub>a domain\<^sub>a aa \<sim>\<^sub>a sim_s tc"
            using intefere_same by fastforce
          from c0 c1 have "(sim_s sc, sim_s sc') \<in> step\<^sub>a aa \<and> (sim_s tc, sim_s tc') \<in> step\<^sub>a aa"
            using action_refine d0 by blast
          with a1 d1 d2 d3 d7 have "sim_s sc' \<sim>\<^sub>ad\<sim>\<^sub>a sim_s tc'"  by blast
          then show ?thesis
            using sim_ifs by blast
        qed
        }
        then show ?thesis by blast
      qed
    }
    then show ?thesis by blast
  qed
  then show ?thesis
    using SM_IFS\<^sub>c.weak_step_consistent_def by fastforce
qed
*)
end



