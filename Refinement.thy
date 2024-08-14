theory Refinement
  imports SecurityModel
begin

locale SM_Refine = SM_IFS mc + SM_IFS ma
  for mc :: "('sc, 'd, 'ac, 'oc) SM"
  and ma :: "('sa, 'd, 'aa, 'oa) SM" +
fixes sim_s :: "'sc \<Rightarrow> 'sa" and
      sim_a :: "'ac \<Rightarrow> 'aa option"
assumes
  init_sim : "sim_s (s0 mc) = s0 ma" and
  action_refine : "sim_a ac = Some aa \<longrightarrow> (sc, tc) \<in> step mc ac \<longrightarrow> (sim_s sc, sim_s tc) \<in> step ma aa" and
  none_refine : "sim_a ac = None \<longrightarrow> (sc, tc) \<in> step mc ac \<longrightarrow> sim_s sc = sim_s tc" and
  intefere_same : "interference mc = interference ma" and 
  dom_refine : "sim_a ac = Some aa \<longrightarrow> domain mc ac = domain ma aa" and 
  sim_ifs : "vpeq ma (sim_s sc) d (sim_s tc) = vpeq mc sc d tc"    
begin

lemma reachR_reach1: "\<forall>s as s'. reachable0 ma (sim_s s) \<and> reachable0 mc s \<and> s' \<in> execute mc as s
                        \<longrightarrow> reachable0 ma (sim_s s')"
proof -
  {
    fix as
    have "\<forall>s s'. reachable0 ma (sim_s s) \<and> reachable0 mc s \<and>  s' \<in> execute mc as s
                        \<longrightarrow> reachable0 ma (sim_s s')"
    proof(induct as)
      case Nil show ?case by (simp add:execute_def)
    next
      case (Cons b bs)
      assume a0: "\<forall>s s'. reachable0 ma (sim_s s) \<and> reachable0 mc s \<and> s' \<in> execute mc bs s 
                   \<longrightarrow> reachable0 ma (sim_s s')"
      show ?case 
      proof -
        {
          fix s s'
            assume b0: "reachable0 ma (sim_s s) \<and> reachable0 mc s \<and> s' \<in> execute mc (b # bs) s"
            have b1: "\<forall>s1. (s, s1) \<in> (step mc) b \<longrightarrow> reachable0 ma (sim_s s1)"
              by (metis action_refine b0 none_refine not_None_eq reachableStep)
            from b0 have "\<exists>s1. (s,s1)\<in> (step mc) b \<and>  (s1 , s') \<in> run mc bs" using execute_def 
              by (metis Image_singleton_iff relcompEpair run_Cons)
            then obtain s1 where b2: "(s,s1) \<in> (step mc) b \<and>  (s1 , s') \<in> run mc bs" by auto
            with b1 have b3: "reachable0 ma (sim_s s1)" by simp
            have b4: "reachable0 mc s1" by (meson b0 b2 reachableStep) 
            with a0 b2 b3 have "reachable0 ma (sim_s s')" 
              by (metis Image_singleton_iff execute_def)
          }
          then show ?thesis by auto
        qed
      qed
    }
    then show ?thesis by auto
  qed


lemma reachR_reach: "reachable0 mc sc \<Longrightarrow> reachable0 ma (sim_s sc)"
  by (metis Image_singleton_iff execute_def init_sim reachR_reach1 reachable0_def reachable_def reachable_s0)

theorem abs_lr_imp : "local_respect ma \<Longrightarrow> local_respect mc"
proof-
  assume a0: "local_respect ma"
  then have a1: "\<forall>aa d sa sa'. reachable0 ma sa \<longrightarrow> (\<not> interference ma (domain ma aa) d) 
                 \<and> (sa, sa') \<in> (step ma) aa \<longrightarrow> (vpeq ma sa d sa')"
    by (simp add: local_respect_def)
  have "\<forall>ac d sc sc'. reachable0 mc sc \<longrightarrow> (\<not> interference mc (domain mc ac) d) 
                          \<and> (sc, sc') \<in> step mc ac \<longrightarrow> (vpeq mc sc d sc')"
  proof-
    {
      fix ac d sc sc'
      assume b0: "reachable0 mc sc"
        and  b1: "\<not> interference mc (domain mc ac) d"
        and  b2: "(sc, sc') \<in> step mc ac"
      have "vpeq mc sc d sc'"
      proof(cases "sim_a ac = None")
        assume c0: "sim_a ac = None"
        with b2 have "sim_s sc = sim_s sc'" by (meson none_refine)
        then show ?thesis
          by (metis sim_ifs vpeq_reflexive_lemma)
      next
        assume d0: "\<not> sim_a ac = None"
        then have  "\<exists>aa. sim_a ac = Some aa" by auto
        then obtain aa where d1: "sim_a ac = Some aa" by force
        then have  "domain mc ac = domain ma aa"
          by (simp add: dom_refine)
        with b1 have d2 :"\<not> interference ma (domain ma aa) d"
          by (simp add: intefere_same)
        from b0 have d3: "reachable0 ma (sim_s sc)" by (simp add: reachR_reach)
        from b2 have d4: "(sim_s sc, sim_s sc') \<in> step ma aa"
          using action_refine d1 by blast
        with a1 d2 d3 have "vpeq ma (sim_s sc) d (sim_s sc')" by blast
        then show ?thesis 
          using sim_ifs by blast
      qed
    }
    then show ?thesis by auto
  qed
  then show ?thesis 
    by (simp add: local_respect_def)
qed

theorem abs_wsc_imp : "weak_step_consistent ma \<Longrightarrow> weak_step_consistent mc"
proof-
  assume a0: "weak_step_consistent ma"
  then have a1: "\<forall>aa d sa ta. reachable0 ma sa \<and> reachable0 ma ta \<longrightarrow> (vpeq ma sa d ta) \<and> 
                 ((interference ma (domain ma aa) d) \<longrightarrow> (vpeq ma sa (domain ma  aa) ta)) 
                 \<longrightarrow> (\<forall> sa' ta'. (sa,sa') \<in> step ma aa \<and> (ta,ta') \<in> step ma aa \<longrightarrow> vpeq ma sa' d ta')"
    by (smt (verit, ccfv_SIG) weak_step_consistent_def)
  have "\<forall>ac d sc tc. reachable0 mc sc \<and> reachable0 mc tc \<longrightarrow> (vpeq mc sc d tc) \<and> 
         ((interference mc (domain mc ac) d) \<longrightarrow> (vpeq mc sc (domain mc ac) tc)) 
         \<longrightarrow> (\<forall> sc' tc'. (sc,sc') \<in> step mc ac \<and> (tc,tc') \<in> step mc ac \<longrightarrow> vpeq mc sc' d tc')"
  proof-
    {
      fix ac d sc tc
      assume b0: "reachable0 mc sc"
        and  b1: "reachable0 mc tc"
        and  b2: "vpeq mc sc d tc"
        and  b3: "(interference mc (domain mc ac) d) \<longrightarrow> (vpeq mc sc (domain mc ac) tc)"
      have "\<forall>sc' tc'. (sc,sc') \<in> step mc ac \<and> (tc,tc') \<in> step mc ac \<longrightarrow> vpeq mc sc' d tc'"
      proof-
        {
          fix sc' tc'
          assume c0: "(sc,sc') \<in> step mc ac"
            and  c1: "(tc,tc') \<in> step mc ac"
          have "vpeq mc sc' d tc'"
          proof(cases "sim_a ac = None")
            assume "sim_a ac = None"
            then have "sim_s sc' = sim_s sc \<and> sim_s tc' = sim_s tc"
              using c0 c1 none_refine by force
            with b2 show ?thesis by (metis b2 sim_ifs)
          next
            assume "\<not> sim_a ac = None"
            then have "\<exists>aa. sim_a ac = Some aa" by auto
            then obtain aa where d0: "sim_a ac = Some aa" by auto
            from b0 have d1: "reachable0 ma (sim_s sc)"
              by (simp add: reachR_reach)
            from b1 have d2: "reachable0 ma (sim_s tc)"
              by (simp add: reachR_reach)
            from b2 have d3: "vpeq ma (sim_s sc) d (sim_s tc)"
              using sim_ifs by blast
          from d0 have d5 : "domain mc ac = domain ma  aa"
            using dom_refine by blast
          then have d6: "interference mc (domain mc ac) d = 
                         interference ma (domain ma aa) d"
            by (simp add: intefere_same)
          from d5 have d7 : "vpeq mc sc (domain mc ac) tc = 
                             vpeq ma (sim_s sc) (domain ma aa) (sim_s tc)"
            using sim_ifs by auto
          with b3 d6 have d8: "(interference ma (domain ma aa) d) 
                \<longrightarrow> (vpeq ma (sim_s sc) (domain ma aa) (sim_s tc))"
            by blast
          from c0 c1 have "(sim_s sc, sim_s sc') \<in> step ma aa \<and> (sim_s tc, sim_s tc') \<in> step ma aa"
            using action_refine d0 by blast
          with a1 d1 d2 d3 d8 have "vpeq ma (sim_s sc') d (sim_s tc')"  by blast
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
    using weak_step_consistent_def by blast
qed
  

end
  




end


