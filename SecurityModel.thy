theory SecurityModel
  imports Main
begin

subsection \<open> Security State Machine \<close>


record ('s, 'd, 'a, 'o) SM = 
  s0 :: "'s"
  step :: "'a \<Rightarrow> ('s \<times> 's) set"
  domain :: "'a \<Rightarrow> 'd"
  obs :: "'d \<Rightarrow> 's \<Rightarrow> 'o"
  vpeq :: "'s \<Rightarrow> 'd \<Rightarrow> 's \<Rightarrow> bool" 
  interference :: "'d \<Rightarrow> 'd \<Rightarrow> bool" 

primrec run :: "('s, 'd, 'a, 'o) SM \<Rightarrow> 'a list \<Rightarrow> ('s \<times> 's) set" 
  where run_Nil: "run m [] = Id" |
  run_Cons: "run m (a#as) = (step m) a O run m as"

definition ivpeq :: "('s, 'd, 'a, 'o) SM \<Rightarrow> 's \<Rightarrow> 'd set \<Rightarrow> 's \<Rightarrow> bool" 
  where "ivpeq m s D t \<equiv> \<forall> d \<in> D. vpeq m s d t"

definition next_states :: "('s, 'd, 'a, 'o) SM \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 's set"
  where "next_states m s a \<equiv> {Q. (s,Q)\<in> step m a}"

definition execute  :: "('s, 'd, 'a, 'o) SM \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> 's set" 
  where "execute m as s = Image (run m as) {s} " 

definition reachable :: " ('s, 'd, 'a, 'o) SM \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"
  where "reachable m s1 s2 \<equiv>  (\<exists>as. (s1,s2) \<in> run m as)"

definition reachable0 :: "('s, 'd, 'a, 'o) SM \<Rightarrow> 's \<Rightarrow> bool" 
  where "reachable0 m s \<equiv> reachable m (s0 m)  s"

lemma reachable_s0 : "reachable0 m (s0 m) "
  by (metis pair_in_Id_conv reachable0_def reachable_def run_Nil)

lemma reachable_self : "reachable m s s"
  by (metis pair_in_Id_conv reachable_def run_Nil)

lemma reachable_step : " (s , s') \<in> step m a \<Longrightarrow> reachable m s s'"
proof-
  assume a0: "(s , s') \<in> step m a"
  then have "(s,s') \<in> run m [a]" by simp
  then show ?thesis 
    by (meson reachable_def)
qed


lemma run_trans : "\<forall>C T V as bs. (C,T)\<in> run m as \<and> (T,V) \<in> run m bs \<longrightarrow> (C,V) \<in> run m (as@bs)"
proof -
  {
    fix T V as bs
    have "\<forall>C. (C,T)\<in> run m as \<and> (T,V) \<in> run m bs \<longrightarrow> (C,V) \<in> run m (as@bs)"
    proof(induct as)
      case Nil show ?case by simp
    next
      case (Cons c cs)
      assume a0: "\<forall>C. (C, T) \<in> run m cs \<and> (T, V) \<in> run m bs \<longrightarrow> (C, V) \<in> run m (cs @ bs)"
      show ?case
      proof-
        {
          fix C
          have "(C, T) \<in> run m (c # cs) \<and> (T, V) \<in> run m bs \<longrightarrow> (C, V) \<in> run m ((c # cs) @ bs) "
          proof
            assume b0: "(C, T) \<in> run m (c # cs) \<and> (T, V) \<in> run m bs"
            from b0 obtain C' where b2: "(C,C')\<in> step m c \<and> (C',T)\<in> run m cs" by auto
            with a0 b0 have "(C',V)\<in>run m (cs@bs)" by blast
            with b2 show "(C, V) \<in> run m ((c # cs) @ bs)"
              using append_Cons relcomp.relcompI run_Cons by auto 
          qed
        }
        then show ?thesis by auto
      qed
    qed
  }
  then show ?thesis by auto
qed


lemma reachable_trans : "\<lbrakk>reachable m C T; reachable m T V\<rbrakk> \<Longrightarrow> reachable m C V"
proof-
  assume a0: "reachable m C T"
  assume a1: "reachable m T V"
  from a0 have "C = T \<or> (\<exists>as. (C,T)\<in>run m as)" using reachable_def 
    by metis
  then show ?thesis
  proof
    assume b0: "C = T"
    show ?thesis 
    proof -
      from a1 have "T = V \<or> (\<exists>as. (T,V)\<in>run m as)" using reachable_def by metis
      then show ?thesis
      proof
        assume c0: "T=V"
        with a0 show ?thesis by simp
      next
        assume c0: "(\<exists>as. (T,V)\<in>run m as)"
        then show ?thesis by (simp add: a1 b0) 
      qed
    qed
  next
    assume b0: "\<exists>as. (C,T)\<in>run m as"
    show ?thesis
    proof -
      from a1 have "T = V \<or> (\<exists>as. (T,V)\<in>run m as)" using reachable_def by metis
      then show ?thesis
      proof
        assume c0: "T=V"
        then show ?thesis using a0 by auto 
      next
        assume c0: "(\<exists>as. (T,V)\<in>run m as)"
        from b0 obtain as where d0: "(C,T)\<in>run m as" by auto
        from c0 obtain bs where d1: "(T,V)\<in>run m bs" by auto
        then show ?thesis using d0 reachable_def run_trans by metis 
      qed
    qed
  qed
qed

lemma reachableStep : "\<lbrakk>reachable0 m C; (C,C')\<in> step m a\<rbrakk> \<Longrightarrow> reachable0 m C'"
proof -
  assume a0: "reachable0 m C"
  assume a1: "(C,C')\<in>(step m) a"
  from a0 have "(C = (s0 m)) \<or> (\<exists>as. ((s0 m),C) \<in> run m as)" unfolding reachable0_def reachable_def by auto
  then show "reachable0 m C'"
  proof
    assume b0: "C = s0 m"
    show "reachable0 m C'"
      using a1 b0 reachable0_def reachable_step by metis
  next
    assume b0: "\<exists>as. ((s0 m),C) \<in> run m as"
    show "reachable0 m C'"
      using a0 a1 reachable0_def reachable_step reachable_trans by metis 
  qed
qed
    
lemma reachable0_reach : "\<lbrakk>reachable0 m C; reachable m C C'\<rbrakk> \<Longrightarrow> reachable0 m C'"
  using reachable0_def reachable_trans by metis

primrec sources :: "('s, 'd, 'a, 'o) SM \<Rightarrow> 'a list  \<Rightarrow> 'd \<Rightarrow> 'd set"
  where sources_Nil:"sources m [] d = {d}" |
  sources_Cons: "sources m (a # as) d = (sources m as d) \<union> {w. w = (domain m) a \<and> 
                                        (\<exists>v. interference m w v \<and> v \<in> sources m as d) }"

declare sources_Nil [simp del]   
declare sources_Cons [simp del]


primrec ipurge :: "('s, 'd, 'a, 'o) SM  \<Rightarrow> 'a list \<Rightarrow> 'd \<Rightarrow> 'a list"
  where ipurge_Nil:   "ipurge m [] u  = []" |
  ipurge_Cons:  "ipurge m (a#as) u = (if (domain m) a \<in> (sources m (a#as) u) then
                                              a # ipurge m as u 
                                           else
                                              ipurge m as u 
                                          )"

definition exec_equiv :: "('s, 'd, 'a, 'o) SM \<Rightarrow> 's \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> 'a list \<Rightarrow> 'd \<Rightarrow> bool" 
  where "exec_equiv m s as t bs d \<equiv>  \<forall>s' t'. ((s,s')\<in> run m as \<and> (t,t')\<in> run m bs) 
        \<longrightarrow> obs m d s' = obs m d t'"


lemma exec_equiv_both:
   "\<lbrakk>reachable0 m s; reachable0 m t; \<forall>s' t'. (s, s') \<in> step m a \<and> (t, t') \<in> step m b
    \<longrightarrow> exec_equiv m s' as t' bs u\<rbrakk> \<Longrightarrow> exec_equiv m s (a # as) t (b # bs) u"
proof -
  assume a0: "reachable0 m s"
  assume a1: "reachable0 m t"
  assume a2: "\<forall>s' t'. (s, s') \<in> step m a \<and> (t, t') \<in> step m b \<longrightarrow> exec_equiv m s' as t' bs u"
  have "\<forall>s'' t''. (s, s'') \<in> run m (a # as) \<and> (t, t'') \<in> run m (b # bs) \<longrightarrow> obs m u s'' = obs m u t''"
  proof -
    {
      fix s'' t''
      assume b0: "(s, s'') \<in> run m (a # as) \<and> (t, t'') \<in> run m (b # bs)"
      then obtain s' where b1: " (s, s') \<in> step m a \<and> (s',s'') \<in> run m as"
        by auto
      from b0 obtain t' where b2: "(t, t') \<in> step m b \<and> (t', t'') \<in> run m bs"
        by auto
      with a2 b1 have b3: "exec_equiv m s' as t' bs u" by blast
      with b0 b1 b2 have "obs m u s'' = obs m u t''" using exec_equiv_def 
        by fastforce
    }
    then show ?thesis by auto
  qed
  then show ?thesis using exec_equiv_def
    by metis
qed

lemma sources_ipurge: "sources m (ipurge m as u) u = sources m as u"
proof -
  have "\<forall>as u. sources m (ipurge m as u) u = sources m as u"
  proof -
    {
      fix as
      have "\<forall>u. sources m (ipurge m as u) u = sources m as u"
      proof(induct as)
        case Nil show ?case by simp
      next
        case (Cons b bs)
        assume a0: "\<forall>u. sources m (ipurge m bs u) u = sources m bs u"
        show ?case
        proof -
          {
            fix u
            have "sources m (ipurge m (b # bs) u) u = sources m (b # bs) u"
            proof(cases "(domain m) b \<in> sources m (b#bs) u")
              assume b0: "(domain m) b \<in> sources m (b#bs) u"
              then have b1: "ipurge m (b # bs) u = b # ipurge m bs u"
                by (simp add: sources_Cons) 
              from a0 have b2: "sources m (ipurge m bs u) u = sources m bs u" by simp
              from b1 have b3: "sources m (ipurge m (b # bs) u) u = sources m (b # ipurge m bs u) u" by simp
              then have b40: "sources m (ipurge m (b # bs) u) u = sources m (ipurge m bs u) u \<union> 
                         {w. w = (domain m) b \<and> (\<exists>v. interference m w v \<and> v \<in> sources m bs u)}"
                by (simp add: b2 sources_Cons)
              with b0 b2 have b41: "(domain m) b \<in> sources m (ipurge m (b # bs) u) u"
                by (metis sources_Cons)
              then have  b4: "sources m (ipurge m (b # bs) u) u = {(domain m) b} \<union> sources m (ipurge m bs u) u"
                using b40 by auto
              from b0 have b5: "sources m (b # bs) u = {(domain m) b} \<union> sources m bs u"
                using sources_Cons by fastforce
              then show ?thesis using a0 b4 by auto 
            next
              assume b0: "\<not> domain m b \<in> sources m (b#bs) u"
              then have b1: "sources m (ipurge m (b # bs) u) u = sources m (ipurge m bs u) u" 
                using sources_Cons by auto 
              from b0 have b2: "sources m (b # bs) u = sources m bs u" 
                by (smt (verit) Collect_empty_eq UnI2 mem_Collect_eq sources_Cons sup_bot_left sup_commute)
              with a0 b1 show ?thesis by auto
            qed
          }
          then show ?thesis by auto
        qed
      qed
    }
    then show ?thesis by auto
  qed
  then show ?thesis by auto
qed

lemma ipurge_eq: "ipurge m as u = ipurge m (ipurge m as u) u"
proof -
  have "\<forall>as u. ipurge m as u = ipurge m (ipurge m as u) u"
  proof -
    {
      fix as
      have "\<forall>u. ipurge m as u = ipurge m (ipurge m as u) u"
      proof(induct as)
        case Nil show ?case by simp
      next
        case (Cons b bs)
        assume a0: "\<forall>u. ipurge m bs u = ipurge m (ipurge m bs u) u"
        show ?case
        proof -
          {
            fix u
            have "ipurge m (b # bs) u = ipurge m (ipurge m (b # bs) u) u "
            proof(cases "(domain m) b \<in> sources m (b#bs) u")
              assume b0: "(domain m) b\<in> sources m (b#bs) u"
              then have b1: "ipurge m (b # bs) u = b # ipurge m bs u" by simp
              then have b2: "ipurge m (ipurge m (b # bs) u) u = ipurge m (b # ipurge m bs u) u" by simp
              have b3: "sources m (b#bs) u = sources m (b#ipurge m bs u) u" using sources_ipurge by (metis b1)
              with b1 b2 show ?thesis using a0 by auto 
            next
              assume b0: "\<not> (domain m) b\<in> sources m (b#bs) u"
              then have b1: "ipurge m (b # bs) u = ipurge m bs u" by simp
              then have b2: "ipurge m (ipurge m (b # bs) u) u = ipurge m (ipurge m bs u) u" by simp
              with b1 show ?thesis  using a0 by auto 
            qed
          }
          then show ?thesis by auto
        qed
      qed
    }
    then show ?thesis by auto
  qed
  then show ?thesis by auto
qed



(* Rushby's noninterference*)
definition noninterference0 :: "('s, 'd, 'a, 'o) SM \<Rightarrow> bool"
  where "noninterference0 m \<equiv> \<forall>u as. exec_equiv m (s0 m) as (s0 m) (ipurge m as u) u"

(* reachable state version of Rushby's noninterference*)
definition noninterference0_r :: "('s, 'd, 'a, 'o) SM \<Rightarrow> bool"
  where "noninterference0_r m \<equiv> \<forall>u as s. reachable0 m s \<longrightarrow> exec_equiv m s as s (ipurge m as u) u"

(* Oheimb's nondeterministic version of noninterference *)
(* It is the same as Oheimb's strong noninterference*)
definition noninterference1 :: "('s, 'd, 'a, 'o) SM \<Rightarrow> bool" 
  where "noninterference1 m \<equiv> \<forall>u as bs. (ipurge m as u = ipurge m bs u) \<longrightarrow> 
         exec_equiv m (s0 m) as (s0 m) bs u"

(* reachable state version of Oheimb's strong noninterference *)
definition noninterference1_r :: "('s, 'd, 'a, 'o) SM \<Rightarrow> bool"
  where "noninterference1_r m \<equiv> \<forall>u as bs s. reachable0 m s \<longrightarrow> ipurge m as u = ipurge m bs u 
         \<longrightarrow> exec_equiv m s as s bs u"

(* Oheimb's nonleakage. The Murray's nonleakage is the same *)
definition nonleakage :: "('s, 'd, 'a, 'o) SM \<Rightarrow> bool" where
  "nonleakage m \<equiv> \<forall>as s t u. (reachable0 m s) \<and> (reachable0 m t) \<longrightarrow> ivpeq m s (sources m as u) t  
                                 \<longrightarrow> exec_equiv m s as t as u"

(* Oheimb's noninfluence *)
definition noninfluence0 ::"('s, 'd, 'a, 'o) SM \<Rightarrow> bool" where
  "noninfluence0 m \<equiv> \<forall> u as s t . (reachable0 m s) \<and> (reachable0 m t) \<longrightarrow> ivpeq m s (sources m as u) t 
                                \<longrightarrow> exec_equiv m s as t (ipurge m as u) u"

(* Murray's noninfluence (without the scheduler) *)
(* replacing ``ipurge bs {C1} u'' by ``ipurge bs {C2} u'' yields and equivalent property as stated in Murray's paper*)
definition noninfluence1 :: "('s, 'd, 'a, 'o) SM \<Rightarrow> bool" where
  "noninfluence1 m \<equiv> \<forall>as bs s t u. (reachable0 m s) \<and> (reachable0 m t) \<longrightarrow> ivpeq m s (sources m as u) t
                     \<longrightarrow> ipurge m as u = ipurge m bs u \<longrightarrow> exec_equiv m s as t bs u"

subsection \<open> Unwinding conditions and unwinding theorem \<close>

definition observed_consistent :: "('s, 'd, 'a, 'o) SM \<Rightarrow> bool" where
 "observed_consistent m \<equiv> (\<forall> s t u. (vpeq m s u t) \<longrightarrow> obs m u s = obs m u t)"


definition weak_step_consistent :: "('s, 'd, 'a, 'o) SM \<Rightarrow> bool" 
  where "weak_step_consistent m \<equiv> \<forall>a d s t. reachable0 m s \<and> reachable0 m t \<longrightarrow> (vpeq m s d t) 
                              \<and> ((interference m (domain m a) d) \<longrightarrow> vpeq m s ((domain m) a) t)
                              \<longrightarrow> (\<forall> s' t'. (s,s') \<in> step m a \<and> (t,t') \<in> step m a 
                              \<longrightarrow> vpeq m s' d t')"

definition weak_step_consistent_e :: "('s, 'd, 'a, 'o) SM \<Rightarrow> 'a \<Rightarrow> bool"
  where  "weak_step_consistent_e m a \<equiv> \<forall>d s t. reachable0 m s \<and> reachable0 m t \<longrightarrow> (vpeq m s d t) 
                              \<and> ((interference m (domain m a) d) \<longrightarrow> vpeq m s (domain m a) t)
                              \<longrightarrow> (\<forall> s' t'. (s,s') \<in> step m a \<and> (t,t') \<in> step m a 
                              \<longrightarrow> vpeq m s' d t')"

    
definition local_respect :: "('s, 'd, 'a, 'o) SM  \<Rightarrow> bool" 
  where "local_respect m \<equiv> \<forall> a d s s'. reachable0 m s \<longrightarrow> (\<not> interference m ((domain m) a) d) 
                          \<and> (s,s') \<in> step m a \<longrightarrow> (vpeq m s d s')"

definition local_respect_e :: "('s, 'd, 'a, 'o) SM  \<Rightarrow> 'a \<Rightarrow> bool" 
  where  "local_respect_e m a \<equiv> \<forall> d s s'. reachable0 m s \<longrightarrow> (\<not> (interference m) ((domain m) a) d) 
                          \<and> (s,s') \<in> step m a \<longrightarrow> (vpeq m s d s')"

lemma local_respect_all_evt : "local_respect m = (\<forall>a. local_respect_e m a)"
  by (simp add: local_respect_def local_respect_e_def)

lemma weak_step_consistent_all_evt : "weak_step_consistent m = (\<forall>a. weak_step_consistent_e m a)"
  by (simp add:weak_step_consistent_def weak_step_consistent_e_def)

locale SM_IFS = 
  fixes m :: "('s, 'd, 'a, 'o) SM"
  assumes 
    vpeq_transitive_lemma : "\<forall>s t r d. vpeq m s d t \<and> vpeq m t d r \<longrightarrow> vpeq m s d r" and
    vpeq_symmetric_lemma : "\<forall>s t d. vpeq m s d t \<longrightarrow> vpeq m t d s" and
    vpeq_reflexive_lemma : "\<forall>s d. vpeq m s d s" 

begin

lemma exec_equiv_sym: "exec_equiv m s as t bs d \<Longrightarrow> exec_equiv m t bs s as d"
  using exec_equiv_def vpeq_symmetric_lemma by metis

subsection \<open>A Infererence Framework of Information Flow Security Properties\<close>
(*
   \<Midarrow>\<Midarrow>\<Midarrow> unwinding conditions
   \<parallel>             \<parallel>
   \<parallel>             \<parallel>(UnwindingTheorem_noninfluence0)
   \<parallel>             \<parallel>
   \<parallel>             \<Down>
   \<parallel>      noninfluence0  \<Midarrow>\<Midarrow>(lm7)\<Longrightarrow>  noninterference0_r  \<Midarrow>\<Midarrow>(lm1)\<Longrightarrow>  noninterference0
   \<parallel>             \<Up>                           \<Up>                              \<Up>
   \<parallel>(UT_nonlk)   \<parallel>(lm8)                      \<parallel>(lm9)                         \<parallel>(lm10)
   \<parallel>             \<parallel>                           \<parallel>                              \<parallel>
   \<parallel>             \<parallel>                           \<parallel>                              \<parallel>
   \<parallel>      noninfluence1  \<Midarrow>\<Midarrow>(lm6)\<Longrightarrow>  noninterference1_r  \<Midarrow>\<Midarrow>(lm2)\<Longrightarrow>  noninterference1
   \<parallel>             \<parallel>
   \<parallel>             \<parallel>(lm5)
   \<parallel>             \<parallel>
   \<parallel>             \<Down>
   \<parallel>\<Midarrow>\<Midarrow>\<Midarrow>\<Longrightarrow>  nonleakage

*)

lemma lm1: "noninterference0_r m \<Longrightarrow> noninterference0 m"
  by (simp add: noninterference0_def noninterference0_r_def reachable_s0)

lemma lm2: "noninterference1_r m \<Longrightarrow> noninterference1 m"
  by (simp add: noninterference1_def noninterference1_r_def reachable_s0)

(*
lemma lm3: "noninterference0 \<Longrightarrow> noninterference1" sorry (*exec_equiv is not transitive, so this is not satisfied*)


lemma lm4: "noninterference0_r \<Longrightarrow> noninterference1_r" sorry (*exec_equiv is not transitive, so this is not satisfied*)
*)

lemma lm5: "noninfluence1 m \<Longrightarrow> nonleakage m" 
  by (simp add: noninfluence1_def nonleakage_def)

(*lemma lm11: "noninfluence0 \<Longrightarrow> nonleakage" *)

lemma lm6: "noninfluence1 m \<Longrightarrow> noninterference1_r m" 
  by (simp add: ivpeq_def noninfluence1_def noninterference1_r_def vpeq_reflexive_lemma)

lemma lm7: "noninfluence0 m \<Longrightarrow> noninterference0_r m"
  by (simp add: ivpeq_def noninfluence0_def noninterference0_r_def vpeq_reflexive_lemma)

lemma lm8: "noninfluence1 m \<Longrightarrow> noninfluence0 m"
  using ipurge_eq noninfluence0_def noninfluence1_def by fastforce
  
lemma lm9: "noninterference1_r m \<Longrightarrow> noninterference0_r m"
  using ipurge_eq noninterference0_r_def noninterference1_r_def by fastforce

lemma lm10: "noninterference1 m \<Longrightarrow> noninterference0 m"
  using ipurge_eq noninterference0_def noninterference1_def by fastforce

subsection \<open>Unwinding Conditions\<close>

lemma sources_unwinding_step:
    "\<lbrakk>ivpeq m s (sources m (a#as) d) t; weak_step_consistent m; (s, s') \<in> step m a; (t, t') \<in> step m a;
      reachable0 m s; reachable0 m t\<rbrakk>  \<Longrightarrow> ivpeq m s' (sources m as d) t'"
proof -
  assume a0: "ivpeq m s (sources m (a#as) d) t"
  assume a1: "weak_step_consistent m"
  assume a2: "(s, s') \<in> step m a"
  assume a3: "(t, t') \<in> step m a"
  assume a4: "reachable0 m s"
  assume a5: "reachable0 m t"
  have a7: "sources m as d \<subseteq> sources m (a#as) d" by (simp add: sources_Cons) 
  have "\<forall>u. u\<in> (sources m as d) \<longrightarrow> vpeq m s' u t'"
  proof -
    {
      fix u
      assume b0: "u \<in> sources m as d"
      from a7 b0 have b1: "u \<in> sources m (a#as) d" by auto
      then have "vpeq m s' u t'"
      proof(cases "interference m (domain m a) u")
        assume c0: "interference m (domain m a) u"
        show ?thesis
        proof -
          have d0: "vpeq m s (domain m a) t"
            by (metis (mono_tags, lifting) CollectI UnI2 a0 b0 c0 ivpeq_def sources_Cons)
          then have "vpeq m s' u t'" 
            by (smt (verit, ccfv_SIG) a0 a1 a2 a3 a4 a5 b1 ivpeq_def weak_step_consistent_def)
          then show ?thesis by auto
        qed
      next
        assume c0: "\<not> (interference m (domain m a) u)"
        show ?thesis 
          by (smt (verit, best) a0 a1 a2 a3 a4 a5 b1 c0 ivpeq_def weak_step_consistent_def)
      qed
    }
    then show ?thesis by auto
  qed
  then show ?thesis 
    by (simp add: ivpeq_def)
qed

lemma sources_preserved_left:
  "\<lbrakk>local_respect m; reachable0 m s; reachable0 m t; (s, s') \<in> step m a; domain m a \<notin> sources m (a#as) u; 
   ivpeq m s (sources m (a#as) u) t\<rbrakk> \<Longrightarrow> ivpeq m s' (sources m as u) t"
  proof -
    assume a1: "local_respect m"
    assume a2: "reachable0 m s"
    assume a3: "reachable0 m t"
    assume a4: "(s, s') \<in> step m a"
    assume a5: "domain m a \<notin> sources m (a#as) u"
    assume a6: "ivpeq m s (sources m (a#as) u) t" 
    have " \<forall>d\<in>sources m as u. vpeq m s' d t"
    proof-
      {
      fix d
      assume b0: "d \<in> sources m as u"
      then have b1: "\<not> interference m (domain m a) d" 
        using a5 sources_Cons by fastforce
      from a6 b0 have b2: "vpeq m s d t" 
        by (simp add: ivpeq_def sources_Cons)
      with b1 have "vpeq m s' d t"
        by (meson a1 a2 a4 local_respect_def vpeq_symmetric_lemma vpeq_transitive_lemma)
    }
    then show ?thesis by simp
  qed
  then show ?thesis by (simp add: ivpeq_def)
qed

theorem UnwindingTheorem_nonleakage:
    assumes p1: "observed_consistent m"
    and     p2: "weak_step_consistent m"
  shows "nonleakage m"
proof(subst nonleakage_def)
  show "\<forall>as s t u. reachable0 m s \<and> reachable0 m t \<longrightarrow> ivpeq m s (sources m as u) t
        \<longrightarrow> exec_equiv m s as t as u"
  proof -
    {
      fix as
      have "\<forall>s t u. reachable0 m s \<and> reachable0 m t \<longrightarrow> ivpeq m s (sources m as u) t
           \<longrightarrow> exec_equiv m s as t as u"
      proof(induct as)
        case Nil
        show ?case 
        proof -
          {
            fix s t u
            assume a0: "ivpeq m s (sources m [] u) t"
            then have a1: "vpeq m s u t"
              by (simp add: ivpeq_def sources_Nil)
            then have "exec_equiv m s [] t [] u"  unfolding exec_equiv_def
              using observed_consistent_def p1 vpeq_def by fastforce
          }
          then show ?thesis by auto
        qed
      next
        case (Cons b bs)
        assume a0: "\<forall>s t u. reachable0 m s \<and> reachable0 m t \<longrightarrow> ivpeq m s (sources m bs u) t
                    \<longrightarrow> exec_equiv m s bs t bs u"
        show ?case
        proof -
          {
            fix s t u
            assume b0: "(reachable0 m s) \<and> (reachable0 m t)"
            assume b1: "ivpeq m s (sources m (b#bs) u) t"
            have "\<forall>s' t'. (s, s') \<in> step m b \<and> (t, t') \<in> step m b \<longrightarrow> exec_equiv m s' bs t' bs u"
              by (meson a0 b0 b1 p2 reachableStep sources_unwinding_step)
            then have "exec_equiv m s (b # bs) t  (b # bs) u" 
              by (simp add: b0 exec_equiv_both)
          }
          then show ?thesis by auto
        qed
      qed
    }
    then show ?thesis by auto
  qed
qed

theorem UnwindingTheorem_noninfluence0:
    assumes p1: "observed_consistent m" 
    and     p2: "local_respect m"
    and     p3: "weak_step_consistent m"
  shows "noninfluence0 m"
proof(subst noninfluence0_def)
  show "\<forall>u as s t. reachable0 m s \<and> reachable0 m t \<longrightarrow> ivpeq m s (sources m as u) t 
        \<longrightarrow> exec_equiv m s as t (ipurge m as u) u"
  proof-
    {
      fix as
      have "\<forall>u s t. reachable0 m s \<and> reachable0 m t \<longrightarrow> ivpeq m s (sources m as u) t 
            \<longrightarrow> exec_equiv m s as t (ipurge m as u) u"
      proof(induct as)
        case Nil show ?case 
        proof -
          {
            fix u s t
            assume a0:"reachable0 m s \<and> reachable0 m t"
            assume a1:"ivpeq m s (sources m [] u) t"
            have a2:"vpeq m s u t" by (metis a1 insertI1 ivpeq_def sources_Nil)
            have a3:"ipurge m [] u = []" by simp
            from a2 have "exec_equiv m s [] t [] u" unfolding exec_equiv_def
              using observed_consistent_def p1 vpeq_def by fastforce
            with a3 have "exec_equiv m s [] t (ipurge m [] u) u" by auto
          }
          then show ?thesis by auto
        qed
      next
        case (Cons b bs)
        assume a0:"\<forall>u s t. reachable0 m s \<and> reachable0 m t \<longrightarrow> ivpeq m s (sources m bs u) t 
                   \<longrightarrow> exec_equiv m s bs t (ipurge m bs u) u"
        show ?case 
        proof-
          {
            fix u s t
            assume b0:"reachable0 m s"
            assume b1:"reachable0 m t"
            assume b2:"ivpeq m s (sources m (b # bs) u) t"
            have " exec_equiv m s (b # bs) t (ipurge m (b # bs) u) u"
            proof(cases "domain m b \<in> sources m (b # bs) u")
              assume d0: "domain m b \<in> sources m (b # bs) u"
              then have d1: "ipurge m (b # bs) u = b # ipurge m bs u" by simp
              have "\<forall>s' t'. (s, s') \<in> step m b \<and> (t, t') \<in> step m b \<longrightarrow> 
                    exec_equiv m s' bs t' (ipurge m bs u) u"
                by (meson a0 b0 b1 b2 p3 reachableStep sources_unwinding_step)
              then show ?thesis using b0 b1 d1 exec_equiv_both by auto
            next
              assume d0: "\<not> domain m b \<in> sources m (b # bs) u"
              then have d1: "ipurge m (b # bs) u = ipurge m bs u" by simp
              have "\<forall>s'. (s, s') \<in> step m b \<longrightarrow> exec_equiv m s' bs t (ipurge m bs u) u"
                by (meson a0 b0 b1 b2 d0 p2 reachableStep sources_preserved_left)
              then show ?thesis
                by (smt (verit) d1 exec_equiv_def relcomp.cases run_Cons) 
            qed
          }
          then show ?thesis by auto
        qed
      qed
    }
    then show ?thesis by auto
  qed
qed

end
end
