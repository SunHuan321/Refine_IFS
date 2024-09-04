theory Anno_SIMP_IFS
  imports PiCore_Anno_SIMP "../PiCore_RG_IFS"
begin

locale Anno_SIMP_IFS = 
  fixes interference :: "'d \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<leadsto> _)" [70,71] 60)
   and  vpeq ::  "'s \<Rightarrow> 'd \<Rightarrow> 's \<Rightarrow> bool" ("(_ \<sim>_\<sim> _)" [70,69,70] 60)
   and  dome :: "'s  \<Rightarrow> ('l, 'k, 's, 's ann_prog option) event \<Rightarrow> 'd"
 assumes  simp_vpeq_trans : "\<forall> a b c u. (a \<sim> u \<sim> b) \<and> (b \<sim> u \<sim> c) \<longrightarrow> (a \<sim> u \<sim> c)"
    and   simp_vpeq_sym : "\<forall> a b u. (a \<sim> u \<sim> b) \<longrightarrow> (b \<sim> u \<sim> a)"
    and   simp_vpeq_refl : "\<forall> a u. (a \<sim> u \<sim> a)"

begin

inductive lr_p_sat :: "'s ann_prog option\<Rightarrow> ('l, 'k, 's, 's ann_prog option) event \<Rightarrow> bool"
    ("\<turnstile>\<^sub>l\<^sub>r _ sat\<^sub>p _" [60] 45)
where
  Basic: "\<lbrakk>\<forall>s u. s \<in> r \<and> \<not> (dome s ev) \<leadsto> u \<longrightarrow> s  \<sim>u\<sim> f s\<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>l\<^sub>r Some (AnnBasic r f) sat\<^sub>p ev"
| Seq: "\<lbrakk> \<turnstile>\<^sub>l\<^sub>r (Some P) sat\<^sub>p ev;  \<turnstile>\<^sub>l\<^sub>r (Some Q) sat\<^sub>p ev\<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>l\<^sub>r Some (AnnSeq P Q) sat\<^sub>p ev"
| Cond: "\<lbrakk> \<turnstile>\<^sub>l\<^sub>r (Some P1) sat\<^sub>p ev;  \<turnstile>\<^sub>l\<^sub>r (Some P2) sat\<^sub>p ev \<rbrakk>
          \<Longrightarrow> \<turnstile>\<^sub>l\<^sub>r Some (AnnCond r b P1 P2) sat\<^sub>p ev"
| While: "\<lbrakk> \<turnstile>\<^sub>l\<^sub>r (Some P) sat\<^sub>p ev \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>l\<^sub>r Some (AnnWhile r b P) sat\<^sub>p ev"
| Await: "\<lbrakk> \<turnstile>\<^sub>I Some (AnnAwait r b P) sat\<^sub>p [pre, rely, guar, post]; r \<subseteq> pre; \<forall>s u. s \<in> pre \<and> (\<not> (dome s ev) \<leadsto> u)
           \<longrightarrow> (\<forall>t. (s, t) \<in> guar \<longrightarrow> s \<sim>u\<sim> t)\<rbrakk>
          \<Longrightarrow> \<turnstile>\<^sub>l\<^sub>r Some (AnnAwait r b P) sat\<^sub>p ev"
| Nondt: "\<lbrakk>\<forall>s  u.  s \<in> r \<and> \<not> (dome s ev) \<leadsto> u \<longrightarrow> (\<forall>t. (s, t) \<in> f \<longrightarrow> s \<sim>u\<sim> t)\<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>l\<^sub>r Some (AnnNondt r f) sat\<^sub>p ev"
| None: "\<turnstile>\<^sub>l\<^sub>r None sat\<^sub>p ev"

inductive sc_p_sat :: "'s ann_prog option\<Rightarrow> ('l, 'k, 's, 's ann_prog option) event \<Rightarrow> bool"
    ("\<turnstile>\<^sub>s\<^sub>c _ sat\<^sub>p _" [60] 45)
where
  Basic: "\<lbrakk>\<forall>s1 s2 u. s1 \<in> r \<and> s2 \<in> r \<and> s1 \<sim>u\<sim> s2 \<and> ((dome s1 ev) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1 ev)\<sim> s2)
           \<longrightarrow> f s1 \<sim>u\<sim> f s2\<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>s\<^sub>c Some (AnnBasic r f) sat\<^sub>p ev"
| Seq: "\<lbrakk> \<turnstile>\<^sub>s\<^sub>c (Some P) sat\<^sub>p ev;  \<turnstile>\<^sub>s\<^sub>c (Some Q) sat\<^sub>p ev\<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>s\<^sub>c Some (AnnSeq P Q) sat\<^sub>p ev"
| Cond: "\<lbrakk> \<turnstile>\<^sub>s\<^sub>c (Some P1) sat\<^sub>p ev;  \<turnstile>\<^sub>s\<^sub>c (Some P2) sat\<^sub>p ev \<rbrakk>
          \<Longrightarrow> \<turnstile>\<^sub>s\<^sub>c (Some (AnnCond r b P1 P2)) sat\<^sub>p ev"
| While: "\<lbrakk> \<turnstile>\<^sub>s\<^sub>c (Some P) sat\<^sub>p ev \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>s\<^sub>c Some (AnnWhile r b P) sat\<^sub>p ev"
| Await: "\<lbrakk> \<turnstile>\<^sub>I Some (AnnAwait r b P) sat\<^sub>p [pre, rely, guar, post];  r \<subseteq> pre;
            \<forall>s1 s2  u. s1 \<in> pre \<and> s2 \<in> pre \<and> s1 \<sim>u\<sim> s2 \<and> ((dome s1  ev) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1  ev)\<sim> s2)
            \<longrightarrow> (\<forall>t1 t2. (s1, t1) \<in> guar \<and> (s2, t2) \<in> guar \<longrightarrow> t1 \<sim>u\<sim> t2)\<rbrakk>
          \<Longrightarrow> \<turnstile>\<^sub>s\<^sub>c Some (AnnAwait r b P) sat\<^sub>p ev"
| Nondt: "\<lbrakk>\<forall>s1 s2  u.  s1 \<in> r \<and> s2 \<in> r \<and> s1 \<sim>u\<sim> s2 \<and> ((dome s1  ev) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1  ev)\<sim> s2) \<longrightarrow>
           (\<forall>t1 t2. (s1, t1) \<in> f \<and> (s2, t2) \<in> f \<longrightarrow> t1 \<sim>u\<sim> t2) \<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>s\<^sub>c Some (AnnNondt r f) sat\<^sub>p ev"
| None: "\<turnstile>\<^sub>s\<^sub>c None sat\<^sub>p ev"

interpretation PiCore_RG_IFS_Validity ptranI petranI None cpts_pI cpts_of_pI prog_validityI ann_preserves_p
               assume_pI commit_pI preserves_p rghoare_pI interference vpeq dome
  using simp_vpeq_trans simp_vpeq_sym simp_vpeq_refl 
  by (smt (verit, best) PiCore_RG_IFS_Validity.intro PiCore_RG_IFS_Validity_axioms.intro event_hoare_axioms)


lemma lr_p_None_Sound: "local_respect_p1 \<Gamma> None ev \<and> local_respect_p2 \<Gamma> None \<S>"
  apply (rule conjI, simp add: local_respect_p1_def ptran'_def none_no_tran')
  by (simp add: local_respect_p2_def ptran'_def none_no_tran')


lemma lr_p_Basic_Sound: "\<forall>s u. s \<in> r \<and> \<not> (dome s ev \<leadsto> u) \<longrightarrow> s \<sim>u\<sim> f s \<Longrightarrow>
                          \<exists>\<S>. Some (AnnBasic r f) \<in> \<S> \<and> local_respect_p \<Gamma> \<S> ev"
  apply (rule_tac x = "{Some (AnnBasic r f), None}" in exI, simp)
  apply (simp add: local_respect_p_def)
  apply (intro conjI)
  apply (simp add: local_respect_p1_def ptran'_def, clarify)
  apply (erule ptran.cases, simp_all)
    apply (simp add: local_respect_p2_def ptran'_def)
    apply fastforce
  by (simp_all add: lr_p_None_Sound)

definition lift_prog_set :: "'s ann_prog \<Rightarrow> 's ann_prog option set \<Rightarrow> 's ann_prog option set"
  where "lift_prog_set Q \<S> \<equiv> {prog. \<exists>P. Some P \<in> \<S> \<and> prog = Some (AnnSeq P Q)} \<union> {Some Q}"


lemma lift_prog_set_respect1 : "local_respect_p1 \<Gamma> (Some P) ev \<Longrightarrow> local_respect_p1 \<Gamma> (Some (AnnSeq P Q)) ev"
  apply (simp add: local_respect_p1_def ptran'_def, clarify)
  by (erule_tac ptran.cases, simp_all)

lemma lr_p_Seq_Sound: "\<lbrakk>\<exists>\<S>. Some P \<in> \<S> \<and> local_respect_p \<Gamma> \<S> ev; \<exists>\<S>. Some Q \<in> \<S> \<and> local_respect_p \<Gamma> \<S> ev\<rbrakk>
                      \<Longrightarrow> \<exists>\<S>. Some (AnnSeq P Q) \<in> \<S> \<and> local_respect_p \<Gamma> \<S> ev"
  apply (erule exE, erule exE)
  apply (rule_tac x = "lift_prog_set Q \<S> \<union> \<S>'" in exI)
  apply (rule conjI, simp add: lift_prog_set_def)
  apply (simp add: local_respect_p_def, clarify)
  apply (rule conjI)
   apply (case_tac "Pa \<in> \<S>'", simp)
   apply (simp add: lift_prog_set_def)
   apply (case_tac "Pa = Some Q", simp, clarsimp)
   apply (simp add: lift_prog_set_respect1)
  apply (case_tac "Pa \<in> \<S>'", simp add: local_respect_p2_def)
  apply (simp add: lift_prog_set_def)
  apply (case_tac "Pa = Some Q", simp, simp add: local_respect_p2_def ptran'_def, clarify)
  apply (erule ptran.cases, simp_all)
  by (meson ann_preserves_p.simps(2))


lemma lr_p_Cond_Sound: "\<lbrakk>\<exists>\<S>. Some P1 \<in> \<S> \<and> local_respect_p \<Gamma> \<S> ev; 
                        \<exists>\<S>.  Some P2 \<in> \<S> \<and> local_respect_p \<Gamma> \<S> ev\<rbrakk>
                        \<Longrightarrow> \<exists>\<S>. Some (AnnCond r b P1 P2) \<in> \<S> \<and> local_respect_p \<Gamma> \<S> ev"
  apply (clarsimp, rule_tac x = "\<S> \<union> \<S>' \<union> {Some (AnnCond r b P1 P2)}" in exI)
  apply (rule conjI, simp)
  apply (rule local_respect_p_insert)
    apply (simp add: local_respect_p_union)
  apply (simp add: local_respect_p1_def ptran'_def)
  using simp_vpeq_refl apply fastforce
  apply (simp add: local_respect_p2_def ptran'_def)
  using UnI1  by fastforce

thm Set.bspec
lemma lr_p_While_Sound: "\<lbrakk>\<exists>\<S>. Some P \<in> \<S> \<and> local_respect_p \<Gamma> \<S> ev \<rbrakk> 
                      \<Longrightarrow> \<exists>\<S>. Some (AnnWhile r b P) \<in> \<S> \<and> local_respect_p \<Gamma> \<S> ev"
  apply (erule exE)
  apply (rule_tac x = "lift_prog_set (AnnWhile r b P) \<S> \<union> {None}" in exI)
  apply (rule conjI, simp add: lift_prog_set_def)
  apply (simp add: local_respect_p_def, clarify)
  apply (rule conjI)
   apply (simp add: lr_p_None_Sound)
  apply (rule conjI)
   apply (simp add: lr_p_None_Sound, clarify)
  apply (rule conjI)
   apply (simp add: lift_prog_set_def)
   apply (case_tac "Pa = Some (AnnWhile r b P)")
    apply (drule_tac x = "Some P" in Set.bspec, simp, clarify)
    apply (simp add: local_respect_p1_def ptran'_def)
  using simp_vpeq_refl apply force
   apply (metis lift_prog_set_respect1)
  apply (simp add: lift_prog_set_def)
  apply (case_tac "Pa = Some (AnnWhile r b P)", simp add: local_respect_p2_def ptran'_def, clarify)
   apply fastforce
  apply (clarify, drule_tac x = "Some Paa" in Set.bspec, simp, drule conjunct2)
  apply (simp add: local_respect_p2_def ptran'_def, clarify)
  apply (erule ptran.cases, simp_all)
  by blast

lemma Await_guar: "\<lbrakk>\<turnstile>\<^sub>I Some (AnnAwait r b P) sat\<^sub>p [pre, rely, guar, post]; 
                    (Some (AnnAwait r b P), s) -c\<rightarrow> (P', s'); s \<in> pre\<rbrakk> \<Longrightarrow> (s, s') \<in> guar"
  apply (drule rgsound_pI, simp add: Anno_SIMP_Hoare_Plus.prog_validity_def)
  apply (drule_tac a = s in allD)
  apply (drule conjunct1)
  apply (drule_tac c = "[(Some (AnnAwait r b P), s), (P', s')]" in subsetD)
   apply (simp add: assume_p_def, rule conjI)
    apply (simp add: cpts_of_p_def cpts_p.CptsPComp cpts_p.CptsPOne)
   apply (metis Suc_less_eq assume_p_defI cpts_p.CptsPComp cpts_p.CptsPOne etran_or_ctran2_disjI1 
          length_Cons less_Suc0 list.size(3) nth_Cons_0 nth_Cons_Suc snd_conv)
  by (metis Suc_less_eq commit_p_defI length_Cons nth_Cons_0 nth_Cons_Suc snd_conv zero_less_Suc)

lemma lr_p_Await_Sound: "\<lbrakk>\<turnstile>\<^sub>I Some (AnnAwait r b P) sat\<^sub>p [pre, rely, guar, post]; r \<subseteq> pre; \<forall>s u. s \<in> pre \<and> 
                          \<not> (dome s ev \<leadsto> u) \<longrightarrow> (\<forall>t. (s, t) \<in> guar \<longrightarrow> s \<sim>u\<sim> t)\<rbrakk> \<Longrightarrow> 
                          \<exists>\<S>. Some (AnnAwait r b P) \<in> \<S> \<and> local_respect_p \<Gamma> \<S> ev"
  apply (rule_tac x = "{Some (AnnAwait r b P), None}" in exI, simp add: local_respect_p_def)
  apply (rule conjI, simp add: local_respect_p1_def ptran'_def, clarify)
   apply (meson Await_guar subsetD)
  apply (intro conjI)
    apply (simp add: local_respect_p2_def ptran'_def)
    apply fastforce
  by (simp_all add: lr_p_None_Sound)

lemma lr_p_Nondt_Sound: " \<forall>s u. s \<in> r \<and> \<not> (dome s ev \<leadsto> u) \<longrightarrow> (\<forall>t. (s, t) \<in> f \<longrightarrow> s \<sim>u\<sim> t) 
                          \<Longrightarrow> \<exists>\<S>. Some (AnnNondt r f) \<in> \<S> \<and> local_respect_p \<Gamma> \<S> ev"
  apply (rule_tac x = "{Some (AnnNondt r f), None}" in exI, simp)
  apply (simp add: local_respect_p_def)
  apply (rule conjI, simp add: local_respect_p1_def ptran'_def, clarify)
   apply auto
    apply (simp add: local_respect_p2_def ptran'_def)
    apply fastforce
  by (simp_all add: lr_p_None_Sound)


theorem lr_p_sound : " \<turnstile>\<^sub>l\<^sub>r P sat\<^sub>p ev \<Longrightarrow> lr_p \<Gamma> P ev"
  apply (simp add: lr_p_def, erule lr_p_sat.induct)
        apply (simp add: lr_p_Basic_Sound)
       apply (simp add: lr_p_Seq_Sound)
      apply (simp add: lr_p_Cond_Sound)
     apply (simp add: lr_p_While_Sound)
    apply (simp add: lr_p_Await_Sound)
   apply (simp add: lr_p_Nondt_Sound)
  using local_respect_p_def lr_p_None_Sound by fastforce

lemma sc_p_None_Sound: "step_consistent_p1 \<Gamma> None ev \<and> step_consistent_p2 \<Gamma> None \<S>"
  by (simp add: none_no_tran step_consistent_p1_def step_consistent_p2_def)

lemma sc_p_Basic_Sound: " \<forall>s1 s2  u. s1 \<in> r \<and> s2 \<in> r \<and> s1 \<sim>u\<sim> s2 \<and> (dome s1 ev \<leadsto> u \<longrightarrow> s1 \<sim>dome s1 ev\<sim> s2) \<longrightarrow> 
        f s1 \<sim>u\<sim> f s2 \<Longrightarrow> \<exists>\<S>. Some (AnnBasic r f) \<in> \<S> \<and> step_consistent_p \<Gamma> \<S> ev"
  apply (rule_tac x = "{Some (AnnBasic r f), None}" in exI, simp)
  apply (simp add: step_consistent_p_def)
  apply (intro conjI)
  apply (simp add: step_consistent_p1_def ptran'_def)
   apply auto
  apply (simp add: step_consistent_p2_def ptran'_def)
    apply fastforce
  by (simp_all add: sc_p_None_Sound)

lemma lift_prog_set_consistent1 : "step_consistent_p1 \<Gamma> (Some P) ev \<Longrightarrow> step_consistent_p1 \<Gamma> (Some (AnnSeq P Q)) ev"
  apply (rule step_consistent_p1_eq, simp add: ptran'_def, clarify)
  apply (erule_tac ptran.cases, simp_all, clarify)
   apply (erule_tac ptran.cases, simp_all, clarify)
  unfolding step_consistent_p1_def
    apply (drule_tac a = "None" and b = "None" and c = "s1" and d = "s2" and e = "s1'" in all5D)
    apply (drule_tac a = "s2'" and b = "u" in all2_impD, simp add: ptran'_def, simp)
   apply fastforce
  apply (erule ptran.cases)
          apply force apply fastforce
        apply (metis ann_preserves_p.simps(2) ann_prog.simps(2) option.inject prod.inject ptran'_def)
       apply force+
  done

lemma sc_p_Seq_Sound: "\<lbrakk> \<exists>\<S>. Some P \<in> \<S> \<and> step_consistent_p \<Gamma> \<S> ev; \<exists>\<S>. Some Q \<in> \<S> \<and> step_consistent_p \<Gamma> \<S> ev\<rbrakk>
                      \<Longrightarrow> \<exists>\<S>. Some (AnnSeq P Q) \<in> \<S> \<and> step_consistent_p \<Gamma> \<S> ev"
  apply (erule exE, erule exE)
  apply (rule_tac x = "lift_prog_set Q \<S> \<union> \<S>'" in exI)
  apply (rule conjI, simp add: lift_prog_set_def)
  apply (simp add: step_consistent_p_def, clarify)
  apply (rule conjI)
   apply (case_tac "Pa \<in> \<S>'", simp)
   apply (simp add: lift_prog_set_def)
   apply (case_tac "Pa = Some Q", simp, clarsimp)
  apply (metis lift_prog_set_consistent1)
  apply (case_tac "Pa \<in> \<S>'", simp add: step_consistent_p2_def)
  apply (simp add: lift_prog_set_def)
  apply (case_tac "Pa = Some Q")
   apply force
  apply (simp add: step_consistent_p2_def ptran'_def, clarify)
  apply (erule ptran.cases, simp_all)
  by (meson ann_preserves_p.simps(2))

lemma sc_p_Cond_Sound: "\<lbrakk>\<exists>\<S>. Some P1 \<in> \<S> \<and> step_consistent_p \<Gamma> \<S> ev; \<exists>\<S>. Some P2 \<in> \<S> \<and> step_consistent_p \<Gamma> \<S> ev\<rbrakk>
                \<Longrightarrow> \<exists>\<S>. Some (AnnCond r b P1 P2) \<in> \<S> \<and> step_consistent_p \<Gamma> \<S> ev"
  apply (clarsimp, rule_tac x = "\<S> \<union> \<S>' \<union> {Some (AnnCond r b P1 P2)}" in exI)
  apply (rule conjI, simp)
  apply (rule step_consistent_p_insert)
    apply (simp add: step_consistent_p_union)
  apply (simp add: step_consistent_p1_def ptran'_def)
   apply auto[1]
  apply (simp add: step_consistent_p2_def ptran'_def)
  by auto

lemma sc_p_While_Sound: "\<lbrakk> \<exists>\<S>. Some P \<in> \<S> \<and> step_consistent_p \<Gamma> \<S> ev\<rbrakk>
                      \<Longrightarrow> \<exists>\<S>. Some (AnnWhile r b P) \<in> \<S> \<and> step_consistent_p \<Gamma> \<S> ev"
  apply (erule exE)
  apply (rule_tac x = "lift_prog_set (AnnWhile r b P) \<S> \<union> {None}" in exI)
  apply (rule conjI, simp add: lift_prog_set_def)
  apply (simp add: step_consistent_p_def, clarify)
  apply (rule conjI, simp add: sc_p_None_Sound)
  apply (rule conjI, simp add: sc_p_None_Sound, clarify)
  apply (rule conjI)
   apply (case_tac "Pa = Some (AnnWhile r b P)")
    apply (drule_tac x = "Some P" in Set.bspec, simp, clarify)
    apply (rule step_consistent_p1_eq, simp add: ann_preserves_p_def ptran'_def, clarify)
    apply (erule ptran.cases, simp_all)
     apply (erule ptran.cases, simp_all, clarify)
    apply force
   apply (smt (verit, ccfv_threshold) Un_iff lift_prog_set_consistent1 lift_prog_set_def mem_Collect_eq singletonD)
  apply (case_tac "Pa = Some (AnnWhile r b P)", simp add: step_consistent_p2_def ptran'_def)
  using lift_prog_set_def apply fastforce
  apply (simp add: step_consistent_p2_def ptran'_def lift_prog_set_def, clarify)
  apply (erule ptran.cases, simp_all)
  by (metis ann_preserves_p.simps(2))

lemma sc_p_Await_Sound: " \<lbrakk>\<turnstile>\<^sub>I Some (AnnAwait r b P) sat\<^sub>p [pre, rely, guar, post] ; r \<subseteq> pre; 
                          \<forall>s1 s2  u. s1 \<in> pre \<and> s2 \<in> pre  \<and> s1 \<sim>u\<sim> s2 \<and> (dome s1  ev \<leadsto> u 
                          \<longrightarrow> s1 \<sim>dome s1  ev\<sim> s2) \<longrightarrow> (\<forall>t1 t2. (s1, t1) \<in> guar \<and> (s2, t2) \<in> guar 
                          \<longrightarrow> t1 \<sim>u\<sim> t2)\<rbrakk> \<Longrightarrow> \<exists>\<S>. Some (AnnAwait r b P) \<in> \<S> \<and> step_consistent_p \<Gamma> \<S> ev"
  apply (rule_tac x = "{Some (AnnAwait r b P), None}" in exI, simp add: step_consistent_p_def)
  apply (intro conjI)
   apply (rule step_consistent_p1_eq, clarify)
   apply (drule_tac a = s1 and b = s2 and c = u  in all3_impD, simp add: subset_eq)
   apply (erule all2_impD, simp add: ann_preserves_p_def)
     apply (simp add: Await_guar subset_eq ptran'_def)
    apply (simp add: step_consistent_p2_def ptran'_def)
    apply fast
  by (simp_all add: sc_p_None_Sound)


lemma sc_p_Nondt_Sound_lemma : "\<forall>s1 s2  u. s1 \<in> r \<and> s2 \<in> r \<and> s1 \<sim>u\<sim> s2 \<and> (dome s1  ev \<leadsto> u \<longrightarrow> s1 \<sim>dome s1 ev\<sim> s2) 
                   \<longrightarrow> (\<forall>t1 t2. (s1, t1) \<in> f \<and> (s2, t2) \<in> f \<longrightarrow> t1 \<sim>u\<sim> t2) 
                   \<Longrightarrow> step_consistent_p1 \<Gamma> (Some (AnnNondt r f)) ev"
proof-
  assume a0: "\<forall>s1 s2  u. s1 \<in> r \<and> s2 \<in> r \<and> s1 \<sim>u\<sim> s2 \<and> (dome s1  ev \<leadsto> u \<longrightarrow> s1 \<sim>dome s1 ev\<sim> s2) 
              \<longrightarrow> (\<forall>t1 t2. (s1, t1) \<in> f \<and> (s2, t2) \<in> f \<longrightarrow> t1 \<sim>u\<sim> t2)"
  then have "\<forall>P1' P2' s1 s2 s1' s2' u.  s1 \<in> r \<and> s2 \<in> r \<and> s1 \<sim>u\<sim> s2 \<and> 
        (dome s1 ev \<leadsto> u \<longrightarrow> s1 \<sim>dome s1 ev\<sim> s2) \<and> (Some (AnnNondt r f), s1) -c\<rightarrow> (P1', s1') \<and> 
        (Some (AnnNondt r f), s2) -c\<rightarrow> (P2', s2') \<longrightarrow> s1' \<sim>u\<sim> s2'"
    by blast
  then have "\<forall>P1' P2' s1 s2 s1' s2' u. ann_preserves_p (Some (AnnNondt r f)) s1 \<and>
       ann_preserves_p (Some (AnnNondt r f)) s2 \<and>  s1 \<sim>u\<sim> s2 \<and> (dome s1 ev \<leadsto> u \<longrightarrow> s1 \<sim>dome s1 ev\<sim> s2) \<and>
       PiCore_Anno_SIMP.ptran' \<Gamma> (Some (AnnNondt r f), s1) (P1', s1') \<and> 
       PiCore_Anno_SIMP.ptran' \<Gamma> (Some (AnnNondt r f), s2) (P2', s2') \<longrightarrow> s1' \<sim>u\<sim> s2'"
    by (metis ann_pre.simps(6) ann_preserves_p.simps(2) ptran'_def)
  then show ?thesis
    by (smt (verit, best) step_consistent_p1_def)
qed

lemma sc_p_Nondt_Sound: "\<forall>s1 s2  u. s1 \<in> r \<and> s2 \<in> r \<and> s1 \<sim>u\<sim> s2 \<and> (dome s1  ev \<leadsto> u \<longrightarrow> s1 \<sim>dome s1 ev\<sim> s2) 
                   \<longrightarrow> (\<forall>t1 t2. (s1, t1) \<in> f \<and> (s2, t2) \<in> f \<longrightarrow> t1 \<sim>u\<sim> t2) 
                   \<Longrightarrow> \<exists>\<S>. Some (AnnNondt r f) \<in> \<S> \<and> step_consistent_p \<Gamma> \<S> ev"
  apply (rule_tac x = "{Some (AnnNondt r f), None}" in exI, simp add: step_consistent_p_def)
  apply (intro conjI)
     apply (rule sc_p_Nondt_Sound_lemma)
     apply blast
    apply (simp add: step_consistent_p2_def ptran'_def)
    apply fastforce
  by (simp_all add: sc_p_None_Sound)

theorem sc_p_sound : "\<turnstile>\<^sub>s\<^sub>c P sat\<^sub>p ev \<Longrightarrow> sc_p \<Gamma> P ev"
  apply (simp add: sc_p_def)
  apply (erule sc_p_sat.induct)
        apply (simp add: sc_p_Basic_Sound)
       apply (simp add: sc_p_Seq_Sound)
      apply (simp add: sc_p_Cond_Sound)
     apply (simp add: sc_p_While_Sound)
    apply (rule sc_p_Await_Sound, simp, simp)
    apply force
   apply (rule sc_p_Nondt_Sound)
   apply force
  using sc_p_None_Sound step_consistent_p_def by fastforce

end






end