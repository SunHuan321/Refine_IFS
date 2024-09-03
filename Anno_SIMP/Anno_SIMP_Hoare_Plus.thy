theory Anno_SIMP_Hoare_Plus
  imports Anno_SIMP_RG_Hoare
begin

inductive rghoare_p :: "['s ann_prog option, 's set, ('s \<times> 's) set, ('s \<times> 's) set, 's set] \<Rightarrow> bool"
    ("\<turnstile>\<^sub>I _ sat\<^sub>p [_, _, _, _]" [60,0,0,0,0] 45)
where
  Basic: "\<lbrakk> pre \<subseteq> r; pre \<subseteq> {s. f s \<in> post}; {(s,t). s \<in> pre \<and> (t=f s)} \<subseteq> guar;
            stable pre rely; stable post rely\<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>I Some (AnnBasic r f) sat\<^sub>p [pre, rely, guar, post]"
| Seq: "\<lbrakk> \<turnstile>\<^sub>I (Some P) sat\<^sub>p [pre, rely, guar, mid]; \<turnstile>\<^sub>I (Some Q) sat\<^sub>p [mid, rely, guar, post] \<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>I Some (AnnSeq P Q) sat\<^sub>p [pre, rely, guar, post]"
| Cond: "\<lbrakk> pre \<subseteq> r;  stable pre rely; \<turnstile>\<^sub>I (Some P1) sat\<^sub>p [pre \<inter> b, rely, guar, post];
           \<turnstile>\<^sub>I (Some P2) sat\<^sub>p [pre \<inter> -b, rely, guar, post]; \<forall>s. (s,s)\<in>guar \<rbrakk>
          \<Longrightarrow> \<turnstile>\<^sub>I Some (AnnCond r b P1 P2) sat\<^sub>p [pre, rely, guar, post]"
| While: "\<lbrakk> pre \<subseteq> r; stable pre rely; (pre \<inter> -b) \<subseteq> post; stable post rely;
            \<turnstile>\<^sub>I (Some P) sat\<^sub>p [pre \<inter> b, rely, guar, pre]; \<forall>s. (s,s)\<in>guar \<rbrakk>
          \<Longrightarrow> \<turnstile>\<^sub>I Some (AnnWhile r b P) sat\<^sub>p [pre, rely, guar, post]"
| Await: "\<lbrakk> pre \<subseteq> r; stable pre rely; stable post rely;
            \<forall>V. \<turnstile>\<^sub>I (Some P) sat\<^sub>p [pre \<inter> b \<inter> {V}, {(s, t). s = t},
                UNIV, {s. (V, s) \<in> guar} \<inter> post] \<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>I Some (AnnAwait r b P) sat\<^sub>p [pre, rely, guar, post]"
| Nondt: "\<lbrakk>pre \<subseteq> r; stable pre rely;
           pre \<subseteq> {s. (\<forall>t. (s,t) \<in> f \<longrightarrow> t \<in> post) \<and> (\<exists>t. (s,t) \<in> f)}; 
            {(s,t). s \<in> pre \<and> (s,t)\<in>f} \<subseteq> guar;  stable post rely\<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>I Some (AnnNondt r f) sat\<^sub>p [pre, rely, guar, post]"
| Conseq: "\<lbrakk> pre \<subseteq> pre'; rely \<subseteq> rely'; guar' \<subseteq> guar; post' \<subseteq> post;
             \<turnstile>\<^sub>I (Some P) sat\<^sub>p [pre', rely', guar', post'] \<rbrakk>
            \<Longrightarrow> \<turnstile>\<^sub>I (Some P) sat\<^sub>p [pre, rely, guar, post]"

| None_hoare: "\<lbrakk> stable pre rely; pre \<subseteq> post \<rbrakk>  \<Longrightarrow> \<turnstile>\<^sub>I None sat\<^sub>p [pre, rely, guar, post]"

definition prog_validity :: "'s ann_prog option \<Rightarrow> 's set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> 's set \<Rightarrow> bool" 
                 ("\<Turnstile>\<^sub>I _ sat\<^sub>p [_, _, _, _]" [60,0,0,0,0] 45) where
  "\<Turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post] \<equiv> 
   \<forall>s. cpts_of_p P s \<inter> assume_p(pre, rely) \<subseteq> commit_p(guar, post) \<inter> preserves_p"

subsection \<open>lemmas of SIMP\<close>

lemma etran_or_ctran2_disjI3:
  "\<lbrakk> x \<in> cpts_p; Suc i<length x; \<not> x!i -c\<rightarrow> x!Suc i\<rbrakk> \<Longrightarrow> x!i -pe\<rightarrow> x!Suc i"
  apply(induct x arbitrary:i)
   apply simp
  apply clarify
  apply(rule cpts_p.cases)
     apply simp+
  using less_Suc_eq_0_disj petran.intros apply force
  apply(case_tac i,simp)
  by simp


lemma stable_id: "stable P Id"
  unfolding stable_def Id_def by auto

lemma stable_id2: "stable P {(s,t). s = t}"
  unfolding stable_def by auto

lemma stable_int2: "stable s r \<Longrightarrow> stable t r \<Longrightarrow> stable (s \<inter> t) r"
  by (metis (full_types) IntD1 IntD2 IntI stable_def)

lemma stable_int3: "stable k r \<Longrightarrow> stable s r \<Longrightarrow> stable t r \<Longrightarrow> stable (k \<inter> s \<inter> t) r"
  by (metis (full_types) IntD1 IntD2 IntI stable_def)

lemma stable_int4: "stable k r \<Longrightarrow> stable s r \<Longrightarrow> stable t r \<Longrightarrow> stable v r \<Longrightarrow>  
                    stable (k \<inter> s \<inter> t \<inter> v) r"
  by (metis (full_types) IntD1 IntD2 IntI stable_def)

lemma stable_int5: "stable k r \<Longrightarrow> stable s r \<Longrightarrow> stable t r \<Longrightarrow> stable v r \<Longrightarrow>  
                    stable y r \<Longrightarrow> stable (k \<inter> s \<inter> t \<inter> v \<inter> y) r"
  by (metis (full_types) IntD1 IntD2 IntI stable_def)

lemma stable_un2: "stable s r \<Longrightarrow> stable t r \<Longrightarrow> stable (s \<union> t) r"
  by (simp add: stable_def)

subsection\<open>Soundness of the Rule of Consequence\<close>

lemma Conseq_sound:
  "\<lbrakk>pre \<subseteq> pre'; rely \<subseteq> rely'; guar' \<subseteq> guar; post' \<subseteq> post;
  \<Turnstile>\<^sub>I P sat\<^sub>p [pre', rely', guar', post']\<rbrakk>
  \<Longrightarrow> \<Turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post]"
  apply(simp add:prog_validity_def assume_p_def commit_p_def)
  apply clarify
  apply(erule_tac x=s in allE)
  by blast

subsection\<open>Soundness of the Await rule\<close>

lemma Await_sound:
  "\<lbrakk>pre \<subseteq> r; stable pre rely; stable post rely;
  \<forall>V. \<turnstile>\<^sub>I Some P sat\<^sub>p [pre \<inter> b \<inter> {s. s = V}, {(s, t). s = t},
                 UNIV, {s. (V, s) \<in> guar} \<inter> post] \<and>
  \<Turnstile>\<^sub>I Some P sat\<^sub>p [pre \<inter> b \<inter> {s. s = V}, {(s, t). s = t},
                 UNIV, {s. (V, s) \<in> guar} \<inter> post] \<rbrakk>
  \<Longrightarrow> \<Turnstile>\<^sub>I Some (AnnAwait r b P) sat\<^sub>p [pre, rely, guar, post]"
  apply(unfold prog_validity_def)
  apply clarify
  apply (rule IntI)
   apply(simp add:commit_p_def)
   apply(rule conjI, clarify)
    apply(simp add:cpts_of_p_def assume_p_def gets_p_def getspc_p_def)
    apply clarify
    apply(frule_tac j=0 and k=i and p= pre in stability,simp_all)
      apply(erule_tac x=ia in allE,simp)
     apply(subgoal_tac "x\<in> cpts_of_p (Some(AnnAwait r b P)) s")
      apply(erule_tac i=i in unique_ctran_Await,force,simp_all)
     apply(simp add:cpts_of_p_def)
(*here starts the different part.*)
    apply(erule ptran.cases,simp_all)
    apply(drule Star_imp_cptn)
    apply clarify
    apply(erule_tac x=sa in allE)
    apply clarify
    apply(erule_tac x=sa in allE)
    apply auto[1]
    apply(drule_tac c=l in subsetD)
     apply (simp add:cpts_of_p_def)
     apply clarify
     apply(erule_tac x=ia and P="\<lambda>i. H i \<longrightarrow> (J i, I i)\<in>ptran" for H J I in allE,simp)
     apply(erule petranE,simp)
    apply simp
   apply clarify
   apply (simp add:gets_p_def getspc_p_def)
   apply(simp add:cpts_of_p_def)
   apply clarify
   apply(frule_tac i="length x - 1" in exists_ctran_Await_None,force)
     apply (case_tac x,simp+)
    apply(rule last_fst_esp,simp add:last_length)
    apply(case_tac x, simp+)
   apply clarify
   apply(simp add:assume_p_def gets_p_def getspc_p_def)
   apply clarify
apply(frule_tac j=0 and k="j" and p= pre and rely = rely in stability,simp_all)
    apply(erule_tac i=j in unique_ctran_Await,force,simp_all)
   apply(case_tac "x!j")
   apply clarify
   apply simp
   apply(drule_tac s="Some (AnnAwait r b P)" in sym,simp)
   apply(case_tac "x!Suc j",simp)
   apply(rule ptran.cases,simp)
           apply(simp_all)
   apply(drule Star_imp_cptn)
   apply clarify
   apply(erule_tac x=sa in allE)
   apply clarify
   apply(erule_tac x=sa in allE)
   apply auto[1]
   apply(drule_tac c=l in subsetD)
    apply (simp add:cpts_of_p_def)
    apply clarify
    apply(erule_tac x=i and P="\<lambda>i. H i \<longrightarrow> (J i, I i)\<in>ptran" for H J I in allE,simp)
    apply(erule petranE,simp)
   apply simp
   apply clarify
   apply(frule_tac j="Suc j" and k="length x - 1" and p=post in stability,simp_all)
     apply(case_tac x,simp+)
    apply(erule_tac x=i in allE)
    apply(erule_tac i=j in unique_ctran_Await,force,simp_all)
      apply force
     apply (simp add: ptran.Await)
    apply linarith
   apply(case_tac x)
    apply(simp add:last_length)+
  apply (case_tac "\<exists>i. Suc i < length x \<and> (x!i) -c\<rightarrow> (x!(Suc i))")
   apply (simp add: preserves_p_def cpts_of_p_def assume_p_def gets_p_def)
   apply clarify
   apply (case_tac "ia \<le> i")
    apply(frule_tac j=0 and k=ia and p= pre in stability, simp_all)
      apply blast
  using unique_ctran_Await apply fastforce
    apply (case_tac "x!ia")
    apply (simp add: getspc_p_def)
    apply blast
   apply(frule_tac j=0 and k=i and p= pre in stability, simp_all)
     apply blast
    apply (smt (verit, best) le_eq_less_or_eq le_trans less_trans_Suc nat_neq_iff unique_ctran_Await)
   apply (case_tac "x ! Suc i")
   apply (erule ptran.cases, simp_all)
    apply (drule_tac i = "Suc i" and j = ia in not_ctran_Finish, simp_all)
   apply (simp add: getspc_p_def)
  apply (subgoal_tac "\<forall>i. Suc i < length x \<longrightarrow> x!i -pe\<rightarrow> x!Suc i")
   apply (simp add: assume_p_def gets_p_def cpts_of_p_def preserves_p_def, clarify)
   apply(frule_tac j=0 and k="i" and p= pre and rely = rely in stability,simp_all)
   apply (case_tac "getspc_p (x ! i)", simp, simp add: getspc_p_def)
   apply blast
  by (metis (mono_tags, lifting) CollectD cpts_of_p_def dual_order.refl etran_or_ctran)

subsection\<open>Soundness of None rule\<close>

lemma none_all_none: "c!0=(None,s) \<and> c \<in> cpts_p \<Longrightarrow> \<forall>i<length c. getspc_p (c ! i) = None"
proof(induct c arbitrary:s)
  case Nil
  then show ?case by simp
next
  case (Cons a c)
  assume p1: "\<And>s. c ! 0 = (None, s) \<and> c \<in> cpts_p \<Longrightarrow> \<forall>i<length c. getspc_p (c ! i) = None"
    and  p2: "(a # c) ! 0 = (None, s) \<and> a # c \<in> cpts_p"
  hence a0: "a = (None,s)" by simp
  thus ?case
    proof(cases "c = []")
      case True
      with a0 show ?thesis by (simp add: getspc_p_def)
    next
      case False
      assume b0: "c \<noteq> []"
      with p2 have c_cpts: "c \<in> cpts_p" using tl_in_cptn by fast
      from b0 obtain c' and b where bc': "c = b # c'"
        using list.exhaust by blast 
      from a0 have "\<not> a -c\<rightarrow> b" by(force elim: ptran.cases)
      with p2 have "a -pe\<rightarrow> b"  using bc' etran_or_ctran2_disjI3[of "a#c" 0] by auto
      hence "fst b = None" using petran.cases
        by (metis a0 prod.collapse) 
      with p1 bc' c_cpts have "\<forall>i<length c. getspc_p (c ! i) = None"
        by (metis nth_Cons_0 prod.collapse)
      with a0 show ?thesis
        by (metis fst_conv getspc_p_def not_ctran_None3' p2)
    qed
      
qed

lemma None_sound_h: "\<forall>x. x \<in> pre \<longrightarrow> (\<forall>y. (x, y) \<in> rely \<longrightarrow> y \<in> pre) \<Longrightarrow>
         pre \<subseteq> post \<Longrightarrow>
         snd (c ! 0) \<in> pre \<Longrightarrow>
         c \<noteq> [] \<Longrightarrow> \<forall>i. Suc i < length c \<longrightarrow> (snd (c ! i), snd (c ! Suc i)) \<in> rely 
      \<Longrightarrow> i < length c \<Longrightarrow> snd (c ! i) \<in> pre"
apply(induct i) by auto

lemma None_sound:
  "\<lbrakk> stable pre rely; pre \<subseteq> post \<rbrakk>
  \<Longrightarrow> \<Turnstile>\<^sub>I None sat\<^sub>p [pre, rely, guar, post]"
proof-
  assume a0: "stable pre rely"
  and a1: "pre \<subseteq> post"

  have "\<forall>c s. c \<in> cpts_of_p None s \<inter> assume_p (pre, rely) \<longrightarrow> c \<in> commit_p (guar, post) \<inter> preserves_p"
  proof-
    {
      fix c s 
      assume b0: "c \<in> cpts_of_p None s \<inter> assume_p (pre, rely)"
      then have b1: "snd (c!0) \<in> pre \<and> (\<forall>i. Suc i<length c \<longrightarrow> 
               c!i -pe\<rightarrow> c!(Suc i) \<longrightarrow> (snd (c!i), snd (c!Suc i)) \<in> rely)"
        by (simp add: assume_p_def gets_p_def)
      then have b2: "\<forall>i<length c. fst (c ! i) = None" using none_all_none 
        by (metis (mono_tags, lifting) CollectD IntD1 b0 cpts_of_p_def getspc_p_def)

      then have b3:  "(\<forall>i. Suc i<length c \<longrightarrow> c!i -c\<rightarrow> c!(Suc i) \<longrightarrow> 
                      (gets_p (c!i), gets_p (c!Suc i)) \<in> guar)"
        by (metis Suc_lessD prog_not_eq_in_ctran surjective_pairing)

      have "\<forall>i. i < length c \<longrightarrow> snd (c ! i) \<in> pre"
      proof-
        {
          fix i 
          have "i < length c \<longrightarrow> snd (c ! i) \<in> pre"
          proof(induct i)
            case 0 then show ?case by (simp add: b1)
          next
            case (Suc i) then show ?case 
              by (metis (no_types, lifting) Anno_SIMP_RG_Hoare.stable_def Suc_lessD 
                 a0 b1 b2 petran.intros prod.collapse)
          qed
        }
        then show ?thesis by blast
      qed
      then have b4: "gets_p (last c) \<in> post" 
        by (metis (no_types, lifting) CollectD IntD1 a1 b0 cptn_not_empty cpts_of_p_def 
           diff_less gets_p_def last_conv_nth length_greater_0_conv subsetD zero_less_one)
      
      from b2 have b5: "c \<in> preserves_p"
        by (simp add: preserves_p_def getspc_p_def)

      with b3 b4 have "c \<in> commit_p (guar, post) \<inter> preserves_p"
        by (simp add: commit_p_def)
    }
    then show ?thesis by auto
  qed

  then show ?thesis 
    by (meson Anno_SIMP_Hoare_Plus.prog_validity_def subsetI)
qed


lemma RG_Sound_equiv: "\<Turnstile> P sat\<^sub>p [pre, rely, guar, post] \<longleftrightarrow> \<Turnstile>\<^sub>I Some P sat\<^sub>p [pre, rely, guar, post]"
  by (simp add: Anno_SIMP_Hoare_Plus.prog_validity_def Anno_SIMP_RG_Hoare.prog_validity_def)

theorem rgsound_p:
  "\<turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post] \<Longrightarrow> \<Turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post]"
  apply(erule rghoare_p.induct)
         apply (smt (verit) Basic_sound RG_Sound_equiv)
        apply (meson RG_Sound_equiv Seq_sound)
       apply (meson Cond_sound RG_Sound_equiv)
      apply (meson RG_Sound_equiv While_sound)
     apply (simp add: Anno_SIMP_Hoare_Plus.Await_sound)
    apply (smt (verit, ccfv_SIG) Nondt_sound RG_Sound_equiv)
   apply (simp add: Anno_SIMP_Hoare_Plus.Conseq_sound)
  by (simp add: None_sound)

end
