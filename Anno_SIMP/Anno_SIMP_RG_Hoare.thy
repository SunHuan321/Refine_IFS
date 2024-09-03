theory Anno_SIMP_RG_Hoare
  imports Anno_SIMP_Tran "../VHelper"
begin

definition stable :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool" where
  "stable \<equiv> \<lambda>f g. (\<forall>x y. x \<in> f \<longrightarrow> (x, y) \<in> g \<longrightarrow> y \<in> f)"

inductive rghoare_p :: "['s ann_prog, 's set, ('s \<times> 's) set, ('s \<times> 's) set, 's set] \<Rightarrow> bool"
    ("\<turnstile> _ sat\<^sub>p [_, _, _, _]" [60,0,0,0,0] 45)
where
  Basic: "\<lbrakk> pre \<subseteq> r; pre \<subseteq> {s. f s \<in> post}; {(s,t). s \<in> pre \<and> (t=f s)} \<subseteq> guar;
            stable pre rely; stable post rely\<rbrakk>
           \<Longrightarrow> \<turnstile> AnnBasic r f sat\<^sub>p [pre, rely, guar, post]"
| Seq: "\<lbrakk> \<turnstile> P sat\<^sub>p [pre, rely, guar, mid]; \<turnstile> Q sat\<^sub>p [mid, rely, guar, post] \<rbrakk>
           \<Longrightarrow> \<turnstile> AnnSeq P Q sat\<^sub>p [pre, rely, guar, post]"
| Cond: "\<lbrakk> pre \<subseteq> r;  stable pre rely; \<turnstile> P1 sat\<^sub>p [pre \<inter> b, rely, guar, post];
           \<turnstile> P2 sat\<^sub>p [pre \<inter> -b, rely, guar, post]; \<forall>s. (s,s)\<in>guar \<rbrakk>
          \<Longrightarrow> \<turnstile> AnnCond r b P1 P2 sat\<^sub>p [pre, rely, guar, post]"
| While: "\<lbrakk> pre \<subseteq> r; stable pre rely; (pre \<inter> -b) \<subseteq> post; stable post rely;
            \<turnstile> P sat\<^sub>p [pre \<inter> b, rely, guar, pre]; \<forall>s. (s,s)\<in>guar \<rbrakk>
          \<Longrightarrow> \<turnstile> AnnWhile r b P sat\<^sub>p [pre, rely, guar, post]"
| Await: "\<lbrakk>  pre \<subseteq> r; stable pre rely; stable post rely;
            \<forall>V. \<turnstile> P sat\<^sub>p [pre \<inter> b \<inter> {V}, {(s, t). s = t},
                UNIV, {s. (V, s) \<in> guar} \<inter> post] \<rbrakk>
           \<Longrightarrow> \<turnstile> AnnAwait r b P sat\<^sub>p [pre, rely, guar, post]"
| Nondt: "\<lbrakk>pre \<subseteq> r; stable pre rely;
           pre \<subseteq> {s. (\<forall>t. (s,t) \<in> f \<longrightarrow> t \<in> post) \<and> (\<exists>t. (s,t) \<in> f)}; 
            {(s,t). s \<in> pre \<and> (s,t)\<in>f} \<subseteq> guar;  stable post rely\<rbrakk>
           \<Longrightarrow> \<turnstile> AnnNondt r f sat\<^sub>p [pre, rely, guar, post]"
| Conseq: "\<lbrakk> pre \<subseteq> pre'; rely \<subseteq> rely'; guar' \<subseteq> guar; post' \<subseteq> post;
             \<turnstile> P sat\<^sub>p [pre', rely', guar', post'] \<rbrakk>
            \<Longrightarrow> \<turnstile> P sat\<^sub>p [pre, rely, guar, post]"

primrec ann_preserves_p :: "('s ann_prog) option \<Rightarrow> 's \<Rightarrow> bool"
  where "ann_preserves_p None s = True" |
        "ann_preserves_p (Some P) s = (s \<in> ann_pre P)"

definition assume_p :: "('s set \<times> ('s \<times> 's) set) \<Rightarrow> ('s confs) set" where
  "assume_p \<equiv> \<lambda>(pre, rely). {c. gets_p (c!0) \<in> pre \<and> (\<forall>i. Suc i<length c \<longrightarrow> 
               c!i -pe\<rightarrow> c!(Suc i) \<longrightarrow> (gets_p (c!i), gets_p (c!Suc i)) \<in> rely)}"

definition commit_p :: "(('s \<times> 's) set \<times> 's set) \<Rightarrow> ('s confs) set" where
  "commit_p \<equiv> \<lambda>(guar, post). {c. (\<forall>i. Suc i<length c \<longrightarrow> 
               c!i -c\<rightarrow> c!(Suc i) \<longrightarrow> (gets_p (c!i), gets_p (c!Suc i)) \<in> guar) \<and> 
               (getspc_p (last c) = None \<longrightarrow> gets_p (last c) \<in> post)}"

definition preserves_p :: "('s confs) set" where
  "preserves_p \<equiv> {c. (\<forall>i. i < length c \<longrightarrow> ann_preserves_p (getspc_p (c!i)) (gets_p (c!i)))}"

definition prog_validity :: "'s ann_prog \<Rightarrow> 's set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> 's set \<Rightarrow> bool" 
                 ("\<Turnstile> _ sat\<^sub>p [_, _, _, _]" [60,0,0,0,0] 45) where
  "\<Turnstile> P sat\<^sub>p [pre, rely, guar, post] \<equiv> 
   \<forall>s. cpts_of_p (Some P) s \<inter> assume_p(pre, rely) \<subseteq> commit_p(guar, post) \<inter> preserves_p"


subsection \<open>Soundness of Programs\<close>

subsection \<open>Some previous lemmas\<close>

lemma tl_of_assum_in_assum:
  "(P, s) # (P, t) # xs \<in> assume_p (pre, rely) \<Longrightarrow> stable pre rely
  \<Longrightarrow> (P, t) # xs \<in> assume_p (pre, rely)"
apply(simp add:assume_p_def)
apply clarify
apply(rule conjI)
 apply(erule_tac x=0 in allE)
 apply(simp (no_asm_use)only:stable_def)
 apply(erule allE,erule allE,erule impE,assumption,erule mp)
 apply(simp add:EnvP)
apply(simp add:getspc_p_def gets_p_def)
apply clarify
apply (fastforce)
done

lemma etran_in_comm:
  "(P, t) # xs \<in> commit_p(guar, post) \<Longrightarrow> (P, s) # (P, t) # xs \<in> commit_p(guar, post)"
apply(simp add:commit_p_def)
apply(simp add:getspc_p_def gets_p_def)
apply clarify
apply(case_tac i,fastforce+)
done

lemma ctran_in_comm:
  "\<lbrakk>(t, s) \<in> guar; t \<in> ann_pre_p P ; (Q, s) # xs \<in> commit_p(guar, post)\<rbrakk>
  \<Longrightarrow> (P, t) # (Q, s) # xs \<in> commit_p(guar, post)"
  apply(simp add:commit_p_def)
  apply(simp add:getspc_p_def gets_p_def)
  apply clarify
  apply(case_tac i, simp)
  by auto

lemma takecptn_is_cptn [rule_format, elim!]:
  "\<forall>j. c \<in> cpts_p \<longrightarrow> take (Suc j) c \<in> cpts_p"
apply(induct "c")
 apply(force elim: cpts_p.cases)
apply clarify
apply(case_tac j)
 apply simp
 apply(rule CptsPOne)
apply simp
apply(force intro:cpts_p.intros elim:cpts_p.cases)
done

lemma dropcptn_is_cptn [rule_format,elim!]:
  "\<forall>j<length c. c \<in> cpts_p \<longrightarrow> drop j c \<in> cpts_p"
apply(induct "c")
 apply(force elim: cpts_p.cases)
apply clarify
apply(case_tac j,simp+)
apply(erule cpts_p.cases)
  apply simp
 apply force
apply force
done

lemma segcptn_is_cptn: "\<lbrakk>l \<in> cpts_p; n < length l; m < n\<rbrakk> 
                    \<Longrightarrow> take (n - m + 1) (drop m l) \<in> cpts_p"
  by (metis Suc_eq_plus1 dropcptn_is_cptn dual_order.strict_trans takecptn_is_cptn)

lemma tl_of_cptn_is_cptn: "\<lbrakk>x # xs \<in> cpts_p; xs \<noteq> []\<rbrakk> \<Longrightarrow> xs  \<in> cpts_p"
apply(subgoal_tac "1 < length (x # xs)")
 apply(drule dropcptn_is_cptn,simp+)
done

lemma notran_p_confeq0: "\<lbrakk>l \<in> cpts_p; Suc 0 < length l; \<not> (l ! 0 -c\<rightarrow> l ! 1)\<rbrakk>
                      \<Longrightarrow> getspc_p (l ! 0) = getspc_p (l ! 1)"
  apply(simp)
  apply(rule cpts_p.cases)
  apply(simp)+
  apply(simp add:getspc_p_def)+
  done

lemma petran_eqconf: "(p1, s1) -pe\<rightarrow> (p2, s2) \<Longrightarrow> p1 = p2"
  apply(rule petran.cases)
  apply(simp)+
  done

lemma notran_p_confeqi: "\<lbrakk>l \<in> cpts_p; Suc i < length l; \<not> (l ! i -c\<rightarrow> l ! Suc i)\<rbrakk>
                      \<Longrightarrow> getspc_p (l ! i) = getspc_p (l ! (Suc i))"
  proof -
    assume p0: "l \<in> cpts_p" and
           p1: "Suc i < length l" and
           p2: "\<not> (l ! i -c\<rightarrow> l ! Suc i)"
    have "\<forall>l i. l \<in> cpts_p \<and>  Suc i < length l \<and> \<not> (l ! i -c\<rightarrow> l ! Suc i)
                \<longrightarrow> getspc_p (l ! i) = getspc_p (l ! (Suc i))"
      proof -
      {
        fix l i
        assume a0: "l \<in> cpts_p \<and> Suc i < length l \<and> \<not> (l ! i -c\<rightarrow> l ! Suc i)"
        then have "getspc_p (l ! i) = getspc_p (l ! (Suc i))"
          proof(induct i)
            case 0 show ?case by (simp add: "0.prems" notran_p_confeq0) 
          next
            case (Suc j)
            let ?subel = "drop (Suc j) l"
            assume b0: "l \<in> cpts_p \<and> Suc (Suc j) < length l \<and> \<not> (l ! Suc j -c\<rightarrow> l ! Suc (Suc j))"            
            then have b1: "?subel \<in> cpts_p" by (simp add: Suc_lessD b0 dropcptn_is_cptn) 
            from b0 have b2: "Suc 0 < length ?subel" by auto 
            from b0 have b3: "\<not> (?subel ! 0 -c\<rightarrow> ?subel ! 1)" by auto
            with b1 b2 have b3: "getspc_p (?subel ! 0) = getspc_p (?subel ! 1)"
              using notran_p_confeq0 by blast
            then show ?case
              by (metis Cons_nth_drop_Suc One_nat_def Suc_lessD b0 nth_Cons_0 nth_Cons_Suc) 
          qed
      }
      then show ?thesis by auto
    qed
    with p0 p1 p2 show ?thesis by auto
  qed

lemma notran_p_confeqi1: "\<lbrakk>l \<in> cpts_p; \<forall>i. Suc i < length l \<longrightarrow> \<not> (l ! i -c\<rightarrow> l ! Suc i); j < length l\<rbrakk>
                      \<Longrightarrow> getspc_p (l ! 0) = getspc_p (l ! j)"
  apply (induct j, simp)
  apply clarsimp
  apply (erule_tac x = j in allE)
  using notran_p_confeqi by blast

lemma notran_p_seg_aux : "\<lbrakk>take (n - m + 1) (drop m l) \<in> cpts_p; m < n; n < length l; \<forall>i. i \<ge> m \<and> i < n \<longrightarrow> 
        \<not> (l ! i -c\<rightarrow> l ! Suc i)\<rbrakk> \<Longrightarrow>  getspc_p (l ! m) = getspc_p (l ! n)"
  apply (drule_tac j = "n - m" in notran_p_confeqi1, simp_all)
  done

lemma notran_seg_take: "\<lbrakk>l \<in> cpts_p; m < n; n < length l; \<forall>i. i \<ge> m \<and> i < n \<longrightarrow> 
                          \<not> (l ! i -c\<rightarrow> l ! Suc i)\<rbrakk> \<Longrightarrow> getspc_p (l ! m) = getspc_p (l ! n)"
  apply (rule notran_p_seg_aux, simp_all)
  by (metis Suc_eq_plus1 segcptn_is_cptn)
 
lemma not_ctran_None [rule_format]:
  "\<forall>s. (None, s)#xs \<in> cpts_p \<longrightarrow> (\<forall>i<length xs. ((None, s)#xs)!i -pe\<rightarrow> xs!i)"
apply(induct xs,simp+)
apply clarify
apply(erule cpts_p.cases,simp)
 apply simp
 apply(case_tac i,simp)
  apply(rule EnvP)
 apply simp
apply(force elim:ptran.cases)
  done

lemma cptn_not_empty [simp]:"[] \<notin> cpts_p"
apply(force elim:cpts_p.cases)
done

lemma etran_or_ctran [rule_format]:
  "\<forall>m i. x\<in>cpts_p \<longrightarrow> m \<le> length x
   \<longrightarrow> (\<forall>i. Suc i < m \<longrightarrow> \<not> x!i -c\<rightarrow> x!Suc i) \<longrightarrow> Suc i < m
   \<longrightarrow> x!i -pe\<rightarrow> x!Suc i"
apply(induct x,simp)
apply clarify
apply(erule cpts_p.cases,simp)
 apply(case_tac i,simp)
  apply(rule EnvP)
 apply simp
 apply(erule_tac x="m - 1" in allE)
 apply(case_tac m,simp,simp)
 apply(subgoal_tac "(\<forall>i. Suc i < nata \<longrightarrow> (((a, t) # xs) ! i, xs ! i) \<notin> ptran)")
  apply force
 apply clarify
 apply(erule_tac x="Suc ia" in allE,simp)
apply(erule_tac x="0" and P="\<lambda>j. H j \<longrightarrow> (J j) \<notin> ptran" for H J in allE,simp)
done

lemma etran_or_ctran2 [rule_format]:
  "\<forall>i. Suc i<length x \<longrightarrow> x\<in>cpts_p \<longrightarrow> (x!i -c\<rightarrow> x!Suc i \<longrightarrow> \<not> x!i -pe\<rightarrow> x!Suc i)
  \<or> (x!i -pe\<rightarrow> x!Suc i \<longrightarrow> \<not> x!i -c\<rightarrow> x!Suc i)"
apply(induct x)
 apply simp
apply clarify
apply(erule cpts_p.cases,simp)
 apply(case_tac i,simp+)
apply(case_tac i,simp)
 apply(force elim:petran.cases)
apply simp
done

lemma etran_or_ctran2_disjI1:
  "\<lbrakk> x\<in>cpts_p; Suc i<length x; x!i -c\<rightarrow> x!Suc i\<rbrakk> \<Longrightarrow> \<not> x!i -pe\<rightarrow> x!Suc i"
by(drule etran_or_ctran2,simp_all)

lemma etran_or_ctran2_disjI2:
  "\<lbrakk> x\<in>cpts_p; Suc i<length x; x!i -pe\<rightarrow> x!Suc i\<rbrakk> \<Longrightarrow> \<not> x!i -c\<rightarrow> x!Suc i"
by(drule etran_or_ctran2,simp_all)


lemma not_ctran_None2 [rule_format]:
  "\<lbrakk> (None, s) # xs \<in>cpts_p; i<length xs\<rbrakk> \<Longrightarrow> \<not> ((None, s) # xs) ! i -c\<rightarrow> xs ! i"
apply(frule not_ctran_None,simp)
apply(case_tac i,simp)
 apply(force elim:petranE)
apply simp
apply(rule etran_or_ctran2_disjI2,simp_all)
apply(force intro:tl_of_cptn_is_cptn)
done

lemma not_ctran_None3 [rule_format]:
  "\<lbrakk> (None, s) # xs \<in>cpts_p; i<length xs\<rbrakk> \<Longrightarrow> getspc_p (xs ! i) = None "
  apply (induct i, simp)
   apply (drule_tac i = 0 in not_ctran_None, simp)
   apply (metis fstI getspc_p_def nth_Cons_0 petranE)
  apply (subgoal_tac "getspc_p (xs ! i) = None")
   apply (drule_tac i = "Suc i" in not_ctran_None, simp)
   apply (metis fstI getspc_p_def nth_Cons_Suc petranE)
  using Suc_lessD by blast

lemma not_ctran_None3' [rule_format]:
  "\<lbrakk>xs \<in>cpts_p; i<length xs; getspc_p (xs ! 0) = None\<rbrakk> \<Longrightarrow> getspc_p (xs ! i) = None"
  apply (case_tac xs, simp)
  apply (case_tac a)
  apply (case_tac aa)
   apply (simp add: cpts_p.CptsPEnv not_ctran_None3)
  by (simp add: getspc_p_def)

lemma not_ctran_Finish [rule_format]:
  "\<lbrakk>xs \<in> cpts_p; i<length xs; getspc_p (xs ! i) = None; j \<ge> i; j < length xs\<rbrakk> 
    \<Longrightarrow> getspc_p (xs ! j) = None"
proof-
  assume a1: "xs \<in> cpts_p"
    and  a2: "i < length xs"
    and  a3: "getspc_p (xs ! i) = None"
    and  a4: "j \<ge> i"
    and  a5: "j < length xs"
  from a1 a2 have "drop i xs \<in> cpts_p" by (simp add: dropcptn_is_cptn)
  with a2 a3 a4 a5 show ?thesis
    by (drule_tac xs = "drop i xs" and i = "j - i" in not_ctran_None3', simp_all)
qed

lemma Ex_first_occurrence [rule_format]: "P (n::nat) \<longrightarrow> (\<exists>m. P m \<and> (\<forall>i<m. \<not> P i))"
apply(rule nat_less_induct)
apply clarify
apply(case_tac "\<forall>m. m<n \<longrightarrow> \<not> P m")
apply auto
done

lemma stability [rule_format]:
  "\<forall>j k. x \<in> cpts_p \<longrightarrow> stable p rely \<longrightarrow> j\<le>k \<longrightarrow> k<length x \<longrightarrow> snd(x!j)\<in>p  \<longrightarrow>
  (\<forall>i. (Suc i)<length x \<longrightarrow>
          (x!i -pe\<rightarrow> x!(Suc i)) \<longrightarrow> (snd(x!i), snd(x!(Suc i))) \<in> rely) \<longrightarrow>
  (\<forall>i. j\<le>i \<and> i<k \<longrightarrow> x!i -pe\<rightarrow> x!Suc i) \<longrightarrow> snd(x!k)\<in>p \<and> fst(x!j)=fst(x!k)"
apply(induct x)
 apply clarify
 apply(force elim:cpts_p.cases)
apply clarify
apply(erule cpts_p.cases,simp)
 apply simp
 apply(case_tac k,simp,simp)
 apply(case_tac j,simp)
  apply(erule_tac x=0 in allE)
  apply(erule_tac x="nat" and P="\<lambda>j. (0\<le>j) \<longrightarrow> (J j)" for J in allE,simp)
  apply(subgoal_tac "t\<in>p")
   apply(subgoal_tac "(\<forall>i. i < length xs \<longrightarrow> ((a, t) # xs) ! i -pe\<rightarrow> xs ! i \<longrightarrow> (snd (((a, t) # xs) ! i), snd (xs ! i)) \<in> rely)")
    apply clarify
    apply(erule_tac x="Suc i" and P="\<lambda>j. (H j) \<longrightarrow> (J j)\<in>petran" for H J in allE,simp)
   apply clarify
   apply(erule_tac x="Suc i" and P="\<lambda>j. (H j) \<longrightarrow> (J j) \<longrightarrow> (T j)\<in>rely" for H J T in allE,simp)
  apply(erule_tac x=0 and P="\<lambda>j. (H j) \<longrightarrow> (J j)\<in>petran \<longrightarrow> T j" for H J T in allE,simp)
  apply(simp(no_asm_use) only:stable_def)
  apply(erule_tac x=b in allE)
  apply(erule_tac x=t in allE)
  apply simp
  apply(erule mp)
  apply(erule mp)
  apply(rule EnvP)
 apply simp
 apply(erule_tac x="nata" in allE)
 apply(erule_tac x="nat" and P="\<lambda>j. (s\<le>j) \<longrightarrow> (J j)" for s J in allE,simp)
 apply(subgoal_tac "(\<forall>i. i < length xs \<longrightarrow> ((a, t) # xs) ! i -pe\<rightarrow> xs ! i \<longrightarrow> (snd (((a, t) # xs) ! i), snd (xs ! i)) \<in> rely)")
  apply clarify
  apply(erule_tac x="Suc i" and P="\<lambda>j. (H j) \<longrightarrow> (J j)\<in>petran" for H J in allE,simp)
 apply clarify
 apply(erule_tac x="Suc i" and P="\<lambda>j. (H j) \<longrightarrow> (J j) \<longrightarrow> (T j)\<in>rely" for H J T in allE,simp)
apply(case_tac k,simp,simp)
apply(case_tac j)
 apply(erule_tac x=0 and P="\<lambda>j. (H j) \<longrightarrow> (J j)\<in>petran" for H J in allE,simp)
 apply(erule petran.cases,simp)
apply(erule_tac x="nata" in allE)
apply(erule_tac x="nat" and P="\<lambda>j. (s\<le>j) \<longrightarrow> (J j)" for s J in allE,simp)
apply(subgoal_tac "(\<forall>i. i < length xs \<longrightarrow> ((Q, t) # xs) ! i -pe\<rightarrow> xs ! i \<longrightarrow> (snd (((Q, t) # xs) ! i), snd (xs ! i)) \<in> rely)")
 apply clarify
 apply(erule_tac x="Suc i" and P="\<lambda>j. (H j) \<longrightarrow> (J j)\<in>petran" for H J in allE,simp)
apply clarify
apply(erule_tac x="Suc i" and P="\<lambda>j. (H j) \<longrightarrow> (J j) \<longrightarrow> (T j)\<in>rely" for H J T in allE,simp)
  done

subsubsection\<open>Soundness of the Rule of Consequence\<close>

lemma Conseq_sound:
  "\<lbrakk>pre \<subseteq> pre'; rely \<subseteq> rely'; guar' \<subseteq> guar; post' \<subseteq> post;
  \<Turnstile> P sat\<^sub>p [pre', rely', guar', post']\<rbrakk>
  \<Longrightarrow> \<Turnstile> P sat\<^sub>p [pre, rely, guar, post]"
  apply (simp add: prog_validity_def)
  apply clarify
  apply(erule_tac x=s in allE)
  apply (rule conjI)
   apply clarify
   apply (simp add: assume_p_def commit_p_def)
   apply(drule_tac c=x in subsetD)
    apply force
   apply force
  apply clarify
  apply (simp add: assume_p_def commit_p_def)
  apply(drule_tac c=x in subsetD)
   apply force
  apply force
  done

subsubsection \<open>Soundness of the Basic rule\<close>

lemma unique_ctran_Basic [rule_format]:
  "\<forall>s i. x \<in> cpts_p \<longrightarrow> x ! 0 = (Some (AnnBasic r f), s) \<longrightarrow>
  Suc i<length x \<longrightarrow> x!i -c\<rightarrow> x!Suc i \<longrightarrow>
  (\<forall>j. Suc j<length x \<longrightarrow> i\<noteq>j \<longrightarrow> x!j -pe\<rightarrow> x!Suc j)"
  apply(induct x,simp)
  apply simp
  apply clarify
  apply(erule cpts_p.cases,simp)
   apply(case_tac i,simp+)
   apply clarify
   apply(case_tac j,simp)
    apply(rule EnvP)
   apply simp
  apply clarify
  apply simp
  apply(case_tac i)
   apply(case_tac j,simp,simp)
   apply(erule ptran.cases,simp_all)
 apply(force elim: not_ctran_None)
apply(ind_cases "((Some (AnnBasic r f), sa), Q, t) \<in> ptran" for sa Q t)
apply simp
apply(drule_tac i=nat in not_ctran_None,simp)
apply(erule petranE,simp)
  done

lemma exists_ctran_Basic_None [rule_format]:
  "\<forall>s i. x \<in> cpts_p \<longrightarrow> x ! 0 = (Some (AnnBasic r f), s)
  \<longrightarrow> i<length x \<longrightarrow> fst(x!i)=None \<longrightarrow> (\<exists>j<i. x!j -c\<rightarrow> x!Suc j)"
apply(induct x,simp)
apply simp
apply clarify
apply(erule cpts_p.cases,simp)
 apply(case_tac i,simp,simp)
 apply(erule_tac x=nat in allE,simp)
 apply clarify
 apply(rule_tac x="Suc j" in exI,simp,simp)
apply clarify
apply(case_tac i,simp,simp)
apply(rule_tac x=0 in exI,simp)
  done

lemma Basic_sound:
  " \<lbrakk> pre \<subseteq> r; pre \<subseteq> {s. f s \<in> post}; {(s,t). s \<in> pre \<and> (t=f s)} \<subseteq> guar;
            stable pre rely; stable post rely\<rbrakk>
  \<Longrightarrow> \<Turnstile> AnnBasic r f sat\<^sub>p [pre, rely, guar, post]"
  apply(unfold prog_validity_def)
  apply clarify
  apply (rule IntI)
   apply(simp add:commit_p_def getspc_p_def gets_p_def)
   apply(rule conjI, clarify)
    apply(simp add:cpts_of_p_def assume_p_def gets_p_def)
    apply clarify
    apply(frule_tac j=0 and k=i and p= pre in stability)
          apply simp_all
      apply(erule_tac x=ia in allE,simp)
     apply(erule_tac i=i and f=f in unique_ctran_Basic,simp_all)
    apply(erule subsetD,simp)
    apply(case_tac "x!i")
    apply clarify
    apply(drule_tac s="Some (AnnBasic r f)" in sym,simp)
    apply(thin_tac "\<forall>j. H j" for H)
    apply(force elim:ptran.cases)
   apply clarify
   apply(simp add:cpts_of_p_def)
   apply clarify
   apply(frule_tac i="length x - 1" and f=f in exists_ctran_Basic_None,simp+)
     apply(case_tac x,simp+)
    apply(rule last_fst_esp,simp add:last_length)
    apply (case_tac x,simp+)
   apply(simp add:assume_p_def gets_p_def)
   apply clarify
   apply(frule_tac j=0 and k="j" and p= pre in stability)
         apply simp_all
     apply(erule_tac x=i in allE,simp)
    apply(erule_tac i=j and f=f in unique_ctran_Basic,simp_all)
   apply(case_tac "x!j")
   apply clarify
   apply simp
   apply(drule_tac s="Some (AnnBasic r f)" in sym,simp)
   apply(case_tac "x!Suc j",simp)
   apply(rule ptran.cases,simp)
           apply(simp_all)
   apply(drule_tac c= b in subsetD,simp)
   apply clarify
   apply(frule_tac j="Suc j" and k="length x - 1" and p= post in stability,simp_all)
      apply blast
     apply blast
    apply(erule_tac x=i in allE)
    apply(erule_tac i=j and f=f in unique_ctran_Basic,simp_all)
     apply arith+
   apply(case_tac x)
    apply(simp add:last_length)+
  apply (case_tac "\<exists>i. Suc i < length x \<and> (x!i) -c\<rightarrow> (x!(Suc i))")
   apply (simp add: preserves_p_def cpts_of_p_def assume_p_def gets_p_def)
   apply clarify
   apply (case_tac "ia \<le> i")
    apply(frule_tac j=0 and k=ia and p= pre in stability, simp_all)
      apply blast
  using unique_ctran_Basic apply fastforce
    apply (case_tac "x!ia")
    apply (simp add: getspc_p_def)
    apply blast
   apply(frule_tac j=0 and k=i and p= pre in stability, simp_all)
     apply blast
    apply(erule_tac i=i and f=f in unique_ctran_Basic,simp_all)
   apply (case_tac "x ! Suc i")
   apply (erule ptran.cases, simp_all)
   apply (drule_tac i = "Suc i" and j = ia in not_ctran_Finish, simp_all)
   apply (simp add: getspc_p_def)
  apply (simp add: preserves_p_def cpts_of_p_def assume_p_def gets_p_def)
  apply clarify 
  apply(frule_tac j=0 and k=i and p= pre in stability, simp_all)
    apply blast
   apply (drule_tac m = "length x" and i = "ia" in etran_or_ctran, simp_all)
  apply (case_tac "x!i")
  apply (simp add: getspc_p_def)
  by blast

subsubsection\<open>Soundness of the Await rule\<close>

lemma unique_ctran_Await [rule_format]:
  "\<forall>s i. x \<in> cpts_p \<longrightarrow> x ! 0 = (Some (AnnAwait r b c), s) \<longrightarrow>
  Suc i<length x \<longrightarrow> x!i -c\<rightarrow> x!Suc i \<longrightarrow>
  (\<forall>j. Suc j<length x \<longrightarrow> i\<noteq>j \<longrightarrow> x!j -pe\<rightarrow> x!Suc j)"
apply(induct x,simp+)
apply clarify
apply(erule cpts_p.cases,simp)
 apply(case_tac i,simp+)
 apply clarify
 apply(case_tac j,simp)
  apply(rule EnvP)
 apply simp
apply clarify
apply simp
apply(case_tac i)
 apply(case_tac j,simp,simp)
 apply(erule ptran.cases,simp_all)
 apply(force elim: not_ctran_None)
apply(ind_cases "((Some (AnnAwait r b c), sa), Q, t) \<in> ptran" for sa Q t,simp)
apply(drule_tac i=nat in not_ctran_None,simp)
apply(erule petranE,simp)
done

lemma exists_ctran_Await_None [rule_format]:
  "\<forall>s i.  x \<in> cpts_p \<longrightarrow> x ! 0 = (Some (AnnAwait r b c), s)
  \<longrightarrow> i<length x \<longrightarrow> fst(x!i)=None \<longrightarrow> (\<exists>j<i. x!j -c\<rightarrow> x!Suc j)"
apply(induct x,simp+)
apply clarify
apply(erule cpts_p.cases,simp)
 apply(case_tac i,simp+)
 apply(erule_tac x=nat in allE,simp)
 apply clarify
 apply(rule_tac x="Suc j" in exI,simp,simp)
apply clarify
apply(case_tac i,simp,simp)
apply(rule_tac x=0 in exI,simp)
done

lemma Star_imp_cptn:
  "(P, s) -c*\<rightarrow> (R, t) \<Longrightarrow> \<exists>l \<in> cpts_of_p P s. (last l)=(R, t)
  \<and> (\<forall>i. Suc i<length l \<longrightarrow> l!i -c\<rightarrow> l!Suc i)"
apply (erule converse_rtrancl_induct2)
 apply(rule_tac x="[(R,t)]" in bexI)
  apply simp
 apply(simp add:cpts_of_p_def)
 apply(rule CptsPOne)
apply clarify
apply(rule_tac x="(a, b)#l" in bexI)
 apply (rule conjI)
  apply(case_tac l,simp add:cpts_of_p_def)
  apply(simp add:last_length)
 apply clarify
apply(case_tac i,simp)
apply(simp add:cpts_of_p_def)
apply force
apply(simp add:cpts_of_p_def)
 apply(case_tac l)
 apply(force elim:cpts_p.cases)
apply simp
apply(erule CptsPComp)
apply clarify
done

lemma Await_sound:
  "\<lbrakk>pre \<subseteq> r; stable pre rely; stable post rely;
   \<forall>V. \<turnstile> P sat\<^sub>p [pre \<inter> b \<inter> {s. s = V}, {(s, t). s = t},
                 UNIV, {s. (V, s) \<in> guar} \<inter> post] \<and>
   \<Turnstile> P sat\<^sub>p [pre \<inter> b \<inter> {s. s = V}, {(s, t). s = t},
                 UNIV, {s. (V, s) \<in> guar} \<inter> post]\<rbrakk>
   \<Longrightarrow> \<Turnstile> AnnAwait r b P sat\<^sub>p [pre, rely, guar, post]"
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
     apply arith+
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


lemma Conseq_sound_r:
  "\<lbrakk> pre \<subseteq> r; stable r rely; \<Turnstile> P sat\<^sub>p [r, rely, guar, post]\<rbrakk>
  \<Longrightarrow>  \<Turnstile> P sat\<^sub>p [pre, rely, guar, post]"
  by (rule Conseq_sound, simp_all)

subsubsection\<open>Soundness of the Conditional rule\<close>


lemma Cond_sound:
  "\<lbrakk> pre \<subseteq> r;  stable pre rely; \<Turnstile> P1 sat\<^sub>p [pre \<inter> b, rely, guar, post];
     \<Turnstile> P2 sat\<^sub>p [pre \<inter> -b, rely, guar, post]; \<forall>s. (s,s)\<in>guar \<rbrakk>
    \<Longrightarrow> \<Turnstile> AnnCond r b P1 P2 sat\<^sub>p [pre, rely, guar, post]"
  apply(unfold prog_validity_def)
  apply clarify
  apply (rule IntI)
   apply(simp add:cpts_of_p_def commit_p_def)
   apply(simp add:getspc_p_def gets_p_def)
   apply(case_tac "\<exists>i. Suc i<length x \<and> x!i -c\<rightarrow> x!Suc i")
    prefer 2
    apply simp
    apply clarify
   apply(frule_tac j="0" and k="length x - 1" and p= pre in stability,simp+)
       apply(case_tac x,simp+)
      apply(simp add:assume_p_def gets_p_def)
     apply(simp add:assume_p_def gets_p_def)
    apply(erule_tac m="length x" in etran_or_ctran,simp+)
    apply(case_tac x, (simp add:last_length)+)
   apply(erule exE)
   apply(drule_tac n=i and P="\<lambda>i. H i \<and> (J i, I i) \<in> ptran" for H J I in Ex_first_occurrence)
  apply clarify
  apply (simp add:assume_p_def gets_p_def)
  apply(frule_tac j=0 and k="m" and p= pre in stability,simp+)
   apply(erule_tac m="Suc m" in etran_or_ctran,simp+)
  apply(erule ptran.cases,simp_all)
    apply(erule_tac x="sa" in allE)
    apply clarify
    apply(drule_tac c="drop (Suc m) x" in subsetD)
    apply simp
    apply clarify
   apply simp
   apply clarify
    apply(case_tac "i\<le>m")
     apply(drule le_imp_less_or_eq)
     apply(erule_tac x=i in allE, erule impE, assumption)
     apply (metis (no_types, lifting) le_neq_implies_less snd_conv)
    apply simp
    apply(erule_tac x="i - (Suc m)" and P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> (I j)\<in>guar" for H J I in allE)
    apply(subgoal_tac "(Suc m)+(i - Suc m) \<le> length x")
     apply(subgoal_tac "(Suc m)+Suc (i - Suc m) \<le> length x")
      apply(rotate_tac -2)
      apply simp
     apply arith
    apply arith
   apply(case_tac "length (drop (Suc m) x)",simp)
   apply(erule_tac x="sa" in allE)
   back
   apply clarify
   apply(drule_tac c="drop (Suc m) x" in subsetD,simp)
    apply clarsimp
   apply clarsimp
   apply(case_tac "i\<le>m")
    apply(drule le_imp_less_or_eq)
    apply(erule disjE)
     apply(erule_tac x=i in allE, erule impE, assumption)
     apply (metis (no_types, lifting) order_le_less snd_eqD)
    apply (metis (no_types, lifting) le_neq_implies_less snd_conv)
   apply(erule_tac x="i - (Suc m)" and P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> (I j)\<in>guar" for H J I in allE)
   apply(subgoal_tac "(Suc m)+(i - Suc m) \<le> length x")
    apply(subgoal_tac "(Suc m)+Suc (i - Suc m) \<le> length x")
     apply(rotate_tac -2)
     apply simp
    apply arith
   apply arith
  apply(simp add:cpts_of_p_def preserves_p_def getspc_p_def gets_p_def)
  apply(case_tac "\<exists>i. Suc i<length x \<and> x!i -c\<rightarrow> x!Suc i")
   prefer 2
  apply clarsimp
   apply(frule_tac j="0" and k="i" and p= pre in stability,simp+)
      apply(simp add:assume_p_def gets_p_def)
     apply(simp add:assume_p_def gets_p_def)
    apply(erule_tac m="length x" in etran_or_ctran,simp+)
   apply (case_tac "x!i")
   apply (simp add: getspc_p_def)
   apply blast
  apply(erule exE, simp add: assume_p_def gets_p_def)
  apply(drule_tac n=i and P="\<lambda>i. H i \<and> (J i, I i) \<in> ptran" for H J I in Ex_first_occurrence)
  apply clarify
  apply (case_tac " ia < m")
   apply(frule_tac j="0" and k= "ia" and p= pre in stability,simp+)
    apply (drule_tac m = "m" and i = "ib" in etran_or_ctran, simp_all)
   apply (case_tac "x!ia")
   apply (simp add: gets_p_def)
   apply blast
  apply(frule_tac j="0" and k= "m" and p= pre in stability,simp+)
   apply(erule_tac m="Suc m" in etran_or_ctran,simp+)
  apply (case_tac "ia = m")
   apply (case_tac "x!m")
   apply (simp add: gets_p_def, clarsimp)
   apply blast
  apply(erule ptran.cases,simp_all)
   apply (erule_tac x = sa in allE, clarify)
   apply(drule_tac c="drop (Suc m) x" in subsetD)
    back
    apply clarsimp
    apply (simp add: dropcptn_is_cptn)
   apply clarsimp
   apply (erule_tac x = "ia - Suc m" in allE)
   back
   back
   apply (erule impE, simp, simp)
  apply (erule_tac x = sa in allE)
  back
  apply auto[1]
  apply(drule_tac c="drop (Suc m) x" in subsetD)
   back
   apply clarsimp
   apply (simp add: dropcptn_is_cptn)
  apply clarsimp
  apply (erule_tac x = "ia - Suc m" in allE)
  back
  back
  apply (erule impE, simp, simp)
  done

subsubsection\<open>Soundness of the Sequential rule\<close>

inductive_cases Seq_cases [elim!]: "(Some (Seq P Q), s) -c\<rightarrow> t"

lemma last_lift_not_None: "fst ((lift Q) ((x#xs)!(length xs))) \<noteq> None"
apply(subgoal_tac "length xs<length (x # xs)")
 apply(drule_tac Q=Q in  lift_nth)
 apply(erule ssubst)
 apply (simp add:lift_def)
 apply(case_tac "(x # xs) ! length xs",simp)
apply simp
  done

lemma Seq_sound1 [rule_format]:
  "x\<in> cpt_p_mod \<Longrightarrow> \<forall>s P. x !0=(Some (AnnSeq P Q), s) \<longrightarrow>
  (\<forall>i<length x. fst(x!i)\<noteq>Some Q) \<longrightarrow>
  (\<exists>xs\<in> cpts_of_p (Some P) s. x=map (lift Q) xs)"
apply(erule cpt_p_mod.induct)
apply(unfold cpts_of_p_def)
apply safe
apply simp_all
    apply(simp add:lift_def)
    apply(rule_tac x="[(Some Pa, s)]" in exI,simp add:CptsPOne)
   apply(subgoal_tac "(\<forall>i < Suc (length xs). fst (((Some (AnnSeq Pa Q), t) # xs) ! i) \<noteq> Some Q)")
    apply clarify
    apply(rule_tac x="(Some Pa, s) #(Some Pa, t) # zs" in exI,simp)
    apply(rule conjI,erule CptsPEnv)
    apply(simp (no_asm_use) add:lift_def)
   apply clarify
   apply(erule_tac x="Suc i" in allE, simp)
 apply(rule_tac x="(Some P0, s) # xs" in exI, simp add:cpts_iff_cpt_p_mod lift_def)
apply(erule_tac x="length xs" in allE, simp)
apply(simp only:Cons_lift_append)
apply(subgoal_tac "length xs < length ((Some P0, s) # xs)")
 apply(simp only :nth_append length_map last_length nth_map)
 apply(case_tac "last((Some P0, s) # xs)")
 apply(simp add:lift_def)
  apply simp
  done

lemma Seq_sound2 [rule_format]:
  "x \<in> cpts_p \<Longrightarrow> \<forall>s P i. x!0=(Some (AnnSeq P Q), s) \<longrightarrow> i<length x
  \<longrightarrow> fst(x!i)=Some Q \<longrightarrow>
  (\<forall>j<i. fst(x!j)\<noteq>(Some Q)) \<longrightarrow>
  (\<exists>xs ys. xs \<in> cpts_of_p (Some P) s \<and> length xs=Suc i
   \<and> ys \<in> cpts_of_p (Some Q) (snd(xs !i)) \<and> x=(map (lift Q) xs)@tl ys)"
apply(erule cpts_p.induct)
apply(unfold cpts_of_p_def)
apply safe
apply simp_all
 apply(case_tac i,simp+)
 apply(erule allE,erule impE,assumption,simp)
 apply clarify
 apply(subgoal_tac "(\<forall>j < nat. fst (((Some (AnnSeq Pa Q), t) # xs) ! j) \<noteq> Some Q)",clarify)
  prefer 2
  apply force
 apply(case_tac xsa,simp,simp)
 apply(rename_tac list)
 apply(rule_tac x="(Some Pa, s) #(Some Pa, t) # list" in exI,simp)
 apply(rule conjI,erule CptsPEnv)
 apply(simp (no_asm_use) add:lift_def)
 apply(rule_tac x=ys in exI,simp)
apply(ind_cases "((Some (AnnSeq Pa Q), sa), t) \<in> ptran" for Pa sa t)
 apply simp
 apply(rule_tac x="(Some Pa, s)#[(None, t)]" in exI,simp)
 apply(rule conjI)
  apply(drule_tac xs="[]" in CptsPComp,force simp add:CptsPOne,simp)
 apply(case_tac i, simp+)
 apply(case_tac nat,simp+)
 apply(rule_tac x="(Some Q,t)#xs" in exI,simp add:lift_def)
   apply(case_tac nat,simp+)
  using nth_Cons_Suc apply auto[1]
apply(case_tac i, simp+)
apply(case_tac nat,simp+)
apply(erule_tac x="Suc nata" in allE,simp)
apply clarify
apply(subgoal_tac "(\<forall>j<Suc nata. fst (((Some (AnnSeq P2 Q), t) # xs) ! j) \<noteq> Some Q)",clarify)
 prefer 2
   apply clarify
  apply (metis (full_types) Suc_less_eq nth_Cons_Suc)
apply(rule_tac x="(Some Pa, s)#(Some P2, t)#(tl xsa)" in exI,simp)
apply(rule conjI,erule CptsPComp)
apply(rule nth_tl_if,force,simp+)
apply(rule_tac x=ys in exI,simp)
  apply(rule conjI)
  apply (simp add: List.nth_tl)
apply(rule conjI,simp add:lift_def)
apply(subgoal_tac "lift Q (Some P2, t) =(Some (AnnSeq P2 Q), t)")
 apply(simp add:Cons_lift del:list.map)
 apply(rule nth_tl_if)
   apply force
  apply simp+
apply(simp add:lift_def)
done


lemma last_lift_not_None2: "fst ((lift Q) (last (x#xs))) \<noteq> None"
apply(simp only:last_length [THEN sym])
apply(subgoal_tac "length xs<length (x # xs)")
 apply(drule_tac Q=Q in  lift_nth)
 apply(erule ssubst)
 apply (simp add:lift_def)
 apply(case_tac "(x # xs) ! length xs",simp)
apply simp
  done

lemma ann_preserves_pre : "\<forall>s. cpts_of_p (Some P) s \<inter> assume_p (pre, rely) \<subseteq> preserves_p \<Longrightarrow> pre \<subseteq> (ann_pre P)"
  apply (simp add: cpts_of_p_def assume_p_def)
  apply clarify
  apply (erule_tac x = x in allE)
  apply (drule_tac c= "[(Some P, x)]" in subsetD)
   apply (simp add: gets_p_def  cpts_p.CptsPOne)
  by (simp add: preserves_p_def getspc_p_def gets_p_def)

lemma preserves_p_append : "\<lbrakk> l = xs @ ys; xs \<in> preserves_p; ys \<in> preserves_p \<rbrakk> \<Longrightarrow> l \<in> preserves_p"
  by (simp add: preserves_p_def nth_append)


lemma lift_step : "lift Q P -c\<rightarrow> lift Q P' \<Longrightarrow> fst P \<noteq> None \<Longrightarrow> P -c\<rightarrow> P'"
  apply (case_tac "fst P")
   apply force
  apply (case_tac "fst P'")
   apply (case_tac "P", case_tac "P'")
   apply (simp add: lift_def)
   apply (erule ptran.cases, simp_all)
   apply (case_tac "P", case_tac "P'")
  apply (simp add: lift_def)
  apply (erule ptran.cases, simp_all)
  done


lemma Seq_sound:
  "\<lbrakk>\<Turnstile> P sat\<^sub>p [pre, rely, guar, mid]; \<Turnstile> Q sat\<^sub>p [mid, rely, guar, post]\<rbrakk>
  \<Longrightarrow> \<Turnstile> AnnSeq P Q sat\<^sub>p [pre, rely, guar, post]"
  apply(unfold prog_validity_def)
  apply clarify
  apply(case_tac "\<exists>i<length x. fst(x!i)=Some Q")
   prefer 2
   apply (simp add:cpts_of_p_def cpts_iff_cpt_p_mod)
   apply clarify
   apply(frule_tac Seq_sound1,force)
    apply force
    apply clarify
   apply(erule_tac x=s in allE,simp)
   apply auto[1]
    apply(drule_tac c=xs in subsetD,simp add:cpts_of_p_def cpts_iff_cpt_p_mod)
     apply(simp add:assume_p_def gets_p_def)
     apply clarify
     apply(erule_tac P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> I j" for H J I in allE,erule impE, assumption)
     apply(simp add:snd_lift)
     apply(erule mp)
     apply(force elim:petranE intro:EnvP simp add:lift_def)
    apply(simp add:commit_p_def)
    apply(rule conjI)
     apply clarify
     apply(erule_tac P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> I j" for H J I in allE,erule impE, assumption)
     apply(simp add:snd_lift getspc_p_def gets_p_def)
     apply(case_tac "(xs!i)")
     apply(case_tac "(xs! Suc i)")
     apply(case_tac "fst(xs!i)")
      apply(erule_tac x=i in allE, simp add:lift_def)
     apply(case_tac "fst(xs!Suc i)")
      apply (metis (no_types, lifting)  One_nat_def add.right_neutral add_Suc_right diff_Suc_1 
      last_lift length_greater_0_conv length_map lift_nth  list.size(3) list.size(4) nth_Cons_0 zero_less_Suc)
     apply (force simp add: lift_def)
    apply(case_tac xs,simp add:cpts_of_p_def)
    apply clarify
    apply (simp del:list.map)
    apply (rename_tac list)
    apply(subgoal_tac "(map (lift Q) ((a, b) # list))\<noteq>[]")
     apply(drule last_conv_nth)
     apply (simp del:list.map)
     apply(simp add:getspc_p_def gets_p_def)
     apply(simp only:last_lift_not_None)
    apply simp
   apply(drule_tac c=xs in subsetD,simp add:cpts_of_p_def cpts_iff_cpt_p_mod)
    back
    apply(simp add:assume_p_def gets_p_def)
    apply clarify
    apply(erule_tac P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> I j" for H J I in allE,erule impE, assumption)
    apply(simp add:snd_lift)
    apply(erule mp)
    apply(force elim:petranE intro:EnvP simp add:lift_def)
   apply (simp add: preserves_p_def, clarsimp)
   apply (case_tac "xs!i")
   apply (case_tac "a")
    apply (simp add: getspc_p_def gets_p_def lift_def)
    apply (rule_tac A = mid in set_mp)
     apply (rule_tac rely = rely in ann_preserves_pre)
     apply auto[1]
    apply(drule_tac c="take (Suc i) xs" in subsetD,simp add:cpts_of_p_def cpts_iff_cpt_p_mod)
     apply (rule conjI)
      apply auto[1]
     apply(simp add:assume_p_def gets_p_def)
     apply auto[1]
    apply (simp add: commit_p_def gets_p_def getspc_p_def take_Suc_conv_app_nth)
   apply (simp add: lift_def getspc_p_def gets_p_def)
   apply auto[1]
(*@{text "\<exists>i<length x. fst (x ! i) = Some Q"}*)
   apply(erule exE)
   apply(drule_tac n=i and P="\<lambda>i. i < length x \<and> fst (x ! i) = Some Q" in Ex_first_occurrence)
   apply clarify
   apply (simp add:cpts_of_p_def)
   apply clarify
   apply(frule_tac i=m in Seq_sound2,force)
      apply simp+
  apply clarify
  apply (rule conjI)
   apply(simp add:commit_p_def)
   apply(erule_tac x=s in allE)
   apply clarify
   apply(drule_tac c=xs in subsetD,simp)
    apply(case_tac "xs=[]",simp)
    apply(simp add:cpts_of_p_def assume_p_def nth_append gets_p_def getspc_p_def)
    apply clarify
    apply(erule_tac x=i in allE)
    back
    apply(simp add:snd_lift)
    apply(erule mp)
    apply(force elim:petranE intro:EnvP simp add:lift_def)
   apply clarsimp
   apply(erule_tac x="snd(xs!m)" in allE)
   apply(simp add:getspc_p_def gets_p_def)
   apply clarify
   apply(drule_tac c=ys in subsetD)
    back
    apply (simp add:cpts_of_p_def assume_p_def)
    apply(case_tac "xs\<noteq>[]")
     apply(drule last_conv_nth,simp)
     apply(rule conjI)
      apply(simp add:gets_p_def)
      apply(case_tac "xs!m")
      apply(case_tac "fst(xs!m)", simp)
      apply(simp add:lift_def nth_append)
     apply clarify 
     apply(simp add:gets_p_def)
     apply(erule_tac x="m+i" in allE)
     back
     back
     apply(case_tac ys,(simp add:nth_append)+)
     apply (case_tac i, (simp add:snd_lift)+)
  
      apply(erule mp)
      apply(case_tac "xs!m")

  apply (metis (no_types, opaque_lifting) lessI snd_lift surjective_pairing)
     apply simp
    apply simp
   apply clarify
   apply(rule conjI,clarify)
    apply(case_tac "i<m",simp add:nth_append)
     apply(simp add:snd_lift)
     apply(erule allE, erule impE, assumption, erule mp)
     apply(case_tac "(xs ! i)")
     apply(case_tac "(xs ! Suc i)")
     apply (case_tac "fst (xs!i)")
      apply (erule_tac x = i in allE, simp add: lift_def)
     apply (rule lift_step, simp, simp)
    apply(erule_tac x="i-m" in allE)
    back
    back
    apply(subgoal_tac "Suc (i - m) < length ys",simp)
     prefer 2
     apply arith
 apply(simp add:nth_append snd_lift)
 apply(rule conjI,clarify)
  apply(subgoal_tac "i=m")
   prefer 2
   apply arith
     apply clarify
     apply(simp add:cpts_of_p_def)
     apply(rule tl_zero)
       apply(erule mp)
       apply(case_tac "lift Q (xs!m)",simp add:snd_lift)
       apply(case_tac "xs!m",case_tac "fst(xs!m)",simp add:lift_def snd_lift)
        apply(case_tac ys,simp+)
       apply(simp add:lift_def)
      apply simp
     apply force
    apply clarify
    apply(rule tl_zero)
      apply(rule tl_zero)
        apply (subgoal_tac "i-m=Suc(i-Suc m)")
         apply simp
         apply(erule mp)
         apply(case_tac ys,simp+)
      apply force
     apply arith
    apply force
   apply clarify
   apply(case_tac "(map (lift Q) xs @ tl ys)\<noteq>[]")
    apply(drule last_conv_nth)
    apply(simp add: snd_lift nth_append)
    apply(rule conjI,clarify)
     apply(case_tac ys,simp+)
    apply clarify
    apply(case_tac ys,simp+)
  apply (rule_tac xs = "map (lift Q) (take m xs)" and ys = "lift Q (xs ! m) # tl ys" in preserves_p_append)
    apply (rule_tac s = "(map (lift Q) (take m xs) @ [lift Q (xs ! m)]) @ tl ys" in trans)
     apply (metis (no_types, lifting) append_eq_append_conv_if length_map lessI nth_map take_Suc_conv_app_nth take_map)
    apply simp
   apply (simp add: preserves_p_def, clarify)
   apply (erule_tac x = s in allE, drule conjunct2) 
   apply(drule_tac c=xs in subsetD, simp add: assume_p_def gets_p_def cpts_of_p_def)
    apply clarify
    apply(erule_tac x = ia and P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> I j" for H J I in allE, erule impE)
     apply linarith
    apply (simp add: nth_append, erule impE)
     apply(force elim:petranE intro:EnvP simp add:lift_def)
    apply (simp add: snd_lift)
   apply (case_tac "xs ! i")
   apply (case_tac "fst (xs ! i)")
    apply (erule_tac x = "i" in allE, simp add: nth_append)
    apply (simp add: lift_def getspc_p_def gets_p_def, clarify)
   apply (simp add: getspc_p_def gets_p_def lift_def)
   apply (metis ann_preserves_p.simps(2) fst_conv less_SucI snd_conv)
   apply (case_tac "xs ! m")
  apply (case_tac "fst (xs ! m)")
   prefer 2
   apply (simp add: nth_append lift_def)
  apply (erule_tac x = s in allE, drule conjunct1)
  apply(drule_tac c=xs in subsetD, simp add: assume_p_def gets_p_def cpts_of_p_def)
   apply clarify
   apply(erule_tac x = i and P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> I j" for H J I in allE, erule impE)
    apply linarith
   apply (simp add: nth_append, erule impE)
    apply(force elim:petranE intro:EnvP simp add:lift_def)
   apply (simp add: snd_lift)
  apply (erule_tac x = b in allE, drule conjunct2)
  apply (drule_tac c = "lift Q (xs ! m) # tl ys" in subsetD)
   apply (simp add: cpts_of_p_def lift_def)
   apply (rule conjI)
  apply (metis Anno_SIMP_Tran.nth_tl cptn_not_empty)
   apply (simp add: assume_p_def gets_p_def)
   apply (rule conjI)
    apply (simp add: commit_p_def)
    apply (metis Zero_not_Suc diff_Suc_1 fst_conv gets_p_def getspc_p_def last_conv_nth length_0_conv snd_conv)
   apply clarify
   apply(erule_tac x = "i + m" and P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> I j" for H J I in allE, erule impE)
    apply simp
   apply (case_tac i, simp add: nth_append)
   apply (simp add: nth_append)
  by simp

subsubsection\<open>Soundness of the While rule\<close>

lemma last_append[rule_format]:
  "\<forall>xs. ys\<noteq>[] \<longrightarrow> ((xs@ys)!(length (xs@ys) - (Suc 0)))=(ys!(length ys - (Suc 0)))"
apply(induct ys)
 apply simp
apply clarify
apply (simp add:nth_append)
done

lemma assum_after_body:
  "\<lbrakk> \<Turnstile> P sat\<^sub>p [pre \<inter> b, rely, guar, pre];
  (Some P, s) # xs \<in> cpt_p_mod; fst (last ((Some P, s) # xs)) = None; s \<in> b;
  (Some (AnnWhile r b P), s) # (Some (AnnSeq P (AnnWhile r b P)), s) #
   map (lift (AnnWhile r b P)) xs @ ys \<in> assume_p (pre, rely)\<rbrakk>
  \<Longrightarrow> (Some (AnnWhile r b P), snd (last ((Some P, s) # xs))) # ys \<in> assume_p (pre, rely)"
  apply(simp add:assume_p_def prog_validity_def cpts_of_p_def cpts_iff_cpt_p_mod gets_p_def)
  apply clarify
  apply(erule_tac x=s in allE)
  apply clarify
   apply(drule_tac c="(Some P, s) # xs" in subsetD,simp)
   apply clarify
   apply(erule_tac x="Suc i" in allE)
   apply simp
   apply(simp add:Cons_lift_append nth_append snd_lift del:list.map)
   apply(erule mp)
   apply(erule petranE,simp)
   apply(case_tac "fst(((Some P, s) # xs) ! i)")
    apply(force intro:EnvP simp add:lift_def)
   apply(force intro:EnvP simp add:lift_def)
  apply(rule conjI)
   apply clarify
   apply(simp add:commit_p_def last_length)
  apply clarify
  apply(rule conjI)
   apply(simp add:commit_p_def getspc_p_def gets_p_def)
  apply clarify
  apply(erule_tac x="Suc(length xs + i)" in allE,simp)
  apply(case_tac i, simp add:nth_append Cons_lift_append snd_lift last_conv_nth lift_def split_def)
  apply(simp add:Cons_lift_append nth_append snd_lift)
  done

lemma lift_assume : "map (lift P) l \<in> assume_p (pre, rely) \<Longrightarrow> l \<in> cpts_p \<Longrightarrow> l \<in> assume_p (pre, rely)"
  apply (simp add: assume_p_def gets_p_def getspc_p_def)
  apply (rule conjI)
   apply (metis cptn_not_empty length_greater_0_conv nth_map snd_lift)
  apply clarify
  apply(erule_tac x="i" in allE,simp add:snd_lift del:list.map)
  apply(case_tac "fst(l!i)")
  apply (erule mp)
  apply(erule petranE,simp add:lift_def)
   apply (rule EnvP)
  apply(erule petranE,simp add:lift_def)
  by (simp add: petran.intros)


lemma While_sound_aux [rule_format]:
  "\<lbrakk> pre \<inter> - b \<subseteq> post; \<Turnstile> P sat\<^sub>p [pre \<inter> b, rely, guar, pre]; \<forall>s. (s, s) \<in> guar;
   stable pre rely;  stable post rely; x \<in> cpt_p_mod \<rbrakk>
  \<Longrightarrow>  \<forall>s xs. x= (Some (AnnWhile r b P),s)#xs \<longrightarrow> x\<in>assume_p(pre, rely) \<longrightarrow> x \<in> commit_p (guar, post)"
  apply(erule cpt_p_mod.induct)
          apply safe
      apply (simp_all del:last.simps)
(*5 subgoals left*)
      apply(simp add:commit_p_def getspc_p_def gets_p_def)
(*4 subgoals left*)
     apply(rule etran_in_comm)
     apply(erule mp)
     apply(erule tl_of_assum_in_assum,simp)
(*While-None*)
    apply(simp add:commit_p_def)
    apply(simp add:cpts_iff_cpt_p_mod [THEN sym])
    apply(rule conjI,clarify)
     apply (rule conjI, clarify)
       apply(force simp add:assume_p_def getspc_p_def gets_p_def)
      apply (simp add: ann_preserves_p_def assume_p_def getspc_p_def gets_p_def)
     apply(force simp add:assume_p_def getspc_p_def gets_p_def)
    apply(simp add: getspc_p_def gets_p_def)
    apply clarify
    apply(rule conjI, clarify)
      apply(case_tac i,simp,simp)
     apply(force simp add:not_ctran_None2)
    apply(subgoal_tac "\<forall>i. Suc i < length ((None, sa) # xs) \<longrightarrow> (((None, sa) # xs) ! i, ((None, sa) # xs) ! Suc i)\<in> petran")
     prefer 2
     apply clarify
     apply(rule_tac m="length ((None, sa) # xs)" in etran_or_ctran,simp+)
      apply(erule not_ctran_None2,simp)
     apply simp+
    apply(frule_tac j="0" and k="length ((None, sa) # xs) - 1" and p=post in stability,simp+)
       apply(force simp add:assume_p_def subsetD gets_p_def)
      apply(simp add:assume_p_def)
      apply clarify
      apply(erule_tac x="i" in allE,simp)
      apply (simp add:gets_p_def)
      apply(erule_tac x="Suc i" in allE,simp)
     apply simp
    apply clarify
    apply (simp add:last_length)
(*WhileOne*)
   apply(rule ctran_in_comm, simp)
    apply(simp add: assume_p_def gets_p_def)
   apply(simp add:Cons_lift del:list.map)
   apply(simp add:commit_p_def del:list.map)
   apply(rule conjI, clarify)
    apply(case_tac "fst(((Some P, sa) # xs) ! i)")
     apply(case_tac "((Some P, sa) # xs) ! i")
     apply (simp add:lift_def)
     apply(ind_cases "(Some (AnnWhile r b P), ba) -c\<rightarrow> t" for ba t)
      apply (simp add:gets_p_def)
     apply (simp add:gets_p_def)
    apply(simp add:snd_lift gets_p_def del:list.map)
    apply(simp only:prog_validity_def cpts_of_p_def cpts_iff_cpt_p_mod)
    apply(erule_tac x=sa in allE)
    apply(drule_tac c="(Some P, sa) # xs" in subsetD)
     apply (simp add:assume_p_def gets_p_def del:list.map)
     apply clarify
     apply(erule_tac x="Suc ia" in allE,simp add:snd_lift del:list.map)
     apply(erule mp)
     apply(case_tac "fst(((Some P, sa) # xs) ! ia)")
      apply(erule petranE,simp add:lift_def)
      apply(rule EnvP)
     apply(erule petranE,simp add:lift_def)
     apply(rule EnvP)
    apply (simp add:commit_p_def getspc_p_def gets_p_def del:list.map)
    apply clarify
    apply(erule allE,erule impE,assumption)
    apply(case_tac "((Some P, sa) # xs) ! i")
    apply(case_tac "xs!i")
    apply(simp add:lift_def)
    apply(case_tac "fst(xs!i)")
     apply force
    apply force
(*last=None*)
   apply(subgoal_tac "(map (lift (AnnWhile r b P)) ((Some P, sa) # xs))\<noteq>[]")
    apply(drule last_conv_nth)
    apply (simp add:getspc_p_def gets_p_def del:list.map)
    apply (metis last.simps last_length last_lift_not_None)
   apply simp
(*WhileMore*)                                                              
  apply(rule ctran_in_comm,simp del:last.simps)
(*metiendo la hipotesis antes de dividir la conclusion.*)
   apply(subgoal_tac "(Some (AnnWhile r b P), snd (last ((Some P, sa) # xs))) # ys \<in> assume_p (pre, rely)")
    apply (simp del:last.simps)
   apply(erule assum_after_body)
      apply (simp del:last.simps)+
(*lo de antes.*)
  apply(simp add:commit_p_def getspc_p_def gets_p_def del:list.map last.simps)
  apply(rule conjI, clarify)
   apply(simp only:Cons_lift_append)
   apply(case_tac "i<length xs")
    apply(simp add:nth_append del:list.map last.simps)
    apply(case_tac "fst(((Some P, sa) # xs) ! i)")
     apply(case_tac "((Some P, sa) # xs) ! i")
     apply (simp add:lift_def del:last.simps)
     apply(ind_cases "(Some (AnnWhile r b P), ba) -c\<rightarrow> t" for ba t)
      apply simp
     apply simp
    apply(simp add:snd_lift del:list.map last.simps)
    apply(simp only:prog_validity_def cpts_of_p_def cpts_iff_cpt_p_mod)
    apply(erule_tac x=sa in allE)
    apply(drule_tac c="(Some P, sa) # xs" in subsetD)
     apply (simp add:assume_p_def getspc_p_def gets_p_def del:list.map last.simps)
     apply clarify
     apply(erule_tac x="Suc ia" in allE,simp add:nth_append snd_lift del:list.map last.simps, erule mp)
     apply(case_tac "fst(((Some P, sa) # xs) ! ia)")
      apply(erule petranE,simp add:lift_def)
      apply(rule EnvP)
     apply(erule petranE,simp add:lift_def)
     apply(rule EnvP)
    apply (simp add:commit_p_def getspc_p_def gets_p_def del:list.map)
    apply clarify
    apply(erule allE,erule impE,assumption)
    apply(case_tac "((Some P, sa) # xs) ! i")
    apply(case_tac "xs!i")
    apply(simp add:lift_def)
    apply(case_tac "fst(xs!i)")
     apply force
    apply force
(*@{text "i \<ge> length xs"}*)
    apply(subgoal_tac "i-length xs <length ys")
     prefer 2
    apply arith
   apply(case_tac "i=length xs")
     apply (simp add:nth_append snd_lift del:list.map last.simps)
     apply(simp add:last_length del:last.simps)
     apply(case_tac "last((Some P, sa) # xs)")
    apply(simp add:lift_def del:last.simps)
    apply auto[1]
(*@{text "i>length xs"}*)
   apply(case_tac "i-length xs")
    apply arith
   apply(simp add:nth_append del:list.map last.simps)
   apply(rotate_tac -3)
   apply(subgoal_tac "i- Suc (length xs)=nat")
    prefer 2
    apply arith
   apply (metis (no_types, lifting) Cons_lift_append List.nth_tl Suc_lessD assum_after_body list.sel(3))
(*last=None*)
  apply clarify
  apply(case_tac ys)
   apply(simp add:Cons_lift del:list.map last.simps)
   apply(subgoal_tac "(map (lift (AnnWhile r b P)) ((Some P, sa) # xs))\<noteq>[]")
    apply(drule last_conv_nth)
    apply (simp del:list.map)
    apply(simp only:last_lift_not_None)
   apply simp
  apply(subgoal_tac "((Some (AnnSeq P (AnnWhile r b P)), sa) # map (lift (AnnWhile r b P)) xs @ ys)\<noteq>[]")
   apply(drule last_conv_nth)
   apply (simp del:list.map last.simps)
   apply(simp add:nth_append del:last.simps)
   apply(rename_tac a list)
   apply(subgoal_tac "((Some (AnnWhile r b P), snd (last ((Some P, sa) # xs))) # a # list)\<noteq>[]")
    apply(drule last_conv_nth)
    apply (metis assum_after_body last_length length_Cons nth_Cons_Suc)
   apply simp
  apply simp
  done

lemma lift_assume_p : "map (lift Q) l \<in> assume_p (pre, rely) \<Longrightarrow> l \<in> assume_p (pre, rely)"
  apply (simp add: assume_p_def)
  apply (rule conjI)
   apply (metis gets_p_def length_0_conv list.simps(8) neq0_conv nth_map snd_lift)
  apply clarify
  apply (case_tac "l ! i")
  apply (case_tac "a")
   apply (erule_tac x = i in allE)
   apply(erule petranE,simp add:lift_def gets_p_def getspc_p_def)
  apply (simp add: petran.intros)
  apply(erule petranE,simp add:lift_def gets_p_def getspc_p_def)
  using petran.intros by fastforce

lemma While_sound_aux1 [rule_format]:
  "\<lbrakk> pre \<subseteq> r; pre \<inter> - b \<subseteq> post; \<Turnstile> P sat\<^sub>p [pre \<inter> b, rely, guar, pre]; \<forall>s. (s, s) \<in> guar;
   stable pre rely;  stable post rely; x \<in> cpt_p_mod \<rbrakk>
  \<Longrightarrow>  \<forall>s xs. x=(Some(AnnWhile r b P),s)#xs \<longrightarrow> x\<in>assume_p(pre, rely) \<longrightarrow> x \<in> preserves_p"
  apply(erule cpt_p_mod.induct)
          apply safe
      apply (simp_all del:last.simps)
(*5 subgoals left*)
      apply(simp add:preserves_p_def assume_p_def getspc_p_def gets_p_def)
      apply blast
(*4 subgoals left*)
  apply (rule_tac xs = "[(Some (AnnWhile r b P), sa)]" and ys = "(Some (AnnWhile r b P), t) # xs"
         in preserves_p_append, simp)
      apply (simp add: assume_p_def preserves_p_def gets_p_def getspc_p_def)
      apply blast
     apply (erule impE, simp add: assume_p_def gets_p_def)
      apply (clarify, rule conjI)
       apply (erule_tac x = "0" in allE, simp add: petran.intros stable_def)
      apply auto[1]
     apply simp
(*While-None*)
    apply (rule_tac xs = "[(Some (AnnWhile r b P), sa)]" and ys = "(None, sa) # xs" in preserves_p_append, simp)
     apply (simp add: preserves_p_def assume_p_def gets_p_def getspc_p_def)
     apply blast
    apply (simp add: preserves_p_def, clarify)
    apply (subgoal_tac "getspc_p (((None, sa) # xs) ! i) = None", simp)
    apply (rule not_ctran_None3', simp_all del: last.simps)
  using cpts_if_cpt_p_mod apply blast
    apply (simp add: getspc_p_def)
(*WhileOne*)
   apply(simp add:Cons_lift del:list.map)
  apply (rule_tac xs = "[(Some (AnnWhile r b P), sa)]" and ys = "map (lift (AnnWhile r b P)) ((Some P, sa) # xs)"
          in preserves_p_append, simp)
    apply (simp add: preserves_p_def assume_p_def gets_p_def getspc_p_def)
    apply blast
   apply (subgoal_tac "(Some P, sa) # xs \<in> assume_p (pre, rely)")
   apply (simp add: preserves_p_def del: list.map, clarify)
   apply(case_tac "fst(((Some P, sa) # xs) ! i)")
    apply(case_tac "((Some P, sa) # xs) ! i")
     apply (simp add: getspc_p_def lift_def gets_p_def del: list.map)
    apply(simp only:prog_validity_def cpts_of_p_def cpts_iff_cpt_p_mod)
    apply (erule_tac x = "sa" in allE, simp del: list.map)
    apply (drule conjunct1)
    apply (drule_tac c = "take (Suc i) ((Some P, sa) # xs)" in subsetD)
      apply (simp add:assume_p_def gets_p_def del:list.map take_Suc_Cons)
  using cpts_if_cpt_p_mod cpts_onlyif_cpt_p_mod takecptn_is_cptn apply blast
     apply clarify
    apply (simp add: commit_p_def del: take_Suc_Cons)
    apply (drule conjunct2)
    apply (erule impE, simp add: getspc_p_def del: take_Suc_Cons)
     apply (metis fst_conv last_snoc length_Cons take_Suc_conv_app_nth)
     apply (simp add: gets_p_def del: take_Suc_Cons)
     apply (metis last_snoc length_Cons snd_conv subset_iff take_Suc_conv_app_nth)
    apply(simp only:prog_validity_def cpts_of_p_def cpts_iff_cpt_p_mod)
    apply (erule_tac x = "sa" in allE, simp del: list.map)
    apply (drule conjunct2)
    apply(drule_tac c="(Some P, sa) # xs" in subsetD)
     apply (simp add:assume_p_def gets_p_def del:list.map)
    apply (simp add: preserves_p_def del: list.map)
    apply (erule_tac x = "i" in allE, simp del: list.map)
    apply(case_tac "((Some P, sa) # xs) ! i")
    apply (simp add: getspc_p_def gets_p_def lift_def del: list.map)
   apply (rule_tac Q = "(AnnWhile r b P)" in lift_assume_p)
   apply (simp add: assume_p_def gets_p_def)
   apply (rule conjI, simp add: lift_def)
   apply clarify
   apply (erule_tac x = "Suc i" in allE, erule impE, simp)
   apply (erule impE, simp, simp)
(*WhileMore*)
  apply(subgoal_tac "(Some (AnnWhile r b P), snd (last ((Some P, sa) # xs))) # ys \<in> assume_p (pre, rely)")
   apply (simp del:last.simps)
   prefer 2
   apply(erule assum_after_body)
      apply (simp del:last.simps)+
  apply (rule_tac xs = "[(Some (AnnWhile r b P), sa)]" and ys = "(Some (AnnSeq P (AnnWhile r b P)), sa) 
        # map (lift (AnnWhile r b P)) xs @ ys" in preserves_p_append, simp)
   apply (simp add: assume_p_def preserves_p_def gets_p_def getspc_p_def)
   apply blast
  apply (rule_tac xs = "(Some (AnnSeq P (AnnWhile r b P)), sa) # map (lift (AnnWhile r b P)) xs" 
        and ys = " ys" in preserves_p_append, simp)
   apply (simp only: Cons_lift)
   apply (subgoal_tac " map (lift (AnnWhile r b P)) ((Some P, sa) # xs) \<in> assume_p (pre, rely)")
    prefer 2
    apply (simp add: assume_p_def gets_p_def getspc_p_def del: last.simps list.map)
    apply (rule conjI, simp add: lift_def)
    apply clarify
    apply (erule_tac x = "Suc i" and P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> I j" for H J I in allE)
    apply (erule impE)
     apply linarith
    apply (erule impE)
     apply (metis (no_types, lifting) Cons_lift_append length_Cons length_map less_SucI nth_Cons_Suc nth_append nth_map)
    apply (metis (no_types, lifting) Cons_lift_append le_imp_less_Suc length_Cons length_map less_imp_le nth_Cons_Suc nth_append nth_map)
   apply (subgoal_tac "(Some P, sa) # xs \<in> assume_p (pre, rely)")
    apply (simp only: preserves_p_def, clarify)
    apply (case_tac "((Some P, sa) # xs) ! i")
    apply (case_tac "a")
     apply(simp only:prog_validity_def cpts_of_p_def cpts_iff_cpt_p_mod)
     apply (erule_tac x = "sa" in allE, simp del: list.map)
     apply (drule conjunct1)
     apply (drule_tac c = "take (Suc i) ((Some P, sa) # xs)" in subsetD)
      apply (simp add:assume_p_def gets_p_def del:list.map take_Suc_Cons last.simps)
      apply clarify
      apply (meson cpts_if_cpt_p_mod cpts_onlyif_cpt_p_mod takecptn_is_cptn)
     apply clarify
     apply (simp add: commit_p_def getspc_p_def gets_p_def lift_def del: take_Suc_Cons last.simps)
     apply (drule conjunct2)
     apply (metis (no_types, lifting) fst_conv last_snoc length_Cons snd_conv subsetD take_Suc_conv_app_nth)
    apply(simp only:prog_validity_def cpts_of_p_def cpts_iff_cpt_p_mod)
    apply (erule_tac x = "sa" in allE, simp del: list.map take_Suc_Cons last.simps)
    apply (drule conjunct2)
    apply (drule_tac c = "(Some P, sa) # xs" in subsetD)
     apply (simp add:assume_p_def gets_p_def del:list.map take_Suc_Cons last.simps)
    apply (simp add: preserves_p_def getspc_p_def gets_p_def lift_def del: list.map take_Suc_Cons last.simps)
    apply (erule_tac x = i in allE, simp add: lift_def del: list.map take_Suc_Cons last.simps)
  using lift_assume_p apply blast
  apply (simp add: preserves_p_def)
  apply clarify
  apply (erule_tac x = "Suc i" in allE, simp)
  done

lemma While_sound:
  "\<lbrakk> pre \<subseteq> r; stable pre rely; pre \<inter> - b \<subseteq> post; stable post rely;
    \<Turnstile> P sat\<^sub>p [pre \<inter> b, rely, guar, pre]; \<forall>s. (s,s)\<in>guar\<rbrakk>
  \<Longrightarrow> \<Turnstile> AnnWhile r b P sat\<^sub>p [pre, rely, guar, post]"
  apply(unfold prog_validity_def)
  apply clarify
  apply (rule IntI)
   apply(erule_tac xs="tl x" in While_sound_aux)
         apply(simp add:prog_validity_def)
        apply force
       apply simp_all
    apply(simp add:cpts_iff_cpt_p_mod cpts_of_p_def)
    apply(simp add:cpts_of_p_def)
    apply clarify
    apply(rule nth_equalityI)
     apply simp_all
     apply(case_tac x,simp+)
    apply(case_tac i,simp+)
   apply(case_tac x,simp+)
   apply(erule_tac xs="tl x" in While_sound_aux1, simp)
        apply(simp add:prog_validity_def)
       apply force
      apply simp_all
   apply(simp add:cpts_iff_cpt_p_mod cpts_of_p_def)
  apply(simp add:cpts_of_p_def)
  apply clarify
  apply(rule nth_equalityI)
   apply simp_all
   apply(case_tac x,simp+)
  apply(case_tac i,simp+)
  apply(case_tac x,simp+)
  done


subsubsection\<open>Soundness of the Nondt rule\<close>

lemma unique_ctran_Nondt [rule_format]:
  "\<forall>s i. x \<in> cpts_p \<longrightarrow> x ! 0 = (Some (AnnNondt r f), s) \<longrightarrow>
  Suc i<length x \<longrightarrow> x!i -c\<rightarrow> x!Suc i \<longrightarrow>
  (\<forall>j. Suc j<length x \<longrightarrow> i\<noteq>j \<longrightarrow> x!j -pe\<rightarrow> x!Suc j)"
apply(induct x,simp)
apply simp
apply clarify
apply(erule cpts_p.cases,simp)
 apply(case_tac i,simp+)
 apply clarify
 apply(case_tac j,simp)
  apply(rule EnvP)
 apply simp
apply clarify
apply simp
apply(case_tac i)
 apply(case_tac j,simp,simp)
 apply(erule ptran.cases,simp_all)
 apply(force elim: not_ctran_None)
apply(ind_cases "((Some (AnnNondt r f), sa), Q, t) \<in> ptran" for sa Q t)
apply simp
apply(drule_tac i=nat in not_ctran_None,simp)
apply(erule petranE,simp)
done

lemma exists_ctran_Nondt_None [rule_format]:
  "\<forall>s i. x \<in> cpts_p \<longrightarrow> x ! 0 = (Some (AnnNondt r f), s)
  \<longrightarrow> i<length x \<longrightarrow> fst(x!i)=None \<longrightarrow> (\<exists>j<i. x!j -c\<rightarrow> x!Suc j)"
apply(induct x,simp)
apply simp
apply clarify
apply(erule cpts_p.cases,simp)
 apply(case_tac i,simp,simp)
 apply(erule_tac x=nat in allE,simp)
 apply clarify
 apply(rule_tac x="Suc j" in exI,simp,simp)
apply clarify
apply(case_tac i,simp,simp)
apply(rule_tac x=0 in exI,simp)
done

lemma Nondt_sound:
  "\<lbrakk>pre \<subseteq> r; stable pre rely; pre \<subseteq> {s. (\<forall>t. (s,t) \<in> f \<longrightarrow> t \<in> post) \<and> (\<exists>t. (s,t) \<in> f)}; 
            {(s,t). s \<in> pre \<and> (s,t)\<in>f} \<subseteq> guar;  stable post rely\<rbrakk>
           \<Longrightarrow> \<Turnstile> AnnNondt r f sat\<^sub>p [pre, rely, guar, post]"
  apply(unfold prog_validity_def)
  apply clarify
  apply (rule IntI)
   apply(simp add:commit_p_def)
   apply(simp add:getspc_p_def gets_p_def)
   apply(rule conjI, clarify)
    apply(simp add:cpts_of_p_def assume_p_def gets_p_def)
    apply clarify
    apply(frule_tac j=0 and k=i and p= pre in stability)
          apply simp_all
      apply(erule_tac x=ia in allE,simp)
     apply(erule_tac i=i and r=r in unique_ctran_Nondt,simp_all)
    apply(erule subsetD,simp)
    apply(case_tac "x!i")
    apply clarify
    apply(drule_tac s="Some (AnnNondt r f)" in sym,simp)
    apply(thin_tac "\<forall>j. H j" for H)
    apply(force elim:ptran.cases)
   apply clarify
   apply(simp add:cpts_of_p_def)
   apply clarify
   apply(frule_tac i="length x - 1" and r=r and f = f in exists_ctran_Nondt_None,simp+)
     apply(case_tac x,simp+)
    apply(rule last_fst_esp,simp add:last_length)
    apply (case_tac x,simp+)
   apply(simp add:assume_p_def gets_p_def)
   apply clarify
   apply(frule_tac j=0 and k="j" and p= pre in stability)
         apply simp_all
     apply(erule_tac x=i in allE,simp)
    apply(erule_tac i=j and r=r in unique_ctran_Nondt,simp_all)
   apply(case_tac "x!j")
   apply clarify
   apply simp
   apply(drule_tac s="Some (AnnNondt r f)" in sym,simp)
   apply(case_tac "x!Suc j",simp)
   apply(rule ptran.cases,simp)
           apply(simp_all)
   apply(drule_tac c=sa in subsetD,simp)
   apply clarify
   apply(frule_tac j="Suc j" and k="length x - 1" and p=post in stability,simp_all)
      apply blast
     apply(case_tac x,simp+)
    apply(erule_tac x=i in allE)
    apply(erule_tac i=j and r=r in unique_ctran_Nondt, simp_all)
     apply arith+
   apply(case_tac x)
    apply(simp add:last_length)+
  apply (case_tac "\<exists>i. Suc i < length x \<and> (x!i) -c\<rightarrow> (x!(Suc i))")
   apply (simp add: preserves_p_def cpts_of_p_def assume_p_def gets_p_def)
   apply clarify
   apply (case_tac "ia \<le> i")
    apply(frule_tac j=0 and k=ia and p= pre in stability, simp_all)
      apply blast
  using unique_ctran_Nondt apply fastforce
    apply (case_tac "x!ia")
    apply (simp add: getspc_p_def)
    apply blast
   apply(frule_tac j=0 and k=i and p= pre in stability, simp_all)
     apply blast
     apply(erule_tac i=i and f=f in unique_ctran_Nondt,simp_all)
   apply (case_tac "x ! Suc i")
   apply (erule ptran.cases, simp_all)
   apply (drule_tac i = "Suc i" and j = ia in not_ctran_Finish, simp_all)
   apply (simp add: getspc_p_def)
  apply (simp add: preserves_p_def cpts_of_p_def assume_p_def gets_p_def)
  apply clarify 
  apply(frule_tac j=0 and k=i and p= pre in stability, simp_all)
    apply blast
   apply (drule_tac m = "length x" and i = "ia" in etran_or_ctran, simp_all)
  apply (case_tac "x!i")
  apply (simp add: getspc_p_def)
  by blast

subsubsection \<open>Soundness of the system for programs\<close>

theorem rgsound_p:
  "\<turnstile> P sat\<^sub>p [pre, rely, guar, post] \<Longrightarrow> \<Turnstile> P sat\<^sub>p [pre, rely, guar, post]"
  apply(erule rghoare_p.induct)
        apply(force elim:Basic_sound)
       apply(force elim:Seq_sound)
      apply(force elim:Cond_sound)
     apply(force elim:While_sound)
    apply(force elim:Await_sound)
   apply(force elim:Nondt_sound)
  apply(erule Conseq_sound,simp+)
  done

end
