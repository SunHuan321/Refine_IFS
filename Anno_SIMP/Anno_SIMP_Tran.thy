theory Anno_SIMP_Tran
  imports Anno_SIMP_Com
begin

type_synonym 's conf = "(('s ann_prog) option) \<times> 's"

definition getspc_p :: "'s conf \<Rightarrow> ('s ann_prog) option" where
  "getspc_p conf \<equiv> fst conf"

definition gets_p :: "'s conf \<Rightarrow> 's" where
  "gets_p conf \<equiv> snd conf"

subsection \<open>Semantics of Programs\<close>

inductive_set
  ptran :: "('s conf \<times> 's conf) set"
  and ptran' :: "'s conf \<Rightarrow> 's conf \<Rightarrow> bool"   ("_ -c\<rightarrow> _" [81,81] 80)
  and ptrans :: "'s conf \<Rightarrow> 's conf \<Rightarrow> bool"   ("_ -c*\<rightarrow> _" [81,81] 80)
where
  "P -c\<rightarrow> Q \<equiv> (P,Q) \<in> ptran"
| "P -c*\<rightarrow> Q \<equiv> (P,Q) \<in>ptran^*" 

| Basic:  "(Some (AnnBasic r f), s) -c\<rightarrow> (None, f s)"
| Seq1:   "(Some P0, s) -c\<rightarrow> (None, t) \<Longrightarrow> (Some (AnnSeq P0 P1), s) -c\<rightarrow> (Some P1, t)"
| Seq2:    "(Some P0, s) -c\<rightarrow> (Some P2, t) \<Longrightarrow> (Some(AnnSeq P0 P1), s) -c\<rightarrow> (Some(AnnSeq P2 P1), t)"
| CondT:  "s\<in>b  \<Longrightarrow> (Some(AnnCond r b P1 P2), s) -c\<rightarrow> (Some P1, s)"
| CondF:  "s\<notin>b \<Longrightarrow> (Some(AnnCond r b P1 P2), s) -c\<rightarrow> (Some P2, s)"
| WhileF: "s\<notin>b \<Longrightarrow> (Some(AnnWhile r b P), s) -c\<rightarrow> (None, s)"
| WhileT: "s\<in>b  \<Longrightarrow> (Some(AnnWhile r b P), s) -c\<rightarrow> (Some(AnnSeq P (AnnWhile r b P)), s)"
| Await:  "\<lbrakk>s\<in>b; (Some P, s) -c*\<rightarrow> (None, t)\<rbrakk> \<Longrightarrow> (Some(AnnAwait r b P), s) -c\<rightarrow> (None, t)" 
| Nondt:  "(s,t)\<in>f \<Longrightarrow> (Some(AnnNondt r f), s) -c\<rightarrow> (None, t)"

subsection \<open>Environment transitions\<close>

inductive_set
  petran :: "('s conf \<times> 's conf) set"
  and petran' :: "'s conf \<Rightarrow> 's conf \<Rightarrow> bool"  ("_ -pe\<rightarrow> _" [81,81] 80)
where
  "P -pe\<rightarrow> Q \<equiv> (P,Q) \<in> petran"
| EnvP: "(P, s) -pe\<rightarrow> (P, t)"

lemma petranE: "p -pe\<rightarrow> p' \<Longrightarrow> (\<And>P s t. p = (P, s) \<Longrightarrow> p' = (P, t) \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (induct p, induct p', erule petran.cases, blast)

subsection \<open>Sequential computations\<close>

subsubsection \<open>Sequential computations of programs\<close>
type_synonym 's confs = "'s conf list"

inductive_set cpts_p :: "'s confs set"
where
  CptsPOne: "[(P,s)] \<in> cpts_p"
| CptsPEnv: "(P, t)#xs \<in> cpts_p \<Longrightarrow> (P,s)#(P,t)#xs \<in> cpts_p"
| CptsPComp: "\<lbrakk>(P,s) -c\<rightarrow> (Q,t); (Q, t)#xs \<in> cpts_p\<rbrakk> \<Longrightarrow> (P,s)#(Q,t)#xs \<in> cpts_p"

definition cpts_of_p :: "('s ann_prog) option \<Rightarrow> 's \<Rightarrow> ('s confs) set" where
  "cpts_of_p P s \<equiv> {l. l!0=(P,s) \<and> l \<in> cpts_p}" 

subsection \<open>Modular definition of program computations\<close>

definition lift :: "'s ann_prog \<Rightarrow> 's conf \<Rightarrow> 's conf" where
  "lift Q \<equiv> \<lambda>(P, s). (if P= None then (Some Q,s) else (Some(AnnSeq (the P) Q), s))"

inductive_set cpt_p_mod :: "('s confs) set"
where
  CptPModOne: "[(P, s)] \<in> cpt_p_mod"
| CptPModEnv: "(P, t)#xs \<in> cpt_p_mod \<Longrightarrow> (P, s)#(P, t)#xs \<in> cpt_p_mod"
| CptPModNone: "\<lbrakk>(Some P, s) -c\<rightarrow> (None, t); (None, t)#xs \<in> cpt_p_mod \<rbrakk> \<Longrightarrow> (Some P,s)#(None, t)#xs \<in>cpt_p_mod"

| CptPModCondT: "\<lbrakk>(Some P0, s)#ys \<in> cpt_p_mod; s \<in> b \<rbrakk> \<Longrightarrow> (Some(AnnCond r b P0 P1), s)#(Some P0, s)#ys \<in> cpt_p_mod"
| CptPModCondF: "\<lbrakk>(Some P1, s)#ys \<in> cpt_p_mod; s \<notin> b \<rbrakk> \<Longrightarrow> (Some(AnnCond r b P0 P1), s)#(Some P1, s)#ys \<in> cpt_p_mod"

| CptPModSeq1: "\<lbrakk>(Some P0, s)#xs \<in> cpt_p_mod; zs=map (lift P1) xs \<rbrakk>
                 \<Longrightarrow> (Some(AnnSeq P0 P1), s)#zs \<in> cpt_p_mod"
| CptPModSeq2: 
  "\<lbrakk>(Some P0, s)#xs \<in> cpt_p_mod; fst(last ((Some P0, s)#xs)) = None; 
  (Some P1, snd(last ((Some P0, s)#xs)))#ys \<in> cpt_p_mod; 
  zs=(map (lift P1) xs)@ys \<rbrakk> \<Longrightarrow> (Some(AnnSeq P0 P1), s)#zs \<in> cpt_p_mod"

| CptPModWhile1: 
  "\<lbrakk> (Some P, s)#xs \<in> cpt_p_mod; s \<in> b; zs=map (lift (AnnWhile r b P)) xs \<rbrakk> 
  \<Longrightarrow> (Some(AnnWhile r b P), s)#(Some(AnnSeq P (AnnWhile r b P)), s)#zs \<in> cpt_p_mod"
| CptPModWhile2: 
  "\<lbrakk> (Some P, s)#xs \<in> cpt_p_mod; fst(last ((Some P, s)#xs))=None; s \<in> b; 
  zs=(map (lift (AnnWhile r b P)) xs)@ys; 
  (Some(AnnWhile r b P), snd(last ((Some P, s)#xs)))#ys \<in> cpt_p_mod\<rbrakk> 
  \<Longrightarrow> (Some(AnnWhile r b P), s)#(Some(AnnSeq P (AnnWhile r b P)), s)#zs \<in> cpt_p_mod"

lemma list_eq_if [rule_format]: 
  "\<forall>ys. xs=ys \<longrightarrow> (length xs = length ys) \<longrightarrow> (\<forall>i<length xs. xs!i=ys!i)"
  by (induct xs) auto

lemma list_eq: "(length xs = length ys \<and> (\<forall>i<length xs. xs!i=ys!i)) = (xs=ys)"
apply(rule iffI)
 apply clarify
 apply(erule nth_equalityI)
 apply simp+
done

lemma nth_tl: "\<lbrakk> ys!0=a; ys\<noteq>[] \<rbrakk> \<Longrightarrow> ys=(a#(tl ys))"
  by (cases ys) simp_all

lemma nth_tl_if [rule_format]: "ys\<noteq>[] \<longrightarrow> ys!0=a \<longrightarrow> P ys \<longrightarrow> P (a#(tl ys))"
  by (induct ys) simp_all

lemma nth_tl_onlyif [rule_format]: "ys\<noteq>[] \<longrightarrow> ys!0=a \<longrightarrow> P (a#(tl ys)) \<longrightarrow> P ys"
  by (induct ys) simp_all

lemma seq_not_eq1: "AnnSeq c1 c2\<noteq>c1"
  by (induct c1) auto

lemma seq_not_eq2: "AnnSeq c1 c2\<noteq>c2"
  by (induct c2) auto

lemma if_not_eq1: "AnnCond r b c1 c2 \<noteq>c1"
  by (induct c1) auto

lemma if_not_eq2: "AnnCond r b c1 c2\<noteq>c2"
  by (induct c2) auto

lemmas seq_and_if_not_eq [simp] = seq_not_eq1 seq_not_eq2 
seq_not_eq1 [THEN not_sym] seq_not_eq2 [THEN not_sym] 
if_not_eq1 if_not_eq2 if_not_eq1 [THEN not_sym] if_not_eq2 [THEN not_sym]

lemma prog_not_eq_in_ctran_aux:
  assumes c: "(P,s) -c\<rightarrow> (Q,t)"
  shows "P\<noteq>Q" using c
  by (induct x1 \<equiv> "(P,s)" x2 \<equiv> "(Q,t)" arbitrary: P s Q t) auto

lemma prog_not_eq_in_ctran [simp]: "\<not> (P,s) -c\<rightarrow> (P,t)"
apply clarify
apply(drule prog_not_eq_in_ctran_aux)
apply simp
  done

lemma tl_in_cptn: "\<lbrakk> a#xs \<in>cpts_p; xs\<noteq>[] \<rbrakk> \<Longrightarrow> xs\<in>cpts_p"
  by (force elim: cpts_p.cases)

lemma tl_zero[rule_format]: 
  "P (ys!Suc j) \<longrightarrow> Suc j<length ys \<longrightarrow> ys\<noteq>[] \<longrightarrow> P (tl(ys)!j)"
  by (induct ys) simp_all

subsection \<open>Equivalence of Sequential and Modular Definitions of Programs.\<close>

lemma last_length: "((a#xs)!(length xs))=last (a#xs)"
  by (induct xs) auto

lemma div_seq [rule_format]: "list \<in> cpt_p_mod \<Longrightarrow>
 (\<forall>s P Q zs. list=(Some (AnnSeq P Q), s)#zs \<longrightarrow>
  (\<exists>xs. (Some P, s)#xs \<in> cpt_p_mod  \<and> (zs=(map (lift Q) xs) \<or>
  ( fst(((Some P, s)#xs)!length xs)=None \<and> 
  (\<exists>ys. (Some Q, snd(((Some P, s)#xs)!length xs))#ys \<in> cpt_p_mod  
  \<and> zs=(map (lift (Q)) xs)@ys)))))"
apply(erule cpt_p_mod.induct)
apply simp_all
    apply clarify
    apply(force intro:CptPModOne)
   apply clarify
   apply(erule_tac x=Pa in allE)
   apply(erule_tac x=Q in allE)
   apply simp
   apply clarify
   apply(erule disjE)
    apply(rule_tac x="(Some Pa,t)#xsa" in exI)
    apply(rule conjI)
     apply clarify
     apply(erule CptPModEnv)
    apply(rule disjI1)
    apply(simp add:lift_def)
   apply clarify
   apply(rule_tac x="(Some Pa,t)#xsa" in exI)
   apply(rule conjI)
    apply(erule CptPModEnv)
   apply(rule disjI2)
   apply(rule conjI)
    apply(case_tac xsa,simp,simp)
   apply(rule_tac x="ys" in exI)
   apply(rule conjI)
    apply simp
   apply(simp add:lift_def)
  apply clarify
  apply(erule ptran.cases,simp_all)
 apply clarify
 apply(rule_tac x="xs" in exI)
 apply simp
 apply clarify
apply(rule_tac x="xs" in exI)
apply(simp add: last_length)
done


lemma cpts_onlyif_cpt_p_mod_aux [rule_format]:
  "\<forall>s Q t xs .((Some a, s), (Q, t)) \<in> ptran \<longrightarrow> (Q, t) # xs \<in> cpt_p_mod 
  \<longrightarrow> (Some a, s) # (Q, t) # xs \<in> cpt_p_mod"
apply(induct a)
apply simp_all
(*basic*)
apply clarify
apply(erule ptran.cases,simp_all)
apply(rule CptPModNone,rule Basic,simp)
apply clarify
apply(erule ptran.cases,simp_all)
(*Seq1*)
apply(rule_tac xs="[(None,t)]" in CptPModSeq2)
  apply(erule CptPModNone)
  apply(rule CptPModOne)
 apply simp
apply simp
apply(simp add:lift_def)
(*Seq2*)
apply(erule_tac x=s in allE)
apply(erule_tac x="Some P2" in allE)
apply(erule allE,erule impE, assumption)
apply(drule div_seq,simp)
apply clarify
apply(erule disjE)
 apply clarify
 apply(erule allE,erule impE, assumption)
 apply(erule_tac CptPModSeq1)
 apply(simp add:lift_def)
apply clarify 
apply(erule allE,erule impE, assumption)
apply(erule_tac CptPModSeq2)
  apply (simp add:last_length)
 apply (simp add:last_length)
apply(simp add:lift_def)
(*Cond*)
apply clarify
apply(erule ptran.cases,simp_all)
apply(force elim: CptPModCondT)
apply(force elim: CptPModCondF)
(*While*)
apply  clarify
apply(erule ptran.cases,simp_all)
apply(rule CptPModNone,erule WhileF,simp)
apply(drule div_seq,force)
apply clarify
apply (erule disjE)
 apply(force elim:CptPModWhile1)
apply clarify
apply(force simp add:last_length elim:CptPModWhile2)
(*await*)
apply clarify
apply(erule ptran.cases,simp_all)
apply(rule CptPModNone,erule Await,simp+)
(*nondt*)
apply clarify
apply(erule ptran.cases,simp_all)
apply(rule CptPModNone,erule Nondt,simp+)
done

lemma cpts_onlyif_cpt_p_mod [rule_format]: "c \<in> cpts_p \<Longrightarrow> c \<in> cpt_p_mod"
apply(erule cpts_p.induct)
  apply(rule CptPModOne)
 apply(erule CptPModEnv)
apply(case_tac P)
 apply simp
 apply(erule ptran.cases,simp_all)
apply(force elim:cpts_onlyif_cpt_p_mod_aux)
done

lemma lift_is_cptn: "c\<in>cpts_p \<Longrightarrow> map (lift P) c \<in> cpts_p"
apply(erule cpts_p.induct)
  apply(force simp add:lift_def CptsPOne)
 apply(force intro:CptsPEnv simp add:lift_def)
apply(force simp add:lift_def intro:CptsPComp Seq2 Seq1 elim:ptran.cases)
done

lemma cptn_append_is_cptn [rule_format]: 
 "\<forall>b a. b#c1\<in>cpts_p \<longrightarrow>  a#c2\<in>cpts_p \<longrightarrow> (b#c1)!length c1=a \<longrightarrow> b#c1@c2\<in>cpts_p"
apply(induct c1)
 apply simp
apply clarify
apply(erule cpts_p.cases,simp_all)
 apply(force intro:CptsPEnv)
apply(force elim:CptsPComp)
done

lemma last_lift: "\<lbrakk>xs\<noteq>[]; fst(xs!(length xs - (Suc 0)))=None\<rbrakk> 
 \<Longrightarrow> fst((map (lift P) xs)!(length (map (lift P) xs)- (Suc 0)))=(Some P)"
  by (cases "(xs ! (length xs - (Suc 0)))") (simp add:lift_def)

lemma last_fst [rule_format]: "P((a#x)!length x) \<longrightarrow> \<not>P a \<longrightarrow> P (x!(length x - (Suc 0)))" 
  by (induct x) simp_all

lemma last_fst_esp: 
 "fst(((Some a,s)#xs)!(length xs))=None \<Longrightarrow> fst(xs!(length xs - (Suc 0)))=None" 
apply(erule last_fst)
apply simp
done

lemma last_snd: "xs\<noteq>[] \<Longrightarrow> 
  snd(((map (lift P) xs))!(length (map (lift P) xs) - (Suc 0)))=snd(xs!(length xs - (Suc 0)))"
  by (cases "(xs ! (length xs - (Suc 0)))") (simp_all add:lift_def)

lemma Cons_lift: "(Some (AnnSeq P Q), s) # (map (lift Q) xs) = map (lift Q) ((Some P, s) # xs)"
  by (simp add:lift_def)

lemma Cons_lift_append: 
  "(Some (AnnSeq P Q), s) # (map (lift Q) xs) @ ys = map (lift Q) ((Some P, s) # xs)@ ys "
  by (simp add:lift_def)

lemma lift_nth: "i<length xs \<Longrightarrow> map (lift Q) xs ! i = lift Q  (xs! i)"
  by (simp add:lift_def)

lemma snd_lift: "i< length xs \<Longrightarrow> snd(lift Q (xs ! i))= snd (xs ! i)"
  by (cases "xs!i") (simp add:lift_def)

lemma cpts_if_cpt_p_mod: "c \<in> cpt_p_mod \<Longrightarrow> c \<in> cpts_p"
apply(erule cpt_p_mod.induct)
        apply(rule CptsPOne)
       apply(erule CptsPEnv)
      apply(erule CptsPComp,simp)
     apply(rule CptsPComp)
      apply(erule CondT,simp)
    apply(rule CptsPComp)
     apply(erule CondF,simp)
(*Seq1*)
apply(erule cpts_p.cases,simp_all)
  apply(rule CptsPOne)
 apply clarify
 apply(drule_tac P=P1 in lift_is_cptn)
 apply(simp add:lift_def)
 apply(rule CptsPEnv,simp)
apply clarify
apply(simp add:lift_def)
apply(rule conjI)
 apply clarify
 apply(rule CptsPComp)
  apply(rule Seq1,simp)
 apply(drule_tac P=P1 in lift_is_cptn)
 apply(simp add:lift_def)
apply clarify
apply(rule CptsPComp)
 apply(rule Seq2,simp)
apply(drule_tac P=P1 in lift_is_cptn)
apply(simp add:lift_def)
(*Seq2*)
apply(rule cptn_append_is_cptn)
  apply(drule_tac P=P1 in lift_is_cptn)
  apply(simp add:lift_def)
 apply simp
apply(simp split: if_split_asm)
apply(frule_tac P=P1 in last_lift)
 apply(rule last_fst_esp)
 apply (simp add:last_length)
apply(simp add:Cons_lift lift_def split_def last_conv_nth)
(*While1*)
apply(rule CptsPComp)
 apply(rule WhileT,simp)
apply(drule_tac P="AnnWhile r b P" in lift_is_cptn)
apply(simp add:lift_def)
(*While2*)
apply(rule CptsPComp)
 apply(rule WhileT,simp)
apply(rule cptn_append_is_cptn)
  apply(drule_tac P="AnnWhile r b P" in lift_is_cptn)
  apply(simp add:lift_def)
 apply simp
apply(simp split: if_split_asm)
apply(frule_tac P="AnnWhile r b P" in last_lift)
 apply(rule last_fst_esp,simp add:last_length)
apply(simp add:Cons_lift lift_def split_def last_conv_nth)
done

theorem cpts_iff_cpt_p_mod: "(c \<in> cpts_p) = (c \<in> cpt_p_mod)"
apply(rule iffI)
 apply(erule cpts_onlyif_cpt_p_mod)
apply(erule cpts_if_cpt_p_mod)
  done


end