theory PiCore_RG_IFS
  imports PiCore_IFS "PiCore/PiCore_Hoare"
begin

print_locale event_hoare

locale PiCore_RG_IFS_Validity = event_hoare ptran petran fin_com cpts_p cpts_of_p prog_validity ann_preserves_p assume_p commit_p preserves_p rghoare_p
for ptran :: "'Env \<Rightarrow> (('prog \<times> 's) \<times> 'prog \<times> 's) set" 
and petran :: "'Env \<Rightarrow> ('s,'prog) pconf \<Rightarrow> ('s,'prog) pconf \<Rightarrow> bool"   ("_ \<turnstile> _ -pe\<rightarrow> _" [81,81,81] 80)
and fin_com :: "'prog"
and cpts_p :: "'Env \<Rightarrow> ('s,'prog) pconfs set"
and cpts_of_p :: "'Env \<Rightarrow> 'prog \<Rightarrow> 's \<Rightarrow> (('s,'prog) pconfs) set"
and prog_validity :: "'Env \<Rightarrow> 'prog \<Rightarrow> 's set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> 's set \<Rightarrow> bool" 
                 ("_ \<Turnstile> _ sat\<^sub>p [_, _, _, _]" [60,60,0,0,0,0] 45)
and ann_preserves_p :: "'prog \<Rightarrow> 's \<Rightarrow> bool"
and assume_p :: "'Env \<Rightarrow> ('s set \<times> ('s \<times> 's) set) \<Rightarrow> (('s,'prog) pconfs) set"
and commit_p :: "'Env \<Rightarrow> (('s \<times> 's) set \<times> 's set) \<Rightarrow> (('s,'prog) pconfs) set"
and preserves_p :: "(('s,'prog) pconfs) set"
and rghoare_p :: "'Env \<Rightarrow> ['prog, 's set, ('s \<times> 's) set, ('s \<times> 's) set, 's set] \<Rightarrow> bool"
    ("_ \<turnstile> _ sat\<^sub>p [_, _, _, _]" [60,60,0,0,0,0] 45)
+
fixes   interference :: "'d \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<leadsto> _)" [70,71] 60)
   and  vpeq ::  "'s \<Rightarrow> 'd \<Rightarrow> 's \<Rightarrow> bool" ("(_ \<sim>_\<sim> _)" [70,69,70] 60)
   and  dome :: "'s  \<Rightarrow> ('l,'k,'s, 'prog) event \<Rightarrow> 'd"
 assumes  vpeq_transitive : "\<forall> a b c u. (a \<sim> u \<sim> b) \<and> (b \<sim> u \<sim> c) \<longrightarrow> (a \<sim> u \<sim> c)"
    and   vpeq_symmetric : "\<forall> a b u. (a \<sim> u \<sim> b) \<longrightarrow> (b \<sim> u \<sim> a)"
    and   vpeq_reflexive : "\<forall> a u. (a \<sim> u \<sim> a)"
begin

definition noninterf1 :: "'d \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<setminus>\<leadsto>\<^sub>v _)" [70,71] 60)
  where "u \<setminus>\<leadsto>\<^sub>v v \<equiv> \<not> (u \<leadsto> v)"

subsection \<open>local_respect program\<close>

definition local_respect_p1 :: "'Env \<Rightarrow> 'prog \<Rightarrow> ('l, 'k, 's,'prog) event \<Rightarrow> bool"
  where  "local_respect_p1 \<Gamma> P ev \<equiv> \<forall> s P' s' u. ann_preserves_p P s \<and> 
         (dome s ev) \<setminus>\<leadsto>\<^sub>v u \<and> (\<Gamma> \<turnstile> (P, s) -c\<rightarrow> (P', s')) \<longrightarrow> s \<sim>u\<sim> s'"

definition local_respect_p2 :: "'Env \<Rightarrow> 'prog \<Rightarrow> 'prog set \<Rightarrow> bool"
  where "local_respect_p2 \<Gamma> P \<S> \<equiv>  (\<forall> s P' s'. ann_preserves_p P s 
         \<and> (\<Gamma> \<turnstile> (P, s) -c\<rightarrow> (P', s')) \<longrightarrow> P' \<in> \<S>)"

definition local_respect_p :: "'Env \<Rightarrow> 'prog set \<Rightarrow> ('l, 'k, 's,'prog) event \<Rightarrow> bool"
  where "local_respect_p \<Gamma> \<S> ev \<equiv> \<forall>P \<in> \<S>. local_respect_p1 \<Gamma> P ev \<and> local_respect_p2 \<Gamma> P \<S>"

lemma local_respect_p_union: "\<lbrakk> local_respect_p \<Gamma> \<S> ev; local_respect_p \<Gamma> \<S>' ev \<rbrakk> \<Longrightarrow> local_respect_p \<Gamma> (\<S> \<union> \<S>') ev"
  apply (simp add: local_respect_p_def, clarify)
  apply (case_tac "P \<in> \<S>", simp)
   apply (meson UnI1 local_respect_p2_def)
  by (metis UnE UnI2 local_respect_p2_def)

lemma local_respect_p_insert: "\<lbrakk>local_respect_p \<Gamma> \<S> ev; local_respect_p1 \<Gamma> P ev; 
                                  local_respect_p2 \<Gamma> P (\<S> \<union> {P})\<rbrakk> \<Longrightarrow> local_respect_p \<Gamma>(\<S> \<union> {P}) ev"
  apply (simp add: local_respect_p_def)
  apply (case_tac "P \<in> \<S>")
  apply (simp add: insert_absorb)
  by (meson insertCI local_respect_p2_def)

definition lr_p :: "'Env \<Rightarrow> 'prog \<Rightarrow> ('l, 'k, 's, 'prog) event \<Rightarrow> bool" ("_ \<turnstile>\<^sub>l\<^sub>r _ sat\<^sub>p _" [60,60, 60] 45)
  where "lr_p \<Gamma> P ev = (\<exists>\<S>.  P \<in> \<S> \<and> local_respect_p \<Gamma> \<S> ev)"

subsection \<open>local_respect event\<close>

definition local_respect_e1 :: "'Env \<Rightarrow> ('l, 'k, 's,'prog) event \<Rightarrow> ('l, 'k, 's,'prog) event \<Rightarrow> bool"
  where "local_respect_e1 \<Gamma> e ev \<equiv> \<forall>s x e' s' x' u t.  ann_preserves_e e s 
  \<and> (dome s ev) \<setminus>\<leadsto>\<^sub>v u \<and> (\<Gamma> \<turnstile> (e, s, x) -et-t\<rightarrow> (e', s', x')) \<longrightarrow> s \<sim>u\<sim> s'"

definition local_respect_e2 :: "'Env \<Rightarrow> ('l, 'k, 's, 'prog) event \<Rightarrow> ('l, 'k, 's, 'prog) event set \<Rightarrow> bool"
  where "local_respect_e2 \<Gamma> e \<S> \<equiv> \<forall>x s t e' s' x'. ann_preserves_e e s 
         \<and> (\<Gamma> \<turnstile> (e, s, x) -et-t\<rightarrow> (e', s', x')) \<longrightarrow> e' \<in> \<S>"

definition local_respect_e :: "'Env \<Rightarrow> ('l, 'k, 's, 'prog) event set \<Rightarrow> ('l, 'k, 's, 'prog) event \<Rightarrow> bool" where
  "local_respect_e \<Gamma> \<S> ev \<equiv> \<forall>e \<in> \<S>. local_respect_e1 \<Gamma> e ev \<and> local_respect_e2 \<Gamma> e \<S>"

lemma local_respect_e_union: "\<lbrakk> local_respect_e \<Gamma> \<S> ev; local_respect_e \<Gamma> \<S>' ev \<rbrakk> \<Longrightarrow> 
                                 local_respect_e \<Gamma> (\<S> \<union> \<S>') ev"
  apply (simp add: local_respect_e_def, clarify)
  apply (case_tac "e \<in> \<S>")
  using local_respect_e2_def apply fastforce
  using local_respect_e2_def by fastforce


lemma local_respect_e_insert: "\<lbrakk>local_respect_e \<Gamma> \<S> ev; local_respect_e1 \<Gamma> e ev; 
                                 local_respect_e2 \<Gamma> e (\<S> \<union> {e})\<rbrakk>  \<Longrightarrow> local_respect_e \<Gamma> (\<S> \<union> {e}) ev"
  apply (simp add: local_respect_e_def, clarify)
  using local_respect_e2_def by fastforce

definition Prog_Trans_Anony :: "'prog set \<Rightarrow> ('l, 'k, 's, 'prog) event set"
  where "Prog_Trans_Anony \<S> \<equiv> {ev. \<exists>P. P \<in> \<S> \<and> ev = AnonyEvent P}"

lemma Prog_Trans_Anony_Respect_aux1 : "local_respect_p1 \<Gamma> P ev  \<Longrightarrow> 
                                       local_respect_e1 \<Gamma> (AnonyEvent P) ev"
  apply  (simp add: local_respect_p1_def local_respect_e1_def, clarify)
  apply (case_tac e', clarify)
   apply (drule_tac a = s and b = x1 and c = s' and d = u  in all4_impD)
    apply (simp add: etran.simps, simp)
  by (meson no_tran2basic)
  
lemma Prog_Trans_Anony_Respect_aux2 : "local_respect_p2 \<Gamma> P \<S> \<Longrightarrow> 
                                       local_respect_e2 \<Gamma> (AnonyEvent P) (Prog_Trans_Anony \<S>)"
  apply (simp add: local_respect_p2_def local_respect_e2_def, clarsimp)
  apply (case_tac "e'", simp add: Prog_Trans_Anony_def)
   apply (erule etran.cases, simp_all)
   apply meson
  by (meson no_tran2basic)
  

lemma Prog_Trans_Anony_Respect: "\<lbrakk>P \<in> \<S>; local_respect_p \<Gamma> \<S> ev \<rbrakk> \<Longrightarrow> 
                         local_respect_e \<Gamma> (Prog_Trans_Anony \<S>) ev"
  apply (simp add: local_respect_p_def  local_respect_e_def Prog_Trans_Anony_def, clarify)
  apply (rule conjI, simp add: local_respect_e1_def, clarify)
   apply (erule etran.cases, simp add: local_respect_p1_def)
   apply blast
  using Prog_Trans_Anony_Respect_aux2 Prog_Trans_Anony_def by auto


lemma lr_e_Anony: "\<lbrakk>\<Gamma> \<turnstile>\<^sub>l\<^sub>r P sat\<^sub>p ev\<rbrakk> \<Longrightarrow> \<exists>\<S>. (AnonyEvent P) \<in> \<S> \<and> local_respect_e \<Gamma> \<S> ev"
  apply (simp add: lr_p_def, clarify)
  apply (rule_tac x = "(Prog_Trans_Anony \<S>)" in exI)
  apply (rule conjI, simp add: Prog_Trans_Anony_def)
  using Prog_Trans_Anony_Respect by blast


lemma lr_e_Basic: "\<lbrakk>ev = BasicEvent e; \<Gamma> \<turnstile>\<^sub>l\<^sub>r body e sat\<^sub>p ev\<rbrakk> \<Longrightarrow> \<exists>\<S>. ev \<in> \<S> \<and> local_respect_e \<Gamma> \<S> ev"
  apply (drule lr_e_Anony, erule exE)
  apply (rule_tac x = "\<S> \<union> {ev}" in exI)
  apply (rule conjI, simp)
  apply (rule local_respect_e_insert, simp)
   apply (simp add: local_respect_e1_def)
  apply (simp add: etran.simps vpeq_reflexive)
  apply (simp add: local_respect_e2_def)
  by (metis ent_spec2' noevtent_notran)

lemma lr_e_Basic1: "\<lbrakk>is_basicevt ev; \<Gamma> \<turnstile>\<^sub>l\<^sub>r the (body_e ev) sat\<^sub>p ev\<rbrakk> \<Longrightarrow> \<exists>\<S>. ev \<in> \<S> \<and> local_respect_e \<Gamma> \<S> ev"
proof-
  assume a0: "is_basicevt ev"
    and  a1: "\<Gamma> \<turnstile>\<^sub>l\<^sub>r the (body_e ev) sat\<^sub>p ev"
  from a0 have "\<exists>e. ev = BasicEvent e" 
    by (metis event.exhaust is_basicevt.simps(1))
  then obtain e where b0: "ev = BasicEvent e" by auto
  with a1 have "\<Gamma> \<turnstile>\<^sub>l\<^sub>r body e sat\<^sub>p ev" by simp
  with b0 show ?thesis
    by (rule_tac e = e in lr_e_Basic, simp_all)
qed

lemma local_respect_event : "\<lbrakk>getspc_e c \<in> \<S> ; local_respect_e \<Gamma> \<S> ev; ann_preserves_e (getspc_e c) (gets_e c); 
                               \<exists>t. \<Gamma> \<turnstile> c -et-t\<rightarrow> c'\<rbrakk>  \<Longrightarrow> getspc_e c' \<in> \<S>"
  apply (case_tac "c", case_tac c', simp add: getspc_e_def gets_e_def)
  using local_respect_e2_def local_respect_e_def by blast

lemma local_next_state : "\<lbrakk>e \<in> \<S> \<and> local_respect_e \<Gamma> \<S> ev; ann_preserves_e e s;
      (dome s ev) \<setminus>\<leadsto>\<^sub>v u; \<Gamma> \<turnstile> (e, s, x) -et-t\<rightarrow> (e', s', x')\<rbrakk> \<Longrightarrow> s \<sim>u\<sim> s'"
  apply (simp add: local_respect_e_def, clarify)
  using local_respect_e1_def by blast

lemma local_respect_forall : "\<lbrakk>e \<in> \<S> ; local_respect_e \<Gamma> \<S> ev; el \<in> cpts_ev \<Gamma> ; getspc_e (el!0) = e; 
        el \<in> preserves_e; i < length el\<rbrakk> \<Longrightarrow> getspc_e (el ! i) \<in> \<S>"
  apply (induct i, simp add: cpts_of_ev_def getspc_e_def)
  apply (case_tac "getspc_e (el ! i) = getspc_e (el ! Suc i)", simp)
  apply (simp add: preserves_e_def)
  by (meson Suc_lessD local_respect_event notran_confeqi)

subsection \<open>step consistent program\<close>

definition step_consistent_p1 :: "'Env \<Rightarrow> 'prog \<Rightarrow> ('l, 'k, 's, 'prog) event \<Rightarrow> bool" 
  where "step_consistent_p1 \<Gamma> P ev \<equiv> \<forall> P1' P2' s1 s2 s1' s2'  u. 
         ann_preserves_p P s1 \<and> ann_preserves_p P s2 \<and> s1 \<sim>u\<sim> s2 \<and> ((dome s1 ev) \<leadsto> u 
          \<longrightarrow> s1 \<sim>(dome s1  ev)\<sim> s2) \<and> (\<Gamma> \<turnstile> (P, s1) -c\<rightarrow> (P1', s1')) \<and> (\<Gamma> \<turnstile> (P, s2) -c\<rightarrow> (P2', s2')) 
          \<longrightarrow> s1' \<sim>u\<sim> s2'"

lemma step_consistent_p1_eq : "\<forall> P1' P2' s1 s2 s1' s2'  u. 
         ann_preserves_p P s1 \<and> ann_preserves_p P s2 \<and> s1 \<sim>u\<sim> s2 \<and> ((dome s1  ev) \<leadsto> u 
          \<longrightarrow> s1 \<sim>(dome s1 ev)\<sim> s2) \<and> (\<Gamma> \<turnstile> (P, s1) -c\<rightarrow> (P1', s1')) \<and> (\<Gamma> \<turnstile> (P, s2) -c\<rightarrow> (P2', s2')) 
          \<longrightarrow> s1' \<sim>u\<sim> s2' \<Longrightarrow> step_consistent_p1 \<Gamma> P ev"
  using step_consistent_p1_def by blast

definition step_consistent_p2 :: "'Env \<Rightarrow> 'prog \<Rightarrow> 'prog set \<Rightarrow> bool"
  where "step_consistent_p2 \<Gamma> P \<S> \<equiv> \<forall>P1' s1 s1'. ann_preserves_p P s1 \<and> (\<Gamma> \<turnstile> (P, s1) -c\<rightarrow> (P1', s1')) \<longrightarrow> P1' \<in> \<S>"


definition step_consistent_p :: "'Env \<Rightarrow> 'prog set \<Rightarrow> ('l, 'k, 's,'prog) event \<Rightarrow> bool"
  where "step_consistent_p \<Gamma> \<S> ev \<equiv> \<forall>P \<in> \<S>. step_consistent_p1 \<Gamma> P ev \<and> step_consistent_p2 \<Gamma> P \<S>"


lemma step_consistent_p_union: "\<lbrakk>step_consistent_p \<Gamma> \<S> ev; step_consistent_p \<Gamma> \<S>' ev \<rbrakk> \<Longrightarrow> step_consistent_p \<Gamma> (\<S> \<union> \<S>') ev"
  apply (simp add: step_consistent_p_def, clarify)
  apply (case_tac "P \<in> \<S>", simp)
   apply (meson UnI1 step_consistent_p2_def)
  by (metis UnE UnI2 step_consistent_p2_def)

lemma step_consistent_p_insert: "\<lbrakk>step_consistent_p \<Gamma> \<S> ev; step_consistent_p1 \<Gamma> P ev; 
                                  step_consistent_p2 \<Gamma> P (\<S> \<union> {P})\<rbrakk> \<Longrightarrow>  step_consistent_p \<Gamma> (\<S> \<union> {P}) ev"
  apply (simp add: step_consistent_p_def)
  apply (case_tac "P \<in> \<S>")
   apply (simp add: insert_absorb)
  by (meson insertCI step_consistent_p2_def)

definition sc_p :: "'Env \<Rightarrow> 'prog \<Rightarrow> ('l, 'k, 's, 'prog) event \<Rightarrow> bool" ("_ \<turnstile>\<^sub>s\<^sub>c _ sat\<^sub>p _" [60,60,60] 45)
  where "sc_p \<Gamma> P ev = (\<exists>\<S>.  P \<in> \<S> \<and> step_consistent_p \<Gamma> \<S> ev)"

subsection \<open>step consistent event\<close>

definition step_consistent_e1 :: "'Env \<Rightarrow> ('l, 'k, 's, 'prog) event \<Rightarrow> ('l, 'k, 's, 'prog) event \<Rightarrow> bool"
  where "step_consistent_e1 \<Gamma> e ev \<equiv> \<forall>e1' e2' s1 s2 x1 x2 s1' s2' x1' x2' u t. 
  (ann_preserves_e e s1 \<and> ann_preserves_e e s2 \<and> s1 \<sim>u\<sim> s2 \<and> ((dome s1  ev) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1  ev)\<sim> s2) 
  \<and> (\<Gamma> \<turnstile> (e, s1, x1) -et-t\<rightarrow> (e1', s1', x1')) \<and> (\<Gamma> \<turnstile> (e, s2, x2) -et-t\<rightarrow> (e2', s2', x2')) \<longrightarrow>
   s1' \<sim>u\<sim> s2')"

lemma step_consistent_e1_eq : "\<forall>e1' e2' s1 s2 x1 x2 s1' s2' x1' x2' u t. 
  ann_preserves_e e s1 \<and> ann_preserves_e e s2 \<and> s1 \<sim>u\<sim> s2 \<and> ((dome s1  ev) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1 ev)\<sim> s2) 
  \<and> (\<Gamma> \<turnstile> (e, s1, x1) -et-t\<rightarrow> (e1', s1', x1')) \<and> (\<Gamma> \<turnstile> (e, s2, x2) -et-t\<rightarrow> (e2', s2', x2')) \<longrightarrow>
   s1' \<sim>u\<sim> s2' \<Longrightarrow> step_consistent_e1 \<Gamma> e ev"
  using step_consistent_e1_def by blast

definition step_consistent_e2 :: "'Env \<Rightarrow> ('l, 'k, 's, 'prog) event \<Rightarrow> ('l, 'k, 's, 'prog) event set \<Rightarrow> bool"
  where "step_consistent_e2 \<Gamma> e \<S> \<equiv>  \<forall>x1 s1 t e1' s1' x1'. ann_preserves_e e s1 \<and> 
         (\<Gamma> \<turnstile> (e, s1, x1) -et-t\<rightarrow> (e1', s1', x1')) \<longrightarrow> e1' \<in> \<S>"


definition step_consistent_e :: "'Env \<Rightarrow> ('l, 'k, 's, 'prog) event set \<Rightarrow> ('l, 'k, 's, 'prog) event \<Rightarrow> bool" where
  "step_consistent_e \<Gamma> \<S> ev \<equiv> \<forall>e \<in> \<S>. step_consistent_e1 \<Gamma> e ev \<and> step_consistent_e2 \<Gamma> e \<S>"


lemma step_consistent_e_union: "\<lbrakk> step_consistent_e \<Gamma> \<S> ev; step_consistent_e \<Gamma> \<S>' ev \<rbrakk> \<Longrightarrow> 
                                 step_consistent_e \<Gamma> (\<S> \<union> \<S>') ev"
  apply (simp add: step_consistent_e_def, clarify)
  apply (case_tac "e \<in> \<S>")
  using step_consistent_e2_def apply fastforce
  using step_consistent_e2_def by fastforce


lemma step_consistent_e_insert: "\<lbrakk>step_consistent_e \<Gamma> \<S> ev; step_consistent_e1 \<Gamma> e ev; 
                                 step_consistent_e2 \<Gamma> e (\<S> \<union> {e})\<rbrakk>  \<Longrightarrow> step_consistent_e \<Gamma> (\<S> \<union> {e}) ev"
  apply (simp add: step_consistent_e_def, clarify)
  using step_consistent_e2_def by fastforce


lemma Prog_Trans_Anony_Consistent_aux1 : "step_consistent_p1 \<Gamma> P ev  \<Longrightarrow> step_consistent_e1 \<Gamma> (AnonyEvent P) ev"
  apply  (simp add: step_consistent_p1_def)
  apply (rule step_consistent_e1_eq, clarify)
  apply (case_tac e1', case_tac e2')
    apply (drule_tac a = x1a and b = x1b and c = s1 and d = s2 and e = s1' in all5D)
    apply (drule_tac a = s2' and b = u in all2_impD)
  using ann_preserves_e.simps(1) etran.cases apply blast
    apply simp
  using no_tran2basic apply blast
  using no_tran2basic by blast


lemma Prog_Trans_Anony_Consistent_aux2 : "step_consistent_p2 \<Gamma> P \<S> \<Longrightarrow> 
                                          step_consistent_e2 \<Gamma> (AnonyEvent P) (Prog_Trans_Anony \<S>)"
  apply (simp add: step_consistent_p2_def step_consistent_e2_def, clarify)
  by (metis Prog_Trans_Anony_Respect_aux2 ann_preserves_e.simps(1) local_respect_e2_def local_respect_p2_def)

lemma Prog_Trans_Anony_Consistent: "\<lbrakk> P \<in> \<S>; step_consistent_p \<Gamma> \<S> ev \<rbrakk> \<Longrightarrow> 
                         step_consistent_e \<Gamma> (Prog_Trans_Anony \<S>) ev"
  apply (simp add: step_consistent_p_def step_consistent_e_def  Prog_Trans_Anony_def, clarify)
  apply (rule conjI, simp add: step_consistent_e1_def, clarify)
   apply (erule etran.cases, simp_all)
   apply (erule etran.cases, simp_all)
  using step_consistent_p1_def apply blast
  using Prog_Trans_Anony_Consistent_aux2 Prog_Trans_Anony_def by force


lemma sc_e_Anony: "\<lbrakk>\<Gamma> \<turnstile>\<^sub>s\<^sub>c P sat\<^sub>p ev\<rbrakk> \<Longrightarrow> \<exists>\<S>. (AnonyEvent P) \<in> \<S> \<and> step_consistent_e \<Gamma> \<S> ev"
  apply (simp add: sc_p_def, clarify)
  apply (rule_tac x = "(Prog_Trans_Anony \<S>)" in exI)
  apply (rule conjI, simp add: Prog_Trans_Anony_def)
  using Prog_Trans_Anony_Consistent by blast


lemma sc_e_Basic: "\<lbrakk>ev = BasicEvent e;  \<Gamma> \<turnstile>\<^sub>s\<^sub>c body e sat\<^sub>p ev\<rbrakk> \<Longrightarrow> \<exists>\<S>. ev \<in> \<S> \<and> step_consistent_e \<Gamma> \<S> ev"
  apply (drule sc_e_Anony, erule exE)
  apply (rule_tac x = "\<S> \<union> {ev}" in exI)
  apply (rule conjI, simp)
  apply (rule step_consistent_e_insert, simp)
   apply (simp add: step_consistent_e1_def)
  apply (metis ent_spec2' noevtent_notran)
  apply (simp add: step_consistent_e2_def)
  by (metis ent_spec2' noevtent_notran)

lemma sc_e_Basic1: "\<lbrakk>is_basicevt ev;  \<Gamma> \<turnstile>\<^sub>s\<^sub>c the (body_e ev) sat\<^sub>p ev\<rbrakk> \<Longrightarrow> \<exists>\<S>. ev \<in> \<S> \<and> step_consistent_e \<Gamma> \<S> ev"
proof-
  assume a0: "is_basicevt ev"
    and  a1: "\<Gamma> \<turnstile>\<^sub>s\<^sub>c the (body_e ev) sat\<^sub>p ev"
  from a0 have "\<exists>e. ev = BasicEvent e" 
    by (metis anonyevt_isnot_basic event.exhaust is_anonyevt.simps(1))
  then obtain e where b0: "ev = BasicEvent e" by auto
  with a1 have "\<Gamma> \<turnstile>\<^sub>s\<^sub>c body e sat\<^sub>p ev" by simp
  with b0 show ?thesis
    by (rule_tac e = e in sc_e_Basic, simp_all)
qed

lemma consistent_next_event : "\<lbrakk>getspc_e c \<in> \<S> ; step_consistent_e \<Gamma> \<S> ev; ann_preserves_e (getspc_e c) (gets_e c); 
                               \<exists>t. \<Gamma> \<turnstile> c -et-t\<rightarrow> c'\<rbrakk>  \<Longrightarrow> getspc_e c' \<in> \<S>"
  apply (case_tac "c", case_tac c', simp add: step_consistent_e_def getspc_e_def gets_e_def)
  using step_consistent_e2_def by fastforce

lemma consistent_next_state : "\<lbrakk>e \<in> \<S> \<and> step_consistent_e \<Gamma> \<S> ev; ann_preserves_e e s1; ann_preserves_e e s2;
                                s1 \<sim>u\<sim> s2; (dome s1  ev) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1 ev)\<sim> s2; 
                                \<Gamma> \<turnstile> (e, s1, x1) -et-t\<rightarrow> (e1', s1', x1'); \<Gamma> \<turnstile> (e, s2, x2) -et-t\<rightarrow> (e2', s2', x2')\<rbrakk> 
                              \<Longrightarrow> s1' \<sim>u\<sim> s2'"
  apply (simp add: step_consistent_e_def, clarify)
  using step_consistent_e1_def by blast

lemma step_consistent_forall : "\<lbrakk>e \<in> \<S> ; step_consistent_e \<Gamma> \<S> ev; el \<in> cpts_ev \<Gamma>; getspc_e (el!0) = e; el \<in> preserves_e;
        i < length el\<rbrakk> \<Longrightarrow> getspc_e (el ! i) \<in> \<S>"
  apply (induct i, simp add: cpts_of_ev_def getspc_e_def)
  apply (case_tac "getspc_e (el ! i) = getspc_e (el ! Suc i)", simp)
  apply (rule_tac c = "el ! i" in consistent_next_event, simp_all)
   apply (simp add: preserves_e_def)
  using notran_confeqi by blast

end

print_locale InfoFlow

locale PiCore_RG_IFS = PiCore_RG_IFS_Validity ptran petran fin_com cpts_p cpts_of_p prog_validity ann_preserves_p
                       assume_p commit_p preserves_p rghoare_p interference vpeq dome
  for ptran :: "'Env \<Rightarrow> (('prog \<times> 's) \<times> 'prog \<times> 's) set"
  and petran :: "'Env \<Rightarrow> 'prog \<times> 's \<Rightarrow> 'prog \<times> 's \<Rightarrow> bool"  (\<open>_ \<turnstile> _ -pe\<rightarrow> _\<close> [81, 81, 81] 80)
  and fin_com :: "'prog"
  and cpts_p :: "'Env \<Rightarrow> ('prog \<times> 's) list set"
  and cpts_of_p :: "'Env \<Rightarrow> 'prog \<Rightarrow> 's \<Rightarrow> ('prog \<times> 's) list set"
  and prog_validity :: "'Env \<Rightarrow> 'prog \<Rightarrow> 's set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> 's set \<Rightarrow> bool"  (\<open>_ \<Turnstile> _ sat\<^sub>p [_, _, _, _]\<close> [60, 60, 0, 0, 0, 0] 45)
  and ann_preserves_p :: "'prog \<Rightarrow> 's \<Rightarrow> bool"
  and assume_p :: "'Env \<Rightarrow> 's set \<times> ('s \<times> 's) set \<Rightarrow> ('prog \<times> 's) list set"
  and commit_p :: "'Env \<Rightarrow> ('s \<times> 's) set \<times> 's set \<Rightarrow> ('prog \<times> 's) list set"
  and preserves_p :: "('prog \<times> 's) list set"
  and rghoare_p :: "'Env \<Rightarrow> 'prog \<Rightarrow> 's set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> 's set \<Rightarrow> bool"  (\<open>_ \<turnstile> _ sat\<^sub>p [_, _, _, _]\<close> [60, 60, 0, 0, 0, 0] 45)
  and interference :: "'d \<Rightarrow> 'd \<Rightarrow> bool"  (\<open>(_ \<leadsto> _)\<close> [70, 71] 60)
  and vpeq :: "'s \<Rightarrow> 'd \<Rightarrow> 's \<Rightarrow> bool"  (\<open>(_ \<sim>_\<sim> _)\<close> [70, 69, 70] 60)
  and dome :: "'s \<Rightarrow> ('l, 'k, 's, 'prog) event \<Rightarrow> 'd" +
fixes \<Gamma> :: 'Env and
      C0 :: "('l,'k,'s, 'prog) pesconf"
  and step :: "('l,'k,'s, 'prog, 'd) action \<Rightarrow> (('l,'k,'s, 'prog) pesconf \<times> ('l,'k,'s, 'prog) pesconf) set"
  and obs :: "'s \<Rightarrow> 'd \<Rightarrow> 'o" (infixl "\<guillemotright>"  55)
  and pesf :: "('l,'k,'s, 'prog) rgformula_par"
  and s0 :: "'s"
  and x0 :: "('l,'k,'s,'prog) x"
  and evtrgfs :: "('l,'k,'s, 'prog) event \<Rightarrow> 's rgformula option" (*a set of events and their rg conditions*)
  and spec_of_parsys :: "('l,'k,'s, 'prog) paresys"
  assumes C0_ParSys: "C0 = (paresys_spec pesf, s0, x0)"
    and   spec_of_parsys: "spec_of_parsys = paresys_spec pesf"
    and   all_evts_are_basic: "\<forall>ef\<in>all_evts pesf. is_basicevt (E\<^sub>e ef)"
    and   parsys_sat_rg: "\<forall>k. \<Gamma> \<turnstile> fst (pesf k) sat\<^sub>s [Pre\<^sub>e\<^sub>s (pesf k), Rely\<^sub>e\<^sub>s (pesf k), Guar\<^sub>e\<^sub>s (pesf k), Post\<^sub>e\<^sub>s (pesf k)]"
    and   parsys_sat_init: "\<forall>k. s0 \<in> Pre\<^sub>e\<^sub>s (pesf k)"
    and   parsys_rg_com: "\<forall>k j. j\<noteq>k \<longrightarrow>  Guar\<^sub>e\<^sub>s (pesf j) \<subseteq> Rely\<^sub>e\<^sub>s (pesf k)"
    and   evt_in_parsys_in_evtrgfs: "\<forall>erg \<in> all_evts pesf. the (evtrgfs (E\<^sub>e erg)) = snd erg"
    and   step_def : "step a \<equiv> {(P, Q). (\<Gamma> \<turnstile> P -pes-(actk a)\<rightarrow> Q) \<and> 
                                ((\<exists>e k. actk a = ((EvtEnt e)\<sharp>k) \<and> eventof a = e 
                                  \<and> dome (gets P)  e = domain a) \<or>
                                  (\<exists>c k. actk a = ((Cmd c)\<sharp>k) \<and> eventof a = (getx P) k 
                                  \<and> dome (gets P) (eventof a) = domain a))}"
begin

lemma parsys_sat: " \<Gamma> \<turnstile> pesf SAT [{s0}, {}, UNIV, UNIV]"
  by (rule ParallelESys, simp_all add: parsys_sat_rg  parsys_sat_init parsys_rg_com)

interpretation PiCore_IFS.InfoFlow ptran petran fin_com \<Gamma> C0 step interference vpeq obs dome
proof
  show " \<forall>a b c u. a \<sim>u\<sim> b \<and> b \<sim>u\<sim> c \<longrightarrow> a \<sim>u\<sim> c"
    using vpeq_transitive by fastforce
  show "\<forall>a b u. a \<sim>u\<sim> b \<longrightarrow> b \<sim>u\<sim> a"
    using vpeq_symmetric by force
  show "\<forall>a u. a \<sim>u\<sim> a"
    using vpeq_reflexive by blast
  show "\<And>a. step a \<equiv>
         {(P, Q). \<Gamma> \<turnstile> P -pes-actk a\<rightarrow> Q \<and>
         ((\<exists>e k. actk a = EvtEnt e\<sharp>k \<and> eventof a = e \<and> dome (gets P) e = domain a) \<or>
         (\<exists>c k. actk a = Cmd c\<sharp>k \<and> eventof a = getx P k \<and> dome (gets P) (eventof a) = domain a))}"
    using step_def by presburger
qed

lemma run_is_cpt: "\<forall>C1 C2 as. (C1,C2) \<in> runC as \<longrightarrow> 
            (\<exists>c. c\<in>cpts_pes \<Gamma> \<and> c!0 = C1 \<and> last c = C2 \<and> Suc (length as) = length c \<and>
                 (\<forall>j. Suc j < length c \<longrightarrow> (\<Gamma> \<turnstile> c!j-pes-(actk (as!j))\<rightarrow>c!Suc j)) )" 
  proof -
  {
    fix C2 as 
    have "\<forall>C1. (C1,C2) \<in> runC as \<longrightarrow> (\<exists>c. c\<in>cpts_pes \<Gamma> \<and> c!0 = C1 \<and> last c = C2 \<and> Suc (length as) = length c \<and>
                           (\<forall>j. Suc j < length c \<longrightarrow> (\<Gamma> \<turnstile> c!j-pes-(actk (as!j))\<rightarrow>c!Suc j)))"
      proof(induct as)
        case Nil
        show ?case
          proof -
          {
            fix C1
            assume a0: "(C1, C2) \<in> runC []"
            then have b1: "C1 = C2" by (simp add:runC_def)
            then have "[C1] \<in> cpts_pes \<Gamma>" by (metis cpts_pes.CptsPesOne prod_cases3) 
            moreover
            have "[C1]!0 = C1" by simp
            moreover
            from b1 have "last [C1] = C2" by simp
            ultimately have "(\<exists>c. c \<in> cpts_pes \<Gamma> \<and> c ! 0 = C1 \<and> last c = C2 \<and> Suc (length []) = length c \<and>
                           (\<forall>j. Suc j < length c \<longrightarrow> (\<Gamma> \<turnstile> c!j-pes-(actk ([]!j))\<rightarrow>c!Suc j)))" by auto
          }
          then show ?thesis by blast
          qed
      next
        case (Cons b bs)
        assume a0: "\<forall>C1. (C1, C2) \<in> runC bs \<longrightarrow> (\<exists>c. c \<in> cpts_pes \<Gamma> \<and> c ! 0 = C1 \<and> last c = C2 \<and> Suc (length bs) = length c \<and>
                           (\<forall>j. Suc j < length c \<longrightarrow> (\<Gamma> \<turnstile>c!j-pes-(actk (bs!j))\<rightarrow>c!Suc j)))"
        then show ?case
          proof -
          {
            fix C1
            assume b0: "(C1, C2) \<in> runC (b # bs)"
            then have "\<exists>R. (C1,R) \<in> step b \<and> (R,C2) \<in> runC bs"
              by (simp add:runC_def)
            then obtain R where b1: "(C1,R) \<in> step b \<and> (R,C2) \<in> runC bs" by auto
            with a0 have "\<exists>c. c \<in> cpts_pes \<Gamma> \<and> c ! 0 = R \<and> last c = C2 \<and> Suc (length bs) = length c \<and>
                           (\<forall>j. Suc j < length c \<longrightarrow> (\<Gamma> \<turnstile> c!j-pes-(actk (bs!j))\<rightarrow>c!Suc j))" by blast
            then obtain c where b2: "c \<in> cpts_pes \<Gamma>\<and> c ! 0 = R \<and> last c = C2 \<and> Suc (length bs) = length c \<and>
                           (\<forall>j. Suc j < length c \<longrightarrow> (\<Gamma> \<turnstile> c!j-pes-(actk (bs!j))\<rightarrow>c!Suc j))" by auto
            then obtain c' where b3: "c=R#c'"
              by (metis cpts_pes_not_empty hd_conv_nth list.exhaust list.sel(1)) 
            from b1 have b4: "\<Gamma> \<turnstile> C1 -pes-(actk b)\<rightarrow> R"
              by (simp add: step_def)
            with b2 b3 have b5: "(C1#c) \<in> cpts_pes \<Gamma>" 
              using pestran_cpts_pes by meson 
            from b2 have b6: "(C1#c)!0 = C1 \<and> last (C1#c) = C2 \<and> Suc (length (b#bs)) = length (C1#c)" by auto
            with b2 b4 have "\<forall>j. Suc j < length (C1#c) \<longrightarrow> (\<Gamma> \<turnstile> (C1#c)!j-pes-(actk ((b # bs)!j))\<rightarrow>(C1#c)!Suc j)"
              by (smt (verit) Zero_neq_Suc diff_Suc_1 length_Cons less_Suc_eq_0_disj nth_Cons')
            with b5 b6 have "\<exists>c. c \<in> cpts_pes \<Gamma> \<and> Suc (length (b # bs)) = length c \<and>
              c ! 0 = C1 \<and> last c = C2 \<and> (\<forall>j. Suc j < length c \<longrightarrow> \<Gamma> \<turnstile> c ! j -pes-actk ((b # bs) ! j)\<rightarrow> c ! Suc j)" 
              by auto
          }
          then show ?thesis by blast
          qed
      qed
  }
  then show ?thesis by auto
qed

lemma run_cpt_preserves: "\<lbrakk>l \<in> cpts_of_pes \<Gamma> (paresys_spec pesf) s0 x0; \<forall>i. Suc i < length l 
      \<longrightarrow> \<not> \<Gamma> \<turnstile> l ! i -pese\<rightarrow> l ! Suc i\<rbrakk> \<Longrightarrow> l \<in> preserves_pes"
  apply (subgoal_tac " \<Gamma> \<Turnstile> paresys_spec pesf SAT [{s0}, {}, UNIV, UNIV]")
   apply (simp add: pes_validity_def)
   apply (drule_tac a = s0 and b = x0 in all2D)
   apply (drule conjunct2)
   apply (drule_tac c = l in subsetD)
    apply (simp add: assume_pes_def gets_def cpts_of_pes_def, simp)
  apply (rule rgsound_pes)
  using parsys_sat by blast

lemma reachable_impl_cpts: "reachableC C1 C2 \<Longrightarrow> \<exists>c. c \<in> cpts_pes \<Gamma>\<and> c!0 = C1 \<and> last c = C2" 
  proof -
    assume "reachableC C1 C2"
    then have "\<exists>as. (C1,C2) \<in> runC as" by (simp add:reachableC_def)
    then obtain as where a1: "(C1,C2) \<in> runC as" by auto
    then show ?thesis using run_is_cpt by blast
  qed

lemma reachable0_impl_cpts: "reachableC0 C \<Longrightarrow> \<exists>c. c \<in> cpts_pes \<Gamma> \<and> c!0 = C0 \<and> last c = C"
  using reachable_impl_cpts reachableC0_def by simp

definition local_respect_events :: "bool" where
  "local_respect_events \<equiv> \<forall>ef. ef\<in>all_evts pesf \<longrightarrow> ( (\<Gamma> \<turnstile>\<^sub>l\<^sub>r the (body_e (E\<^sub>e ef)) sat\<^sub>p (E\<^sub>e ef)) \<or>
   (\<forall>u s1 s2. (s1, s2) \<in> Guar\<^sub>e ef \<longrightarrow> ((dome s1 (E\<^sub>e ef)) \<setminus>\<leadsto>\<^sub>v u \<longrightarrow> s1 \<sim>u\<sim> s2)))"

definition step_consistent_events :: "bool" where
  "step_consistent_events \<equiv> \<forall>ef. ef\<in>all_evts pesf  \<longrightarrow>\<Gamma> \<turnstile>\<^sub>s\<^sub>c the (body_e (E\<^sub>e ef)) sat\<^sub>p (E\<^sub>e ef)"

lemma rg_lr_imp_lr: "local_respect_events \<Longrightarrow> local_respectC"
proof-
  assume p0: "local_respect_events"
  then have p1: "\<forall>ef. ef\<in>all_evts pesf  \<longrightarrow> ((\<exists>\<S>. (E\<^sub>e ef) \<in> \<S> \<and> local_respect_e \<Gamma> \<S> (E\<^sub>e ef)) \<or> 
                 (\<forall>u s1 s2. (s1, s2) \<in> Guar\<^sub>e ef \<longrightarrow> ((dome s1 (E\<^sub>e ef)) \<setminus>\<leadsto>\<^sub>v u \<longrightarrow> s1 \<sim>u\<sim> s2)))"
    using all_evts_are_basic local_respect_events_def lr_e_Basic1 by blast
  show ?thesis
  proof-
    {
      fix a u C
      assume a0: "reachableC0 C"
         and a1: "(domain (a::('l,'k,'s,'prog,'d) action)) \<setminus>\<leadsto>\<^sub>v u"
      have "\<forall> C'. (C'\<in>nextC C a) \<longrightarrow> (C \<sim>.u.\<sim> C')"
      proof-
        {
          fix C'
          assume b0: "C'\<in>nextC C a"
          then have b1: "(C,C')\<in>step a" by (simp add:nextC_def)
          then have b2: "(\<Gamma> \<turnstile> C -pes-(actk a)\<rightarrow> C') \<and> ((\<exists>e k. actk a = ((EvtEnt e)\<sharp>k) \<and> eventof a = e 
                          \<and> dome (gets C) e = domain a) \<or> (\<exists>c k. actk a = ((Cmd c)\<sharp>k) \<and> 
                          eventof a = (getx C) k \<and> dome (gets C) (eventof a) = domain a))"
            by (simp add:step_def)
          obtain act_k and e and d where b3: "a = \<lparr>actk = act_k,eventof = e, domain=d\<rparr>"
            using action.cases by blast
          with b2 have b4: "(\<Gamma> \<turnstile> C -pes-act_k\<rightarrow> C') \<and> ((\<exists>e k. act_k = ((EvtEnt e)\<sharp>k) \<and> eventof a = e 
                             \<and> dome (gets C) e = domain a) \<or> (\<exists>c k. act_k = ((Cmd c)\<sharp>k) \<and> 
                             eventof a = (getx C) k \<and> dome (gets C) (eventof a) = domain a))"
            by simp
          obtain act and k where b5: "act_k = act\<sharp>k"
            by (metis actk.cases get_actk_def)
          obtain pes1 and s1 and x1 where b6: "C = (pes1,s1,x1)" using prod_cases3 by blast 
          obtain pes2 and s2 and x2 where b7: "C' = (pes2,s2,x2)" using prod_cases3 by blast
          from b4 b5 b6 b7 have "\<exists>es'. (\<Gamma> \<turnstile> (pes1 k, s1, x1) -es-(act\<sharp>k)\<rightarrow> (es', s2, x2)) \<and> pes2 = pes1(k:=es')"
            using pestran_estran by force
          then obtain es' where b8: "(\<Gamma> \<turnstile> (pes1 k, s1, x1) -es-(act\<sharp>k)\<rightarrow> (es', s2, x2)) \<and> pes2 = pes1(k:=es')" by auto
          from b5 have "C \<sim>.u.\<sim> C'"
          proof(induct act)
            case (Cmd x) 
            assume c0: "act_k = Cmd x\<sharp>k"
            from a0 have "\<exists>as. (C0,C) \<in> runC as" by (simp add:reachableC0_def reachableC_def)
            then obtain as where "(C0,C) \<in> runC as" by auto
            then have "(\<exists>c. c\<in>cpts_pes \<Gamma> \<and> c!0 = C0 \<and> last c = C \<and> Suc (length as) = length c \<and>
                       (\<forall>j. Suc j < length c \<longrightarrow> (\<Gamma> \<turnstile> c!j-pes-(actk (as!j))\<rightarrow>c!Suc j)) )"
              using run_is_cpt by blast
            then obtain c where c1: "c\<in>cpts_pes \<Gamma> \<and> c!0 = C0 \<and> last c = C \<and> Suc (length as) = length c \<and>
                        (\<forall>j. Suc j < length c \<longrightarrow> (\<Gamma> \<turnstile> c!j-pes-(actk (as!j))\<rightarrow>c!Suc j))" by auto
            with b1 have c2: "c@[C']\<in>cpts_pes \<Gamma>" using cpts_pes_onemore step_def
              by (metis (no_types, lifting) b4 cpts_pes_not_empty last_conv_nth)
            with c1 have c3: "c @ [C'] \<in> cpts_of_pes \<Gamma> (paresys_spec pesf) s0 x0" 
              using cpts_of_pes_def[of \<Gamma> "paresys_spec pesf" s0 x0] C0_ParSys
              by (smt cpts_pes_not_empty length_greater_0_conv mem_Collect_eq nth_append)
            moreover
            from c1 have c4: "(c @ [C']) ! (length (c @ [C']) - 2) = C"
              by (metis Suc_1 diff_Suc_1 diff_Suc_Suc last_conv_nth length_0_conv length_append_singleton
                  lessI nat.simps(3) nth_append)
            moreover
            have c5: "(c @ [C']) ! (length (c @ [C']) - 1) = C'" by simp
            moreover
            from b1 c1 have c50: "\<forall>j. Suc j < length (c @ [C']) \<longrightarrow> (\<Gamma> \<turnstile> (c @ [C'])!j-pes-(actk ((as@[a])!j))
                    \<rightarrow>(c @ [C'])!Suc j)"
              by (smt Suc_1 Suc_lessI Suc_less_eq action.simps(1) b3 b4 c4 diff_Suc_1 diff_Suc_Suc
                  length_append_singleton nth_append nth_append_length) 
            ultimately have r1: "(gets C, gets C')\<in>Guar\<^sub>f (the (evtrgfs (getx C k)))" 
              using b1 b3 b4 c0 c1 act_cptpes_sat_guar_curevt_new2 [rule_format, of \<Gamma> pesf "{s0}" UNIV s0 evtrgfs "c@[C']"]
                     step_def[of a] parsys_sat_rg all_evts_are_basic evt_in_parsys_in_evtrgfs parsys_sat
              by (smt One_nat_def Suc_1 append_is_Nil_conv butlast_snoc diff_Suc_1  diff_Suc_eq_diff_pred 
                 diff_Suc_less insertI1 length_butlast length_greater_0_conv not_Cons_self2)      
            from c3 c50 have c51: "\<forall>k i. Suc i < length (c @ [C']) \<longrightarrow> (\<exists>ca. \<Gamma> \<turnstile> (c @ [C']) ! i -pes-Cmd ca\<sharp>k\<rightarrow> 
                    (c @ [C']) ! Suc i) \<longrightarrow> (\<exists>ef\<in>all_evts pesf. getx ((c @ [C']) ! i) k = fst ef) " 
              using all_evts_are_basic cur_evt_in_specevts [of "c@[C']" \<Gamma> pesf] by (metis E\<^sub>e_def) 
            moreover
            from b1 b3 c0 have c52: "\<Gamma> \<turnstile> C-pes-Cmd x\<sharp>k\<rightarrow>C'" using step_def by simp
            ultimately have "(\<exists>ef\<in>all_evts pesf. getx C k = fst ef)"
              using c1 c4 c5
            proof -

              have f1: "\<forall>k n. \<not> Suc n < length (c @ [C']) \<or>
                        (\<forall>ca. (\<not> \<Gamma> \<turnstile> ((c @ [C']) ! n) -pes-(Cmd ca\<sharp>k)\<rightarrow> ((c @ [C']) ! Suc n)) \<or> 
                        (\<exists>p. p \<in> all_evts pesf \<and> fst p = getx ((c @ [C']) ! n) k))"
                by (metis c51)
              have f2: "\<forall>ps. c ! length as = (c @ ps) ! length as"
                by (metis (no_types) c1 lessI nth_append)
              have "c ! length as = C"
                by (metis (no_types) append_Nil c1 diff_Suc_1 id_take_nth_drop last_length 
                    length_Cons take_0 zero_less_Suc)
              then show ?thesis
                using f2 f1 by (metis c52 c1 c5 diff_Suc_1 length_append_singleton lessI)
            qed
            then obtain ef where c7: "ef\<in>all_evts pesf \<and> getx C k = fst ef" by auto
            from c0 have "\<not>(\<exists>e k. act_k = EvtEnt e\<sharp>k)"
              by (simp add: get_actk_def) 
            with b3 b4 c0 have c70: "\<exists>x k. act_k = Cmd x\<sharp>k \<and> eventof a = getx C k \<and> dome (gets C) (eventof a) = domain a"
              by simp
            with a1 b3 c0 have c8: "eventof a = getx C k \<and> dome (gets C) (eventof a) = domain a" 
              by (metis actk.iffs get_actk_def)

            with a1 b3 b6 c7 have c9 : "(dome s1  (E\<^sub>e ef)) \<setminus>\<leadsto>\<^sub>v u" 
              using gets_def E\<^sub>e_def by (metis fst_conv snd_conv)

            from p1 c7 have c10: "(\<exists>\<S>. (E\<^sub>e ef) \<in> \<S> \<and> local_respect_e \<Gamma> \<S> (E\<^sub>e ef)) \<or> 
            (\<forall>u s1 s2. (s1, s2) \<in> Guar\<^sub>e ef \<longrightarrow> ((dome s1 (E\<^sub>e ef)) \<setminus>\<leadsto>\<^sub>v u \<longrightarrow> s1 \<sim>u\<sim> s2))"
              by presburger
            then have " s1 \<sim>u\<sim> s2"
            proof
              assume d0: "\<exists>\<S>. E\<^sub>e ef \<in> \<S> \<and> local_respect_e \<Gamma> \<S> (E\<^sub>e ef)"
              let ?pes = "paresys_spec pesf"
              let ?i = "length (c @ [C']) - 2"
              have "\<exists>\<S>. AnonyEvent x \<in> \<S> \<and> local_respect_e \<Gamma> \<S> (E\<^sub>e ef)"
              proof-
                {
                  have "\<exists>el j.  getspc_e (el!0) = getx C k \<and> j < length el \<and>  el!j = rm_evtsys1 
                        ((getspc C k), gets C, getx C) \<and> el \<in> cpts_ev \<Gamma> \<and> el \<in> preserves_e"
                    using act_cptpes_sat_e_sim[rule_format, of \<Gamma> pesf "{s0}" UNIV s0 evtrgfs "c @ [C']"
                        x0 ?i k] parsys_sat_rg all_evts_are_basic evt_in_parsys_in_evtrgfs c1 c3 c4
                        c5 c50 c52 parsys_sat
                    by (smt One_nat_def Suc_1 Suc_diff_Suc Suc_less_eq diff_less insertI1
                        length_append_singleton zero_less_Suc)
                  then obtain el and j where e0: "getspc_e (el!0) = getx C k \<and> j < length el \<and> 
                     el!j = rm_evtsys1 ((getspc C k), gets C, getx C) \<and> el \<in> cpts_ev \<Gamma> \<and> el \<in> preserves_e"
                    by auto
                with c7 have e1: "getspc_e (el!0) = E\<^sub>e ef \<and> j < length el \<and> 
                               el!j = rm_evtsys1 ((getspc C k), gets C, getx C) 
                               \<and> el \<in> cpts_ev \<Gamma> \<and> el \<in> preserves_e"  by (simp add: E\<^sub>e_def)
                with c7 d0 have "\<exists>\<S>. (E\<^sub>e ef) \<in> \<S> \<and> local_respect_e \<Gamma> \<S> (E\<^sub>e ef)" by blast
                then obtain \<S> where e2: "(E\<^sub>e ef) \<in> \<S> \<and> local_respect_e \<Gamma> \<S> (E\<^sub>e ef)" by auto

                from b5 b8 b4 c0 have "\<exists>es. getspc C k = EvtSeq (AnonyEvent x) es"
                  by (metis pes_cmd_tran_anonyevt pesconf_trip)
                then obtain es where "getspc C k = EvtSeq (AnonyEvent x) es" by auto
                with e0 b8 have e3: "el!j = (AnonyEvent x, s1, x1)" 
                  using rm_evtsys1_def 
                  by (metis EvtSeqrm Pair_inject b6 esconf_trip pesconf_trip)
                with e0 e1 e2 e3 have "AnonyEvent x \<in> \<S>"
                  using local_respect_forall[of "E\<^sub>e ef" \<S> \<Gamma> "E\<^sub>e ef" el j]
                  by (metis getspc_e_def fstI)
                with e2 show ?thesis by auto
              }
            qed

            then obtain \<S> where d1: "AnonyEvent x \<in> \<S> \<and> local_respect_e \<Gamma> \<S> (E\<^sub>e ef)" by auto

            have d2: "ann_preserves_e (AnonyEvent x) s1"
            proof- 
              {
                from c3 c50 have "c @ [C'] \<in> preserves_pes"
                  using run_cpt_preserves pes_tran_not_etran1 by blast
                with c4 b6 have "ann_preserves_pes pes1 s1"
                  apply (simp add: preserves_pes_def)
                  apply (erule_tac x = "?i" in allE)
                  by (simp add: getspc_def gets_def)
                then have f0 : "ann_preserves_es (pes1 k) s1"
                  by (simp add: ann_preserves_pes_def)
                from b5 b8 c52 c0 have "\<exists>es. pes1 k = EvtSeq (AnonyEvent x) es"
                  by (metis  evtseq_cmd_tran_anonyevt)
                then obtain es where "pes1 k = EvtSeq (AnonyEvent x) es" by auto
                with f0 have "ann_preserves_e (AnonyEvent x) s1"
                  by (simp add: ann_preserves_es_def)
              }
              then show ?thesis by auto
            qed

            with b6 b7 c52 c9 d1 show ?thesis 
              by (metis local_next_state pes_cmd_tran_anonyevt1)
          next
            assume f0: "\<forall>u s1 s2. (s1, s2) \<in> Guar\<^sub>e ef \<longrightarrow> dome s1 (E\<^sub>e ef) \<setminus>\<leadsto>\<^sub>v u \<longrightarrow> s1 \<sim>u\<sim> s2"
            from p1 b6 b7 c7 c8 r1 have "(gets C, gets C')\<in>Guar\<^sub>e ef"
              using evt_in_parsys_in_evtrgfs Guar\<^sub>f_def E\<^sub>e_def Guar\<^sub>e_def by metis
            with f0 show ?thesis using p1 b6 b7 c7 c8 a1 E\<^sub>e_def
              by (metis fst_conv gets_def snd_conv)
          qed

          then show ?case
            by (simp add: b6 b7 gets_def vpeqC_def)
        next
          case (EvtEnt x)
          from b5 b8 have "s1 = s2" 
            using entevt_notchgstate by (metis EvtEnt.prems evtent_is_basicevt)
          with b6 b7 show ?case by (simp add: gets_def vpeqC_def vpeq_reflexive)
        qed
      }
      then show ?thesis by auto
    qed
  }
  then show ?thesis using local_respectC_def 
    by (metis (no_types, lifting) SM_IFS.intro SM_IFS.noninterf_def noninterf1_def 
       vpeqC_reflexive vpeqC_symmetric vpeqC_transitive)
qed
qed


lemma rg_sc_imp_sc: "step_consistent_events \<Longrightarrow> weak_step_consistentC"
proof-
  assume p0: "step_consistent_events"
  then have p1: "\<forall>ef. ef\<in>all_evts pesf  \<longrightarrow> (\<exists>\<S>. (E\<^sub>e ef) \<in> \<S> \<and> step_consistent_e \<Gamma> \<S> (E\<^sub>e ef))"
    by (simp add: all_evts_are_basic sc_e_Basic1 step_consistent_events_def)
  show ?thesis
  proof-
    {
      fix a u C1 C2
      assume a0: "(reachableC0 C1) \<and> (reachableC0 C2)"
      and    a1: "(C1 \<sim>.u.\<sim> C2) \<and> (((domain (a::('l,'k,'s,'prog,'d) action)) \<leadsto> u) \<longrightarrow> (C1 \<sim>.(domain a).\<sim> C2))"
      have "\<forall>C1' C2'. (C1'\<in>nextC C1 a) \<and> (C2'\<in>nextC C2 a) \<longrightarrow> (C1' \<sim>.u.\<sim> C2')"
      proof-
        {
          fix C1' C2'
          assume b0: "(C1'\<in>nextC C1 a) \<and> (C2'\<in>nextC C2 a)"
          obtain act_k and e and d where b3: "a = \<lparr>actk = act_k,eventof = e, domain=d\<rparr>"
            using action.cases by blast 
          obtain act and k where b5: "act_k = act\<sharp>k"
            by (metis actk.cases get_actk_def)

          from b0 have b1: "(C1, C1') \<in> step a" by (simp add: nextC_def)
          then have b2: "(\<Gamma> \<turnstile> C1 -pes-(actk a)\<rightarrow> C1') \<and>
                         ((\<exists>e k. actk a = ((EvtEnt e)\<sharp>k) \<and> eventof a = e \<and> dome (gets C1) e = domain a) \<or>
                         (\<exists>c k. actk a = ((Cmd c)\<sharp>k) \<and> eventof a = (getx C1) k \<and> dome (gets C1) (eventof a) = domain a))"
            by (simp add: step_def)
          with b3 have b4: "(\<Gamma> \<turnstile> C1 -pes-act_k\<rightarrow> C1') \<and> 
                            ((\<exists>e k. act_k = ((EvtEnt e)\<sharp>k) \<and> eventof a = e \<and> dome (gets C1) e = domain a) \<or>
                            (\<exists>c k. act_k = ((Cmd c)\<sharp>k) \<and> eventof a = (getx C1) k \<and> dome (gets C1) (eventof a) = domain a))"
            by simp

          from b0 have b6: "(C2,C2')\<in>step a" by (simp add:nextC_def)
          then have "(\<Gamma> \<turnstile> C2 -pes-(actk a)\<rightarrow> C2') \<and>
                     ((\<exists>e k. actk a = ((EvtEnt e)\<sharp>k) \<and> eventof a = e \<and> dome (gets C2) e = domain a) \<or>
                     (\<exists>c k. actk a = ((Cmd c)\<sharp>k) \<and> eventof a = (getx C2) k \<and> dome (gets C2) (eventof a) = domain a))"
            by (simp add:step_def)
          with b3 have b7: "(\<Gamma> \<turnstile> C2 -pes-act_k\<rightarrow> C2') \<and> 
                            ((\<exists>e k. act_k = ((EvtEnt e)\<sharp>k) \<and> eventof a = e \<and> dome (gets C2) e = domain a) \<or>
                            (\<exists>c k. act_k = ((Cmd c)\<sharp>k) \<and> eventof a = (getx C2) k \<and> dome (gets C2) (eventof a) = domain a))"
            by simp
          obtain pes1 and s1 and x1 where b8: "C1 = (pes1,s1,x1)" using prod_cases3 by blast 
          obtain pes1' and s1' and x1' where b9: "C1' = (pes1',s1',x1')" using prod_cases3 by blast
          obtain pes2 and s2 and x2 where b10: "C2 = (pes2,s2,x2)" using prod_cases3 by blast
          obtain pes2' and s2' and x2' where b11: "C2' = (pes2',s2',x2')" using prod_cases3 by blast
          from b4 b5 b8 b9 have "\<exists>es'. (\<Gamma> \<turnstile> (pes1 k, s1, x1) -es-(act\<sharp>k)\<rightarrow> (es', s1', x1')) \<and> pes1' = pes1(k:=es')" 
            using pestran_estran [of \<Gamma> pes1 s1 x1 act k pes1' s1' x1'] by simp
          then obtain es1' where b12: "(\<Gamma> \<turnstile> (pes1 k, s1, x1) -es-(act\<sharp>k)\<rightarrow> (es1', s1', x1')) \<and> pes1' = pes1(k:=es1')" by auto
          from b5 b7 b10 b11 have "\<exists>es'. (\<Gamma> \<turnstile> (pes2 k, s2, x2) -es-(act\<sharp>k)\<rightarrow> (es', s2', x2')) \<and> pes2' = pes2(k:=es')" 
            using pestran_estran [of \<Gamma> pes2 s2 x2 act k pes2' s2' x2'] by simp
          then obtain es2' where b13: "(\<Gamma> \<turnstile> (pes2 k, s2, x2) -es-(act\<sharp>k)\<rightarrow> (es2', s2', x2')) \<and> pes2' = pes2(k:=es2')"
            by auto

          from b5 have "C1' \<sim>.u.\<sim> C2'"
          proof(induct act)
            case (Cmd c)
            assume c0: "act_k = Cmd c\<sharp>k"

            from a0 have "\<exists>as. (C0, C1) \<in> runC as" by (simp add: reachableC0_def reachableC_def)
            then obtain as1 where "(C0, C1) \<in> runC as1" by auto
            then have "(\<exists>c. c\<in>cpts_pes \<Gamma> \<and> c!0 = C0 \<and> last c = C1 \<and> Suc (length as1) = length c \<and>
                              (\<forall>j. Suc j < length c \<longrightarrow> (\<Gamma> \<turnstile> c!j-pes-(actk (as1!j))\<rightarrow>c!Suc j)) )"
              using run_is_cpt by blast
            then obtain c1 where c1: "c1\<in>cpts_pes \<Gamma> \<and> c1!0 = C0 \<and> last c1 = C1 \<and> Suc (length as1) = length c1 \<and>
                (\<forall>j. Suc j < length c1 \<longrightarrow> (\<Gamma> \<turnstile> c1!j-pes-(actk (as1!j))\<rightarrow>c1!Suc j))" by auto
            with b1 have c2: "c1@[C1']\<in>cpts_pes \<Gamma>" using cpts_pes_onemore step_def
              by (metis (no_types, lifting) b4 cpts_pes_not_empty last_conv_nth)
            with c1 have c3: "c1 @ [C1'] \<in> cpts_of_pes \<Gamma>(paresys_spec pesf) s0 x0" 
              using cpts_of_pes_def[of \<Gamma> "paresys_spec pesf" s0 x0] C0_ParSys
              by (smt cpts_pes_not_empty length_greater_0_conv mem_Collect_eq nth_append)
            moreover
            from c1 have c4: "(c1 @ [C1']) ! (length (c1 @ [C1']) - 2) = C1"
              by (metis Suc_1 diff_Suc_1 diff_Suc_Suc last_conv_nth length_0_conv length_append_singleton 
                  lessI nat.distinct(1) nth_append)
              
            moreover
            have c5: "(c1 @ [C1']) ! (length (c1 @ [C1']) - 1) = C1'" by simp
            moreover
            from b1 c1 have c50: "\<forall>j. Suc j < length (c1 @ [C1']) \<longrightarrow> 
             (\<Gamma> \<turnstile> (c1 @ [C1'])!j-pes-(actk ((as1@[a])!j))\<rightarrow>(c1 @ [C1'])!Suc j)"
              by (smt Suc_1 Suc_lessI Suc_less_eq action.simps(1) b3 b4 c4 diff_Suc_1 
                  diff_Suc_Suc length_append_singleton nth_append nth_append_length) 

            from a0 have "\<exists>as. (C0,C2) \<in> runC as" by (simp add:reachableC0_def reachableC_def)
            then obtain as2 where "(C0,C2) \<in> runC as2" by auto
            then have "(\<exists>c. c\<in>cpts_pes \<Gamma> \<and> c!0 = C0 \<and> last c = C2 \<and> Suc (length as2) = length c \<and>
                        (\<forall>j. Suc j < length c \<longrightarrow> (\<Gamma> \<turnstile> c!j-pes-(actk (as2!j))\<rightarrow>c!Suc j)) )"
              using run_is_cpt by blast
            then obtain c2 where c7: "c2\<in>cpts_pes \<Gamma> \<and> c2!0 = C0 \<and> last c2 = C2 \<and> Suc (length as2) = length c2 \<and>
                     (\<forall>j. Suc j < length c2 \<longrightarrow> (\<Gamma> \<turnstile> c2!j-pes-(actk (as2!j))\<rightarrow>c2!Suc j))" by auto
            with b6 have c8: "c2@[C2']\<in>cpts_pes \<Gamma>" using cpts_pes_onemore step_def
              by (metis (no_types, lifting) b7 cpts_pes_not_empty last_conv_nth)
            with c7 have c9: "c2 @ [C2'] \<in> cpts_of_pes \<Gamma> (paresys_spec pesf) s0 x0" 
              using cpts_of_pes_def[of \<Gamma> "paresys_spec pesf" s0 x0] C0_ParSys
              by (smt cpts_pes_not_empty length_greater_0_conv mem_Collect_eq nth_append) 
            moreover
            from c7 have c10: "(c2 @ [C2']) ! (length (c2 @ [C2']) - 2) = C2"
              by (metis Suc_1 diff_Suc_1 diff_Suc_Suc last_conv_nth length_0_conv length_append_singleton 
                  lessI nat.distinct(1) nth_append)
            moreover
            have c11: "(c2 @ [C2']) ! (length (c2 @ [C2']) - 1) = C2'" by simp
            moreover
            from b1 c7 have c60: "\<forall>j. Suc j < length (c2 @ [C2']) \<longrightarrow> 
              (\<Gamma> \<turnstile> (c2 @ [C2'])!j-pes-(actk ((as2@[a])!j))\<rightarrow>(c2 @ [C2'])!Suc j)"
              by (smt Suc_1 Suc_lessI Suc_less_eq action.simps(1) b3 b7 c10 diff_Suc_1 
                 diff_Suc_Suc length_append_singleton nth_append nth_append_length) 


            from c3 c50 have c51: "\<forall>k i. Suc i < length (c1 @ [C1']) \<longrightarrow>
                      (\<exists>ca. \<Gamma> \<turnstile> (c1 @ [C1']) ! i -pes-Cmd ca\<sharp>k\<rightarrow> (c1 @ [C1']) ! Suc i) \<longrightarrow>
                      (\<exists>ef\<in>all_evts pesf. getx ((c1 @ [C1']) ! i) k = fst ef) " 
              using all_evts_are_basic cur_evt_in_specevts [of "c1@[C1']" \<Gamma> pesf] by (metis E\<^sub>e_def)
            moreover
            from b1 b3 c0 have c52: "\<Gamma> \<turnstile> C1-pes-Cmd c\<sharp>k\<rightarrow>C1'" using step_def by simp
            from c9 c60 have c61: "\<forall>k i. Suc i < length (c2 @ [C2']) \<longrightarrow>
                      (\<exists>ca. \<Gamma> \<turnstile> (c2 @ [C2']) ! i -pes-Cmd ca\<sharp>k\<rightarrow> (c2 @ [C2']) ! Suc i) \<longrightarrow>
                      (\<exists>ef\<in>all_evts pesf. getx ((c2 @ [C2']) ! i) k = fst ef) " 
              using all_evts_are_basic cur_evt_in_specevts [of "c2@[C2']" \<Gamma> pesf] by (metis E\<^sub>e_def)
            moreover
            from b6 b3 c0 have c62: "\<Gamma> \<turnstile> C2-pes-Cmd c\<sharp>k\<rightarrow>C2'" using step_def by simp

            ultimately have "(\<exists>ef\<in>all_evts pesf. getx C1 k = fst ef)"
              using c1 c4 c5
            proof-

              have f1: "\<forall>k n. \<not> Suc n < length (c1 @ [C1']) \<or>
                        (\<forall>ca. (\<not> \<Gamma> \<turnstile> ((c1 @ [C1']) ! n) -pes-(Cmd ca\<sharp>k)\<rightarrow> ((c1 @ [C1']) ! Suc n)) \<or> 
                        (\<exists>p. p \<in> all_evts pesf \<and> fst p = getx ((c1 @ [C1']) ! n) k))"
                by (metis c51)
              from c1 have f2: "\<forall>ps. c1 ! length as1 = (c1 @ ps) ! length as1" 
                by (metis (no_types) c1 lessI nth_append)
              have "c1 ! length as1 = C1"
                by (metis (no_types) append_Nil c1 diff_Suc_1 id_take_nth_drop last_length 
                    length_Cons take_0 zero_less_Suc)
              then show ?thesis
                using f2 f1 by (metis c52 c1 c5 diff_Suc_1 length_append_singleton lessI)
            qed

            then obtain ef where c12: "ef\<in>all_evts pesf \<and> getx C1 k = E\<^sub>e ef" 
              by (metis E\<^sub>e_def)
            from c0 have c12_1: "\<not>(\<exists>e k. act_k = EvtEnt e\<sharp>k)"
              by (simp add: get_actk_def) 
            with b3 b4 c0 have c13: "\<exists>x k. act_k = Cmd c\<sharp>k \<and> eventof a = getx C1 k \<and> dome (gets C1) (eventof a) = domain a"
              by (metis actk.iffs get_actk_def)
            with a1 b3 c0 have c14: "eventof a = getx C1 k \<and> dome (gets C1) (eventof a) = domain a"
              by (metis actk.ext_inject get_actk_def)

            let ?pes = "paresys_spec pesf"
            let ?i = "length (c1 @ [C1']) - 2"
            have "\<exists>\<S>. AnonyEvent c \<in> \<S> \<and> step_consistent_e \<Gamma> \<S> (E\<^sub>e ef)"
            proof-
              {
                have "\<exists>el j.  getspc_e (el!0) = getx C1 k \<and> j < length el \<and> 
                     el!j = rm_evtsys1 ((getspc C1 k), gets C1, getx C1) \<and> el \<in> cpts_ev \<Gamma> \<and> el \<in> preserves_e"
                  using act_cptpes_sat_e_sim[rule_format, of \<Gamma> pesf "{s0}" UNIV s0 evtrgfs "c1 @ [C1']"
                        x0 ?i k] parsys_sat_rg all_evts_are_basic evt_in_parsys_in_evtrgfs c1 c3 c4
                       c5 c50 c52 parsys_sat
                  by (smt One_nat_def Suc_1 Suc_diff_Suc Suc_less_eq diff_less insertI1  length_append_singleton 
                      zero_less_Suc)
                then obtain el and j where e0: "getspc_e (el!0) = getx C1 k \<and> j < length el \<and> 
                     el!j = rm_evtsys1 ((getspc C1 k), gets C1, getx C1) \<and> el \<in> cpts_ev \<Gamma> \<and> el \<in> preserves_e"
                  by auto
                with c12 have c120: "getspc_e (el!0) = E\<^sub>e ef \<and> j < length el \<and> el!j = rm_evtsys1 ((getspc C1 k), gets C1, getx C1) 
                               \<and> el \<in> cpts_ev \<Gamma> \<and> el \<in> preserves_e" by simp
                with c12 p1 have "\<exists>\<S>. (E\<^sub>e ef) \<in> \<S> \<and> step_consistent_e \<Gamma> \<S> (E\<^sub>e ef)" by blast
                then obtain \<S> where e1: "(E\<^sub>e ef) \<in> \<S> \<and> step_consistent_e \<Gamma> \<S> (E\<^sub>e ef)" by auto

                from b5 b8 b12 c0 have "\<exists>es. getspc C1 k = EvtSeq (AnonyEvent c) es"
                  by (metis evtseq_cmd_tran_anonyevt fst_conv getspc_def)
                then obtain es where "getspc C1 k = EvtSeq (AnonyEvent c) es" by auto
                with e0 b8 have e2: "el!j = (AnonyEvent c, s1, x1)" 
                  using rm_evtsys1_def 
                  by (metis EvtSeqrm esconf_trip fst_conv gets_def getx_def snd_conv)
                with e0 e1 e2 c120 have "AnonyEvent c \<in> \<S>"
                  using step_consistent_forall[of "E\<^sub>e ef" \<S> \<Gamma> "E\<^sub>e ef" el j]
                  by (metis getspc_e_def fstI)
                with e1 show ?thesis by auto
              }
            qed
      
        then obtain \<S> where d0: "AnonyEvent c \<in> \<S> \<and> step_consistent_e \<Gamma> \<S> (E\<^sub>e ef)" by auto

        have d1: "ann_preserves_e (AnonyEvent c) s1"
        proof-     
          {
            from c3 c50 have "c1 @ [C1'] \<in> preserves_pes" 
              using run_cpt_preserves pes_tran_not_etran1 by blast
            with c4 b8 have "ann_preserves_pes pes1 s1"
              apply (simp add: preserves_pes_def)
              apply (erule_tac x = "?i" in allE)
              by (simp add: getspc_def gets_def)
            then have f0 : "ann_preserves_es (pes1 k) s1"
              by (simp add: ann_preserves_pes_def)
            from b8 c52 have "\<exists>es. pes1 k = EvtSeq (AnonyEvent c) es"
              using b12 b5 c0 evtseq_cmd_tran_anonyevt by fastforce
            then obtain es where "pes1 k = EvtSeq (AnonyEvent c) es" by auto
            with f0 have "ann_preserves_e (AnonyEvent c) s1"
              by (simp add: ann_preserves_es_def)
          }
          then show ?thesis by auto
        qed

        let ?j = "length (c2 @ [C2']) - 2"
        have d2: "ann_preserves_e (AnonyEvent c) s2"
        proof-     
          {
            from c9 c60 have "c2 @ [C2'] \<in> preserves_pes" 
              using pes_tran_not_etran1 run_cpt_preserves by blast
            with c10 b10 have "ann_preserves_pes pes2 s2"
              apply (simp add: preserves_pes_def)
              apply (erule_tac x = "?j" in allE)
              by (simp add: getspc_def gets_def)
            then have f0 : "ann_preserves_es (pes2 k) s2"
              by (simp add: ann_preserves_pes_def)
            from b10 c62 have "\<exists>es. pes2 k = EvtSeq (AnonyEvent c) es"
              using b13 b5 c0 evtseq_cmd_tran_anonyevt by fastforce
            then obtain es where "pes2 k = EvtSeq (AnonyEvent c) es" by auto
            with f0 have "ann_preserves_e (AnonyEvent c) s2"
              by (simp add: ann_preserves_es_def)
          }
          then show ?thesis by auto
        qed

        from b8 b9 c52 have "\<exists>e1. \<Gamma> \<turnstile> (AnonyEvent c, s1, x1) -et-Cmd c\<sharp>k\<rightarrow> (e1, s1', x1')"
          by (simp add:  pes_cmd_tran_anonyevt1)
        then obtain e1 where d3 : "\<Gamma> \<turnstile> (AnonyEvent c, s1, x1) -et-Cmd c\<sharp>k\<rightarrow> (e1, s1', x1')"by auto

        from b10 b11 c62 have "\<exists>e2. \<Gamma> \<turnstile> (AnonyEvent c, s2, x2) -et-Cmd c\<sharp>k\<rightarrow> (e2, s2', x2')"
          by (simp add:  pes_cmd_tran_anonyevt1)
        then obtain e2 where d4: "\<Gamma> \<turnstile> (AnonyEvent c, s2, x2) -et-Cmd c\<sharp>k\<rightarrow> (e2, s2', x2')" by auto

        from c14 a1 b3 b8 b10 c12 have d5: "(dome s1 (E\<^sub>e ef)) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1 (E\<^sub>e ef))\<sim> s2" 
          using gets_def vpeqC_def  by (metis fst_conv snd_conv) 

        from a1 b8 b10 have d5 : "s1 \<sim>u\<sim> s2"
          by (simp add: gets_def vpeqC_def)

        from c14 a1 b3 b8 b10 c12 have d6: "(dome s1 (E\<^sub>e ef)) \<leadsto> u \<longrightarrow> s1 \<sim>(dome s1 (E\<^sub>e ef))\<sim> s2" 
          using gets_def vpeqC_def by (metis fst_conv snd_conv) 

        with d0 d1 d2 d3 d4 d5 have "s1' \<sim>u\<sim> s2'"
          using consistent_next_state by blast

        then show ?case by (simp add: b11 b9 gets_def vpeqC_def)
          next
            case (EvtEnt x)
            from b12 have r1: "s1 = s1'" using entevt_notchgstate
              by (metis EvtEnt.prems b5 evtent_is_basicevt)
            from b13 have r2: "s2 = s2'" using entevt_notchgstate
              by (metis EvtEnt.prems b5 evtent_is_basicevt) 
            from a1 b8 b9 b10 b11 r1 r2 show ?case using gets_def vpeqC_def vpeq_reflexive
              by (metis fst_conv snd_conv)
          qed
        }
        then show ?thesis by auto qed
    }
    then show ?thesis using weak_step_consistentC_def by blast
  qed
qed

interpretation SM_IFS C0 step domain obsC vpeqC interference
  using SM_IFS_def vpeqC_reflexive vpeqC_symmetric vpeqC_transitive by blast

subsection \<open>Unwinding Theorem\<close>

thm PiCore_nonleakage

theorem PiCore_RG_nonleakage: "\<lbrakk> observed_consistentC; step_consistent_events \<rbrakk> \<Longrightarrow> nonleakage"
  by (rule PiCore_nonleakage, simp_all add: rg_sc_imp_sc)

theorem PiCore_RG_noninfluence0: "\<lbrakk>observed_consistentC; local_respect_events;step_consistent_events\<rbrakk> 
                                  \<Longrightarrow> noninfluence0"
  by (rule PiCore_noninfluence0, simp_all add: rg_sc_imp_sc rg_lr_imp_lr )

end


end

