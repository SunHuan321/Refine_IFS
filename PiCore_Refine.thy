theory PiCore_Refine
  imports PiCore_IFS Refinement
begin

print_locale InfoFlow

locale PiCore_Refine =
  InfoFlow\<^sub>c: InfoFlow ptran\<^sub>c petran\<^sub>c fin_com\<^sub>c C0\<^sub>c step\<^sub>c interference\<^sub>c vpeq\<^sub>c obs\<^sub>c dome\<^sub>c +
  InfoFlow\<^sub>a: InfoFlow ptran\<^sub>a petran\<^sub>a fin_com\<^sub>a C0\<^sub>a step\<^sub>a interference\<^sub>a vpeq\<^sub>a obs\<^sub>a dome\<^sub>a
  for ptran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> (('prog\<^sub>c \<times> 's\<^sub>c) \<times> 'prog\<^sub>c \<times> 's\<^sub>c) set" 
  and petran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> 'prog\<^sub>c \<times> 's\<^sub>c \<Rightarrow> 'prog\<^sub>c \<times> 's\<^sub>c \<Rightarrow> bool" 
  and fin_com\<^sub>c :: "'prog\<^sub>c"
  and C0\<^sub>c  :: "('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) pesconf"
  and step\<^sub>c :: "('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c, 'd) action \<Rightarrow> (('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) pesconf \<times> ('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) pesconf) set"
  and interference\<^sub>c :: "'d \<Rightarrow> 'd \<Rightarrow> bool" 
  and vpeq\<^sub>c :: "'s\<^sub>c \<Rightarrow> 'd \<Rightarrow> 's\<^sub>c \<Rightarrow> bool" 
  and obs\<^sub>c :: "'s\<^sub>c \<Rightarrow> 'd \<Rightarrow> 'o\<^sub>c" 
  and dome\<^sub>c :: "'s\<^sub>c \<Rightarrow> ('l\<^sub>c, 'k\<^sub>c, 's\<^sub>c, 'prog\<^sub>c) event \<Rightarrow> 'd"
  and ptran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> (('prog\<^sub>a \<times> 's\<^sub>a) \<times> 'prog\<^sub>a \<times> 's\<^sub>a) set"
  and petran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> 'prog\<^sub>a \<times> 's\<^sub>a \<Rightarrow> 'prog\<^sub>a \<times> 's\<^sub>a \<Rightarrow> bool" 
  and fin_com\<^sub>a :: "'prog\<^sub>a"
  and C0\<^sub>a :: "('l\<^sub>a, 'k\<^sub>a, 's\<^sub>a, 'prog\<^sub>a) pesconf"
  and step\<^sub>a :: "('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a, 'd) action \<Rightarrow> (('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) pesconf \<times> ('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) pesconf) set" 
  and interference\<^sub>a :: "'d \<Rightarrow> 'd \<Rightarrow> bool" 
  and vpeq\<^sub>a ::  "'s\<^sub>a \<Rightarrow> 'd \<Rightarrow> 's\<^sub>a \<Rightarrow> bool"
  and obs\<^sub>a :: "'s\<^sub>a \<Rightarrow> 'd \<Rightarrow> 'o\<^sub>a" 
  and dome\<^sub>a :: "'s\<^sub>a \<Rightarrow> ('l\<^sub>a, 'k\<^sub>a, 's\<^sub>a, 'prog\<^sub>a) event \<Rightarrow> 'd" +
fixes sim_s ::  "('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) pesconf \<Rightarrow> ('l\<^sub>a, 'k\<^sub>a, 's\<^sub>a, 'prog\<^sub>a) pesconf"
  and sim_a :: "('l\<^sub>c, 'k\<^sub>c, 's\<^sub>c, 'prog\<^sub>c, 'd) action \<Rightarrow> ('l\<^sub>a, 'k\<^sub>a, 's\<^sub>a, 'prog\<^sub>a, 'd) action option"
assumes
  init_sim : "sim_s C0\<^sub>c = C0\<^sub>a" and
  action_refine : "sim_a a\<^sub>c = Some a\<^sub>a \<longrightarrow> (C\<^sub>c, C'\<^sub>c) \<in> step\<^sub>c a\<^sub>c \<longrightarrow> (sim_s C\<^sub>c, sim_s C'\<^sub>c) \<in> step\<^sub>a a\<^sub>a" and
  none_refine : "sim_a a\<^sub>c = None \<longrightarrow> (C\<^sub>c, C'\<^sub>c) \<in> step\<^sub>c a\<^sub>c \<longrightarrow> sim_s C\<^sub>c = sim_s C'\<^sub>c" and
  intefere_same : "interference\<^sub>c  = interference\<^sub>a" and 
  dom_refine : "sim_a a\<^sub>c = Some a\<^sub>a \<longrightarrow> domain a\<^sub>c = domain a\<^sub>a" and 
  sim_ifs : "vpeq\<^sub>a (gets (sim_s C\<^sub>c)) d (gets (sim_s C'\<^sub>c)) = vpeq\<^sub>c (gets C\<^sub>c) d (gets C'\<^sub>c)"   

begin

definition vpeqc :: "('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) pesconf \<Rightarrow> 'd \<Rightarrow> ('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) pesconf \<Rightarrow> bool" 
   where "vpeqc C1 u C2 \<equiv> vpeq\<^sub>c (gets C1) u (gets C2)"

definition obsc :: " 'd \<Rightarrow> ('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) pesconf \<Rightarrow> 'o\<^sub>c" 
  where "obsc d C = obs\<^sub>c (gets C) d"

definition vpeqa :: "('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) pesconf \<Rightarrow> 'd \<Rightarrow> ('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) pesconf \<Rightarrow> bool" 
   where "vpeqa C1 u C2 \<equiv> vpeq\<^sub>a (gets C1) u (gets C2)"

definition obsa :: " 'd \<Rightarrow> ('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) pesconf \<Rightarrow> 'o\<^sub>a" 
  where "obsa d C = obs\<^sub>a (gets C) d"

interpretation SM_Refine C0\<^sub>c step\<^sub>c domain InfoFlow\<^sub>c.obsC InfoFlow\<^sub>c.vpeqC interference\<^sub>c
                         C0\<^sub>a step\<^sub>a domain InfoFlow\<^sub>a.obsC InfoFlow\<^sub>a.vpeqC interference\<^sub>a
                         sim_s sim_a
proof
  show " \<forall>a b c u. InfoFlow\<^sub>c.vpeqC a u b \<and> InfoFlow\<^sub>c.vpeqC b u c \<longrightarrow> InfoFlow\<^sub>c.vpeqC a u c"
    using InfoFlow\<^sub>c.vpeqC_transitive by force
  show "\<forall>a b u. InfoFlow\<^sub>c.vpeqC a u b \<longrightarrow> InfoFlow\<^sub>c.vpeqC b u a"
    using InfoFlow\<^sub>c.vpeqC_symmetric by blast
  show " \<forall>a u. InfoFlow\<^sub>c.vpeqC a u a"
    using InfoFlow\<^sub>c.vpeqC_reflexive by blast
  show " \<forall>a b c u. InfoFlow\<^sub>a.vpeqC a u b \<and> InfoFlow\<^sub>a.vpeqC b u c \<longrightarrow> InfoFlow\<^sub>a.vpeqC a u c"
    using InfoFlow\<^sub>a.vpeqC_transitive by fastforce
  show "\<forall>a b u. InfoFlow\<^sub>a.vpeqC a u b \<longrightarrow> InfoFlow\<^sub>a.vpeqC b u a"
    using InfoFlow\<^sub>a.vpeqC_symmetric by force
  show "\<forall>a u. InfoFlow\<^sub>a.vpeqC a u a"
    using InfoFlow\<^sub>a.vpeqC_reflexive by blast
  show "sim_s C0\<^sub>c = C0\<^sub>a"
    by (simp add: init_sim)
  show "\<And>a\<^sub>c a\<^sub>a s\<^sub>c t\<^sub>c. sim_a a\<^sub>c = Some a\<^sub>a \<longrightarrow> (s\<^sub>c, t\<^sub>c) \<in> step\<^sub>c a\<^sub>c \<longrightarrow> (sim_s s\<^sub>c, sim_s t\<^sub>c) \<in> step\<^sub>a a\<^sub>a"
    by (simp add: action_refine)
  show "\<And>a\<^sub>c s\<^sub>c t\<^sub>c. sim_a a\<^sub>c = None \<longrightarrow> (s\<^sub>c, t\<^sub>c) \<in> step\<^sub>c a\<^sub>c \<longrightarrow> sim_s s\<^sub>c = sim_s t\<^sub>c"
    by (simp add: none_refine)
  show "interference\<^sub>c = interference\<^sub>a"
    using  intefere_same by force
  show "\<And>a\<^sub>c a\<^sub>a. sim_a a\<^sub>c = Some a\<^sub>a \<longrightarrow> domain a\<^sub>c = domain a\<^sub>a"
    by (simp add:  dom_refine)
  show "\<And>s\<^sub>c d t\<^sub>c. InfoFlow\<^sub>a.vpeqC (sim_s s\<^sub>c) d (sim_s t\<^sub>c) = InfoFlow\<^sub>c.vpeqC s\<^sub>c d t\<^sub>c"
    by (simp add: InfoFlow\<^sub>a.vpeqC_def InfoFlow\<^sub>c.vpeqC_def sim_ifs)
qed

theorem PiCore_abs_lr_imp: "InfoFlow\<^sub>a.local_respectC \<Longrightarrow> InfoFlow\<^sub>c.local_respectC"
  using InfoFlow\<^sub>a.local_respectC_equiv InfoFlow\<^sub>c.local_respectC_equiv abs_lr_imp by blast

theorem PiCore_abs_wsc_imp: "InfoFlow\<^sub>a.weak_step_consistentC \<Longrightarrow> InfoFlow\<^sub>c.weak_step_consistentC"
  using InfoFlow\<^sub>a.weak_step_consistentC_equiv InfoFlow\<^sub>c.weak_step_consistentC_equiv abs_wsc_imp by fastforce

end

end
