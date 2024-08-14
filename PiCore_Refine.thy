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

definition PiCore_SM\<^sub>c :: "(('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) pesconf, 'd, ('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c, 'd) action, 'o\<^sub>c) SM"
  where "PiCore_SM\<^sub>c \<equiv> \<lparr>s0 = C0\<^sub>c, step = step\<^sub>c, domain = domain, obs = obsc, vpeq = vpeqc, interference = interference\<^sub>c\<rparr>"

definition PiCore_SM\<^sub>a :: "(('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) pesconf, 'd, ('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a, 'd) action, 'o\<^sub>a) SM"
  where "PiCore_SM\<^sub>a \<equiv> \<lparr>s0 = C0\<^sub>a, step = step\<^sub>a, domain = domain, obs = obsa, vpeq = vpeqa, interference = interference\<^sub>a\<rparr>"

interpretation SM_Refine PiCore_SM\<^sub>c PiCore_SM\<^sub>a sim_s sim_a
proof
  show " \<forall>s t r d. vpeq PiCore_SM\<^sub>c s d t \<and> vpeq PiCore_SM\<^sub>c t d r \<longrightarrow> vpeq PiCore_SM\<^sub>c s d r"
    by (metis (no_types, opaque_lifting) InfoFlow\<^sub>c.vpeq_transitive PiCore_SM\<^sub>c_def SM.select_convs(5) vpeqc_def)
  show "\<forall>s t d. vpeq PiCore_SM\<^sub>c s d t \<longrightarrow> vpeq PiCore_SM\<^sub>c t d s"
    using InfoFlow\<^sub>c.vpeq_symmetric PiCore_SM\<^sub>c_def vpeqc_def by auto
  show "\<forall>s d. vpeq PiCore_SM\<^sub>c s d s"
    by (simp add: InfoFlow\<^sub>c.vpeq_reflexive PiCore_SM\<^sub>c_def vpeqc_def)
  show "\<forall>s t r d. vpeq PiCore_SM\<^sub>a s d t \<and> vpeq PiCore_SM\<^sub>a t d r \<longrightarrow> vpeq PiCore_SM\<^sub>a s d r"
    by (metis (no_types, lifting) InfoFlow\<^sub>a.vpeq_transitive PiCore_SM\<^sub>a_def SM.select_convs(5) vpeqa_def)
  show "\<forall>s t d. vpeq PiCore_SM\<^sub>a s d t \<longrightarrow> vpeq PiCore_SM\<^sub>a t d s"
    by (simp add: InfoFlow\<^sub>a.vpeq_symmetric PiCore_SM\<^sub>a_def vpeqa_def)
  show "\<forall>s d. vpeq PiCore_SM\<^sub>a s d s"
    by (simp add: InfoFlow\<^sub>a.vpeq_reflexive PiCore_SM\<^sub>a_def vpeqa_def)
  show " sim_s (s0 PiCore_SM\<^sub>c) = s0 PiCore_SM\<^sub>a"
    by (simp add: PiCore_SM\<^sub>a_def PiCore_SM\<^sub>c_def init_sim)
  show "\<And>ac aa sc tc. sim_a ac = Some aa \<longrightarrow> (sc, tc) \<in> step PiCore_SM\<^sub>c ac \<longrightarrow> (sim_s sc, sim_s tc) \<in> step PiCore_SM\<^sub>a aa"
    by (simp add: PiCore_SM\<^sub>a_def PiCore_SM\<^sub>c_def action_refine)
  show "\<And>ac sc tc. sim_a ac = None \<longrightarrow> (sc, tc) \<in> step PiCore_SM\<^sub>c ac \<longrightarrow> sim_s sc = sim_s tc"
    by (simp add: PiCore_SM\<^sub>c_def none_refine)
  show "interference PiCore_SM\<^sub>c = interference PiCore_SM\<^sub>a"
    using PiCore_SM\<^sub>a_def PiCore_SM\<^sub>c_def intefere_same by force
  show "\<And>ac aa. sim_a ac = Some aa \<longrightarrow> SM.domain PiCore_SM\<^sub>c ac = SM.domain PiCore_SM\<^sub>a aa"
    by (simp add: PiCore_SM\<^sub>a_def PiCore_SM\<^sub>c_def dom_refine)
  show " \<And>sc d tc. vpeq PiCore_SM\<^sub>a (sim_s sc) d (sim_s tc) = vpeq PiCore_SM\<^sub>c sc d tc"
    by (simp add: PiCore_SM\<^sub>a_def PiCore_SM\<^sub>c_def sim_ifs vpeqa_def vpeqc_def)
qed

theorem PiCore_abs_lr_imp: "local_respect PiCore_SM\<^sub>a \<Longrightarrow> local_respect PiCore_SM\<^sub>c"
  using abs_lr_imp by blast

theorem PiCore_abs_wsc_imp: "weak_step_consistent PiCore_SM\<^sub>a \<Longrightarrow> weak_step_consistent PiCore_SM\<^sub>c"
  using abs_wsc_imp by fastforce

end

end
