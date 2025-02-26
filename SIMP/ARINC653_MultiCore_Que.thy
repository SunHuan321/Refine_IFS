theory ARINC653_MultiCore_Que
  imports PiCore_SIMP_Syntax Ref_SIMP PiCore_SIMP_Ref
begin


subsection \<open>System specification\<close>

type_synonym max_buffer_size = nat
type_synonym buffer_size = nat

typedecl Part
typedecl Sched
typedecl Message 
typedecl Port
typedecl Core

typedecl QChannel

consts ARINC_Env\<^sub>c :: "SIMP_Env\<^sub>c"
consts ARINC_Env\<^sub>a :: "SIMP_Env\<^sub>a"

record Config = c2s :: "Core \<Rightarrow> Sched"
                p2s :: "Part \<Rightarrow> Sched"
                p2p :: "Port \<Rightarrow> Part"
                chsrc :: "QChannel \<Rightarrow> Port"
                chdest :: "QChannel \<Rightarrow> Port"  
                chmax :: "QChannel \<Rightarrow> nat"
axiomatization conf::Config 
  where bij_c2s: "bij (c2s conf)" 
  
lemma inj_surj_c2s: "inj (c2s conf) \<and> surj (c2s conf)"
  using bij_c2s by (simp add: bij_def) 

definition is_src_qport :: "Config \<Rightarrow> Port \<Rightarrow> bool"
  where "is_src_qport sc p \<equiv> (p\<in>range (chsrc sc))"

definition is_dest_qport :: "Config \<Rightarrow> Port \<Rightarrow> bool"
  where "is_dest_qport sc p \<equiv> (p\<in>range (chdest sc))"

definition port_of_part :: "Config \<Rightarrow> Port \<Rightarrow> Part \<Rightarrow> bool"
  where "port_of_part sc po pa \<equiv> ((p2p sc) po = pa)"

definition ch_srcqport :: "Config \<Rightarrow> Port \<Rightarrow> QChannel"
  where "ch_srcqport sc p \<equiv> SOME c. (chsrc sc) c = p"

definition ch_destqport :: "Config \<Rightarrow> Port \<Rightarrow> QChannel"
  where "ch_destqport sc p \<equiv> SOME c. (chdest sc) c = p"

datatype PartMode = IDLE | READY | RUN

datatype EL = Core_InitE  
  | ScheduleE Part
  | Send_Que_MessageE Port Message 
  | Recv_Que_MessageE Port

datatype Domain = P Part | S Sched | F 

type_synonym EventLabel = "EL \<times> Core" 

definition get_evt_label :: "EL \<Rightarrow> Core \<Rightarrow> EventLabel" ("_ \<rhd> _" [0,0] 20)
  where "get_evt_label el k \<equiv> (el,k)"

primrec part_on_core :: "Config \<Rightarrow> Domain \<Rightarrow> Domain \<Rightarrow> bool"
  where "part_on_core cfg (P d1) d2 = (case d2 of
                                        P d22 \<Rightarrow> False |
                                        S d22 \<Rightarrow> d22 = ((p2s cfg) d1) |
                                        F \<Rightarrow> False )" |
        "part_on_core cfg (S d1) d2 = False" |
        "part_on_core cfg F d2 = False"

definition ch_conn :: "Config \<Rightarrow> Part \<Rightarrow> Part \<Rightarrow> bool"
  where "ch_conn cfg p1 p2 \<equiv> (\<exists>ch. (p2p cfg) ((chsrc cfg) ch) = p1 \<and> (p2p cfg) ((chdest cfg) ch) = p2)"

primrec ch_conn2 :: "Config \<Rightarrow> Domain \<Rightarrow> Domain \<Rightarrow> bool"
  where "ch_conn2 cfg (P p1) d2 = (case d2 of
                                    (P p2) \<Rightarrow> ch_conn cfg p1 p2 |
                                    (S s2) \<Rightarrow> False |
                                      F  \<Rightarrow> False)" |                                     
        "ch_conn2 cfg (S p1) d2 = False" |
        "ch_conn2 cfg F d2 = False"

definition interf :: "Domain \<Rightarrow> Domain \<Rightarrow> bool" ("(_ \<leadsto> _)" [70,71] 60)
  where "interf d1 d2 \<equiv> if d1 = d2 then True
                         else if part_on_core conf d2 d1 then True
                         else if ch_conn2 conf d1 d2 then True
                         else False"

definition noninterf :: "Domain \<Rightarrow> Domain \<Rightarrow> bool" ("(_ \<setminus>\<leadsto> _)" [70,71] 60)
  where "u \<setminus>\<leadsto> v \<equiv> \<not> (u \<leadsto> v)"

subsubsection \<open>Implementation Specification\<close>

record State\<^sub>c = cur\<^sub>c :: "Sched \<Rightarrow> Part option"
                qlock\<^sub>c :: "QChannel \<Rightarrow> Core option"
                qbuf\<^sub>c :: "QChannel \<Rightarrow> Message list"
                qbufsize\<^sub>c :: "QChannel \<Rightarrow> nat"
                obsize\<^sub>c :: "QChannel \<Rightarrow> nat"
                partst\<^sub>c :: "Part \<Rightarrow> PartMode"

type_synonym Prog\<^sub>c = "State\<^sub>c com option"

definition Core_Init\<^sub>c :: "Core \<Rightarrow> (EventLabel, Core, State\<^sub>c, Prog\<^sub>c) event" 
  where "Core_Init\<^sub>c k \<equiv> 
    EVENT Core_InitE \<rhd> k 
    THEN      
      \<acute>partst\<^sub>c := (\<lambda>p. if p2s conf p = c2s conf k \<and> \<acute>partst\<^sub>c p = IDLE then READY else \<acute>partst\<^sub>c p) 
    END"

definition System_Init\<^sub>c :: "Config \<Rightarrow> (State\<^sub>c \<times> (EventLabel, Core, State\<^sub>c, Prog\<^sub>c) x)"
  where "System_Init\<^sub>c cfg \<equiv> (\<lparr>cur\<^sub>c=(\<lambda>s. None),
                            qlock\<^sub>c = (\<lambda>c. None),
                            qbuf\<^sub>c = (\<lambda>c. []),
                            qbufsize\<^sub>c = (\<lambda>c. 0),
                            obsize\<^sub>c = (\<lambda>c. 0),
                            partst\<^sub>c = (\<lambda>p. IDLE)\<rparr>, 
                            (\<lambda>k. Core_Init\<^sub>c k))"

definition Schedule\<^sub>c :: "Core \<Rightarrow> Part \<Rightarrow> (EventLabel, Core, State\<^sub>c, Prog\<^sub>c) event" 
  where "Schedule\<^sub>c k p \<equiv> 
    EVENT ScheduleE p \<rhd> k 
    WHERE
      p2s conf p = c2s conf k \<and> (\<acute>partst\<^sub>c p \<noteq> IDLE) \<and> (\<acute>cur\<^sub>c (c2s conf k) = None 
          \<or> p2s conf (the (\<acute>cur\<^sub>c((c2s conf) k))) = c2s conf k)
    THEN
        ATOMIC
          IF (\<acute>cur\<^sub>c((c2s conf) k) \<noteq> None) THEN    
           \<acute>partst\<^sub>c := \<acute>partst\<^sub>c(the (\<acute>cur\<^sub>c ((c2s conf) k)) := READY);;
           \<acute>cur\<^sub>c := \<acute>cur\<^sub>c((c2s conf) k := None)
          FI;;
         \<acute>cur\<^sub>c := \<acute>cur\<^sub>c((c2s conf k) := Some p);;
         \<acute>partst\<^sub>c := \<acute>partst\<^sub>c(p := RUN)
        END
    END"

definition Send_Que_Message\<^sub>c :: "Core \<Rightarrow> Port \<Rightarrow> Message \<Rightarrow> (EventLabel, Core, State\<^sub>c, Prog\<^sub>c) event" 
  where "Send_Que_Message\<^sub>c k p m \<equiv> 
    EVENT Send_Que_MessageE p m \<rhd> k 
    WHERE
      is_src_qport conf p
      \<and> \<acute>cur\<^sub>c (c2s conf k) \<noteq> None
      \<and> port_of_part conf p (the (\<acute>cur\<^sub>c (c2s conf k)))
    THEN
      AWAIT \<acute>qlock\<^sub>c (ch_srcqport conf p) = None THEN
        \<acute>qlock\<^sub>c := \<acute>qlock\<^sub>c (ch_srcqport conf p := Some k)
      END;;
      IF \<acute>qbufsize\<^sub>c (ch_srcqport conf p) < chmax conf (ch_srcqport conf p) THEN 
        \<acute>qbuf\<^sub>c := \<acute>qbuf\<^sub>c (ch_srcqport conf p := \<acute>qbuf\<^sub>c (ch_srcqport conf p) @ [m]);;
        \<acute>qbufsize\<^sub>c := \<acute>qbufsize\<^sub>c (ch_srcqport conf p := \<acute>qbufsize\<^sub>c (ch_srcqport conf p) + 1)
      FI;;
      ATOMIC
        \<acute>qlock\<^sub>c := \<acute>qlock\<^sub>c (ch_srcqport conf p := None);;
        \<acute>obsize\<^sub>c := \<acute>obsize\<^sub>c (ch_srcqport conf p := \<acute>qbufsize\<^sub>c (ch_srcqport conf p))
      END   
    END"

definition Recv_Que_Message\<^sub>c :: "Core \<Rightarrow> Port \<Rightarrow> (EventLabel, Core, State\<^sub>c, Prog\<^sub>c) event" 
  where "Recv_Que_Message\<^sub>c k p \<equiv> 
    EVENT Recv_Que_MessageE p \<rhd> k 
    WHERE
      is_dest_qport conf p 
      \<and> \<acute>cur\<^sub>c (c2s conf k) \<noteq> None
      \<and> port_of_part conf p (the (\<acute>cur\<^sub>c (c2s conf k)))
    THEN 
      AWAIT \<acute>qlock\<^sub>c (ch_destqport conf p) = None THEN
        \<acute>qlock\<^sub>c := \<acute>qlock\<^sub>c (ch_destqport conf p := Some k)
      END;;
      IF \<acute>qbufsize\<^sub>c (ch_destqport conf p) > 0 THEN 
        \<acute>qbuf\<^sub>c := \<acute>qbuf\<^sub>c (ch_destqport conf p := tl (\<acute>qbuf\<^sub>c (ch_destqport conf p)));;
        \<acute>qbufsize\<^sub>c := \<acute>qbufsize\<^sub>c (ch_destqport conf p := \<acute>qbufsize\<^sub>c (ch_destqport conf p) - 1)
      FI;;
      ATOMIC
        \<acute>qlock\<^sub>c := \<acute>qlock\<^sub>c (ch_destqport conf p := None);;
        \<acute>obsize\<^sub>c := \<acute>obsize\<^sub>c (ch_destqport conf p := \<acute>qbufsize\<^sub>c (ch_destqport conf p))
      END
    END"


definition EvtSys_on_Core\<^sub>c :: "Core \<Rightarrow> (EventLabel, Core, State\<^sub>c, Prog\<^sub>c) esys"
  where "EvtSys_on_Core\<^sub>c k = EvtSeq (Core_Init\<^sub>c k) (EvtSys
  (\<Union>p.{Schedule\<^sub>c k p} \<union> (\<Union>(p, m). {Send_Que_Message\<^sub>c k p m}) \<union> (\<Union>p.{Recv_Que_Message\<^sub>c k p})))"

definition ARINCXKernel_Spec\<^sub>c :: "(EventLabel, Core, State\<^sub>c, Prog\<^sub>c) paresys"
  where "ARINCXKernel_Spec\<^sub>c \<equiv> (\<lambda>k. EvtSys_on_Core\<^sub>c k)"

axiomatization s0\<^sub>c where s0c_init: "s0\<^sub>c \<equiv> fst (System_Init\<^sub>c conf)"
axiomatization x0\<^sub>c where x0c_init: "x0\<^sub>c \<equiv> snd (System_Init\<^sub>c conf)"
axiomatization C0\<^sub>c where C0c_init: "C0\<^sub>c = (ARINCXKernel_Spec\<^sub>c, s0\<^sub>c, x0\<^sub>c)"

(*
definition domevt\<^sub>c :: "State\<^sub>c \<Rightarrow> (EventLabel, Core, State\<^sub>c, Prog\<^sub>c) event \<Rightarrow> Domain"
  where "domevt\<^sub>c s e \<equiv> let c = get_evt_core e in (let el = get_evt_el e in  
                         (if (el_is_on_Part el \<and> is_basicevt e) 
                              \<and> (cur\<^sub>c s) (c2s conf c) \<noteq> None
                              then P (the ((cur\<^sub>c s) (c2s conf c)))
                          else if (el_is_on_Sched el \<and> is_basicevt e) then S (c2s conf c)
                          else F))" 
*)

primrec el_domevt\<^sub>c :: "EL \<Rightarrow> Core \<Rightarrow> State\<^sub>c \<Rightarrow> Domain"
  where "el_domevt\<^sub>c Core_InitE k s = S (c2s conf k)"
  | "el_domevt\<^sub>c (ScheduleE _) k s = S (c2s conf k)"
  | "el_domevt\<^sub>c (Send_Que_MessageE _ _) k s = (case ((cur\<^sub>c s) (c2s conf k)) of None \<Rightarrow> F | Some p \<Rightarrow> P p)"
  | "el_domevt\<^sub>c (Recv_Que_MessageE _) k s = (case ((cur\<^sub>c s) (c2s conf k)) of None \<Rightarrow> F | Some p \<Rightarrow> P p)"

primrec domevt\<^sub>c :: "State\<^sub>c \<Rightarrow> (EventLabel, Core, State\<^sub>c, Prog\<^sub>c) event \<Rightarrow> Domain"
  where "domevt\<^sub>c s (AnonyEvent _) = F"
  | "domevt\<^sub>c s (BasicEvent e) = el_domevt\<^sub>c (fst (label e)) (snd (label e)) s"

definition exec_step\<^sub>c :: "SIMP_Env\<^sub>c \<Rightarrow> (EventLabel, Core, State\<^sub>c, Prog\<^sub>c, Domain) action \<Rightarrow> 
 ((EventLabel, Core, State\<^sub>c, Prog\<^sub>c) pesconf \<times> (EventLabel, Core, State\<^sub>c, Prog\<^sub>c) pesconf) set"
  where "exec_step\<^sub>c \<Gamma>\<^sub>c a \<equiv> {(P,Q). (\<Gamma>\<^sub>c \<turnstile>\<^sub>c P-pes-(actk a)\<rightarrow> Q) \<and>((\<exists>e k. actk a = ((EvtEnt e)\<sharp>k) \<and> eventof a = e 
                         \<and> domevt\<^sub>c (gets P) e = domain a) \<or> (\<exists>c k. actk a = ((Cmd c)\<sharp>k) 
                         \<and> eventof a = (getx P) k \<and> domevt\<^sub>c (gets P) (eventof a) = domain a))}"

definition state_obs_sched\<^sub>c :: "State\<^sub>c \<Rightarrow> Sched \<Rightarrow> State\<^sub>c"
  where "state_obs_sched\<^sub>c s d \<equiv> s0\<^sub>c\<lparr>cur\<^sub>c :=(cur\<^sub>c s0\<^sub>c) (d := (cur\<^sub>c s) d)\<rparr>"

definition obs_cap_part\<^sub>c :: "State\<^sub>c \<Rightarrow> Part \<Rightarrow> (QChannel \<Rightarrow> nat)"
  where "obs_cap_part\<^sub>c s p  \<equiv> \<lambda>c. if (p2p conf) ((chdest conf) c) = p then obsize\<^sub>c s c else obsize\<^sub>c s0\<^sub>c c"

lemma obs_cap_equivc : "\<lbrakk>\<forall>c. p2p conf (chdest conf c) = x1 \<longrightarrow> obsize\<^sub>c s1 c = obsize\<^sub>c s2 c\<rbrakk> 
                        \<Longrightarrow>  obs_cap_part\<^sub>c s2 x1 = obs_cap_part\<^sub>c s1 x1"
  apply (simp add: obs_cap_part\<^sub>c_def)
  by force

definition state_obs_part\<^sub>c :: "State\<^sub>c \<Rightarrow> Part \<Rightarrow> State\<^sub>c"
  where "state_obs_part\<^sub>c s p \<equiv> s0\<^sub>c\<lparr>partst\<^sub>c := (partst\<^sub>c s0\<^sub>c) (p := (partst\<^sub>c s) p), 
                                  obsize\<^sub>c := obs_cap_part\<^sub>c s p\<rparr>"

primrec state_obs\<^sub>c :: "State\<^sub>c \<Rightarrow> Domain \<Rightarrow> State\<^sub>c"
  where "state_obs\<^sub>c s (P p) = state_obs_part\<^sub>c s p" |
        "state_obs\<^sub>c s (S p) = state_obs_sched\<^sub>c s p"|
        "state_obs\<^sub>c s F = s0\<^sub>c"

definition state_equiv\<^sub>c :: "State\<^sub>c \<Rightarrow> Domain \<Rightarrow> State\<^sub>c \<Rightarrow> bool" ("(_ \<sim>\<^sub>c_\<sim>\<^sub>c _)" [70,69,70] 60)
  where "state_equiv\<^sub>c s d t \<equiv> state_obs\<^sub>c s d = state_obs\<^sub>c t d"

lemma state_equiv_transitivec: "\<lbrakk>s \<sim>\<^sub>c d \<sim>\<^sub>c t; t \<sim>\<^sub>c d \<sim>\<^sub>c r\<rbrakk> \<Longrightarrow> s \<sim>\<^sub>c d \<sim>\<^sub>c r"
  by (simp add:state_equiv\<^sub>c_def)
    
lemma state_equiv_symmetricc : "s \<sim>\<^sub>c d \<sim>\<^sub>c t \<Longrightarrow> t \<sim>\<^sub>c d \<sim>\<^sub>c s"
  by (simp add:state_equiv\<^sub>c_def)

lemma state_equiv_reflexivec : "s \<sim>\<^sub>c d \<sim>\<^sub>c s"
  by (simp add:state_equiv\<^sub>c_def)


interpretation ARINC653\<^sub>c: InfoFlow ptranI\<^sub>c petranI\<^sub>c None ARINC_Env\<^sub>c C0\<^sub>c "exec_step\<^sub>c ARINC_Env\<^sub>c" interf state_equiv\<^sub>c state_obs\<^sub>c domevt\<^sub>c
proof
  show "\<forall>a b c u. a \<sim>\<^sub>cu\<sim>\<^sub>c b \<and> b \<sim>\<^sub>cu\<sim>\<^sub>c c \<longrightarrow> a \<sim>\<^sub>cu\<sim>\<^sub>c c"
    using state_equiv_transitivec by blast
  show "\<forall>a b u. a \<sim>\<^sub>cu\<sim>\<^sub>c b \<longrightarrow> b \<sim>\<^sub>cu\<sim>\<^sub>c a"
    using state_equiv_symmetricc by blast
  show "\<forall>a u. a \<sim>\<^sub>cu\<sim>\<^sub>c a"
    by (simp add: state_equiv_reflexivec)
  show "\<And>a. exec_step\<^sub>c ARINC_Env\<^sub>c a \<equiv> {(P, Q). ARINC_Env\<^sub>c \<turnstile>\<^sub>c P -pes-actk a\<rightarrow> Q \<and> 
        ((\<exists>e k. actk a = EvtEnt e\<sharp>k \<and> eventof a = e \<and> domevt\<^sub>c (gets P) e = domain a) 
        \<or> (\<exists>c k. actk a = Cmd c\<sharp>k \<and> eventof a = getx P k \<and> domevt\<^sub>c (gets P) (eventof a) = domain a))}"
    by (simp add: exec_step\<^sub>c_def) 
qed

subsubsection \<open>Abstraction Specification\<close>

record State\<^sub>a = cur\<^sub>a :: "Sched \<Rightarrow> Part option"
                qbuf\<^sub>a :: "QChannel \<Rightarrow> Message list"
                qbufsize\<^sub>a :: "QChannel \<Rightarrow> nat"              
                partst\<^sub>a :: "Part \<Rightarrow> PartMode"

type_synonym Prog\<^sub>a = "State\<^sub>a com option"

definition Core_Init\<^sub>a :: "Core \<Rightarrow> (EventLabel, Core, State\<^sub>a, Prog\<^sub>a) event" 
  where "Core_Init\<^sub>a k \<equiv> 
    EVENT Core_InitE \<rhd> k 
    THEN      
      \<acute>partst\<^sub>a := (\<lambda>p. if p2s conf p = c2s conf k \<and> \<acute>partst\<^sub>a p = IDLE then READY else \<acute>partst\<^sub>a p)
    END"

definition System_Init\<^sub>a :: "Config \<Rightarrow> (State\<^sub>a \<times> (EventLabel, Core, State\<^sub>a, Prog\<^sub>a) x)"
  where "System_Init\<^sub>a cfg \<equiv> (\<lparr>cur\<^sub>a=(\<lambda>s. None),
                            qbuf\<^sub>a = (\<lambda>c. []),
                            qbufsize\<^sub>a = (\<lambda>c. 0),
                            partst\<^sub>a = (\<lambda>p. IDLE)\<rparr>, 
                            (\<lambda>k. Core_Init\<^sub>a k))"

definition Schedule\<^sub>a :: "Core \<Rightarrow> Part \<Rightarrow> (EventLabel, Core, State\<^sub>a, Prog\<^sub>a) event" 
  where "Schedule\<^sub>a k p \<equiv> 
    EVENT ScheduleE p \<rhd> k 
    WHERE
      p2s conf p = c2s conf k \<and> (\<acute>partst\<^sub>a p \<noteq> IDLE) \<and> (\<acute>cur\<^sub>a (c2s conf k) = None 
          \<or> p2s conf (the (\<acute>cur\<^sub>a((c2s conf) k))) = c2s conf k)
    THEN
        ATOMIC
          IF (\<acute>cur\<^sub>a((c2s conf) k) \<noteq> None) THEN    
           \<acute>partst\<^sub>a := \<acute>partst\<^sub>a(the (\<acute>cur\<^sub>a ((c2s conf) k)) := READY)
          FI;;
         \<acute>cur\<^sub>a := \<acute>cur\<^sub>a((c2s conf k) := Some p);;
         \<acute>partst\<^sub>a := \<acute>partst\<^sub>a(p := RUN)
        END
    END"

definition Send_Que_Message\<^sub>a :: "Core \<Rightarrow> Port \<Rightarrow> Message \<Rightarrow> (EventLabel, Core, State\<^sub>a, Prog\<^sub>a) event" 
  where "Send_Que_Message\<^sub>a k p m \<equiv> 
    EVENT Send_Que_MessageE p m \<rhd> k 
    WHERE
      is_src_qport conf p
      \<and> \<acute>cur\<^sub>a (c2s conf k) \<noteq> None
      \<and> port_of_part conf p (the (\<acute>cur\<^sub>a (c2s conf k)))
    THEN
      ATOMIC
        IF \<acute>qbufsize\<^sub>a (ch_srcqport conf p) < chmax conf (ch_srcqport conf p) THEN 
          \<acute>qbuf\<^sub>a := \<acute>qbuf\<^sub>a (ch_srcqport conf p := \<acute>qbuf\<^sub>a (ch_srcqport conf p) @ [m]);;
          \<acute>qbufsize\<^sub>a := \<acute>qbufsize\<^sub>a (ch_srcqport conf p := \<acute>qbufsize\<^sub>a (ch_srcqport conf p) + 1)
        FI
      END  
    END"

definition Recv_Que_Message\<^sub>a :: "Core \<Rightarrow> Port \<Rightarrow> (EventLabel, Core, State\<^sub>a, Prog\<^sub>a) event" 
  where "Recv_Que_Message\<^sub>a k p \<equiv> 
    EVENT Recv_Que_MessageE p \<rhd> k 
    WHERE
      is_dest_qport conf p 
      \<and> \<acute>cur\<^sub>a (c2s conf k) \<noteq> None
      \<and> port_of_part conf p (the (\<acute>cur\<^sub>a (c2s conf k)))
    THEN 
      ATOMIC
        IF \<acute>qbufsize\<^sub>a (ch_destqport conf p) > 0 THEN 
        \<acute>qbuf\<^sub>a := \<acute>qbuf\<^sub>a (ch_destqport conf p := tl (\<acute>qbuf\<^sub>a (ch_destqport conf p)));;
        \<acute>qbufsize\<^sub>a := \<acute>qbufsize\<^sub>a (ch_destqport conf p := \<acute>qbufsize\<^sub>a (ch_destqport conf p) - 1)
        FI
      END
    END"

definition EvtSys_on_Core\<^sub>a :: "Core \<Rightarrow> (EventLabel, Core, State\<^sub>a, Prog\<^sub>a) esys"
  where "EvtSys_on_Core\<^sub>a k = EvtSeq (Core_Init\<^sub>a k) (EvtSys
  (\<Union>p.{Schedule\<^sub>a k p} \<union> (\<Union>(p, m). {Send_Que_Message\<^sub>a k p m}) \<union> (\<Union>p.{Recv_Que_Message\<^sub>a k p})))"

definition ARINCXKernel_Spec\<^sub>a :: "(EventLabel, Core, State\<^sub>a, Prog\<^sub>a) paresys"
  where "ARINCXKernel_Spec\<^sub>a \<equiv> (\<lambda>k. EvtSys_on_Core\<^sub>a k)"

axiomatization s0\<^sub>a where s0a_init: "s0\<^sub>a \<equiv> fst (System_Init\<^sub>a conf)"
axiomatization x0\<^sub>a where x0a_init: "x0\<^sub>a \<equiv> snd (System_Init\<^sub>a conf)"
axiomatization C0\<^sub>a where C0a_init: "C0\<^sub>a = (ARINCXKernel_Spec\<^sub>a, s0\<^sub>a, x0\<^sub>a)"


primrec el_domevt\<^sub>a :: "EL \<Rightarrow> Core \<Rightarrow> State\<^sub>a \<Rightarrow> Domain"
  where "el_domevt\<^sub>a Core_InitE k s = S (c2s conf k)"
  | "el_domevt\<^sub>a (ScheduleE _) k s = S (c2s conf k)"
  | "el_domevt\<^sub>a (Send_Que_MessageE _ _) k s = (case ((cur\<^sub>a s) (c2s conf k)) of None \<Rightarrow> F | Some p \<Rightarrow> P p)"
  | "el_domevt\<^sub>a (Recv_Que_MessageE _) k s = (case ((cur\<^sub>a s) (c2s conf k)) of None \<Rightarrow> F | Some p \<Rightarrow> P p)"

primrec domevt\<^sub>a :: "State\<^sub>a \<Rightarrow> (EventLabel, Core, State\<^sub>a, Prog\<^sub>a) event \<Rightarrow> Domain"
  where "domevt\<^sub>a s (AnonyEvent _) = F"
  | "domevt\<^sub>a s (BasicEvent e) = el_domevt\<^sub>a (fst (label e)) (snd (label e)) s"

definition exec_step\<^sub>a :: "SIMP_Env\<^sub>a \<Rightarrow> (EventLabel, Core, State\<^sub>a, Prog\<^sub>a, Domain) action \<Rightarrow> 
 ((EventLabel, Core, State\<^sub>a, Prog\<^sub>a) pesconf \<times> (EventLabel, Core, State\<^sub>a, Prog\<^sub>a) pesconf) set"
  where "exec_step\<^sub>a \<Gamma>\<^sub>a a \<equiv> {(P,Q). (\<Gamma>\<^sub>a \<turnstile>\<^sub>a P-pes-(actk a)\<rightarrow> Q) \<and>((\<exists>e k. actk a = ((EvtEnt e)\<sharp>k) \<and> eventof a = e 
                         \<and> domevt\<^sub>a (gets P) e = domain a) \<or> (\<exists>c k. actk a = ((Cmd c)\<sharp>k) 
                         \<and> eventof a = (getx P) k \<and> domevt\<^sub>a (gets P) (eventof a) = domain a))}"

definition state_obs_sched\<^sub>a :: "State\<^sub>a \<Rightarrow> Sched \<Rightarrow> State\<^sub>a"
  where "state_obs_sched\<^sub>a s d \<equiv> s0\<^sub>a\<lparr>cur\<^sub>a :=(cur\<^sub>a s0\<^sub>a) (d := (cur\<^sub>a s) d)\<rparr>"

definition obs_cap_part\<^sub>a :: "State\<^sub>a \<Rightarrow> Part \<Rightarrow> (QChannel \<Rightarrow> nat)"
  where "obs_cap_part\<^sub>a s p  \<equiv> \<lambda>c. if (p2p conf) ((chdest conf) c) = p then qbufsize\<^sub>a s c else qbufsize\<^sub>a s0\<^sub>a c"

lemma obs_cap_equiva : "\<lbrakk>\<forall>c. p2p conf (chdest conf c) = x1 \<longrightarrow> qbufsize\<^sub>a s1 c = qbufsize\<^sub>a s2 c\<rbrakk> 
                        \<Longrightarrow>  obs_cap_part\<^sub>a s2 x1 = obs_cap_part\<^sub>a s1 x1"
  apply (simp add: obs_cap_part\<^sub>a_def)
  by force

definition state_obs_part\<^sub>a :: "State\<^sub>a \<Rightarrow> Part \<Rightarrow> State\<^sub>a"
  where "state_obs_part\<^sub>a s p \<equiv> s0\<^sub>a\<lparr>partst\<^sub>a := (partst\<^sub>a s0\<^sub>a) (p := (partst\<^sub>a s) p), 
                                  qbufsize\<^sub>a := obs_cap_part\<^sub>a s p\<rparr>"

primrec state_obs\<^sub>a :: "State\<^sub>a \<Rightarrow> Domain \<Rightarrow> State\<^sub>a"
  where "state_obs\<^sub>a s (P p) = state_obs_part\<^sub>a s p" |
        "state_obs\<^sub>a s (S p) = state_obs_sched\<^sub>a s p"|
        "state_obs\<^sub>a s F = s0\<^sub>a"

definition state_equiv\<^sub>a :: "State\<^sub>a \<Rightarrow> Domain \<Rightarrow> State\<^sub>a \<Rightarrow> bool" ("(_ \<sim>\<^sub>a_\<sim>\<^sub>a _)" [70,69,70] 60)
  where "state_equiv\<^sub>a s d t \<equiv> state_obs\<^sub>a s d = state_obs\<^sub>a t d"

lemma state_equiv_transitivea: "\<lbrakk>s \<sim>\<^sub>a d \<sim>\<^sub>a t; t \<sim>\<^sub>a d \<sim>\<^sub>a r\<rbrakk> \<Longrightarrow> s \<sim>\<^sub>a d \<sim>\<^sub>a r"
  by (simp add:state_equiv\<^sub>a_def)
    
lemma state_equiv_symmetrica : "s \<sim>\<^sub>a d \<sim>\<^sub>a t \<Longrightarrow> t \<sim>\<^sub>a d \<sim>\<^sub>a s"
  by (simp add:state_equiv\<^sub>a_def)

lemma state_equiv_reflexivea : "s \<sim>\<^sub>a d \<sim>\<^sub>a s"
  by (simp add:state_equiv\<^sub>a_def)

interpretation ARINC653\<^sub>a: InfoFlow ptranI\<^sub>a petranI\<^sub>a None ARINC_Env\<^sub>a C0\<^sub>a "exec_step\<^sub>a ARINC_Env\<^sub>a" interf state_equiv\<^sub>a state_obs\<^sub>a domevt\<^sub>a
proof
  show "\<forall>a b c u. a \<sim>\<^sub>au\<sim>\<^sub>a b \<and> b \<sim>\<^sub>au\<sim>\<^sub>a c \<longrightarrow> a \<sim>\<^sub>au\<sim>\<^sub>a c"
    using state_equiv_transitivea by blast
  show "\<forall>a b u. a \<sim>\<^sub>au\<sim>\<^sub>a b \<longrightarrow> b \<sim>\<^sub>au\<sim>\<^sub>a a"
    using state_equiv_symmetrica by blast
  show " \<forall>a u. a \<sim>\<^sub>au\<sim>\<^sub>a a"
    by (simp add: state_equiv_reflexivea)
  show "\<And>a. exec_step\<^sub>a ARINC_Env\<^sub>a a \<equiv> {(P, Q). ARINC_Env\<^sub>a \<turnstile>\<^sub>a P -pes-actk a\<rightarrow> Q \<and> 
        ((\<exists>e k. actk a = EvtEnt e\<sharp>k \<and> eventof a = e \<and> domevt\<^sub>a (gets P) e = domain a) \<or> 
        (\<exists>c k. actk a = Cmd c\<sharp>k \<and> eventof a = getx P k \<and> domevt\<^sub>a (gets P) (eventof a) = domain a))} "
    by (simp add: exec_step\<^sub>a_def) 
qed

subsection \<open>Simulation Relation\<close>

definition state_inv :: " (State\<^sub>c \<times> State\<^sub>a) set" 
  where "state_inv = {(s\<^sub>c, s\<^sub>a). cur\<^sub>c s\<^sub>c = cur\<^sub>a s\<^sub>a \<and> partst\<^sub>c s\<^sub>c = partst\<^sub>a s\<^sub>a \<and> obsize\<^sub>c s\<^sub>c = qbufsize\<^sub>a s\<^sub>a
         \<and> (\<forall>q. qlock\<^sub>c s\<^sub>c q = None \<longrightarrow> obsize\<^sub>c s\<^sub>c q = qbufsize\<^sub>c s\<^sub>c q)}"

primrec ev_el_map :: "EL \<Rightarrow> Core \<Rightarrow> (EventLabel, Core, State\<^sub>a, Prog\<^sub>a) event"
  where "ev_el_map Core_InitE k = Core_Init\<^sub>a k"
  | "ev_el_map (ScheduleE p) k = Schedule\<^sub>a k p"
  | "ev_el_map (Send_Que_MessageE p m) k = Send_Que_Message\<^sub>a k p m"
  | "ev_el_map (Recv_Que_MessageE p) k = Recv_Que_Message\<^sub>a k p"

primrec ev_map :: "(EventLabel, Core, State\<^sub>c, Prog\<^sub>c) event \<Rightarrow> (EventLabel, Core, State\<^sub>a, Prog\<^sub>a) event"
  where "ev_map (AnonyEvent _) = AnonyEvent None"
  | "ev_map (BasicEvent e) = ev_el_map (fst (label e)) (snd (label e))"

lemma ev_map_init: "ev_map (Core_Init\<^sub>c k) = Core_Init\<^sub>a k"
  by (simp add: ev_map_def get_evt_label_def label_def Core_Init\<^sub>c_def)

lemma ev_map_schedule: "ev_map (Schedule\<^sub>c k p) = Schedule\<^sub>a k p"
  by (simp add: ev_map_def get_evt_label_def label_def Schedule\<^sub>c_def)

lemma ev_map_send: "ev_map (Send_Que_Message\<^sub>c k p m) = Send_Que_Message\<^sub>a k p m"
  by (simp add: ev_map_def get_evt_label_def label_def Send_Que_Message\<^sub>c_def)

lemma ev_map_recv: "ev_map (Recv_Que_Message\<^sub>c k p) = Recv_Que_Message\<^sub>a k p"
  by (simp add: ev_map_def get_evt_label_def label_def Recv_Que_Message\<^sub>c_def)

definition init_map :: "Core \<Rightarrow> State\<^sub>c com \<rightharpoonup> State\<^sub>a com"
  where "init_map k = 
        [ \<acute>partst\<^sub>c := (\<lambda>p. if p2s conf p = c2s conf k \<and> \<acute>partst\<^sub>c p = IDLE then READY else \<acute>partst\<^sub>c p)
       \<mapsto> \<acute>partst\<^sub>a := (\<lambda>p. if p2s conf p = c2s conf k \<and> \<acute>partst\<^sub>a p = IDLE then READY else \<acute>partst\<^sub>a p)]"

definition schedule_map :: "Core \<Rightarrow> Part \<Rightarrow> State\<^sub>c com \<rightharpoonup> State\<^sub>a com"
  where "schedule_map k p = 
        [ATOMIC
           IF (\<acute>cur\<^sub>c((c2s conf) k) \<noteq> None) THEN    
             \<acute>partst\<^sub>c := \<acute>partst\<^sub>c(the (\<acute>cur\<^sub>c ((c2s conf) k)) := READY);;
             \<acute>cur\<^sub>c := \<acute>cur\<^sub>c((c2s conf) k := None)
           FI;;
           \<acute>cur\<^sub>c := \<acute>cur\<^sub>c((c2s conf k) := Some p);;
           \<acute>partst\<^sub>c := \<acute>partst\<^sub>c(p := RUN)
         END
      \<mapsto> ATOMIC
           IF (\<acute>cur\<^sub>a((c2s conf) k) \<noteq> None) THEN    
             \<acute>partst\<^sub>a := \<acute>partst\<^sub>a(the (\<acute>cur\<^sub>a ((c2s conf) k)) := READY)
           FI;;
           \<acute>cur\<^sub>a := \<acute>cur\<^sub>a((c2s conf k) := Some p);;
           \<acute>partst\<^sub>a := \<acute>partst\<^sub>a(p := RUN)
         END]"

definition send_map :: "Core \<Rightarrow> Port \<Rightarrow> Message \<Rightarrow> State\<^sub>c com \<rightharpoonup> State\<^sub>a com"
  where "send_map k p m = 
        [ATOMIC
          \<acute>qlock\<^sub>c := \<acute>qlock\<^sub>c (ch_srcqport conf p := None);;
          \<acute>obsize\<^sub>c := \<acute>obsize\<^sub>c (ch_srcqport conf p := \<acute>qbufsize\<^sub>c (ch_srcqport conf p))
         END
      \<mapsto> ATOMIC
          IF \<acute>qbufsize\<^sub>a (ch_srcqport conf p) < chmax conf (ch_srcqport conf p) THEN 
            \<acute>qbuf\<^sub>a := \<acute>qbuf\<^sub>a (ch_srcqport conf p := \<acute>qbuf\<^sub>a (ch_srcqport conf p) @ [m]);;
            \<acute>qbufsize\<^sub>a := \<acute>qbufsize\<^sub>a (ch_srcqport conf p := \<acute>qbufsize\<^sub>a (ch_srcqport conf p) + 1)
          FI
          END]"

definition recv_map :: "Core \<Rightarrow> Port \<Rightarrow> State\<^sub>c com \<rightharpoonup> State\<^sub>a com"
  where "recv_map k p = 
        [ATOMIC
          \<acute>qlock\<^sub>c := \<acute>qlock\<^sub>c (ch_destqport conf p := None);;
          \<acute>obsize\<^sub>c := \<acute>obsize\<^sub>c (ch_destqport conf p := \<acute>qbufsize\<^sub>c (ch_destqport conf p))
         END
      \<mapsto> ATOMIC
           IF \<acute>qbufsize\<^sub>a (ch_destqport conf p) > 0 THEN 
             \<acute>qbuf\<^sub>a := \<acute>qbuf\<^sub>a (ch_destqport conf p := tl (\<acute>qbuf\<^sub>a (ch_destqport conf p)));;
             \<acute>qbufsize\<^sub>a := \<acute>qbufsize\<^sub>a (ch_destqport conf p := \<acute>qbufsize\<^sub>a (ch_destqport conf p) - 1)
           FI
         END]"

primrec ev_el_prog_map :: "EL \<Rightarrow> Core \<Rightarrow> State\<^sub>c com \<rightharpoonup> State\<^sub>a com"
  where "ev_el_prog_map Core_InitE k = init_map k"
  | "ev_el_prog_map (ScheduleE p) k = schedule_map k p"
  | "ev_el_prog_map (Send_Que_MessageE p m) k = send_map k p m"
  | "ev_el_prog_map (Recv_Que_MessageE p) k = recv_map k p"

primrec ev_prog_map :: "(EventLabel, Core, State\<^sub>c, Prog\<^sub>c) event \<Rightarrow> State\<^sub>c com option \<rightharpoonup> State\<^sub>a com option"
  where "ev_prog_map (AnonyEvent _) = Map.empty"
  | "ev_prog_map (BasicEvent e) = zetaI (ev_el_prog_map (fst (label e)) (snd (label e)))"

lemma ev_prog_map_init: "ev_prog_map (Core_Init\<^sub>c k) = zetaI (init_map k)"
  by (simp add: ev_prog_map_def ev_el_prog_map_def get_evt_label_def label_def Core_Init\<^sub>c_def)

lemma ev_prog_map_sched: "ev_prog_map (Schedule\<^sub>c k p) = zetaI (schedule_map k p)"
  by (simp add: ev_prog_map_def ev_el_prog_map_def get_evt_label_def label_def Schedule\<^sub>c_def)

lemma ev_prog_map_send: "ev_prog_map (Send_Que_Message\<^sub>c k p m) = zetaI (send_map k p m)"
  by (simp add: ev_prog_map_def ev_el_prog_map_def get_evt_label_def label_def Send_Que_Message\<^sub>c_def)

lemma ev_prog_map_recv: "ev_prog_map (Recv_Que_Message\<^sub>c k p) = zetaI (recv_map k p)"
  by (simp add: ev_prog_map_def ev_el_prog_map_def get_evt_label_def label_def Recv_Que_Message\<^sub>c_def)

lemma ARINC_dom_sim : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> state_inv; ev_map e\<^sub>c = e\<^sub>a \<rbrakk> \<Longrightarrow> domevt\<^sub>c s\<^sub>c e\<^sub>c = domevt\<^sub>a s\<^sub>a e\<^sub>a"
  apply (case_tac e\<^sub>c, simp add: ev_map_def)
  using domevt\<^sub>a_def domevt\<^sub>c_def apply force
  apply (case_tac x2, case_tac a, case_tac aa)
     apply (simp add: domevt\<^sub>a_def domevt\<^sub>c_def ev_map_def el_domevt\<^sub>a_def el_domevt\<^sub>c_def 
            ev_el_prog_map_def label_def state_inv_def Core_Init\<^sub>a_def get_evt_label_def)
     apply auto[1]
     apply (simp add: domevt\<^sub>a_def domevt\<^sub>c_def ev_map_def el_domevt\<^sub>a_def el_domevt\<^sub>c_def 
            ev_el_prog_map_def label_def state_inv_def Schedule\<^sub>a_def get_evt_label_def)
    apply auto[1]
     apply (simp add: domevt\<^sub>a_def domevt\<^sub>c_def ev_map_def el_domevt\<^sub>a_def el_domevt\<^sub>c_def 
            ev_el_prog_map_def label_def state_inv_def Send_Que_Message\<^sub>a_def get_evt_label_def)
   apply auto[1]
     apply (simp add: domevt\<^sub>a_def domevt\<^sub>c_def ev_map_def el_domevt\<^sub>a_def el_domevt\<^sub>c_def 
            ev_el_prog_map_def label_def state_inv_def Recv_Que_Message\<^sub>a_def get_evt_label_def)
  by auto

lemma ARINC_sim_state_ifs : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> state_inv; (t\<^sub>c, t\<^sub>a) \<in> state_inv\<rbrakk> \<Longrightarrow> s\<^sub>a \<sim>\<^sub>a d \<sim>\<^sub>a t\<^sub>a = s\<^sub>c \<sim>\<^sub>c d \<sim>\<^sub>c t\<^sub>c"
  apply (case_tac d)
    apply (simp add: state_equiv\<^sub>a_def state_equiv\<^sub>c_def state_obs_part\<^sub>c_def state_obs_part\<^sub>a_def
         System_Init\<^sub>a_def System_Init\<^sub>c_def s0a_init s0c_init)
  apply (smt (verit, del_insts) CollectD case_prodD obs_cap_equiva obs_cap_equivc obs_cap_part\<^sub>a_def 
     obs_cap_part\<^sub>c_def state_inv_def)
   apply (simp add: state_inv_def state_equiv\<^sub>a_def state_equiv\<^sub>c_def state_obs_sched\<^sub>c_def
           state_obs_sched\<^sub>a_def System_Init\<^sub>a_def System_Init\<^sub>c_def s0a_init s0c_init)
  by (simp add: state_equiv\<^sub>a_def state_equiv\<^sub>c_def)

subsection \<open>Rely-guarantee Proof of programs\<close>


abbreviation "init\<^sub>c_rely k \<equiv> \<lbrace>(\<forall>p. p2s conf p = c2s conf k \<longrightarrow> \<ordfeminine>partst\<^sub>c p = \<ordmasculine>partst\<^sub>c p)\<rbrace> \<union> Id"
abbreviation "init\<^sub>c_guar k \<equiv> \<lbrace>\<ordfeminine>cur\<^sub>c = \<ordmasculine>cur\<^sub>c \<and> \<ordfeminine>qbuf\<^sub>c = \<ordmasculine>qbuf\<^sub>c \<and> \<ordfeminine>qbufsize\<^sub>c = \<ordmasculine>qbufsize\<^sub>c
            \<and> \<ordfeminine>qlock\<^sub>c = \<ordmasculine>qlock\<^sub>c \<and> \<ordfeminine>obsize\<^sub>c = \<ordmasculine>obsize\<^sub>c  
            \<and> (\<forall>p. p2s conf p = c2s conf k \<longrightarrow> \<ordmasculine>partst\<^sub>c p = IDLE \<and> \<ordfeminine>partst\<^sub>c p = READY)
            \<and> (\<forall>p. p2s conf p \<noteq> c2s conf k \<longrightarrow> \<ordfeminine>partst\<^sub>c p = \<ordmasculine>partst\<^sub>c p)\<rbrace> \<union> Id"

abbreviation "init_pre k \<equiv> state_inv \<inter> {(s\<^sub>c, s\<^sub>a). (\<forall>p. p2s conf p = c2s conf k \<longrightarrow> partst\<^sub>c s\<^sub>c p = IDLE)}"
abbreviation "init_post \<equiv> state_inv"


abbreviation "init\<^sub>a_rely k \<equiv> UNIV"
abbreviation "init\<^sub>a_guar k \<equiv> UNIV"

lemma core_init_sim : "prog_sim_pre 
      (Some (\<acute>partst\<^sub>c := (\<lambda>p. if p2s conf p = c2s conf k \<and> \<acute>partst\<^sub>c p = IDLE then READY else \<acute>partst\<^sub>c p)))
      (init\<^sub>c_rely k) (init\<^sub>c_guar k) 
      state_inv (init_map k) (init_pre k) init_post
      (Some (\<acute>partst\<^sub>a := (\<lambda>p. if p2s conf p = c2s conf k \<and> \<acute>partst\<^sub>a p = IDLE then READY else \<acute>partst\<^sub>a p)))
      (init\<^sub>a_rely k) (init\<^sub>a_guar k)"
  apply (rule Basic_Sound, simp_all add: init_map_def)
  apply (simp add: stable_alpha)
   apply (rule stable_conj, simp add: stable_alpha)
   apply (simp add: Stable_def related_transitions_def)
  apply blast
  apply clarify
  apply (simp add: state_inv_def)
  by force

abbreviation "schedule\<^sub>c_rely k p \<equiv> \<lbrace>\<ordfeminine>cur\<^sub>c (c2s conf k) = \<ordmasculine>cur\<^sub>c (c2s conf k) \<and>
                                   (\<forall>p. p2s conf p = c2s conf k \<longrightarrow> \<ordfeminine>partst\<^sub>c p = \<ordmasculine>partst\<^sub>c p)\<rbrace> \<union> Id"

abbreviation "schedule\<^sub>c_guar k  \<equiv> \<lbrace>\<ordfeminine>qbuf\<^sub>c = \<ordmasculine>qbuf\<^sub>c \<and> \<ordfeminine>qbufsize\<^sub>c = \<ordmasculine>qbufsize\<^sub>c \<and> \<ordfeminine>qlock\<^sub>c = \<ordmasculine>qlock\<^sub>c 
      \<and> \<ordfeminine>obsize\<^sub>c = \<ordmasculine>obsize\<^sub>c \<and> (\<forall>c. c \<noteq> k \<longrightarrow> \<ordfeminine>cur\<^sub>c (c2s conf c) = \<ordmasculine>cur\<^sub>c (c2s conf c))
      \<and> (\<forall>p. p2s conf p \<noteq> c2s conf k \<longrightarrow> \<ordfeminine>partst\<^sub>c p = \<ordmasculine>partst\<^sub>c p)\<rbrace> \<union> Id"


abbreviation "schedule_pre1 k \<equiv> {(s\<^sub>c, s\<^sub>a). 
  ((cur\<^sub>c s\<^sub>c) (c2s conf k) \<noteq> None \<longrightarrow> p2s conf (the ((cur\<^sub>c s\<^sub>c) (c2s conf k))) = c2s conf k) \<and>
  ((cur\<^sub>a s\<^sub>a) (c2s conf k) \<noteq> None \<longrightarrow> p2s conf (the ((cur\<^sub>a s\<^sub>a) (c2s conf k))) = c2s conf k)}"

abbreviation "schdule_pre k p \<equiv> state_inv \<inter> \<lbrace>p2s conf p = c2s conf k\<rbrace> \<inter> schedule_pre1 k"
abbreviation "schdule_post \<equiv> state_inv"

abbreviation "schedule\<^sub>a_rely \<equiv> UNIV"
abbreviation "schedule\<^sub>a_guar \<equiv> UNIV"



abbreviation "sched_await_mid1\<^sub>c s k p \<equiv> 
    {s'. ((cur\<^sub>c s) (c2s conf k) = None \<longrightarrow> s' = s \<lparr>cur\<^sub>c := (cur\<^sub>c s) ((c2s conf k) := Some p)\<rparr>) \<and> 
         ((cur\<^sub>c s) (c2s conf k) \<noteq> None \<longrightarrow> s' = s \<lparr>cur\<^sub>c := (cur\<^sub>c s) ((c2s conf k) := Some p),
                   partst\<^sub>c := (partst\<^sub>c s) (the ((cur\<^sub>c s) (c2s conf k)) := READY)\<rparr>)}"

abbreviation "sched_await_mid2\<^sub>c s k  \<equiv> 
    {s'. ((cur\<^sub>c s) (c2s conf k) = None \<longrightarrow> s' = s) \<and> 
         ((cur\<^sub>c s) (c2s conf k) \<noteq> None \<longrightarrow> s' = s \<lparr>cur\<^sub>c := (cur\<^sub>c s) ((c2s conf k) := None),
                   partst\<^sub>c := (partst\<^sub>c s) (the ((cur\<^sub>c s) (c2s conf k)) := READY)\<rparr>)}"

abbreviation "sched_await_if_mid\<^sub>c s k  \<equiv> 
    {s'. (cur\<^sub>c s) (c2s conf k) \<noteq> None \<and> s' = s \<lparr>partst\<^sub>c := (partst\<^sub>c s) (the ((cur\<^sub>c s) (c2s conf k)) := READY)\<rparr>}"

abbreviation "sched_await_post\<^sub>c s k p \<equiv> 
    {s'. ((cur\<^sub>c s) (c2s conf k) = None \<longrightarrow> s' = s \<lparr>cur\<^sub>c := (cur\<^sub>c s) ((c2s conf k) := Some p),
                                                 partst\<^sub>c := (partst\<^sub>c s) (p := RUN)\<rparr>) \<and> 
         ((cur\<^sub>c s) (c2s conf k) \<noteq> None \<longrightarrow> s' = s \<lparr>cur\<^sub>c := (cur\<^sub>c s) ((c2s conf k) := Some p),
                   partst\<^sub>c := (partst\<^sub>c s) (the ((cur\<^sub>c s) (c2s conf k)) := READY, p:= RUN)\<rparr>)}"

lemma schedc_await_sat_post: "\<lbrakk>p2s conf p = c2s conf k; 
      (\<exists>y. cur\<^sub>c s\<^sub>c (c2s conf k) = Some y) \<longrightarrow> p2s conf (the (cur\<^sub>c s\<^sub>c (c2s conf k))) = c2s conf k\<rbrakk> \<Longrightarrow>
      \<turnstile> Await UNIV
          (IF \<exists>y. \<acute>cur\<^sub>c (c2s conf k) = Some y THEN 
             \<acute>partst\<^sub>c := \<acute>partst\<^sub>c(the (\<acute>cur\<^sub>c (c2s conf k)) := READY);; 
             \<acute>cur\<^sub>c := \<acute>cur\<^sub>c(c2s conf k := None) 
           FI;;
           \<acute>cur\<^sub>c := \<acute>cur\<^sub>c(c2s conf k \<mapsto> p);;
           \<acute>partst\<^sub>c := \<acute>partst\<^sub>c (p := RUN))
           sat [{s\<^sub>c}, Id, schedule\<^sub>c_guar k, sched_await_post\<^sub>c s\<^sub>c k p]"
  apply (rule Await, simp_all add: stable_def, clarify)
  apply (case_tac "s\<^sub>c \<noteq> V")
   apply (rule Seq[where mid = "{}"])
  apply (rule Seq[where mid = "{}"])
     apply (rule Cond, simp add: stable_def)
       apply (rule Seq[where mid = "{}"])
        apply (rule Basic, simp_all add: stable_def)
      apply (rule Basic, simp_all add: stable_def)
     apply (simp add: Skip_def, rule Basic, simp_all add: stable_def)
    apply (rule Basic, simp_all add: stable_def)
   apply (rule Basic, simp_all add: stable_def)
  apply (rule Seq[where mid = "sched_await_mid1\<^sub>c s\<^sub>c k p"])
   apply (rule Seq[where mid = "sched_await_mid2\<^sub>c s\<^sub>c k"])
    apply (rule Cond, simp add: stable_def)
      apply (rule Seq[where mid = "sched_await_if_mid\<^sub>c s\<^sub>c k"])
       apply (rule Basic)
          apply blast
       apply (simp add: stable_def)+
      apply (rule Basic)
         apply auto[1]
       apply (simp add: stable_def)+
     apply (simp add: Skip_def, rule Basic)
        apply auto[1]
     apply (simp add: stable_def)+
   apply (rule Basic)
      apply auto[1]
      apply (metis State\<^sub>c.surjective State\<^sub>c.update_convs(1) State\<^sub>c.update_convs(6))
    apply (simp add: stable_def)+
  apply (rule Basic, clarsimp)
     apply (case_tac "cur\<^sub>c s\<^sub>c (c2s conf k) = None", simp)
      apply (meson inj_eq inj_surj_c2s)
     apply (simp add: inj_eq inj_surj_c2s)
  by (simp add: stable_def)+

abbreviation "sched_await_mid1\<^sub>a s k p \<equiv> 
    {s'. ((cur\<^sub>a s) (c2s conf k) = None \<longrightarrow> s' = s \<lparr>cur\<^sub>a := (cur\<^sub>a s) ((c2s conf k) := Some p)\<rparr>) \<and> 
         ((cur\<^sub>a s) (c2s conf k) \<noteq> None \<longrightarrow> s' = s \<lparr>cur\<^sub>a := (cur\<^sub>a s) ((c2s conf k) := Some p),
                   partst\<^sub>a := (partst\<^sub>a s) (the ((cur\<^sub>a s) (c2s conf k)) := READY)\<rparr>)}"

abbreviation "sched_await_mid2\<^sub>a s k  \<equiv> 
    {s'. ((cur\<^sub>a s) (c2s conf k) = None \<longrightarrow> s' = s) \<and> 
         ((cur\<^sub>a s) (c2s conf k) \<noteq> None \<longrightarrow> s' = s \<lparr>
          partst\<^sub>a := (partst\<^sub>a s) (the ((cur\<^sub>a s) (c2s conf k)) := READY)\<rparr>)}"

abbreviation "sched_await_post\<^sub>a s k p \<equiv> 
    {s'. ((cur\<^sub>a s) (c2s conf k) = None \<longrightarrow> s' = s \<lparr>cur\<^sub>a := (cur\<^sub>a s) ((c2s conf k) := Some p),
                                                 partst\<^sub>a := (partst\<^sub>a s) (p := RUN)\<rparr>) \<and>
         ((cur\<^sub>a s) (c2s conf k) \<noteq> None \<longrightarrow>s' = s \<lparr>cur\<^sub>a := (cur\<^sub>a s) ((c2s conf k) := Some p),
                   partst\<^sub>a := (partst\<^sub>a s) (the ((cur\<^sub>a s) (c2s conf k)) := READY, p := RUN)\<rparr>)}"

lemma scheda_await_sat_post: "\<lbrakk>p2s conf p = c2s conf k; 
      (\<exists>y. cur\<^sub>a s\<^sub>a (c2s conf k) = Some y) \<longrightarrow> p2s conf (the (cur\<^sub>a s\<^sub>a (c2s conf k))) = c2s conf k\<rbrakk> \<Longrightarrow>
      \<turnstile> Await UNIV 
          (IF \<exists>y. \<acute>cur\<^sub>a (c2s conf k) = Some y THEN 
            \<acute>partst\<^sub>a := \<acute>partst\<^sub>a(the (\<acute>cur\<^sub>a (c2s conf k)) := READY) 
           FI;; 
          \<acute>cur\<^sub>a := \<acute>cur\<^sub>a(c2s conf k \<mapsto> p);; 
          \<acute>partst\<^sub>a := \<acute>partst\<^sub>a(p := RUN)) 
          sat [{s\<^sub>a}, Id, schedule\<^sub>a_guar, sched_await_post\<^sub>a s\<^sub>a k p]"
  apply (rule Await, simp_all add: stable_def, clarify)
  apply (case_tac "s\<^sub>a \<noteq> V")
   apply (rule Seq[where mid = "{}"])
    apply (rule Seq[where mid = "{}"])
     apply (rule Cond, simp add: stable_def)
        apply (rule Basic, simp_all add: stable_def)
     apply (simp add: Skip_def, rule Basic, simp_all add: stable_def)
    apply (rule Basic, simp_all add: stable_def)
   apply (rule Basic, simp_all add: stable_def)
  apply (rule Seq[where mid = "sched_await_mid1\<^sub>a s\<^sub>a k p"])
   apply (rule Seq[where mid = "sched_await_mid2\<^sub>a s\<^sub>a k"])
    apply (rule Cond)
       apply (simp add: stable_def)+
      apply (rule Basic)
         apply auto[1]
        apply (simp add: stable_def)+
     apply (simp add: Skip_def, rule Basic)
        apply auto[1]
       apply (simp add: stable_def)+
   apply (rule Basic, case_tac "cur\<^sub>a s\<^sub>a (c2s conf k) = None", simp, clarsimp)
     apply (simp add: stable_def)+
  apply (rule Basic, case_tac "cur\<^sub>a s\<^sub>a (c2s conf k) = None", simp, clarsimp)
  by (simp add: stable_def)+

lemma schedule_not_stuck: "not_stuck UNIV 
      (IF (\<acute>cur\<^sub>a((c2s conf) k) \<noteq> None) THEN    
         \<acute>partst\<^sub>a := \<acute>partst\<^sub>a(the (\<acute>cur\<^sub>a ((c2s conf) k)) := READY)
      FI;;
     \<acute>cur\<^sub>a := \<acute>cur\<^sub>a((c2s conf k) := Some p);;
     \<acute>partst\<^sub>a := \<acute>partst\<^sub>a(p := RUN))"
  apply (rule not_stuck_Seq)+
    apply (rule not_stuck_If, simp_all add: Skip_def)
  by (rule not_stuck_Basic)+

lemma sched_await_post_inv: "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> state_inv; s\<^sub>c' \<in> sched_await_post\<^sub>c s\<^sub>c k p; 
      s\<^sub>a' \<in> sched_await_post\<^sub>a s\<^sub>a k p\<rbrakk> \<Longrightarrow> (s\<^sub>c', s\<^sub>a') \<in> schdule_post"
  apply (simp add: state_inv_def, clarsimp)
  by (case_tac "(cur\<^sub>c s\<^sub>c) (c2s conf k) = None", simp_all)

lemma schedule_sim : "prog_sim_pre 
      (Some 
      (ATOMIC
         IF (\<acute>cur\<^sub>c((c2s conf) k) \<noteq> None) THEN    
           \<acute>partst\<^sub>c := \<acute>partst\<^sub>c(the (\<acute>cur\<^sub>c ((c2s conf) k)) := READY);;
           \<acute>cur\<^sub>c := \<acute>cur\<^sub>c((c2s conf) k := None)
         FI;;
         \<acute>cur\<^sub>c := \<acute>cur\<^sub>c((c2s conf k) := Some p);;
         \<acute>partst\<^sub>c := \<acute>partst\<^sub>c(p := RUN)
       END))
      (schedule\<^sub>c_rely k p) (schedule\<^sub>c_guar k) 
      state_inv (schedule_map k p) (schdule_pre k p) schdule_post
      (Some 
      (ATOMIC
         IF (\<acute>cur\<^sub>a((c2s conf) k) \<noteq> None) THEN    
           \<acute>partst\<^sub>a := \<acute>partst\<^sub>a(the (\<acute>cur\<^sub>a ((c2s conf) k)) := READY)
          FI;;
         \<acute>cur\<^sub>a := \<acute>cur\<^sub>a((c2s conf k) := Some p);;
         \<acute>partst\<^sub>a := \<acute>partst\<^sub>a(p := RUN)
       END))
       schedule\<^sub>a_rely schedule\<^sub>a_guar"
  apply (rule Await_Await_Sound, simp_all add: rel_eq_def Stable_def stable_alpha schedule_map_def)
  using Stable_def stable_alpha apply fastforce
  apply (simp add: related_transitions_def)
  apply (metis (mono_tags, lifting) CollectD case_prodD state_inv_def)
   apply (simp add: Skip_def not_stuck_Basic not_stuck_If not_stuck_Seq, clarsimp)
  apply (rule_tac x = "sched_await_post\<^sub>c s\<^sub>c k p" in exI)
  apply (rule conjI, rule schedc_await_sat_post, simp+)
  apply (rule_tac x = "sched_await_post\<^sub>a s\<^sub>a k p" in exI)
  apply (rule conjI, rule scheda_await_sat_post, simp+)
  using sched_await_post_inv by force


abbreviation "send\<^sub>c_rely k ch \<equiv> \<lbrace>\<ordfeminine>cur\<^sub>c (c2s conf k) = \<ordmasculine>cur\<^sub>c (c2s conf k) \<and>
             (\<ordmasculine>qlock\<^sub>c ch = Some k \<longrightarrow> \<ordfeminine>qlock\<^sub>c ch = \<ordmasculine>qlock\<^sub>c ch \<and> \<ordfeminine>qbuf\<^sub>c ch = \<ordmasculine>qbuf\<^sub>c ch 
            \<and> \<ordfeminine>qbufsize\<^sub>c ch = \<ordmasculine>qbufsize\<^sub>c ch \<and> \<ordfeminine>obsize\<^sub>c ch = \<ordmasculine>obsize\<^sub>c ch)\<rbrace> \<union> Id"

abbreviation "send\<^sub>c_guar k ch \<equiv> 
      {(s, s'). (qlock\<^sub>c s) ch = None \<and> s' = s \<lparr>qlock\<^sub>c := (qlock\<^sub>c s) (ch:= Some k)\<rparr>}
    \<union> {(s, s'). \<exists>ms. (qlock\<^sub>c s) ch = Some k \<and> s' = s \<lparr>qbuf\<^sub>c := (qbuf\<^sub>c s) (ch := ms)\<rparr>}
    \<union> {(s, s'). \<exists>n. (qlock\<^sub>c s) ch = Some k \<and> s' = s \<lparr>qbufsize\<^sub>c := (qbufsize\<^sub>c s) (ch :=  n)\<rparr>}
    \<union> {(s, s'). \<exists>n. (qlock\<^sub>c s) ch = Some k \<and> s' = s \<lparr>qlock\<^sub>c := (qlock\<^sub>c s) (ch := None),
                                                obsize\<^sub>c := (obsize\<^sub>c s) (ch := n) \<rparr>} \<union> Id"

(*
abbreviation "send_pre1 k p \<equiv> {(s\<^sub>c, s\<^sub>a). 
  ((cur\<^sub>c s\<^sub>c) (c2s conf k) \<noteq> None \<and> port_of_part conf p (the ((cur\<^sub>c s\<^sub>c) (c2s conf k)))) \<and>
  ((cur\<^sub>a s\<^sub>a) (c2s conf k) \<noteq> None \<and> port_of_part conf p (the ((cur\<^sub>a s\<^sub>a) (c2s conf k))))}"
*)

abbreviation "send_pre  \<equiv> state_inv"
abbreviation "send_post \<equiv> state_inv"

abbreviation "send\<^sub>a_rely \<equiv> UNIV"
abbreviation "send\<^sub>a_guar \<equiv> UNIV"

lemma senda_not_stuck: "not_stuck UNIV 
      (IF \<acute>qbufsize\<^sub>a (ch_srcqport conf p) < chmax conf (ch_srcqport conf p) THEN 
            \<acute>qbuf\<^sub>a := \<acute>qbuf\<^sub>a (ch_srcqport conf p := \<acute>qbuf\<^sub>a (ch_srcqport conf p) @ [m]);;
            \<acute>qbufsize\<^sub>a := \<acute>qbufsize\<^sub>a (ch_srcqport conf p := \<acute>qbufsize\<^sub>a (ch_srcqport conf p) + 1)
       FI)"
  apply (rule not_stuck_If, simp_all add: Skip_def)
   apply (rule not_stuck_Seq)
  by (rule not_stuck_Basic)+


abbreviation "sendc_unlock_await_post s ch  \<equiv> {s'. s' = s \<lparr>qlock\<^sub>c := (qlock\<^sub>c s) (ch := None),
                                               obsize\<^sub>c := (obsize\<^sub>c s) (ch := (qbufsize\<^sub>c s ch)) \<rparr>}"

abbreviation "sendc_unlock_await_mid s ch  \<equiv> {s'. s' = s \<lparr>qlock\<^sub>c := (qlock\<^sub>c s) (ch := None) \<rparr>}"

lemma sendc_unlock_await_sat_post: "qlock\<^sub>c s\<^sub>c (ch_srcqport conf p) = Some k \<Longrightarrow>
      \<turnstile> Await UNIV
          (\<acute>qlock\<^sub>c := \<acute>qlock\<^sub>c(ch_srcqport conf p := None);;
           \<acute>obsize\<^sub>c := \<acute>obsize\<^sub>c (ch_srcqport conf p :=\<acute>qbufsize\<^sub>c (ch_srcqport conf p)))
      sat [{s\<^sub>c}, Id, send\<^sub>c_guar k (ch_srcqport conf p), sendc_unlock_await_post s\<^sub>c (ch_srcqport conf p)]"
  apply (rule Await)        
    apply (simp add: stable_def)+
  apply (clarsimp, case_tac "V \<noteq> s\<^sub>c")
   apply (rule Seq[where mid = "{}"])
    apply (rule Basic)
       apply (simp add: stable_def)+
   apply (rule Basic)
      apply (simp add: stable_def)+
  apply (rule Seq[where mid = "sendc_unlock_await_mid s\<^sub>c  (ch_srcqport conf p)"])
   apply (rule Basic)
      apply (simp add: stable_def)+
  apply (rule Basic, clarsimp)
     apply blast
  by (simp add: stable_def)+

abbreviation "senda_await_post s m ch  \<equiv> {s'. 
   (qbufsize\<^sub>a s ch < chmax conf ch \<longrightarrow> s' = s \<lparr> qbuf\<^sub>a := (qbuf\<^sub>a s) (ch := (qbuf\<^sub>a s ch) @ [m]),
   qbufsize\<^sub>a := (qbufsize\<^sub>a s) (ch := (qbufsize\<^sub>a s ch) + 1)\<rparr>) \<and>
   (qbufsize\<^sub>a s ch \<ge> chmax conf ch \<longrightarrow> s' = s)}"

abbreviation "senda_await_mid s m ch  \<equiv> {s'. s' = s \<lparr> qbuf\<^sub>a := (qbuf\<^sub>a s) (ch := (qbuf\<^sub>a s ch) @ [m])\<rparr>}
              \<inter> \<lbrace>(qbufsize\<^sub>a s) ch  < chmax conf ch\<rbrace>"

lemma senda_await_sat_post: " 
    \<turnstile> Await UNIV
        (IF \<acute>qbufsize\<^sub>a (ch_srcqport conf p) < chmax conf (ch_srcqport conf p) THEN 
          \<acute>qbuf\<^sub>a := \<acute>qbuf\<^sub>a(ch_srcqport conf p := \<acute>qbuf\<^sub>a (ch_srcqport conf p) @ [m]);; 
          \<acute>qbufsize\<^sub>a := \<acute>qbufsize\<^sub>a(ch_srcqport conf p := Suc (\<acute>qbufsize\<^sub>a (ch_srcqport conf p))) FI) 
      sat [{s\<^sub>a}, Id, send\<^sub>a_guar, senda_await_post s\<^sub>a m (ch_srcqport conf p)]"
  apply (rule Await)
    apply (simp add: stable_def)+
  apply (clarsimp, case_tac "V \<noteq> s\<^sub>a")
   apply (rule Cond)
      apply (simp add: stable_def)+
     apply (rule Seq[where mid = "{}"])
      apply (rule Basic)
         apply (simp add: stable_def)+
     apply (rule Basic)
        apply (simp add: stable_def)+
    apply (simp add: Skip_def, rule Basic)
       apply (simp add: stable_def)+
  apply (rule Cond)
     apply (simp add: stable_def)+
    apply (rule Seq[where mid = "senda_await_mid s\<^sub>a m (ch_srcqport conf p)"])
     apply (rule Basic, clarsimp)
       apply (simp add: stable_def)+
  apply (rule conjI, clarsimp)
     apply (rule Basic, clarsimp)
       apply (simp add: stable_def)+
    apply (clarsimp, rule Basic)
       apply (simp add: stable_def)+
   apply (simp add: Skip_def, rule Basic, clarsimp)
  by (simp add: stable_def)+

abbreviation "send_unlock_pre k ch \<equiv> state_inv \<inter> 
    {(s\<^sub>c, s\<^sub>a). qlock\<^sub>c s\<^sub>c ch = Some k \<and> 
              (obsize\<^sub>c s\<^sub>c ch < chmax conf ch \<longrightarrow> qbufsize\<^sub>c s\<^sub>c ch = obsize\<^sub>c s\<^sub>c ch + 1) \<and> 
              (obsize\<^sub>c s\<^sub>c ch \<ge> chmax conf ch \<longrightarrow> qbufsize\<^sub>c s\<^sub>c ch = obsize\<^sub>c s\<^sub>c ch)}"

lemma send_await_post_inv: "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> send_unlock_pre k ch; s\<^sub>c' \<in> sendc_unlock_await_post s\<^sub>c ch;
      s\<^sub>a' \<in> senda_await_post s\<^sub>a m ch\<rbrakk> \<Longrightarrow> (s\<^sub>c', s\<^sub>a') \<in> send_post"
  apply (case_tac "obsize\<^sub>c s\<^sub>c ch < chmax conf ch", simp add: state_inv_def, clarify)
   apply presburger
  apply (simp add: state_inv_def, clarify)
  by presburger

lemma send_unlock_sim: "prog_sim_pre (Some 
      (ATOMIC
          \<acute>qlock\<^sub>c := \<acute>qlock\<^sub>c (ch_srcqport conf p := None);;
          \<acute>obsize\<^sub>c := \<acute>obsize\<^sub>c (ch_srcqport conf p := \<acute>qbufsize\<^sub>c (ch_srcqport conf p))
       END))
      (send\<^sub>c_rely k (ch_srcqport conf p)) (send\<^sub>c_guar k (ch_srcqport conf p)) 
      state_inv (send_map k p m) (send_unlock_pre k (ch_srcqport conf p)) send_post
      (Some 
      (ATOMIC
         IF \<acute>qbufsize\<^sub>a (ch_srcqport conf p) < chmax conf (ch_srcqport conf p) THEN 
            \<acute>qbuf\<^sub>a := \<acute>qbuf\<^sub>a (ch_srcqport conf p := \<acute>qbuf\<^sub>a (ch_srcqport conf p) @ [m]);;
            \<acute>qbufsize\<^sub>a := \<acute>qbufsize\<^sub>a (ch_srcqport conf p := \<acute>qbufsize\<^sub>a (ch_srcqport conf p) + 1)
         FI
       END))
      send\<^sub>a_rely send\<^sub>a_guar"
  apply (rule Await_Await_Sound)
  using UNIV_I case_prodD colltrue_eq_univ rel_eq_def apply fastforce
       apply (simp add: send_map_def)
      apply (simp add: stable_alpha)
     apply simp
    apply (rule stable_conj, simp add: stable_alpha)
    apply (simp add: Stable_def related_transitions_def)
    apply auto[1]
  using senda_not_stuck apply auto[1]
  apply clarsimp
  apply (rule_tac x = "sendc_unlock_await_post s\<^sub>c (ch_srcqport conf p)" in exI)
  apply (rule conjI)
  using sendc_unlock_await_sat_post apply auto[1]
  apply (rule_tac x = "senda_await_post s\<^sub>a m (ch_srcqport conf p)" in exI)
  apply (rule conjI)
  using senda_await_sat_post apply auto[1]
  by (clarsimp, rule send_await_post_inv, simp_all)

abbreviation "send_sim_mid1 k ch \<equiv> send_unlock_pre k ch"
abbreviation "send_sim_mid2 k ch \<equiv> state_inv \<inter> {(s\<^sub>c, s\<^sub>a). qlock\<^sub>c s\<^sub>c ch = Some k \<and> qbufsize\<^sub>c s\<^sub>c ch = obsize\<^sub>c s\<^sub>c ch}"


lemma send_sim_none1: "prog_sim_pre (Some 
      (AWAIT \<acute>qlock\<^sub>c (ch_srcqport conf p) = None THEN
        \<acute>qlock\<^sub>c := \<acute>qlock\<^sub>c (ch_srcqport conf p := Some k)
       END))
      (send\<^sub>c_rely k (ch_srcqport conf p)) (send\<^sub>c_guar k (ch_srcqport conf p)) 
      state_inv Map.empty send_pre (send_sim_mid2 k (ch_srcqport conf p))
      None
      send\<^sub>a_rely send\<^sub>a_guar"
  apply (rule Await_None_Sound)
       apply simp+
     apply (simp add: Stable_def related_transitions_def)+
    apply auto[1]
   apply simp
  apply clarsimp
  apply (rule Await)
    apply (simp add: stable_def)+
  apply (clarsimp, rule Basic, clarsimp)
     apply (simp add: state_inv_def)
     apply auto[1]
    apply (simp add: stable_def)+
   apply auto[1]
  by (simp add: stable_def)

abbreviation "send_sim_none_if_mid k ch \<equiv> state_inv \<inter> {(s\<^sub>c, s\<^sub>a). qbufsize\<^sub>c s\<^sub>c ch < chmax conf ch}
             \<inter> {(s\<^sub>c, s\<^sub>a). qlock\<^sub>c s\<^sub>c ch = Some k \<and> qbufsize\<^sub>c s\<^sub>c ch = obsize\<^sub>c s\<^sub>c ch}"

lemma send_sim_none2: "prog_sim_pre (Some 
      (IF \<acute>qbufsize\<^sub>c (ch_srcqport conf p) < chmax conf (ch_srcqport conf p) THEN 
         \<acute>qbuf\<^sub>c := \<acute>qbuf\<^sub>c (ch_srcqport conf p := \<acute>qbuf\<^sub>c (ch_srcqport conf p) @ [m]);;
         \<acute>qbufsize\<^sub>c := \<acute>qbufsize\<^sub>c (ch_srcqport conf p := \<acute>qbufsize\<^sub>c (ch_srcqport conf p) + 1)
       FI))
      (send\<^sub>c_rely k (ch_srcqport conf p)) (send\<^sub>c_guar k (ch_srcqport conf p))
      state_inv Map.empty (send_sim_mid2 k (ch_srcqport conf p)) (send_sim_mid1 k (ch_srcqport conf p))
      None
      send\<^sub>a_rely send\<^sub>a_guar"
  apply auto
  apply (rule If_Comm_Branch_Sound)
        apply simp+
      apply (simp add: Stable_def related_transitions_def)
       apply auto
   apply (rule_tac \<zeta>\<^sub>1 = Map.empty and \<gamma>\<^sub>1 = "send_sim_none_if_mid k (ch_srcqport conf p)" in Seq_Skip_Sound)
      apply blast
     apply simp
    apply (rule Basic_None_Sound)
         apply blast+
       apply (simp add: Stable_def related_transitions_def)
       apply fastforce
      apply (simp add: Stable_def related_transitions_def)
      apply fastforce
     apply (simp add: state_inv_def)
     apply auto[1]
    apply simp
   apply (rule Basic_None_Sound)
        apply blast+
      apply (simp add: Stable_def related_transitions_def)
      apply fastforce
     apply (simp add: Stable_def related_transitions_def)
     apply fastforce
    apply (simp add: state_inv_def)
    apply auto[1]
   apply simp
  apply (simp add: Skip_def, rule Basic_None_Sound)
       apply blast+
     apply (simp add: Stable_def related_transitions_def)
     apply fastforce
    apply (simp add: Stable_def related_transitions_def)
    apply fastforce
   apply (simp add: state_inv_def)
  by auto

lemma send_sim: "prog_sim_pre (Some 
      (AWAIT \<acute>qlock\<^sub>c (ch_srcqport conf p) = None THEN
        \<acute>qlock\<^sub>c := \<acute>qlock\<^sub>c (ch_srcqport conf p := Some k)
       END;;
       IF \<acute>qbufsize\<^sub>c (ch_srcqport conf p) < chmax conf (ch_srcqport conf p) THEN 
         \<acute>qbuf\<^sub>c := \<acute>qbuf\<^sub>c (ch_srcqport conf p := \<acute>qbuf\<^sub>c (ch_srcqport conf p) @ [m]);;
         \<acute>qbufsize\<^sub>c := \<acute>qbufsize\<^sub>c (ch_srcqport conf p := \<acute>qbufsize\<^sub>c (ch_srcqport conf p) + 1)
       FI;;
       ATOMIC
         \<acute>qlock\<^sub>c := \<acute>qlock\<^sub>c (ch_srcqport conf p := None);;
         \<acute>obsize\<^sub>c := \<acute>obsize\<^sub>c (ch_srcqport conf p := \<acute>qbufsize\<^sub>c (ch_srcqport conf p))
       END))
      (send\<^sub>c_rely k (ch_srcqport conf p)) (send\<^sub>c_guar k (ch_srcqport conf p)) 
      state_inv (send_map k p m) send_pre send_post
      (Some 
      (ATOMIC
         IF \<acute>qbufsize\<^sub>a (ch_srcqport conf p) < chmax conf (ch_srcqport conf p) THEN 
            \<acute>qbuf\<^sub>a := \<acute>qbuf\<^sub>a (ch_srcqport conf p := \<acute>qbuf\<^sub>a (ch_srcqport conf p) @ [m]);;
            \<acute>qbufsize\<^sub>a := \<acute>qbufsize\<^sub>a (ch_srcqport conf p := \<acute>qbufsize\<^sub>a (ch_srcqport conf p) + 1)
         FI
       END))
      send\<^sub>a_rely send\<^sub>a_guar"
  apply (rule_tac \<zeta>\<^sub>1 = Map.empty and \<gamma>\<^sub>1 = "send_sim_mid1 k (ch_srcqport conf p)" in Seq_Skip_Sound)
    apply (simp add: send_map_def)+
   apply (rule_tac \<zeta>\<^sub>1 = Map.empty and \<gamma>\<^sub>1 = "send_sim_mid2 k (ch_srcqport conf p)" in Seq_Skip_Sound)
      apply simp+
  using send_sim_none1 apply auto[1]
  using send_sim_none2 apply auto[1]
  using send_unlock_sim by auto


abbreviation "recv\<^sub>c_rely k ch \<equiv> \<lbrace>\<ordfeminine>cur\<^sub>c (c2s conf k) = \<ordmasculine>cur\<^sub>c (c2s conf k) \<and>
             (\<ordmasculine>qlock\<^sub>c ch = Some k \<longrightarrow> \<ordfeminine>qlock\<^sub>c ch = \<ordmasculine>qlock\<^sub>c ch \<and> \<ordfeminine>qbuf\<^sub>c ch = \<ordmasculine>qbuf\<^sub>c ch 
            \<and> \<ordfeminine>qbufsize\<^sub>c ch = \<ordmasculine>qbufsize\<^sub>c ch \<and> \<ordfeminine>obsize\<^sub>c ch = \<ordmasculine>obsize\<^sub>c ch)\<rbrace> \<union> Id"

abbreviation "recv\<^sub>c_guar k ch \<equiv> 
      {(s, s'). (qlock\<^sub>c s) ch = None \<and> s' = s \<lparr>qlock\<^sub>c := (qlock\<^sub>c s) (ch:= Some k)\<rparr>}
    \<union> {(s, s'). \<exists>ms. (qlock\<^sub>c s) ch = Some k \<and> s' = s \<lparr>qbuf\<^sub>c := (qbuf\<^sub>c s) (ch := ms)\<rparr>}
    \<union> {(s, s'). \<exists>n. (qlock\<^sub>c s) ch = Some k \<and> s' = s \<lparr>qbufsize\<^sub>c := (qbufsize\<^sub>c s) (ch :=  n)\<rparr>}
    \<union> {(s, s'). \<exists>n. (qlock\<^sub>c s) ch = Some k \<and> s' = s \<lparr>qlock\<^sub>c := (qlock\<^sub>c s) (ch := None),
                                                obsize\<^sub>c := (obsize\<^sub>c s) (ch := n) \<rparr>} \<union> Id"

(*
abbreviation "send_pre1 k p \<equiv> {(s\<^sub>c, s\<^sub>a). 
  ((cur\<^sub>c s\<^sub>c) (c2s conf k) \<noteq> None \<and> port_of_part conf p (the ((cur\<^sub>c s\<^sub>c) (c2s conf k)))) \<and>
  ((cur\<^sub>a s\<^sub>a) (c2s conf k) \<noteq> None \<and> port_of_part conf p (the ((cur\<^sub>a s\<^sub>a) (c2s conf k))))}"
*)

abbreviation "recv_pre  \<equiv> state_inv"
abbreviation "recv_post \<equiv> state_inv"

abbreviation "recv\<^sub>a_rely \<equiv> UNIV"
abbreviation "recv\<^sub>a_guar \<equiv> UNIV"

lemma recva_not_stuck: "not_stuck UNIV 
      (IF \<acute>qbufsize\<^sub>a (ch_destqport conf p) > 0 THEN 
             \<acute>qbuf\<^sub>a := \<acute>qbuf\<^sub>a (ch_destqport conf p := tl (\<acute>qbuf\<^sub>a (ch_destqport conf p)));;
             \<acute>qbufsize\<^sub>a := \<acute>qbufsize\<^sub>a (ch_destqport conf p := \<acute>qbufsize\<^sub>a (ch_destqport conf p) - 1)
       FI)"
  apply (rule not_stuck_If, simp_all add: Skip_def)
   apply (rule not_stuck_Seq)
  by (rule not_stuck_Basic)+

abbreviation "recvc_unlock_await_post s ch  \<equiv> {s'. s' = s \<lparr>qlock\<^sub>c := (qlock\<^sub>c s) (ch := None),
                                               obsize\<^sub>c := (obsize\<^sub>c s) (ch := (qbufsize\<^sub>c s ch)) \<rparr>}"

abbreviation "recvc_unlock_await_mid s ch  \<equiv> {s'. s' = s \<lparr>qlock\<^sub>c := (qlock\<^sub>c s) (ch := None) \<rparr>}"

lemma recvc_unlock_await_sat_post: "qlock\<^sub>c s\<^sub>c (ch_destqport conf p) = Some k \<Longrightarrow>
      \<turnstile> Await UNIV
          (\<acute>qlock\<^sub>c := \<acute>qlock\<^sub>c(ch_destqport conf p := None);;
           \<acute>obsize\<^sub>c := \<acute>obsize\<^sub>c (ch_destqport conf p :=\<acute>qbufsize\<^sub>c (ch_destqport conf p)))
      sat [{s\<^sub>c}, Id, recv\<^sub>c_guar k (ch_destqport conf p), recvc_unlock_await_post s\<^sub>c (ch_destqport conf p)]"
  apply (rule Await)        
    apply (simp add: stable_def)+
  apply (clarsimp, case_tac "V \<noteq> s\<^sub>c")
   apply (rule Seq[where mid = "{}"])
    apply (rule Basic)
       apply (simp add: stable_def)+
   apply (rule Basic)
      apply (simp add: stable_def)+
  apply (rule Seq[where mid = "recvc_unlock_await_mid s\<^sub>c (ch_destqport conf p)"])
   apply (rule Basic)
      apply (simp add: stable_def)+
  apply (rule Basic, clarsimp)
     apply blast
  by (simp add: stable_def)+

abbreviation "recva_await_post s ch  \<equiv> {s'. 
   (qbufsize\<^sub>a s ch > 0 \<longrightarrow> s' = s \<lparr> qbuf\<^sub>a := (qbuf\<^sub>a s) (ch := tl (qbuf\<^sub>a s ch)),
    qbufsize\<^sub>a := (qbufsize\<^sub>a s) (ch := (qbufsize\<^sub>a s ch) - 1)\<rparr>) \<and>
   (qbufsize\<^sub>a s ch = 0 \<longrightarrow> s' = s)}"

abbreviation "recva_await_mid s ch  \<equiv> {s'. s' = s \<lparr> qbuf\<^sub>a := (qbuf\<^sub>a s) (ch := tl (qbuf\<^sub>a s ch))\<rparr>}
              \<inter> \<lbrace>(qbufsize\<^sub>a s) ch > 0\<rbrace>"

lemma recva_await_sat_post: " 
    \<turnstile> Await UNIV
        (IF \<acute>qbufsize\<^sub>a (ch_destqport conf p) > 0 THEN 
          \<acute>qbuf\<^sub>a := \<acute>qbuf\<^sub>a (ch_destqport conf p := tl (\<acute>qbuf\<^sub>a (ch_destqport conf p)));;
          \<acute>qbufsize\<^sub>a := \<acute>qbufsize\<^sub>a (ch_destqport conf p := \<acute>qbufsize\<^sub>a (ch_destqport conf p) - 1)
         FI) 
      sat [{s\<^sub>a}, Id, recv\<^sub>a_guar, recva_await_post s\<^sub>a  (ch_destqport conf p)]"
  apply (rule Await)
    apply (simp add: stable_def)+
  apply (clarsimp, case_tac "V \<noteq> s\<^sub>a")
   apply (rule Cond)
      apply (simp add: stable_def)+
     apply (rule Seq[where mid = "{}"])
      apply (rule Basic)
         apply (simp add: stable_def)+
     apply (rule Basic)
        apply (simp add: stable_def)+
    apply (simp add: Skip_def, rule Basic)
       apply (simp add: stable_def)+
  apply (rule Cond)
     apply (simp add: stable_def)+
    apply (rule Seq[where mid = "recva_await_mid s\<^sub>a (ch_destqport conf p)"])
     apply (rule Basic, clarsimp)
       apply (simp add: stable_def)+
  apply (rule conjI, clarsimp)
     apply (rule Basic, clarsimp)
       apply (simp add: stable_def)+
    apply (clarsimp, rule Basic)
       apply (simp add: stable_def)+
   apply (simp add: Skip_def, rule Basic, clarsimp)
  by (simp add: stable_def)+

abbreviation "recv_unlock_pre k ch \<equiv> state_inv \<inter> 
    {(s\<^sub>c, s\<^sub>a). qlock\<^sub>c s\<^sub>c ch = Some k \<and> 
              (obsize\<^sub>c s\<^sub>c ch > 0  \<longrightarrow> qbufsize\<^sub>c s\<^sub>c ch = obsize\<^sub>c s\<^sub>c ch - 1) \<and> 
              (obsize\<^sub>c s\<^sub>c ch = 0  \<longrightarrow> qbufsize\<^sub>c s\<^sub>c ch = obsize\<^sub>c s\<^sub>c ch)}"

lemma recv_await_post_inv: "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> recv_unlock_pre k ch; s\<^sub>c' \<in> recvc_unlock_await_post s\<^sub>c ch;
      s\<^sub>a' \<in> recva_await_post s\<^sub>a ch\<rbrakk> \<Longrightarrow> (s\<^sub>c', s\<^sub>a') \<in> recv_post"
  apply (case_tac "obsize\<^sub>c s\<^sub>c ch > 0", simp add: state_inv_def, clarify)
   apply presburger
  apply (simp add: state_inv_def, clarify)
  by force

lemma recv_unlock_sim: "prog_sim_pre (Some 
      (ATOMIC
          \<acute>qlock\<^sub>c := \<acute>qlock\<^sub>c (ch_destqport conf p := None);;
          \<acute>obsize\<^sub>c := \<acute>obsize\<^sub>c (ch_destqport conf p := \<acute>qbufsize\<^sub>c (ch_destqport conf p))
       END))
      (recv\<^sub>c_rely k (ch_destqport conf p)) (recv\<^sub>c_guar k (ch_destqport conf p)) 
      state_inv (recv_map k p) (recv_unlock_pre k (ch_destqport conf p)) send_post
      (Some 
      (ATOMIC
         IF \<acute>qbufsize\<^sub>a (ch_destqport conf p) > 0 THEN 
             \<acute>qbuf\<^sub>a := \<acute>qbuf\<^sub>a (ch_destqport conf p := tl (\<acute>qbuf\<^sub>a (ch_destqport conf p)));;
             \<acute>qbufsize\<^sub>a := \<acute>qbufsize\<^sub>a (ch_destqport conf p := \<acute>qbufsize\<^sub>a (ch_destqport conf p) - 1)
         FI
       END))
      send\<^sub>a_rely send\<^sub>a_guar"
  apply (rule Await_Await_Sound)
  using UNIV_I case_prodD colltrue_eq_univ rel_eq_def apply fastforce
       apply (simp add: recv_map_def)
      apply (simp add: stable_alpha)
     apply simp
    apply (rule stable_conj, simp add: stable_alpha)
    apply (simp add: Stable_def related_transitions_def)
    apply auto[1]
  using recva_not_stuck apply auto[1]
  apply clarsimp
  apply (rule_tac x = "recvc_unlock_await_post s\<^sub>c (ch_destqport conf p)" in exI)
  apply (rule conjI)
  using recvc_unlock_await_sat_post apply auto[1]
  apply (rule_tac x = "recva_await_post s\<^sub>a (ch_destqport conf p)" in exI)
  apply (rule conjI)
  using recva_await_sat_post apply auto[1]
  by (clarsimp, rule recv_await_post_inv, simp_all)

abbreviation "recv_sim_mid1 k ch \<equiv> recv_unlock_pre k ch"
abbreviation "recv_sim_mid2 k ch \<equiv> state_inv \<inter> {(s\<^sub>c, s\<^sub>a). qlock\<^sub>c s\<^sub>c ch = Some k \<and> qbufsize\<^sub>c s\<^sub>c ch = obsize\<^sub>c s\<^sub>c ch}"


lemma recv_sim_none1: "prog_sim_pre (Some 
      (AWAIT \<acute>qlock\<^sub>c (ch_destqport conf p) = None THEN
        \<acute>qlock\<^sub>c := \<acute>qlock\<^sub>c (ch_destqport conf p := Some k)
       END))
      (recv\<^sub>c_rely k (ch_destqport conf p)) (recv\<^sub>c_guar k (ch_destqport conf p)) 
      state_inv Map.empty recv_pre (recv_sim_mid2 k (ch_destqport conf p))
      None
      recv\<^sub>a_rely recv\<^sub>a_guar"
  apply (rule Await_None_Sound)
       apply simp+
     apply (simp add: Stable_def related_transitions_def)+
    apply auto[1]
   apply simp
  apply clarsimp
  apply (rule Await)
    apply (simp add: stable_def)+
  apply (clarsimp, rule Basic, clarsimp)
     apply (simp add: state_inv_def)
     apply auto[1]
    apply (simp add: stable_def)+
   apply auto[1]
  by (simp add: stable_def)

abbreviation "recv_sim_none_if_mid k ch \<equiv> state_inv \<inter> {(s\<^sub>c, s\<^sub>a). qbufsize\<^sub>c s\<^sub>c ch > 0}
             \<inter> {(s\<^sub>c, s\<^sub>a). qlock\<^sub>c s\<^sub>c ch = Some k \<and> qbufsize\<^sub>c s\<^sub>c ch = obsize\<^sub>c s\<^sub>c ch}"

lemma recv_sim_none2: "prog_sim_pre (Some 
      (IF \<acute>qbufsize\<^sub>c (ch_destqport conf p) > 0 THEN 
        \<acute>qbuf\<^sub>c := \<acute>qbuf\<^sub>c (ch_destqport conf p := tl (\<acute>qbuf\<^sub>c (ch_destqport conf p)));;
        \<acute>qbufsize\<^sub>c := \<acute>qbufsize\<^sub>c (ch_destqport conf p := \<acute>qbufsize\<^sub>c (ch_destqport conf p) - 1)
      FI))
      (recv\<^sub>c_rely k (ch_destqport conf p)) (recv\<^sub>c_guar k (ch_destqport conf p))
      state_inv Map.empty (recv_sim_mid2 k (ch_destqport conf p)) (recv_sim_mid1 k (ch_destqport conf p))
      None
      recv\<^sub>a_rely recv\<^sub>a_guar"
  apply auto
  apply (rule If_Comm_Branch_Sound)
        apply simp+
      apply (simp add: Stable_def related_transitions_def)
       apply auto
   apply (rule_tac \<zeta>\<^sub>1 = Map.empty and \<gamma>\<^sub>1 = "recv_sim_none_if_mid k (ch_destqport conf p)" in Seq_Skip_Sound)
      apply blast
     apply simp
    apply (rule Basic_None_Sound)
         apply blast+
       apply (simp add: Stable_def related_transitions_def)
       apply fastforce
      apply (simp add: Stable_def related_transitions_def)
      apply fastforce
     apply (simp add: state_inv_def)
     apply auto[1]
    apply simp
   apply (rule Basic_None_Sound)
        apply blast+
      apply (simp add: Stable_def related_transitions_def)
      apply fastforce
     apply (simp add: Stable_def related_transitions_def)
     apply fastforce
    apply (simp add: state_inv_def)
    apply auto[1]
   apply simp
  apply (simp add: Skip_def, rule Basic_None_Sound)
       apply blast+
     apply (simp add: Stable_def related_transitions_def)
     apply fastforce
    apply (simp add: Stable_def related_transitions_def)
    apply fastforce
   apply (simp add: state_inv_def)
  by auto

lemma recv_sim: "prog_sim_pre (Some 
      (AWAIT \<acute>qlock\<^sub>c (ch_destqport conf p) = None THEN
        \<acute>qlock\<^sub>c := \<acute>qlock\<^sub>c (ch_destqport conf p := Some k)
      END;;
      IF \<acute>qbufsize\<^sub>c (ch_destqport conf p) > 0 THEN 
        \<acute>qbuf\<^sub>c := \<acute>qbuf\<^sub>c (ch_destqport conf p := tl (\<acute>qbuf\<^sub>c (ch_destqport conf p)));;
        \<acute>qbufsize\<^sub>c := \<acute>qbufsize\<^sub>c (ch_destqport conf p := \<acute>qbufsize\<^sub>c (ch_destqport conf p) - 1)
      FI;;
      ATOMIC
        \<acute>qlock\<^sub>c := \<acute>qlock\<^sub>c (ch_destqport conf p := None);;
        \<acute>obsize\<^sub>c := \<acute>obsize\<^sub>c (ch_destqport conf p := \<acute>qbufsize\<^sub>c (ch_destqport conf p))
      END))
      (recv\<^sub>c_rely k (ch_destqport conf p)) (recv\<^sub>c_guar k (ch_destqport conf p)) 
      state_inv (recv_map k p) recv_pre recv_post
      (Some 
      (ATOMIC
         IF \<acute>qbufsize\<^sub>a (ch_destqport conf p) > 0 THEN 
           \<acute>qbuf\<^sub>a := \<acute>qbuf\<^sub>a (ch_destqport conf p := tl (\<acute>qbuf\<^sub>a (ch_destqport conf p)));;
           \<acute>qbufsize\<^sub>a := \<acute>qbufsize\<^sub>a (ch_destqport conf p := \<acute>qbufsize\<^sub>a (ch_destqport conf p) - 1)
         FI
      END))
      recv\<^sub>a_rely recv\<^sub>a_guar"
  apply (rule_tac \<zeta>\<^sub>1 = Map.empty and \<gamma>\<^sub>1 = "recv_sim_mid1 k (ch_destqport conf p)" in Seq_Skip_Sound)
     apply (simp add: recv_map_def)+
   apply (rule_tac \<zeta>\<^sub>1 = Map.empty and \<gamma>\<^sub>1 = "recv_sim_mid2 k (ch_destqport conf p)" in Seq_Skip_Sound)
      apply simp+
  using recv_sim_none1 apply auto[1]
  using recv_sim_none2 apply auto[1]
  using recv_unlock_sim by auto

subsection \<open>Rely-guarantee Proof for event systems\<close>

abbreviation "evtsys_rely\<^sub>c k \<equiv> \<lbrace>\<ordfeminine>cur\<^sub>c (c2s conf k) = \<ordmasculine>cur\<^sub>c (c2s conf k) 
     \<and> (\<forall>p. p2s conf p = c2s conf k \<longrightarrow> \<ordfeminine>partst\<^sub>c p = \<ordmasculine>partst\<^sub>c p)
     \<and> (\<forall>ch. (\<ordmasculine>qlock\<^sub>c ch = Some k \<longrightarrow> \<ordfeminine>qlock\<^sub>c ch = \<ordmasculine>qlock\<^sub>c ch \<and> \<ordfeminine>qbuf\<^sub>c ch = \<ordmasculine>qbuf\<^sub>c ch 
     \<and> \<ordfeminine>qbufsize\<^sub>c ch = \<ordmasculine>qbufsize\<^sub>c ch \<and> \<ordfeminine>obsize\<^sub>c ch = \<ordmasculine>obsize\<^sub>c ch))\<rbrace>"

abbreviation "evtsys_guar\<^sub>c k \<equiv> \<lbrace>\<forall>k'. k' \<noteq> k \<longrightarrow> \<ordfeminine>cur\<^sub>c (c2s conf k') = \<ordmasculine>cur\<^sub>c (c2s conf k') 
     \<and> (\<forall>p. p2s conf p \<noteq> c2s conf k \<longrightarrow> \<ordfeminine>partst\<^sub>c p = \<ordmasculine>partst\<^sub>c p)
     \<and> (\<forall>ch. (\<ordmasculine>qlock\<^sub>c ch \<noteq> Some k \<longrightarrow> \<ordfeminine>qlock\<^sub>c ch = \<ordmasculine>qlock\<^sub>c ch \<and> \<ordfeminine>qbuf\<^sub>c ch = \<ordmasculine>qbuf\<^sub>c ch 
     \<and> \<ordfeminine>qbufsize\<^sub>c ch = \<ordmasculine>qbufsize\<^sub>c ch \<and> \<ordfeminine>obsize\<^sub>c ch = \<ordmasculine>obsize\<^sub>c ch))\<rbrace> \<union> 
     {(s, s'). \<exists>ch. (qlock\<^sub>c s) ch = None \<and> s' = s \<lparr>qlock\<^sub>c := (qlock\<^sub>c s) (ch:= Some k)\<rparr>}"

abbreviation "evtsys_rely\<^sub>a k \<equiv> UNIV"
abbreviation "evtsys_guar\<^sub>a k \<equiv> UNIV"

lemma evtsys_rely_guar_compat: "i \<noteq> j \<Longrightarrow> evtsys_guar\<^sub>c i \<subseteq> evtsys_rely\<^sub>c j"
  apply clarsimp
  apply (rule conjI)
  using inj_eq inj_surj_c2s apply fastforce
  by auto

lemma core_init_e_sim : "e_sim 
     \<Gamma>\<^sub>c (Core_Init\<^sub>c k, s0\<^sub>c, x0\<^sub>c) (evtsys_rely\<^sub>c k) (evtsys_guar\<^sub>c k) 
     state_inv ((zetaI (init_map k))) state_inv 
     \<Gamma>\<^sub>a (Core_Init\<^sub>a k, s0\<^sub>a, x0\<^sub>a) UNIV UNIV"
  apply (simp add: Core_Init\<^sub>c_def Core_Init\<^sub>a_def)
  apply (rule_tac \<xi> = "init_pre k" in PiCore_SIMP_Refine.BasicEvt_Rule')
       apply (simp add: rel_guard_eq_def)+
     apply (simp add: Stable_e_def related_transitions_e_def s0c_init s0a_init)
     apply auto[1]
    apply (simp add: System_Init\<^sub>a_def System_Init\<^sub>c_def rel_guard_eq_def s0a_init s0c_init state_inv_def)
   apply simp
  apply clarsimp
  apply (rule_tac \<zeta> = "init_map k" in sim_implies_simI)
   apply (rule_tac \<xi> = "init_pre k" in prog_sim_pre_implies_sim, simp_all)
  apply (rule_tac \<xi> = "init_pre k" and \<gamma> = state_inv and R\<^sub>c = "init\<^sub>c_rely k" and G\<^sub>c = "init\<^sub>c_guar k" 
         and R\<^sub>a = UNIV and G\<^sub>a = UNIV in Conseq_Sound)
  using core_init_sim apply blast
  apply simp+
     apply blast
    apply simp
  apply force
  by simp

lemma sched_e_sim: "(s\<^sub>c, s\<^sub>a) \<in> state_inv \<Longrightarrow> e_sim 
        \<Gamma>\<^sub>c (Schedule\<^sub>c k p, s\<^sub>c, x\<^sub>c) (evtsys_rely\<^sub>c k) (evtsys_guar\<^sub>c k)
        state_inv (zetaI (schedule_map k p)) state_inv 
        \<Gamma>\<^sub>a (Schedule\<^sub>a k p, s\<^sub>a, x\<^sub>a) UNIV UNIV"
  apply (simp add: Schedule\<^sub>c_def Schedule\<^sub>a_def)
  apply (rule_tac \<xi> = "state_inv" in PiCore_SIMP_Refine.BasicEvt_Rule')
       apply (simp add: state_inv_def rel_guard_eq_def)
       apply auto[1]
      apply simp
  using stable_e_alpha apply blast
    apply simp+
  apply clarsimp
  apply (rule_tac \<zeta> = "schedule_map k p" in sim_implies_simI)
   apply (rule_tac \<xi> = "schdule_pre k p" in prog_sim_pre_implies_sim)
  apply (rule_tac \<xi> = "schdule_pre k p" and \<gamma> = state_inv and R\<^sub>c = "schedule\<^sub>c_rely k p" and G\<^sub>c = "schedule\<^sub>c_guar k" 
         and R\<^sub>a = UNIV and G\<^sub>a = UNIV in Conseq_Sound)
  using schedule_sim apply auto[1]
         apply simp_all
    apply auto[1]
  apply auto[1]
  apply (simp add: rel_guard_and_def)
  by force


lemma send_e_sim: "(s\<^sub>c, s\<^sub>a) \<in> state_inv \<Longrightarrow> e_sim 
        \<Gamma>\<^sub>c (Send_Que_Message\<^sub>c k p m, s\<^sub>c, x\<^sub>c) (evtsys_rely\<^sub>c k) (evtsys_guar\<^sub>c k)
        state_inv (zetaI (send_map k p m)) state_inv 
        \<Gamma>\<^sub>a (Send_Que_Message\<^sub>a k p m, s\<^sub>a, x\<^sub>a) UNIV UNIV"
  apply (simp add: Send_Que_Message\<^sub>c_def Send_Que_Message\<^sub>a_def)
  apply (rule_tac \<xi> = "state_inv" in PiCore_SIMP_Refine.BasicEvt_Rule')
       apply (simp add: state_inv_def rel_guard_eq_def)
       apply auto[1]
      apply simp
  using stable_e_alpha apply blast
    apply simp+
  apply clarsimp
  apply (rule_tac \<zeta> = "send_map k p m" in sim_implies_simI)
   apply (rule_tac \<xi> = "send_pre" in prog_sim_pre_implies_sim)
    apply (rule_tac \<xi> = "send_pre" and \<gamma> = state_inv and R\<^sub>c = "send\<^sub>c_rely k (ch_srcqport conf p)" 
    and G\<^sub>c = "send\<^sub>c_guar k (ch_srcqport conf p)" and R\<^sub>a = UNIV and G\<^sub>a = UNIV in Conseq_Sound)
  using send_sim apply auto[1]
         apply simp_all
   apply auto[1]
  apply (simp add: rel_guard_and_def)
  by auto

lemma recv_e_sim: "(s\<^sub>c, s\<^sub>a) \<in> state_inv \<Longrightarrow> e_sim 
        \<Gamma>\<^sub>c (Recv_Que_Message\<^sub>c k p, s\<^sub>c, x\<^sub>c) (evtsys_rely\<^sub>c k) (evtsys_guar\<^sub>c k)
        state_inv (zetaI (recv_map k p)) state_inv 
        \<Gamma>\<^sub>a (Recv_Que_Message\<^sub>a k p, s\<^sub>a, x\<^sub>a) UNIV UNIV"
  apply (simp add: Recv_Que_Message\<^sub>c_def Recv_Que_Message\<^sub>a_def)
  apply (rule_tac \<xi> = "state_inv" in PiCore_SIMP_Refine.BasicEvt_Rule')
       apply (simp add: state_inv_def rel_guard_eq_def)
       apply auto[1]
      apply simp
  using stable_e_alpha apply blast
    apply simp+
  apply clarsimp
  apply (rule_tac \<zeta> = "recv_map k p" in sim_implies_simI)
   apply (rule_tac \<xi> = "recv_pre" in prog_sim_pre_implies_sim)
    apply (rule_tac \<xi> = "recv_pre" and \<gamma> = state_inv and R\<^sub>c = "recv\<^sub>c_rely k (ch_destqport conf p)" 
    and G\<^sub>c = "recv\<^sub>c_guar k (ch_destqport conf p)" and R\<^sub>a = UNIV and G\<^sub>a = UNIV in Conseq_Sound)
  using recv_sim apply auto[1]
         apply simp_all
   apply auto[1]
  apply (simp add: rel_guard_and_def)
  by auto

lemma EvtSys_on_Core_sim : "es_sim 
      \<Gamma>\<^sub>c (EvtSys_on_Core\<^sub>c k, s0\<^sub>c, x0\<^sub>c) (evtsys_rely\<^sub>c k) (evtsys_guar\<^sub>c k)
      k state_inv ev_map ev_prog_map
      \<Gamma>\<^sub>a (EvtSys_on_Core\<^sub>a k, s0\<^sub>a, x0\<^sub>a) UNIV UNIV"
  apply (simp add: EvtSys_on_Core\<^sub>c_def EvtSys_on_Core\<^sub>a_def)
  apply (rule_tac \<gamma> = state_inv in PiCore_SIMP_Refine.EvtSeq_rule, simp_all)
  apply (simp add: ev_prog_map_init)
  using core_init_e_sim apply force
    apply (simp add: Core_Init\<^sub>c_def, clarsimp)
   apply (rule_tac \<gamma> = state_inv in PiCore_SIMP_Refine.EvtSys_rule, simp add: Schedule\<^sub>c_def
          Send_Que_Message\<^sub>c_def Recv_Que_Message\<^sub>c_def)
        apply auto[1]
       apply auto[1]
  using ev_map_schedule apply blast
  using ev_map_send apply blast
  using ev_map_recv apply blast
      apply auto[1] 
        apply (simp add: ev_map_schedule ev_prog_map_sched)
  using sched_e_sim apply force
       apply (simp add: ev_map_send ev_prog_map_send)
  using send_e_sim apply force
      apply (simp add: ev_map_recv ev_prog_map_recv)
  using recv_e_sim apply force
     apply simp+
  using stable_e_alpha apply blast
  by (simp add: ev_map_init)

theorem Arinc_sim: "pes_sim \<Gamma>\<^sub>c C0\<^sub>c state_inv ev_map ev_prog_map \<Gamma>\<^sub>a C0\<^sub>a"
  apply (simp add: C0c_init C0a_init)
  apply (rule_tac R\<^sub>c = evtsys_rely\<^sub>c and G\<^sub>c = evtsys_guar\<^sub>c and R\<^sub>a = evtsys_rely\<^sub>a and G\<^sub>a = evtsys_guar\<^sub>a 
        in PiCore_SIMP_Refine.Pes_rule)
   apply (simp add: ARINCXKernel_Spec\<^sub>c_def ARINCXKernel_Spec\<^sub>a_def, clarsimp)
  using EvtSys_on_Core_sim apply force
  using evtsys_rely_guar_compat by blast

subsection \<open>Refinement between implementation and Abstraction\<close>

interpretation ARINC_Sim_IFS: PiCore_Sim_IFS prog_simI
  ptranI\<^sub>c petranI\<^sub>c None ARINC_Env\<^sub>c C0\<^sub>c "exec_step\<^sub>c ARINC_Env\<^sub>c" interf state_equiv\<^sub>c state_obs\<^sub>c domevt\<^sub>c
  ptranI\<^sub>a petranI\<^sub>a None ARINC_Env\<^sub>a C0\<^sub>a "exec_step\<^sub>a ARINC_Env\<^sub>a" interf state_equiv\<^sub>a state_obs\<^sub>a domevt\<^sub>a
  state_inv ev_map ev_prog_map
proof
  show "pes_sim ARINC_Env\<^sub>c C0\<^sub>c recv_post ev_map ev_prog_map ARINC_Env\<^sub>a C0\<^sub>a"
    by (simp add: Arinc_sim)
  show "\<And>s\<^sub>c s\<^sub>a e\<^sub>c e\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> recv_post \<Longrightarrow> ev_map e\<^sub>c = e\<^sub>a \<Longrightarrow> domevt\<^sub>c s\<^sub>c e\<^sub>c = domevt\<^sub>a s\<^sub>a e\<^sub>a"
    by (simp add: ARINC_dom_sim)
  show "interf \<preceq>\<^sub>p interf"
    by (simp add: policy_refine_refl)
  show "\<And>s\<^sub>c s\<^sub>a t\<^sub>c t\<^sub>a d. (s\<^sub>c, s\<^sub>a) \<in> recv_post \<Longrightarrow> (t\<^sub>c, t\<^sub>a) \<in> recv_post \<Longrightarrow> s\<^sub>a \<sim>\<^sub>ad\<sim>\<^sub>a t\<^sub>a = s\<^sub>c \<sim>\<^sub>cd\<sim>\<^sub>c t\<^sub>c"
    using ARINC_sim_state_ifs by auto
qed

theorem ARINC_abs_lr_imp: "ARINC653\<^sub>a.local_respectC \<Longrightarrow> ARINC653\<^sub>c.local_respectC"
  by (simp add: ARINC_Sim_IFS.PiCore_abs_lr_imp)

theorem ARINC_abs_wsc_imp: "ARINC653\<^sub>a.weak_step_consistentC \<Longrightarrow> ARINC653\<^sub>c.weak_step_consistentC"
  by (simp add: ARINC_Sim_IFS.PiCore_abs_wsc_imp)

end
