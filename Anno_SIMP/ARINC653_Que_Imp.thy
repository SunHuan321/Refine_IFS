theory ARINC653_Que_Imp
  imports PiCore_Anno_SIMP_Syntax "../PiCore_RG_IFS" Anno_SIMP_IFS
begin

type_synonym max_buffer_size = nat
type_synonym buffer_size = nat

typedecl Part
typedecl Sched
typedecl Message 
typedecl Port
typedecl Core

typedecl QChannel

consts ARINC_Env :: "Anno_Env"

record Config = c2s :: "Core \<Rightarrow> Sched"
                p2s :: "Part \<Rightarrow> Sched"
                p2p :: "Port \<Rightarrow> Part"
                chsrc :: "QChannel \<Rightarrow> Port"
                chdest :: "QChannel \<Rightarrow> Port"  
                chmax :: "QChannel \<Rightarrow> nat"
  
axiomatization conf::Config 
  where bij_c2s: "bij (c2s conf)" 
(*
    and surj_p2c: "surj (p2s conf)" 
    and portsrc_disj: "\<forall>c1 c2. c1 \<noteq> c2 \<longrightarrow> (chsrc conf) c1 \<noteq> (chsrc conf) c2" 
    and portdest_disj: "\<forall>c1 c2. c1 \<noteq> c2 \<longrightarrow> (chdest conf) c1 \<noteq> (chdest conf) c2" 
*)

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

record State = cur :: "Sched \<Rightarrow> Part option"
               qbuf :: "QChannel \<Rightarrow> Message list"
               qbufsize :: "QChannel \<Rightarrow> nat"
               partst :: "Part \<Rightarrow> PartMode"

datatype EL = Core_InitE | ScheduleE | Send_Que_MessageE |  Recv_Que_MessageE

datatype parameter = Port Port | Message Message | Partition Part

type_synonym EventLabel = "EL \<times> (parameter list \<times> Core)" 
type_synonym Prog = "State ann_prog option"

definition get_evt_label :: "EL \<Rightarrow> parameter list \<Rightarrow> Core \<Rightarrow> EventLabel" ("_ _ \<rhd> _" [0,0,0] 20)
  where "get_evt_label el ps k \<equiv> (el,(ps,k))"

definition get_evt_core :: "(EventLabel, Core, State, Prog) event \<Rightarrow> Core"
  where "get_evt_core ev =  snd (snd (the (label_e ev)))"

definition get_evt_el :: "(EventLabel, Core, State, Prog) event \<Rightarrow> EL"
  where "get_evt_el ev =  fst (the (label_e ev))"

definition Core_Init :: "Core \<Rightarrow> (EventLabel, Core, State, Prog) event" 
  where "Core_Init k \<equiv> 
    EVENT Core_InitE [] \<rhd> k 
    THEN 
      \<lbrace>\<forall>p. p2s conf p = c2s conf k \<longrightarrow> \<acute>partst p = IDLE\<rbrace>
      \<acute>partst := (\<lambda>p. if p2s conf p = c2s conf k \<and> \<acute>partst p = IDLE then READY else \<acute>partst p) 
    END"

definition System_Init :: "Config \<Rightarrow> (State \<times> (EventLabel, Core, State, Prog) x)"
  where "System_Init cfg \<equiv> (\<lparr>cur=(\<lambda>c. None ),
                            qbuf = (\<lambda>c. []),
                            qbufsize = (\<lambda>c. 0),
                            partst = (\<lambda>p. IDLE)\<rparr>, 
                            (\<lambda>k. Core_Init k))"

definition Schedule :: "Core \<Rightarrow> Part \<Rightarrow> (EventLabel, Core, State, Prog) event" 
  where "Schedule k p \<equiv> 
    EVENT ScheduleE [Partition p] \<rhd> k 
    WHERE
      p2s conf p = c2s conf k \<and> (\<acute>partst p \<noteq> IDLE) \<and> (\<acute>cur (c2s conf k) = None 
          \<or> p2s conf (the (\<acute>cur((c2s conf) k))) = c2s conf k)
    THEN
      \<lbrace>p2s conf p = c2s conf k \<and> (\<acute>partst p \<noteq> IDLE) \<and> (\<acute>cur((c2s conf) k) = None \<or> p2s conf (the (\<acute>cur((c2s conf) k))) = c2s conf k)\<rbrace> 
        IF (\<acute>cur((c2s conf) k) \<noteq> None) THEN 
        \<lbrace>p2s conf p = c2s conf k  \<and> p2s conf (the (\<acute>cur((c2s conf) k))) = c2s conf k\<rbrace> 
              ATOMIC
          \<lbrace>True\<rbrace> \<acute>partst := \<acute>partst(the (\<acute>cur ((c2s conf) k)) := READY);;
          \<lbrace>True\<rbrace> \<acute>cur := \<acute>cur((c2s conf) k := None)
               END
            FI;;
      
      (\<lbrace>p2s conf p = c2s conf k \<and> \<acute>cur(c2s conf k) = None \<rbrace>
         ATOMIC
        \<lbrace>True\<rbrace> \<acute>cur := \<acute>cur((c2s conf k) := Some p);;
        \<lbrace>True\<rbrace> \<acute>partst := \<acute>partst(p := RUN)
        END)

    END"


definition Send_Que_Message :: "Core \<Rightarrow> Port \<Rightarrow> Message \<Rightarrow> (EventLabel, Core, State, Prog) event" 
  where "Send_Que_Message k p m \<equiv> 
    EVENT Send_Que_MessageE [Port p, Message m] \<rhd> k 
    WHERE
      is_src_qport conf p
      \<and> \<acute>cur (c2s conf k) \<noteq> None
      \<and> port_of_part conf p (the (\<acute>cur (c2s conf k)))
    THEN
     \<lbrace>is_src_qport conf p \<and> \<acute>cur (c2s conf k) \<noteq> None \<and> port_of_part conf p (the (\<acute>cur (c2s conf k)))\<rbrace> 
     ATOMIC
     \<lbrace>True\<rbrace> IF \<acute>qbufsize (ch_srcqport conf p) < chmax conf (ch_srcqport conf p) THEN 
     \<lbrace>True\<rbrace> \<acute>qbuf := \<acute>qbuf (ch_srcqport conf p := \<acute>qbuf (ch_srcqport conf p) @ [m]);;
     \<lbrace>True\<rbrace> \<acute>qbufsize := \<acute>qbufsize (ch_srcqport conf p := \<acute>qbufsize (ch_srcqport conf p) + 1)
            FI
      END
    END"


definition Recv_Que_Message :: "Core \<Rightarrow> Port \<Rightarrow> (EventLabel, Core, State, Prog) event" 
  where "Recv_Que_Message k p \<equiv> 
    EVENT Recv_Que_MessageE [Port p] \<rhd> k 
    WHERE
      is_dest_qport conf p 
      \<and> \<acute>cur (c2s conf k) \<noteq> None
      \<and> port_of_part conf p (the (\<acute>cur (c2s conf k)))
    THEN 
        \<lbrace>is_dest_qport conf p  \<and> \<acute>cur (c2s conf k) \<noteq> None \<and> port_of_part conf p (the (\<acute>cur ((c2s conf) k))) \<rbrace>
        AWAIT \<acute>qbufsize (ch_destqport conf p) > 0 THEN 
          \<lbrace>True\<rbrace> \<acute>qbuf := \<acute>qbuf (ch_destqport conf p := tl (\<acute>qbuf (ch_destqport conf p)));;
          \<lbrace>True\<rbrace> \<acute>qbufsize := \<acute>qbufsize (ch_destqport conf p := \<acute>qbufsize (ch_destqport conf p) - 1)
        END
    END"