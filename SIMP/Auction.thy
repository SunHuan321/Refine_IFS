theory Auction
  imports PiCore_SIMP_Syntax Ref_SIMP PiCore_SIMP_Ref
begin

subsection \<open>System specification\<close>

type_synonym Auc_Id = nat
type_synonym Auc_Qt = nat
consts Auc_Env\<^sub>c :: "SIMP_Env\<^sub>c"
consts Auc_Env\<^sub>a :: "SIMP_Env\<^sub>a"


datatype Auc_Status = READY | RUNNING | CLOSED

datatype EL = Start_AuctionE Auc_Qt
  | Close_AuctionE
  | Publish_ResE
  | Register_BidE Auc_Id Auc_Qt

datatype Domain = User Auc_Id | Server | Publisher | F

datatype Core = User_CPU Auc_Id
  | Server_CPU

datatype Res = Success "Auc_Id \<times> Auc_Qt"
  | UnSuccess

type_synonym EventLabel = "EL \<times> Core" 

definition get_evt_label :: "EL \<Rightarrow> Core \<Rightarrow> EventLabel" ("_ \<rhd> _" [0,0] 20)
  where "get_evt_label el k \<equiv> (el,k)"

primrec is_user :: "Domain \<Rightarrow> bool"
  where "is_user (User _) = True"
  | "is_user Server = False"
  | "is_user Publisher = False"
  | "is_user F = False"

definition interf :: "Domain \<Rightarrow> Domain \<Rightarrow> bool" ("(_ \<leadsto> _)" [70,71] 60)
  where "interf d1 d2 \<equiv> if d1 = d2 then True
                         else if (is_user d1) \<and> d2 = Server then True
                         else if d1 = Server \<and> d2 = Publisher then True
                         else if d1 = Publisher \<and> (is_user d2) then True
                         else False"

definition noninterf :: "Domain \<Rightarrow> Domain \<Rightarrow> bool" ("(_ \<setminus>\<leadsto> _)" [70,71] 60)
  where "u \<setminus>\<leadsto> v \<equiv> \<not> (u \<leadsto> v)"

subsubsection \<open>Implementation Specification\<close>

record State\<^sub>c = status\<^sub>c :: "Auc_Status"
                reserve\<^sub>c :: "Auc_Qt"
                lock\<^sub>c :: "Core option"
                max_bid\<^sub>c :: "Auc_Id \<times> Auc_Qt"
                log_bid\<^sub>c :: "(Auc_Id \<times> Auc_Qt) list"
                obs_st\<^sub>c :: "Auc_Status"
                obs_max\<^sub>c :: "Auc_Id \<times> Auc_Qt"
                obs_log\<^sub>c :: "(Auc_Id \<times> Auc_Qt) list"
                res\<^sub>c :: "Res"
                
type_synonym Prog\<^sub>c = "State\<^sub>c com option"

definition Start_Auction\<^sub>c :: "Auc_Qt \<Rightarrow> (EventLabel, Core, State\<^sub>c, Prog\<^sub>c) event" 
  where "Start_Auction\<^sub>c qt \<equiv> 
    EVENT Start_AuctionE qt \<rhd> Server_CPU 
    WHERE \<acute>status\<^sub>c = CLOSED
    THEN
      ATOMIC  
        \<acute>res\<^sub>c := UnSuccess ;;
        \<acute>lock\<^sub>c := None ;;
        \<acute>status\<^sub>c := READY ;;
        \<acute>obs_st\<^sub>c := READY ;;
        \<acute>reserve\<^sub>c := qt
      END
    END"

definition Close_Auction\<^sub>c :: "(EventLabel, Core, State\<^sub>c, Prog\<^sub>c) event" 
  where "Close_Auction\<^sub>c \<equiv> 
    EVENT Close_AuctionE \<rhd> Server_CPU 
    WHERE \<acute>status\<^sub>c \<noteq> CLOSED
    THEN  
      AWAIT \<acute>lock\<^sub>c = None THEN 
        \<acute>lock\<^sub>c := Some Server_CPU 
      END ;;
      ATOMIC    
        \<acute>status\<^sub>c := CLOSED ;;
        \<acute>obs_st\<^sub>c := CLOSED
      END
    END"

definition Publish_Res\<^sub>c :: "(EventLabel, Core, State\<^sub>c, Prog\<^sub>c) event" 
  where "Publish_Res\<^sub>c  \<equiv> 
    EVENT Publish_ResE \<rhd> Server_CPU
    WHERE \<acute>status\<^sub>c = CLOSED
    THEN 
      IF snd \<acute>max_bid\<^sub>c > \<acute>reserve\<^sub>c
      THEN
         \<acute>res\<^sub>c := Success \<acute>max_bid\<^sub>c
      ELSE
         \<acute>res\<^sub>c := UnSuccess
      FI
    END"

definition Register_Bid\<^sub>c :: "Auc_Id \<Rightarrow> Auc_Qt \<Rightarrow> (EventLabel, Core, State\<^sub>c, Prog\<^sub>c) event"
  where "Register_Bid\<^sub>c uid qt \<equiv> 
    EVENT Register_BidE uid qt \<rhd> (User_CPU uid)
    WHERE \<acute>status\<^sub>c = RUNNING \<or> \<acute>status\<^sub>c = READY
    THEN
      AWAIT \<acute>lock\<^sub>c = None THEN 
        \<acute>lock\<^sub>c := Some (User_CPU uid) 
      END ;;
      IF \<acute>status\<^sub>c = READY
      THEN
         \<acute>max_bid\<^sub>c := (uid, qt) ;;
         \<acute>log_bid\<^sub>c := [(uid, qt)];;
         \<acute>status\<^sub>c := RUNNING
      ELSE
         \<acute>log_bid\<^sub>c := \<acute>log_bid\<^sub>c @ [(uid, qt)] ;;
          IF snd \<acute>max_bid\<^sub>c < qt
          THEN
             \<acute>max_bid\<^sub>c := (uid, qt)
          FI
      FI ;;
      ATOMIC
        \<acute>lock\<^sub>c := None ;;
        \<acute>obs_log\<^sub>c := \<acute>log_bid\<^sub>c ;;
        \<acute>obs_max\<^sub>c := \<acute>max_bid\<^sub>c ;;
        \<acute>obs_st\<^sub>c := \<acute>status\<^sub>c
      END
     END"

primrec Auction_Spec\<^sub>c :: "(EventLabel, Core, State\<^sub>c, Prog\<^sub>c) paresys"
  where "Auction_Spec\<^sub>c (User_CPU uid) = EvtSys (\<Union>qt. {Register_Bid\<^sub>c uid qt})"
  | "Auction_Spec\<^sub>c Server_CPU = EvtSys (\<Union>qt. {Start_Auction\<^sub>c qt} \<union> {Close_Auction\<^sub>c, Publish_Res\<^sub>c}) "


abbreviation s0\<^sub>c :: State\<^sub>c
  where "s0\<^sub>c \<equiv> \<lparr>status\<^sub>c = CLOSED, reserve\<^sub>c = 0, lock\<^sub>c = Some Server_CPU,  max_bid\<^sub>c = (0, 0), 
  log_bid\<^sub>c = [(0, 0)], obs_st\<^sub>c = CLOSED, obs_max\<^sub>c = (0,0), obs_log\<^sub>c = [(0, 0)], res\<^sub>c = UnSuccess\<rparr>"
consts x0\<^sub>c :: "(EventLabel, Core, State\<^sub>c, Prog\<^sub>c) x"

abbreviation C0\<^sub>c :: "(EventLabel, Core, State\<^sub>c, Prog\<^sub>c) pesconf"
  where "C0\<^sub>c \<equiv> (Auction_Spec\<^sub>c, s0\<^sub>c, x0\<^sub>c)"

primrec el_domevt\<^sub>c :: "EL  \<Rightarrow> Domain"
  where "el_domevt\<^sub>c (Start_AuctionE _) = Server"
  | "el_domevt\<^sub>c Close_AuctionE = Server"
  | "el_domevt\<^sub>c Publish_ResE = Publisher"
  | "el_domevt\<^sub>c (Register_BidE uid _) = User uid"

primrec domevt\<^sub>c :: "State\<^sub>c \<Rightarrow> (EventLabel, Core, State\<^sub>c, Prog\<^sub>c) event \<Rightarrow> Domain"
  where "domevt\<^sub>c s (AnonyEvent _) = F"
  | "domevt\<^sub>c s (BasicEvent e) = el_domevt\<^sub>c (fst (label e))"

definition exec_step\<^sub>c :: "SIMP_Env\<^sub>c \<Rightarrow> (EventLabel, Core, State\<^sub>c, Prog\<^sub>c, Domain) action \<Rightarrow> 
 ((EventLabel, Core, State\<^sub>c, Prog\<^sub>c) pesconf \<times> (EventLabel, Core, State\<^sub>c, Prog\<^sub>c) pesconf) set"
  where "exec_step\<^sub>c \<Gamma>\<^sub>c a \<equiv> {(P,Q). (\<Gamma>\<^sub>c \<turnstile>\<^sub>c P-pes-(actk a)\<rightarrow> Q) \<and>((\<exists>e k. actk a = ((EvtEnt e)\<sharp>k) \<and> eventof a = e 
                         \<and> domevt\<^sub>c (gets P) e = domain a) \<or> (\<exists>c k. actk a = ((Cmd c)\<sharp>k) 
                         \<and> eventof a = (getx P) k \<and> domevt\<^sub>c (gets P) (eventof a) = domain a))}"

definition state_obs_server\<^sub>c :: "State\<^sub>c \<Rightarrow> State\<^sub>c"
  where "state_obs_server\<^sub>c s \<equiv> s0\<^sub>c\<lparr>obs_st\<^sub>c := obs_st\<^sub>c s, obs_max\<^sub>c := obs_max\<^sub>c s, 
                                  obs_log\<^sub>c := obs_log\<^sub>c s, reserve\<^sub>c := reserve\<^sub>c s\<rparr>"

definition state_obs_user\<^sub>c :: "State\<^sub>c \<Rightarrow> State\<^sub>c"
  where "state_obs_user\<^sub>c s  \<equiv> s0\<^sub>c\<lparr>res\<^sub>c := res\<^sub>c s\<rparr>"

definition state_obs_pulisher\<^sub>c :: "State\<^sub>c \<Rightarrow> State\<^sub>c"
  where "state_obs_pulisher\<^sub>c s  \<equiv> s0\<^sub>c\<lparr>res\<^sub>c := res\<^sub>c s\<rparr>"


primrec state_obs\<^sub>c :: "State\<^sub>c \<Rightarrow> Domain \<Rightarrow> State\<^sub>c"
  where "state_obs\<^sub>c s Server = state_obs_server\<^sub>c s" |
        "state_obs\<^sub>c s (User _) = state_obs_user\<^sub>c s"|
        "state_obs\<^sub>c s Publisher = state_obs_pulisher\<^sub>c s"|
        "state_obs\<^sub>c s F = s0\<^sub>c"

definition state_equiv\<^sub>c :: "State\<^sub>c \<Rightarrow> Domain \<Rightarrow> State\<^sub>c \<Rightarrow> bool" ("(_ \<sim>\<^sub>c_\<sim>\<^sub>c _)" [70,69,70] 60)
  where "state_equiv\<^sub>c s d t \<equiv> state_obs\<^sub>c s d = state_obs\<^sub>c t d"

lemma state_equiv_transitivec: "\<lbrakk>s \<sim>\<^sub>c d \<sim>\<^sub>c t; t \<sim>\<^sub>c d \<sim>\<^sub>c r\<rbrakk> \<Longrightarrow> s \<sim>\<^sub>c d \<sim>\<^sub>c r"
  by (simp add:state_equiv\<^sub>c_def)
    
lemma state_equiv_symmetricc : "s \<sim>\<^sub>c d \<sim>\<^sub>c t \<Longrightarrow> t \<sim>\<^sub>c d \<sim>\<^sub>c s"
  by (simp add:state_equiv\<^sub>c_def)

lemma state_equiv_reflexivec : "s \<sim>\<^sub>c d \<sim>\<^sub>c s"
  by (simp add:state_equiv\<^sub>c_def)

interpretation Auction\<^sub>c: InfoFlow ptranI\<^sub>c petranI\<^sub>c None Auc_Env\<^sub>c C0\<^sub>c "exec_step\<^sub>c Auc_Env\<^sub>c" interf state_equiv\<^sub>c state_obs\<^sub>c domevt\<^sub>c
proof
  show "\<forall>a b c u. a \<sim>\<^sub>cu\<sim>\<^sub>c b \<and> b \<sim>\<^sub>cu\<sim>\<^sub>c c \<longrightarrow> a \<sim>\<^sub>cu\<sim>\<^sub>c c"
    using state_equiv_transitivec by blast
  show "\<forall>a b u. a \<sim>\<^sub>cu\<sim>\<^sub>c b \<longrightarrow> b \<sim>\<^sub>cu\<sim>\<^sub>c a"
    using state_equiv_symmetricc by blast
  show "\<forall>a u. a \<sim>\<^sub>cu\<sim>\<^sub>c a"
    by (simp add: state_equiv_reflexivec)
  show "\<And>a. exec_step\<^sub>c Auc_Env\<^sub>c a \<equiv> {(P, Q). Auc_Env\<^sub>c \<turnstile>\<^sub>c P -pes-actk a\<rightarrow> Q \<and> 
        ((\<exists>e k. actk a = EvtEnt e\<sharp>k \<and> eventof a = e \<and> domevt\<^sub>c (gets P) e = domain a) 
        \<or> (\<exists>c k. actk a = Cmd c\<sharp>k \<and> eventof a = getx P k \<and> domevt\<^sub>c (gets P) (eventof a) = domain a))}"
    by (simp add: exec_step\<^sub>c_def) 
qed

subsubsection \<open>Abstraction Specification\<close>

record State\<^sub>a = status\<^sub>a :: "Auc_Status"
                reserve\<^sub>a :: "Auc_Qt"
                max_bid\<^sub>a :: "Auc_Id \<times> Auc_Qt"
                log_bid\<^sub>a :: "(Auc_Id \<times> Auc_Qt) list"
                res\<^sub>a :: "Res"
                
type_synonym Prog\<^sub>a = "State\<^sub>a com option"

definition Start_Auction\<^sub>a :: "Auc_Qt \<Rightarrow> (EventLabel, Core, State\<^sub>a, Prog\<^sub>a) event" 
  where "Start_Auction\<^sub>a qt \<equiv> 
    EVENT Start_AuctionE qt \<rhd> Server_CPU 
    WHERE \<acute>status\<^sub>a = CLOSED
    THEN
      ATOMIC
        \<acute>res\<^sub>a := UnSuccess ;;
        \<acute>status\<^sub>a := READY ;;
        \<acute>reserve\<^sub>a := qt
      END
    END"

definition Close_Auction\<^sub>a :: "(EventLabel, Core, State\<^sub>a, Prog\<^sub>a) event" 
  where "Close_Auction\<^sub>a \<equiv> 
    EVENT Close_AuctionE \<rhd> Server_CPU 
    WHERE \<acute>status\<^sub>a \<noteq> CLOSED
    THEN 
      ATOMIC    
        \<acute>status\<^sub>a := CLOSED
      END
    END"

definition Publish_Res\<^sub>a :: "(EventLabel, Core, State\<^sub>a, Prog\<^sub>a) event" 
  where "Publish_Res\<^sub>a  \<equiv> 
    EVENT Publish_ResE \<rhd> Server_CPU
    WHERE \<acute>status\<^sub>a = CLOSED
    THEN
      ATOMIC
        IF snd \<acute>max_bid\<^sub>a > \<acute>reserve\<^sub>a
        THEN
          \<acute>res\<^sub>a := Success \<acute>max_bid\<^sub>a
        ELSE
          \<acute>res\<^sub>a := UnSuccess
        FI
      END
    END"

definition Register_Bid\<^sub>a :: "Auc_Id \<Rightarrow> Auc_Qt \<Rightarrow> (EventLabel, Core, State\<^sub>a, Prog\<^sub>a) event"
  where "Register_Bid\<^sub>a uid qt \<equiv> 
    EVENT Register_BidE uid qt \<rhd> (User_CPU uid)
    WHERE \<acute>status\<^sub>a = READY \<or> \<acute>status\<^sub>a = RUNNING
    THEN
      ATOMIC
        IF \<acute>status\<^sub>a = READY
        THEN
         \<acute>log_bid\<^sub>a := [(uid, qt)];;
         \<acute>max_bid\<^sub>a := (uid, qt) ;;
         \<acute>status\<^sub>a := RUNNING
        ELSE
         \<acute>log_bid\<^sub>a := \<acute>log_bid\<^sub>a @ [(uid, qt)] ;;
          IF qt > snd \<acute>max_bid\<^sub>a
          THEN
             \<acute>max_bid\<^sub>a := (uid, qt)
          FI
        FI
      END
     END"

primrec Auction_Spec\<^sub>a :: "(EventLabel, Core, State\<^sub>a, Prog\<^sub>a) paresys"
  where "Auction_Spec\<^sub>a (User_CPU uid) = EvtSys (\<Union>qt. {Register_Bid\<^sub>a uid qt})"
  | "Auction_Spec\<^sub>a Server_CPU = EvtSys (\<Union>qt. {Start_Auction\<^sub>a qt} \<union> {Close_Auction\<^sub>a, Publish_Res\<^sub>a})"


abbreviation s0\<^sub>a :: State\<^sub>a
  where "s0\<^sub>a \<equiv> \<lparr>status\<^sub>a = CLOSED, reserve\<^sub>a = 0, max_bid\<^sub>a = (0, 0), log_bid\<^sub>a = [(0, 0)], res\<^sub>a = UnSuccess \<rparr>"
consts x0\<^sub>a :: "(EventLabel, Core, State\<^sub>a, Prog\<^sub>a) x"

abbreviation C0\<^sub>a :: "(EventLabel, Core, State\<^sub>a, Prog\<^sub>a) pesconf"
  where "C0\<^sub>a \<equiv> (Auction_Spec\<^sub>a, s0\<^sub>a, x0\<^sub>a)"

primrec el_domevt\<^sub>a :: "EL  \<Rightarrow> Domain"
  where "el_domevt\<^sub>a (Start_AuctionE _) = Server"
  | "el_domevt\<^sub>a Close_AuctionE = Server"
  | "el_domevt\<^sub>a Publish_ResE = Publisher"
  | "el_domevt\<^sub>a (Register_BidE uid _) = User uid"

primrec domevt\<^sub>a :: "State\<^sub>a \<Rightarrow> (EventLabel, Core, State\<^sub>a, Prog\<^sub>a) event \<Rightarrow> Domain"
  where "domevt\<^sub>a s (AnonyEvent _) = F"
  | "domevt\<^sub>a s (BasicEvent e) = el_domevt\<^sub>c (fst (label e))"

definition exec_step\<^sub>a :: "SIMP_Env\<^sub>a \<Rightarrow> (EventLabel, Core, State\<^sub>a, Prog\<^sub>a, Domain) action \<Rightarrow> 
 ((EventLabel, Core, State\<^sub>a, Prog\<^sub>a) pesconf \<times> (EventLabel, Core, State\<^sub>a, Prog\<^sub>a) pesconf) set"
  where "exec_step\<^sub>a \<Gamma>\<^sub>a a \<equiv> {(P,Q). (\<Gamma>\<^sub>a \<turnstile>\<^sub>a P-pes-(actk a)\<rightarrow> Q) \<and>((\<exists>e k. actk a = ((EvtEnt e)\<sharp>k) \<and> eventof a = e 
                         \<and> domevt\<^sub>a (gets P) e = domain a) \<or> (\<exists>c k. actk a = ((Cmd c)\<sharp>k) 
                         \<and> eventof a = (getx P) k \<and> domevt\<^sub>a (gets P) (eventof a) = domain a))}"

definition state_obs_server\<^sub>a :: "State\<^sub>a \<Rightarrow> State\<^sub>a"
  where "state_obs_server\<^sub>a s \<equiv> s0\<^sub>a\<lparr>status\<^sub>a := status\<^sub>a s, max_bid\<^sub>a := max_bid\<^sub>a s,
                                  log_bid\<^sub>a := log_bid\<^sub>a s, reserve\<^sub>a := reserve\<^sub>a s\<rparr>"

definition state_obs_user\<^sub>a :: "State\<^sub>a \<Rightarrow> State\<^sub>a"
  where "state_obs_user\<^sub>a s  \<equiv> s0\<^sub>a\<lparr>res\<^sub>a := res\<^sub>a s\<rparr>"

definition state_obs_pulisher\<^sub>a :: "State\<^sub>a \<Rightarrow> State\<^sub>a"
  where "state_obs_pulisher\<^sub>a s  \<equiv> s0\<^sub>a\<lparr>res\<^sub>a := res\<^sub>a s\<rparr>"


primrec state_obs\<^sub>a :: "State\<^sub>a \<Rightarrow> Domain \<Rightarrow> State\<^sub>a"
  where "state_obs\<^sub>a s Server = state_obs_server\<^sub>a s" |
        "state_obs\<^sub>a s (User _) = state_obs_user\<^sub>a s"|
        "state_obs\<^sub>a s Publisher = state_obs_pulisher\<^sub>a s"|
        "state_obs\<^sub>a s F = s0\<^sub>a"

definition state_equiv\<^sub>a :: "State\<^sub>a \<Rightarrow> Domain \<Rightarrow> State\<^sub>a \<Rightarrow> bool" ("(_ \<sim>\<^sub>a_\<sim>\<^sub>a _)" [70,69,70] 60)
  where "state_equiv\<^sub>a s d t \<equiv> state_obs\<^sub>a s d = state_obs\<^sub>a t d"

lemma state_equiv_transitivea: "\<lbrakk>s \<sim>\<^sub>a d \<sim>\<^sub>a t; t \<sim>\<^sub>a d \<sim>\<^sub>a r\<rbrakk> \<Longrightarrow> s \<sim>\<^sub>a d \<sim>\<^sub>a r"
  by (simp add:state_equiv\<^sub>a_def)
    
lemma state_equiv_symmetrica : "s \<sim>\<^sub>a d \<sim>\<^sub>a t \<Longrightarrow> t \<sim>\<^sub>a d \<sim>\<^sub>a s"
  by (simp add:state_equiv\<^sub>a_def)

lemma state_equiv_reflexivea : "s \<sim>\<^sub>a d \<sim>\<^sub>a s"
  by (simp add:state_equiv\<^sub>a_def)

interpretation Auction\<^sub>a: InfoFlow ptranI\<^sub>a petranI\<^sub>a None Auc_Env\<^sub>a C0\<^sub>a "exec_step\<^sub>a Auc_Env\<^sub>a" interf state_equiv\<^sub>a state_obs\<^sub>a domevt\<^sub>a
proof
  show "\<forall>a b c u. a \<sim>\<^sub>au\<sim>\<^sub>a b \<and> b \<sim>\<^sub>au\<sim>\<^sub>a c \<longrightarrow> a \<sim>\<^sub>au\<sim>\<^sub>a c"
    using state_equiv_transitivea by blast
  show "\<forall>a b u. a \<sim>\<^sub>au\<sim>\<^sub>a b \<longrightarrow> b \<sim>\<^sub>au\<sim>\<^sub>a a"
    using state_equiv_symmetrica by blast
  show "\<forall>a u. a \<sim>\<^sub>au\<sim>\<^sub>a a"
    by (simp add: state_equiv_reflexivea)
  show "\<And>a. exec_step\<^sub>a Auc_Env\<^sub>a a \<equiv> {(P, Q). Auc_Env\<^sub>a \<turnstile>\<^sub>a P -pes-actk a\<rightarrow> Q \<and> 
        ((\<exists>e k. actk a = EvtEnt e\<sharp>k \<and> eventof a = e \<and> domevt\<^sub>a (gets P) e = domain a) 
        \<or> (\<exists>c k. actk a = Cmd c\<sharp>k \<and> eventof a = getx P k \<and> domevt\<^sub>a (gets P) (eventof a) = domain a))}"
    by (simp add: exec_step\<^sub>a_def) 
qed

fun first_max_auc_qt :: "(Auc_Id \<times> Auc_Qt) list \<Rightarrow> (Auc_Id \<times> Auc_Qt) option" where
  "first_max_auc_qt [] = None" |
  "first_max_auc_qt (x # xs) =
     (case first_max_auc_qt xs of
        None \<Rightarrow> Some x |
        Some y \<Rightarrow> if snd x \<ge> snd y then Some x else Some y)"

lemma first_None_implies_Nil: "first_max_auc_qt xs = None \<Longrightarrow> xs = []"
  apply (case_tac xs, simp)
  apply (case_tac "first_max_auc_qt list", simp, simp)
  by (metis option.distinct(1))

lemma first_max_append : "\<lbrakk>first_max_auc_qt l1 = Some (id1, qt1); first_max_auc_qt l2 = Some (id2, qt2)\<rbrakk>
      \<Longrightarrow> first_max_auc_qt (l1 @ l2) = (if qt1 \<ge> qt2 then Some (id1, qt1) else Some (id2, qt2))"
proof (induction l1 arbitrary: l2 id1 qt1)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  proof(cases "first_max_auc_qt xs")
    case None
    then have "xs = []"
      by (simp add: first_None_implies_Nil)
    then show ?thesis
      using Cons.prems(1) Cons.prems(2) by auto
  next
    case (Some a)
    then obtain id1' qt1' where a0: "a = (id1', qt1')"
      using nat_gcd.cases by blast
    then show ?thesis
    proof(cases "snd x \<ge> qt1'")
      case True
      then have "x = (id1, qt1)"
        using a0 Cons.prems(1) Some by force
      then have "first_max_auc_qt (xs @ l2) = (if qt2 \<le> qt1' then Some (id1', qt1') else Some (id2, qt2))"
        using Cons.IH Cons.prems(2) Some a0 by blast
      then show ?thesis 
        using True \<open>x = (id1, qt1)\<close> append_Cons by auto
    next
      case False
      then show ?thesis 
        using Cons.IH Cons.prems(1) Cons.prems(2) Some a0 by auto
    qed
  qed
qed

lemma first_max_add_not_max: "\<lbrakk>first_max_auc_qt xs = Some (muid, mqt); qt \<le> mqt\<rbrakk> \<Longrightarrow> 
       first_max_auc_qt (xs @ [(uid, qt)]) = Some (muid, mqt)"
  by (simp add: first_max_append)

lemma first_max_add_max: "\<lbrakk>first_max_auc_qt xs = Some (muid, mqt); qt > mqt\<rbrakk> \<Longrightarrow> 
       first_max_auc_qt (xs @ [(uid, qt)]) = Some (uid, qt)"
  by (simp add: first_max_append)

definition is_max :: "(Auc_Id \<times> Auc_Qt) \<Rightarrow> (Auc_Id \<times> Auc_Qt) list \<Rightarrow> bool"
  where "is_max a xs = (first_max_auc_qt xs = Some a)"

lemma is_max_add_not_max: "\<lbrakk>is_max (muid, mqt) xs; qt \<le> mqt\<rbrakk> \<Longrightarrow> is_max (muid, mqt) (xs @ [(uid, qt)])"
  by (simp add: first_max_add_not_max is_max_def)

lemma is_max_add_max: "\<lbrakk>is_max (muid, mqt) xs; qt > mqt\<rbrakk> \<Longrightarrow> is_max (uid, qt) (xs @ [(uid, qt)])"
  using first_max_add_max is_max_def by blast

definition state_inv :: " (State\<^sub>c \<times> State\<^sub>a) set" 
  where "state_inv = {(s\<^sub>c, s\<^sub>a). reserve\<^sub>c s\<^sub>c = reserve\<^sub>a s\<^sub>a \<and> res\<^sub>c s\<^sub>c = res\<^sub>a s\<^sub>a
         \<and> obs_st\<^sub>c s\<^sub>c = status\<^sub>a s\<^sub>a \<and> obs_log\<^sub>c s\<^sub>c = log_bid\<^sub>a s\<^sub>a \<and> obs_max\<^sub>c s\<^sub>c = max_bid\<^sub>a s\<^sub>a \<and> 
         is_max (obs_max\<^sub>c s\<^sub>c) (obs_log\<^sub>c s\<^sub>c) \<and> is_max (max_bid\<^sub>a s\<^sub>a) (log_bid\<^sub>a s\<^sub>a) \<and> 
         ((status\<^sub>c s\<^sub>c \<noteq> CLOSED) = (status\<^sub>a s\<^sub>a \<noteq> CLOSED)) \<and>
         ((lock\<^sub>c s\<^sub>c = None \<or> lock\<^sub>c s\<^sub>c = Some Server_CPU) \<longrightarrow> 
         (obs_st\<^sub>c s\<^sub>c = status\<^sub>c s\<^sub>c \<and> obs_log\<^sub>c s\<^sub>c = log_bid\<^sub>c s\<^sub>c \<and> obs_max\<^sub>c s\<^sub>c = max_bid\<^sub>c s\<^sub>c)) \<and>
         (status\<^sub>c s\<^sub>c = CLOSED \<longrightarrow> lock\<^sub>c s\<^sub>c = Some Server_CPU) \<and> (res\<^sub>c s\<^sub>c = UnSuccess \<or> 
         (\<exists>r. res\<^sub>c s\<^sub>c = Success r \<and> is_max r (log_bid\<^sub>c s\<^sub>c) \<and> snd r > reserve\<^sub>c s\<^sub>c \<and> status\<^sub>c s\<^sub>c = CLOSED))}"

primrec ev_el_map :: "EL \<Rightarrow> (EventLabel, Core, State\<^sub>a, Prog\<^sub>a) event"
  where "ev_el_map (Start_AuctionE qt) = Start_Auction\<^sub>a qt"
  | "ev_el_map Close_AuctionE = Close_Auction\<^sub>a"
  | "ev_el_map Publish_ResE = Publish_Res\<^sub>a"
  | "ev_el_map (Register_BidE uid qt) = Register_Bid\<^sub>a uid qt"

primrec ev_map :: "(EventLabel, Core, State\<^sub>c, Prog\<^sub>c) event \<Rightarrow> (EventLabel, Core, State\<^sub>a, Prog\<^sub>a) event"
  where "ev_map (AnonyEvent _) = AnonyEvent None"
  | "ev_map (BasicEvent e) = ev_el_map (fst (label e))"

lemma ev_map_start: "ev_map (Start_Auction\<^sub>c uid) = Start_Auction\<^sub>a uid"
  by (simp add: ev_map_def get_evt_label_def label_def Start_Auction\<^sub>c_def)

lemma ev_map_close: "ev_map Close_Auction\<^sub>c = Close_Auction\<^sub>a"
  by (simp add: ev_map_def get_evt_label_def label_def Close_Auction\<^sub>c_def)

lemma ev_map_publish: "ev_map Publish_Res\<^sub>c = Publish_Res\<^sub>a"
  by (simp add: ev_map_def get_evt_label_def label_def Publish_Res\<^sub>c_def)

lemma ev_map_register: "ev_map (Register_Bid\<^sub>c uid qt) = Register_Bid\<^sub>a uid qt"
  by (simp add: ev_map_def get_evt_label_def label_def Register_Bid\<^sub>c_def)

definition start_map :: "Auc_Id \<Rightarrow> State\<^sub>c com \<rightharpoonup> State\<^sub>a com"
  where "start_map qt = 
 [ATOMIC \<acute>res\<^sub>c := UnSuccess ;; \<acute>lock\<^sub>c := None ;; \<acute>status\<^sub>c := READY ;; \<acute>obs_st\<^sub>c := READY ;; \<acute>reserve\<^sub>c := qt END \<mapsto> 
  ATOMIC \<acute>res\<^sub>a := UnSuccess ;; \<acute>status\<^sub>a := READY ;; \<acute>reserve\<^sub>a := qt END]"

definition close_map :: "State\<^sub>c com \<rightharpoonup> State\<^sub>a com"
  where "close_map = [ATOMIC \<acute>status\<^sub>c := CLOSED ;; \<acute>obs_st\<^sub>c := CLOSED END \<mapsto> ATOMIC \<acute>status\<^sub>a := CLOSED END]"

definition publish_map :: "State\<^sub>c com \<rightharpoonup> State\<^sub>a com"
  where "publish_map = [\<acute>res\<^sub>c := Success \<acute>max_bid\<^sub>c  \<mapsto>
         ATOMIC IF snd \<acute>max_bid\<^sub>a > \<acute>reserve\<^sub>a THEN \<acute>res\<^sub>a := Success \<acute>max_bid\<^sub>a ELSE \<acute>res\<^sub>a := UnSuccess FI END, 
         \<acute>res\<^sub>c := UnSuccess \<mapsto>
         ATOMIC IF snd \<acute>max_bid\<^sub>a > \<acute>reserve\<^sub>a THEN \<acute>res\<^sub>a := Success \<acute>max_bid\<^sub>a ELSE \<acute>res\<^sub>a := UnSuccess FI END]"

definition register_map :: "Auc_Id \<Rightarrow> Auc_Qt \<Rightarrow> State\<^sub>c com \<rightharpoonup> State\<^sub>a com"
  where "register_map uid qt = [ATOMIC \<acute>lock\<^sub>c := None ;; \<acute>obs_log\<^sub>c := \<acute>log_bid\<^sub>c ;;
        \<acute>obs_max\<^sub>c := \<acute>max_bid\<^sub>c ;; \<acute>obs_st\<^sub>c := \<acute>status\<^sub>c END \<mapsto> 
        ATOMIC
        IF \<acute>status\<^sub>a = READY
        THEN
         \<acute>log_bid\<^sub>a := [(uid, qt)];;
         \<acute>max_bid\<^sub>a := (uid, qt) ;;
         \<acute>status\<^sub>a := RUNNING
        ELSE
         \<acute>log_bid\<^sub>a := \<acute>log_bid\<^sub>a @ [(uid, qt)] ;;
          IF qt > snd \<acute>max_bid\<^sub>a
          THEN
             \<acute>max_bid\<^sub>a := (uid, qt)
          FI
        FI
      END]"

primrec ev_el_prog_map :: "EL \<Rightarrow> State\<^sub>c com \<rightharpoonup> State\<^sub>a com"
  where "ev_el_prog_map (Start_AuctionE qt)  = start_map qt"
  | "ev_el_prog_map Close_AuctionE  = close_map"
  | "ev_el_prog_map Publish_ResE  = publish_map"
  | "ev_el_prog_map (Register_BidE uid qt)  = register_map uid qt"

primrec ev_prog_map :: "(EventLabel, Core, State\<^sub>c, Prog\<^sub>c) event \<Rightarrow> State\<^sub>c com option \<rightharpoonup> State\<^sub>a com option"
  where "ev_prog_map (AnonyEvent _) = Map.empty"
  | "ev_prog_map (BasicEvent e) = zetaI (ev_el_prog_map (fst (label e)))"

lemma ev_prog_map_start: "ev_prog_map (Start_Auction\<^sub>c qt) = zetaI (start_map qt)"
  by (simp add: ev_prog_map_def ev_el_prog_map_def get_evt_label_def label_def Start_Auction\<^sub>c_def)

lemma ev_prog_map_close: "ev_prog_map Close_Auction\<^sub>c = zetaI close_map"
  by (simp add: ev_prog_map_def ev_el_prog_map_def get_evt_label_def label_def Close_Auction\<^sub>c_def)

lemma ev_prog_map_publish: "ev_prog_map Publish_Res\<^sub>c = zetaI publish_map"
  by (simp add: ev_prog_map_def ev_el_prog_map_def get_evt_label_def label_def Publish_Res\<^sub>c_def)

lemma ev_prog_map_register: "ev_prog_map (Register_Bid\<^sub>c uid qt) = zetaI (register_map uid qt)"
  by (simp add: ev_prog_map_def ev_el_prog_map_def get_evt_label_def label_def Register_Bid\<^sub>c_def)

lemma Auction_dom_sim : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> state_inv; ev_map e\<^sub>c = e\<^sub>a \<rbrakk> \<Longrightarrow> domevt\<^sub>c s\<^sub>c e\<^sub>c = domevt\<^sub>a s\<^sub>a e\<^sub>a"
  apply (case_tac e\<^sub>c, simp add: ev_map_def)
  using domevt\<^sub>a_def domevt\<^sub>c_def apply force
  apply (case_tac x2, case_tac a, case_tac aa)
     apply (simp add: domevt\<^sub>a_def domevt\<^sub>c_def ev_map_def el_domevt\<^sub>a_def el_domevt\<^sub>c_def 
            ev_el_prog_map_def label_def state_inv_def Start_Auction\<^sub>a_def get_evt_label_def)
     apply auto[1]
     apply (simp add: domevt\<^sub>a_def domevt\<^sub>c_def ev_map_def el_domevt\<^sub>a_def el_domevt\<^sub>c_def 
            ev_el_prog_map_def label_def state_inv_def Close_Auction\<^sub>a_def get_evt_label_def)
    apply auto[1]
     apply (simp add: domevt\<^sub>a_def domevt\<^sub>c_def ev_map_def el_domevt\<^sub>a_def el_domevt\<^sub>c_def 
            ev_el_prog_map_def label_def state_inv_def Publish_Res\<^sub>a_def get_evt_label_def)
   apply auto[1]
     apply (simp add: domevt\<^sub>a_def domevt\<^sub>c_def ev_map_def el_domevt\<^sub>a_def el_domevt\<^sub>c_def 
            ev_el_prog_map_def label_def state_inv_def Register_Bid\<^sub>a_def get_evt_label_def)
  by auto

lemma Auction_sim_state_ifs : "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> state_inv; (t\<^sub>c, t\<^sub>a) \<in> state_inv\<rbrakk> \<Longrightarrow> s\<^sub>a \<sim>\<^sub>a d \<sim>\<^sub>a t\<^sub>a = s\<^sub>c \<sim>\<^sub>c d \<sim>\<^sub>c t\<^sub>c"
  apply (simp add: state_inv_def, case_tac d)
    apply (simp add: state_equiv\<^sub>a_def state_equiv\<^sub>c_def state_obs_user\<^sub>a_def state_obs_user\<^sub>c_def)
    apply (simp add:  state_equiv\<^sub>a_def state_equiv\<^sub>c_def state_obs_server\<^sub>a_def state_obs_server\<^sub>c_def)
    apply auto[1]
   apply (simp add: state_equiv\<^sub>a_def state_equiv\<^sub>c_def state_obs_pulisher\<^sub>a_def state_obs_pulisher\<^sub>c_def)
  by (simp add: state_equiv\<^sub>a_def state_equiv\<^sub>c_def)


subsection \<open>Rely-guarantee Proof of programs\<close>

(*
abbreviation "start\<^sub>c_rely \<equiv> \<lbrace>\<ordfeminine>status\<^sub>c = \<ordmasculine>status\<^sub>c \<and> \<rbrace>"
abbreviation "start\<^sub>c_guar \<equiv> \<lbrace>\<ordfeminine>max_bid\<^sub>c = \<ordmasculine>max_bid\<^sub>c \<and> \<ordfeminine>log_bid\<^sub>c = \<ordmasculine>log_bid\<^sub>c \<and>
                             \<ordfeminine>obs_log\<^sub>c = \<ordmasculine>obs_log\<^sub>c\<rbrace>"

abbreviation "start\<^sub>a_rely \<equiv> UNIV"
abbreviation "start\<^sub>a_guar \<equiv> UNIV"
*)

abbreviation "server\<^sub>c_rely \<equiv> \<lbrace>\<ordfeminine>reserve\<^sub>c = \<ordmasculine>reserve\<^sub>c \<and> \<ordfeminine>res\<^sub>c = \<ordmasculine>res\<^sub>c \<and> 
             (\<ordmasculine>status\<^sub>c = RUNNING \<longrightarrow> \<ordfeminine>status\<^sub>c = \<ordmasculine>status\<^sub>c) \<and>
             (\<ordmasculine>lock\<^sub>c = Some Server_CPU \<longrightarrow> 
             (\<ordfeminine>lock\<^sub>c = \<ordmasculine>lock\<^sub>c \<and> \<ordfeminine>status\<^sub>c = \<ordmasculine>status\<^sub>c \<and> \<ordfeminine>max_bid\<^sub>c = \<ordmasculine>max_bid\<^sub>c \<and> \<ordfeminine>log_bid\<^sub>c = \<ordmasculine>log_bid\<^sub>c \<and> 
              \<ordfeminine>obs_st\<^sub>c = \<ordmasculine>obs_st\<^sub>c \<and> \<ordfeminine>obs_max\<^sub>c = \<ordmasculine>obs_max\<^sub>c \<and> \<ordfeminine>obs_log\<^sub>c = \<ordmasculine>obs_log\<^sub>c))\<rbrace>"

abbreviation "server\<^sub>c_guar \<equiv> \<lbrace>\<ordmasculine>lock\<^sub>c \<noteq> Some Server_CPU \<longrightarrow> 
              (\<ordfeminine>lock\<^sub>c = \<ordmasculine>lock\<^sub>c \<and> \<ordfeminine>status\<^sub>c = \<ordmasculine>status\<^sub>c \<and> \<ordfeminine>max_bid\<^sub>c = \<ordmasculine>max_bid\<^sub>c \<and> \<ordfeminine>log_bid\<^sub>c = \<ordmasculine>log_bid\<^sub>c \<and> 
               \<ordfeminine>obs_st\<^sub>c = \<ordmasculine>obs_st\<^sub>c \<and> \<ordfeminine>obs_max\<^sub>c = \<ordmasculine>obs_max\<^sub>c \<and> \<ordfeminine>obs_log\<^sub>c = \<ordmasculine>obs_log\<^sub>c)\<rbrace> \<union> 
              {(s, s'). (lock\<^sub>c s) = None \<and> s' = s\<lparr>lock\<^sub>c := Some Server_CPU\<rparr>}"

abbreviation "server\<^sub>a_rely \<equiv> UNIV"
abbreviation "server\<^sub>a_guar \<equiv> UNIV"

abbreviation "start_pre \<equiv> state_inv \<inter> {(s\<^sub>c, s\<^sub>a). status\<^sub>c s\<^sub>c = CLOSED}"
abbreviation "start_post \<equiv> state_inv"

lemma start_awaitc : 
  "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> state_inv; status\<^sub>c s\<^sub>c = CLOSED\<rbrakk> \<Longrightarrow> 
  \<turnstile> Await UNIV (\<acute>res\<^sub>c := UnSuccess ;; \<acute>lock\<^sub>c := None ;; \<acute>status\<^sub>c := READY ;; \<acute>obs_st\<^sub>c := READY ;; 
     \<acute>reserve\<^sub>c := qt) sat [{s\<^sub>c}, Id, server\<^sub>c_guar, 
     {s\<^sub>c \<lparr>res\<^sub>c := UnSuccess, lock\<^sub>c := None, status\<^sub>c := READY, obs_st\<^sub>c := READY, reserve\<^sub>c := qt\<rparr>}]"
  apply (rule Await, simp_all add: stable_def, clarify)
  apply (case_tac "s\<^sub>c \<noteq> V")
   apply (rule Seq[where mid = "{}"])+
    apply (rule Basic, simp_all add: stable_def)+
  apply (rule Seq[where mid = "{s\<^sub>c\<lparr>res\<^sub>c := UnSuccess, lock\<^sub>c := None, status\<^sub>c := READY, obs_st\<^sub>c := READY\<rparr>}"])
   apply (rule Seq[where mid = "{s\<^sub>c\<lparr>res\<^sub>c := UnSuccess, lock\<^sub>c := None, status\<^sub>c := READY\<rparr>}"])
    apply (rule Seq[where mid = "{s\<^sub>c\<lparr>res\<^sub>c := UnSuccess, lock\<^sub>c := None\<rparr>}"])
     apply (rule Seq[where mid = "{s\<^sub>c\<lparr>res\<^sub>c := UnSuccess\<rparr>}"])
      apply (rule Basic, simp_all add: stable_def)+
  by (simp add: state_inv_def)

lemma start_awaita : 
  "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> state_inv; status\<^sub>c s\<^sub>c = CLOSED\<rbrakk> \<Longrightarrow> 
  \<turnstile> Await UNIV (\<acute>res\<^sub>a := UnSuccess ;; \<acute>status\<^sub>a := READY ;; \<acute>reserve\<^sub>a := qt) sat 
  [{s\<^sub>a}, Id, server\<^sub>a_guar, {s\<^sub>a \<lparr>res\<^sub>a := UnSuccess, status\<^sub>a := READY, reserve\<^sub>a := qt\<rparr>}]"
  apply (rule Await, simp_all add: stable_def, clarify)
  apply (case_tac "s\<^sub>a \<noteq> V")
   apply (rule Seq[where mid = "{}"])+
    apply (rule Basic, simp_all add: stable_def)+
  apply (rule Seq[where mid = "{s\<^sub>a\<lparr>res\<^sub>a := UnSuccess, status\<^sub>a := READY\<rparr>}"])
  apply (rule Seq[where mid = "{s\<^sub>a\<lparr>res\<^sub>a := UnSuccess\<rparr>}"])
  by (rule Basic, simp_all add: stable_def)+

lemma start_sim : "prog_sim_pre 
      (Some (ATOMIC \<acute>res\<^sub>c := UnSuccess ;; \<acute>lock\<^sub>c := None ;; \<acute>status\<^sub>c := READY ;; \<acute>obs_st\<^sub>c := READY ;; 
      \<acute>reserve\<^sub>c := qt END))
      server\<^sub>c_rely server\<^sub>c_guar
      state_inv (start_map qt) start_pre start_post
      (Some (ATOMIC \<acute>res\<^sub>a := UnSuccess ;; \<acute>status\<^sub>a := READY ;; \<acute>reserve\<^sub>a := qt END))
      server\<^sub>a_rely server\<^sub>a_guar"
  apply (rule Await_Await_Sound, simp add: rel_eq_def, simp add: start_map_def)
      apply (simp add: stable_alpha, simp)
    apply (simp add: Stable_def related_transitions_def state_inv_def)
  apply (smt (verit, best))
   apply (rule not_stuck_Seq)+
     apply (simp add: not_stuck_Basic)+
  apply clarsimp
  apply (rule_tac x = "{s\<^sub>c \<lparr>res\<^sub>c := UnSuccess, lock\<^sub>c := None, status\<^sub>c := READY, obs_st\<^sub>c := READY, reserve\<^sub>c := qt\<rparr>}" in exI)
  apply (rule conjI, simp add: start_awaitc)
  apply (rule_tac x = "{s\<^sub>a \<lparr>res\<^sub>a := UnSuccess, status\<^sub>a := READY, reserve\<^sub>a := qt\<rparr>}" in exI)
  apply (rule conjI, simp add: start_awaita)
  apply (simp add: state_inv_def)
  by auto

(*
abbreviation "close\<^sub>c_rely \<equiv> \<lbrace>\<ordfeminine>status\<^sub>c = \<ordmasculine>status\<^sub>c \<and> (\<ordmasculine>lock\<^sub>c = Some Server_CPU \<longrightarrow> \<ordfeminine>lock\<^sub>c  = \<ordmasculine>lock\<^sub>c)\<rbrace>"
abbreviation "close\<^sub>c_guar \<equiv> \<lbrace>\<ordfeminine>max_bid\<^sub>c = \<ordmasculine>max_bid\<^sub>c \<and> \<ordfeminine>log_bid\<^sub>c = \<ordmasculine>log_bid\<^sub>c \<and> \<ordfeminine>obs_log\<^sub>c = \<ordmasculine>obs_log\<^sub>c\<rbrace>"

abbreviation "close\<^sub>a_rely \<equiv> \<lbrace>\<ordfeminine>status\<^sub>a = \<ordmasculine>status\<^sub>a\<rbrace>"
abbreviation "close\<^sub>a_guar \<equiv> UNIV"
*)

abbreviation "close_pre \<equiv> state_inv"
abbreviation "close_post \<equiv> state_inv"

abbreviation "close_pre1 \<equiv> state_inv \<inter> {(s\<^sub>c, s\<^sub>a). status\<^sub>c s\<^sub>c \<noteq> CLOSED \<and> lock\<^sub>c s\<^sub>c = Some Server_CPU}"

lemma close_awaitc: "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> close_post; status\<^sub>c s\<^sub>c \<noteq> CLOSED; lock\<^sub>c s\<^sub>c = Some Server_CPU \<rbrakk> \<Longrightarrow> 
      \<turnstile> ATOMIC \<acute>status\<^sub>c := CLOSED;; \<acute>obs_st\<^sub>c := CLOSED END sat 
        [{s\<^sub>c}, Id, server\<^sub>c_guar, {s\<^sub>c\<lparr>status\<^sub>c := CLOSED, obs_st\<^sub>c := CLOSED\<rparr>}]"
  apply (rule Await, simp_all add: stable_def, clarsimp)
  apply (case_tac "s\<^sub>c \<noteq> V", simp)
   apply (rule Seq[where mid = "{}"])+
    apply (rule Basic, simp_all add: stable_def)+
  apply (rule Seq[where mid = "{s\<^sub>c\<lparr>status\<^sub>c := CLOSED\<rparr>}"])
  by (rule Basic, simp_all add: stable_def)+

lemma close_awaita: "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> close_post; status\<^sub>c s\<^sub>c \<noteq> CLOSED;  lock\<^sub>c s\<^sub>c = Some Server_CPU \<rbrakk> \<Longrightarrow> 
        \<turnstile> ATOMIC \<acute>status\<^sub>a := CLOSED END sat [{s\<^sub>a}, Id, server\<^sub>a_guar, {s\<^sub>a\<lparr>status\<^sub>a := CLOSED\<rparr>}]"
  apply (rule Await, simp_all add: stable_def, clarsimp)
  apply (case_tac "s\<^sub>a \<noteq> V")
  by (rule Basic, simp_all add: stable_def)+

lemma close_sim : "prog_sim_pre 
      (Some (AWAIT \<acute>lock\<^sub>c = None THEN \<acute>lock\<^sub>c := Some Server_CPU 
      END ;; ATOMIC \<acute>status\<^sub>c := CLOSED ;; \<acute>obs_st\<^sub>c := CLOSED END))
      server\<^sub>c_rely server\<^sub>c_guar
      state_inv close_map close_pre close_post
      (Some (ATOMIC \<acute>status\<^sub>a := CLOSED END))
      server\<^sub>a_rely server\<^sub>a_guar"
  apply (rule_tac \<zeta>\<^sub>1 = close_map and \<gamma>\<^sub>1 = close_pre1 in Seq_Skip_Sound, simp, simp add: close_map_def)
   apply (rule Await_None_Sound, simp, simp add: close_map_def)
      apply (simp add: Stable_def related_transitions_def state_inv_def)
      apply (smt (verit, best))
     apply (simp add: Stable_def related_transitions_def state_inv_def)
     apply (smt (verit, best))
    apply simp
   apply clarsimp
   apply (rule Await, simp add: stable_def, simp add: stable_def, clarsimp)
   apply (rule Basic, simp, simp add: state_inv_def)
     apply auto[1]
    apply (simp add: stable_def state_inv_def)
   apply (simp add: stable_def state_inv_def)
    apply auto[1]
   apply (simp add: stable_def state_inv_def)
   apply auto[1]
  apply (rule Await_Await_Sound, simp add: rel_eq_def)
       apply (simp add: close_map_def, simp add: stable_alpha, simp)
    apply (simp add: Stable_def state_inv_def related_transitions_def)
    apply (smt (verit, best))
   apply (simp add: not_stuck_Basic)
  apply clarify
  apply (rule_tac x = "{s\<^sub>c \<lparr>status\<^sub>c := CLOSED, obs_st\<^sub>c := CLOSED\<rparr>}" in exI)
  apply (rule_tac x = "{s\<^sub>a \<lparr>status\<^sub>a := CLOSED \<rparr>}" in exI)
  apply (rule conjI)
  using close_awaitc apply auto[1]
  apply (rule conjI)
  using close_awaita apply auto[1]
  apply (simp add: state_inv_def)
  by auto

(*
abbreviation "publish\<^sub>c_rely \<equiv> \<lbrace>\<ordfeminine>res\<^sub>c = \<ordmasculine>res\<^sub>c \<and> \<ordfeminine>status\<^sub>c = \<ordmasculine>status\<^sub>c \<and> \<ordfeminine>reserve\<^sub>c = \<ordmasculine>reserve\<^sub>c \<and>
              (\<ordmasculine>lock\<^sub>c = Some Server_CPU \<longrightarrow> (\<ordfeminine>lock\<^sub>c = \<ordmasculine>lock\<^sub>c \<and> \<ordfeminine>max_bid\<^sub>c = \<ordmasculine>max_bid\<^sub>c \<and> 
              \<ordfeminine>log_bid\<^sub>c = \<ordmasculine>log_bid\<^sub>c \<and> \<ordfeminine>obs_log\<^sub>c = \<ordmasculine>obs_log\<^sub>c))\<rbrace>"
abbreviation "publish\<^sub>c_guar \<equiv> \<lbrace>\<ordfeminine>max_bid\<^sub>c = \<ordmasculine>max_bid\<^sub>c \<and> \<ordfeminine>log_bid\<^sub>c = \<ordmasculine>log_bid\<^sub>c \<and> \<ordfeminine>obs_log\<^sub>c = \<ordmasculine>obs_log\<^sub>c \<and>
              \<ordfeminine>max_bid\<^sub>c = \<ordmasculine>max_bid\<^sub>c \<and> \<ordfeminine>log_bid\<^sub>c = \<ordmasculine>log_bid\<^sub>c \<and> \<ordfeminine>obs_log\<^sub>c = \<ordmasculine>obs_log\<^sub>c\<rbrace>"

abbreviation "publish\<^sub>a_rely \<equiv> \<lbrace>\<ordfeminine>status\<^sub>a = \<ordmasculine>status\<^sub>a \<and> \<ordfeminine>reserve\<^sub>a = \<ordmasculine>reserve\<^sub>a \<rbrace>"
abbreviation "publish\<^sub>a_guar \<equiv> UNIV"
*)

abbreviation "publish_pre \<equiv> state_inv \<inter> {(s\<^sub>c, s\<^sub>a). status\<^sub>c s\<^sub>c = CLOSED}"
abbreviation "publish_post \<equiv> state_inv"

lemma publish_sim : "prog_sim_pre 
      (Some (IF snd \<acute>max_bid\<^sub>c > \<acute>reserve\<^sub>c THEN \<acute>res\<^sub>c := Success \<acute>max_bid\<^sub>c  ELSE \<acute>res\<^sub>c := UnSuccess
      FI))
      server\<^sub>c_rely server\<^sub>c_guar
      state_inv publish_map publish_pre publish_post
      (Some (ATOMIC IF snd \<acute>max_bid\<^sub>a > \<acute>reserve\<^sub>a THEN \<acute>res\<^sub>a := Success \<acute>max_bid\<^sub>a ELSE \<acute>res\<^sub>a := UnSuccess FI  END))
      server\<^sub>a_rely server\<^sub>a_guar"
  apply (rule If_Comm_Branch_Sound, simp, simp add: publish_map_def, simp_all)
     apply (simp add: Stable_def related_transitions_def state_inv_def)
     apply (smt (verit, best))
    apply (rule Basic_Await_Sound)
           apply force
          apply (simp add: Stable_def related_transitions_def state_inv_def)
          apply (smt (verit, best))
         apply (simp add: publish_map_def, simp add: stable_alpha, simp)
      apply (rule not_stuck_If)
       apply (rule not_stuck_Basic)+
     apply auto[1]
    apply (clarsimp, rule Await, simp add: stable_def, simp add: stable_def)
    apply (clarsimp, rule Cond, simp add: stable_def)
       apply auto[1]
      apply (rule Basic, simp_all)
       apply (simp add: state_inv_def, clarify)
       apply (metis prod.collapse)
      apply (simp add: stable_def)
      apply force
     apply (simp add: stable_def)
    apply (rule Basic)
  apply (smt (z3) ComplD IntE mem_Collect_eq prod.simps(2) state_inv_def subsetI)
      apply auto[1]
     apply (simp add: stable_def)
     apply blast
    apply (simp add: stable_def)
   apply (rule Basic_Await_Sound)
  apply force
         apply (simp add: Stable_def related_transitions_def state_inv_def)
         apply (smt (verit, best))
        apply (simp add: publish_map_def, simp add: stable_alpha, simp)
     apply (rule not_stuck_If)
      apply (rule not_stuck_Basic)+
    apply auto[1]
   apply (clarsimp, rule Await, simp add: stable_def, simp add: stable_def)
   apply (clarsimp, rule Cond, simp add: stable_def)
      apply auto[1]
     apply (rule Basic, simp_all)
  apply (simp add: state_inv_def)
      apply fastforce
     apply (simp add: stable_def)
     apply blast
    apply (simp add: stable_def)
   apply (rule Basic, simp_all)
     apply (simp add: state_inv_def)
     apply auto[1]
    apply (simp add: stable_def)
    apply auto[1]
   apply (simp add: stable_def)
  by auto

abbreviation "register\<^sub>c_rely uid \<equiv> \<lbrace>\<ordmasculine>lock\<^sub>c = Some (User_CPU uid) \<longrightarrow> 
              (\<ordfeminine>lock\<^sub>c = \<ordmasculine>lock\<^sub>c \<and> \<ordfeminine>status\<^sub>c = \<ordmasculine>status\<^sub>c \<and> \<ordfeminine>max_bid\<^sub>c = \<ordmasculine>max_bid\<^sub>c \<and> \<ordfeminine>log_bid\<^sub>c = \<ordmasculine>log_bid\<^sub>c \<and>
               \<ordfeminine>obs_st\<^sub>c = \<ordmasculine>obs_st\<^sub>c \<and> \<ordfeminine>obs_max\<^sub>c = \<ordmasculine>obs_max\<^sub>c \<and> \<ordfeminine>obs_log\<^sub>c = \<ordmasculine>obs_log\<^sub>c)\<rbrace>"

abbreviation "register\<^sub>c_guar uid \<equiv> \<lbrace>\<ordfeminine>res\<^sub>c = \<ordmasculine>res\<^sub>c \<and> \<ordfeminine>reserve\<^sub>c = \<ordmasculine>reserve\<^sub>c \<and> 
              (\<ordmasculine>status\<^sub>c = RUNNING \<longrightarrow> \<ordfeminine>status\<^sub>c = \<ordmasculine>status\<^sub>c) \<and>
              (\<ordmasculine>lock\<^sub>c \<noteq> Some (User_CPU uid) \<longrightarrow> 
              (\<ordfeminine>lock\<^sub>c = \<ordmasculine>lock\<^sub>c \<and> \<ordfeminine>status\<^sub>c = \<ordmasculine>status\<^sub>c \<and> \<ordfeminine>max_bid\<^sub>c = \<ordmasculine>max_bid\<^sub>c \<and> \<ordfeminine>log_bid\<^sub>c = \<ordmasculine>log_bid\<^sub>c \<and>
               \<ordfeminine>obs_st\<^sub>c = \<ordmasculine>obs_st\<^sub>c \<and> \<ordfeminine>obs_max\<^sub>c = \<ordmasculine>obs_max\<^sub>c \<and> \<ordfeminine>obs_log\<^sub>c = \<ordmasculine>obs_log\<^sub>c))\<rbrace> \<union>
              {(s, s'). (lock\<^sub>c s) = None \<and> s' = s \<lparr>lock\<^sub>c := Some (User_CPU uid)\<rparr>}"

abbreviation "register\<^sub>a_rely \<equiv> UNIV"
abbreviation "register\<^sub>a_guar \<equiv> UNIV"

abbreviation "register_pre \<equiv> state_inv"
abbreviation "register_post \<equiv> state_inv"

abbreviation "register_mid1 uid qt \<equiv> state_inv \<inter> {(s\<^sub>c, s\<^sub>a). lock\<^sub>c s\<^sub>c = Some (User_CPU uid) \<and> 
  (obs_st\<^sub>c s\<^sub>c = READY \<longrightarrow> (max_bid\<^sub>c s\<^sub>c = (uid, qt) \<and> log_bid\<^sub>c s\<^sub>c = [(uid, qt)] \<and> status\<^sub>c s\<^sub>c = RUNNING)) \<and> 
  (obs_st\<^sub>c s\<^sub>c \<noteq> READY \<longrightarrow> (log_bid\<^sub>c s\<^sub>c = (obs_log\<^sub>c s\<^sub>c) @ [(uid, qt)] \<and> status\<^sub>c s\<^sub>c = obs_st\<^sub>c s\<^sub>c \<and> 
  (qt > snd (obs_max\<^sub>c s\<^sub>c) \<longrightarrow>  max_bid\<^sub>c s\<^sub>c = (uid, qt)) \<and> (qt \<le> snd (obs_max\<^sub>c s\<^sub>c) \<longrightarrow>  max_bid\<^sub>c s\<^sub>c = obs_max\<^sub>c s\<^sub>c)))}"

abbreviation "register_mid2 uid \<equiv> state_inv \<inter> {(s\<^sub>c, s\<^sub>a). lock\<^sub>c s\<^sub>c = Some (User_CPU uid) \<and> 
              obs_st\<^sub>c s\<^sub>c = status\<^sub>c s\<^sub>c \<and> obs_log\<^sub>c s\<^sub>c = log_bid\<^sub>c s\<^sub>c \<and> obs_max\<^sub>c s\<^sub>c = max_bid\<^sub>c s\<^sub>c}"

lemma registera_not_stuck: "not_stuck UNIV (IF \<acute>status\<^sub>a = READY THEN
      \<acute>log_bid\<^sub>a := [(uid, qt)];; \<acute>max_bid\<^sub>a := (uid, qt) ;;\<acute>status\<^sub>a := RUNNING
       ELSE \<acute>log_bid\<^sub>a := \<acute>log_bid\<^sub>a @ [(uid, qt)] ;; IF qt > snd \<acute>max_bid\<^sub>a THEN
       \<acute>max_bid\<^sub>a := (uid, qt) FI FI)"
  apply (rule not_stuck_If)
   apply (rule not_stuck_Seq)+
     apply (rule not_stuck_Basic)+
  apply (rule not_stuck_Seq, rule not_stuck_Basic)
  apply (rule not_stuck_If, rule not_stuck_Basic)
  by (simp add: Skip_def, rule not_stuck_Basic)

lemma register_sim_none1: "prog_sim_pre
      (Some (AWAIT \<acute>lock\<^sub>c = None THEN \<acute>lock\<^sub>c := Some (User_CPU uid) END))
      (register\<^sub>c_rely uid) (register\<^sub>c_guar uid) state_inv Map.empty register_pre (register_mid2 uid)
      None register\<^sub>a_rely register\<^sub>a_guar"
  apply (rule Await_None_Sound)
       apply simp+
  apply (simp add: stable_alpha)
    apply (simp add: Stable_def state_inv_def related_transitions_def)
  apply (smt (verit, best))
   apply simp
  apply clarsimp
  apply (rule Await)
    apply (simp add: stable_def)+
  apply (clarsimp, rule Basic, clarsimp)
     apply (simp add: state_inv_def)
     apply auto[1]
    apply (simp add: stable_def)+
   apply auto[1]
  apply (simp add: stable_def)
  by auto

lemma register_sim_none2_branch1: "prog_sim_pre 
      (Some (\<acute>max_bid\<^sub>c := (uid, qt);; \<acute>log_bid\<^sub>c := [(uid, qt)];; \<acute>status\<^sub>c := RUNNING))
      (register\<^sub>c_rely uid) (register\<^sub>c_guar uid) state_inv Map.empty 
      ((register_mid2 uid) \<inter> {(s\<^sub>c, s\<^sub>a). s\<^sub>c \<in> \<lbrace>\<acute>status\<^sub>c = READY\<rbrace>}) (register_mid1 uid qt)
      None register\<^sub>a_rely register\<^sub>a_guar"
  apply (rule_tac \<zeta>\<^sub>1 = Map.empty and \<gamma>\<^sub>1 = "state_inv \<inter> {(s\<^sub>c, s\<^sub>a). lock\<^sub>c s\<^sub>c = Some (User_CPU uid) 
  \<and> obs_st\<^sub>c s\<^sub>c = READY \<and>  max_bid\<^sub>c s\<^sub>c = (uid, qt) \<and> log_bid\<^sub>c s\<^sub>c = [(uid, qt)]}" in Seq_Skip_Sound)
     apply auto[1]
    apply simp
   apply (rule_tac \<zeta>\<^sub>1 = Map.empty and \<gamma>\<^sub>1 = "state_inv \<inter> {(s\<^sub>c, s\<^sub>a). lock\<^sub>c s\<^sub>c = Some (User_CPU uid)
         \<and> obs_st\<^sub>c s\<^sub>c = READY \<and> max_bid\<^sub>c s\<^sub>c = (uid, qt)}" in Seq_Skip_Sound)
      apply auto[1]
     apply simp
    apply (rule Basic_None_Sound)
         apply auto
      apply (simp add: Stable_def state_inv_def related_transitions_def)
      apply (smt (verit, best))
     apply (simp add: Stable_def state_inv_def related_transitions_def)
     apply (smt (verit, best))
    apply (simp add: state_inv_def)
    apply auto[1]
   apply (rule Basic_None_Sound, simp, simp)
      apply (simp add: Stable_def state_inv_def related_transitions_def)
      apply (smt (verit, best))
     apply (simp add: Stable_def state_inv_def related_transitions_def)
    apply (smt (verit, best))
    apply (simp add: state_inv_def)
    apply auto[1]
   apply simp
  apply (rule Basic_None_Sound, simp, simp)
     apply (simp add: Stable_def state_inv_def related_transitions_def)
  apply (smt (verit, best))
    apply (simp add: Stable_def state_inv_def related_transitions_def)
    apply (smt (verit, best))
   apply (simp add: state_inv_def)
  by auto

lemma register_sim_none2_branch2: "prog_sim_pre 
      (Some (\<acute>log_bid\<^sub>c := \<acute>log_bid\<^sub>c @ [(uid, qt)];; IF snd \<acute>max_bid\<^sub>c < qt THEN \<acute>max_bid\<^sub>c :=
       (uid, qt) FI))
      (register\<^sub>c_rely uid) (register\<^sub>c_guar uid) state_inv Map.empty 
      ((register_mid2 uid) \<inter> {(s\<^sub>c, s\<^sub>a). s\<^sub>c \<notin> \<lbrace>\<acute>status\<^sub>c = READY\<rbrace>}) (register_mid1 uid qt)
      None register\<^sub>a_rely register\<^sub>a_guar"
  apply (rule_tac \<zeta>\<^sub>1 = Map.empty and \<gamma>\<^sub>1 = "state_inv \<inter> {(s\<^sub>c, s\<^sub>a). lock\<^sub>c s\<^sub>c = Some (User_CPU uid) \<and> 
   obs_st\<^sub>c s\<^sub>c = status\<^sub>c s\<^sub>c  \<and> obs_max\<^sub>c s\<^sub>c = max_bid\<^sub>c s\<^sub>c \<and>
   obs_st\<^sub>c s\<^sub>c \<noteq> READY \<and> log_bid\<^sub>c s\<^sub>c = (obs_log\<^sub>c s\<^sub>c) @ [(uid, qt)]}" in Seq_Skip_Sound)
     apply auto[1]
    apply simp
   apply (rule Basic_None_Sound, simp)
        apply auto[1]
       apply simp
      apply (simp add: Stable_def state_inv_def related_transitions_def)
      apply (smt (verit, best))
     apply (simp add: Stable_def state_inv_def related_transitions_def)
     apply (smt (verit, best))
    apply (simp add: state_inv_def)
    apply auto[1]
  apply simp
  apply (rule If_Comm_Branch_Sound, simp_all)
     apply (simp add: Stable_def state_inv_def related_transitions_def)
     apply (smt (verit, best))
    apply (rule Basic_None_Sound)
         apply auto[1]
        apply auto[1]
       apply (simp add: Stable_def state_inv_def related_transitions_def)
       apply (smt (verit, best))
      apply (simp add: Stable_def state_inv_def related_transitions_def)
      apply (smt (verit, best))
     apply (simp add: state_inv_def, clarsimp)
    apply auto[1]
   apply (simp add: Skip_def, rule Basic_None_Sound)
        apply auto
   apply (simp add: Stable_def state_inv_def related_transitions_def)
   apply (smt (verit, best))
  apply (simp add: Stable_def state_inv_def related_transitions_def)
  by (smt (verit, best))

lemma register_sim_none2: "prog_sim_pre
      (Some (IF \<acute>status\<^sub>c = READY THEN \<acute>max_bid\<^sub>c := (uid, qt);; \<acute>log_bid\<^sub>c := [(uid, qt)];; \<acute>status\<^sub>c := RUNNING
       ELSE \<acute>log_bid\<^sub>c := \<acute>log_bid\<^sub>c @ [(uid, qt)];; IF snd \<acute>max_bid\<^sub>c < qt THEN \<acute>max_bid\<^sub>c := (uid, qt) FI
       FI))
      (register\<^sub>c_rely uid) (register\<^sub>c_guar uid) state_inv Map.empty (register_mid2 uid) (register_mid1 uid qt)
      None register\<^sub>a_rely register\<^sub>a_guar"
  apply (rule If_Comm_Branch_Sound, simp_all)
  apply (simp add: Stable_def state_inv_def related_transitions_def)
     apply (smt (verit, best))
  using register_sim_none2_branch1 apply auto[1]
  using register_sim_none2_branch2 apply auto[1]
  by force

lemma not_stuck_unlock: " not_stuck \<lbrace>True\<rbrace>
     (IF \<acute>status\<^sub>a = READY THEN \<acute>log_bid\<^sub>a := [(uid, qt)];; \<acute>max_bid\<^sub>a := (uid, qt);; \<acute>status\<^sub>a := RUNNING
      ELSE \<acute>log_bid\<^sub>a := \<acute>log_bid\<^sub>a @ [(uid, qt)];; IF snd \<acute>max_bid\<^sub>a < qt THEN \<acute>max_bid\<^sub>a := (uid, qt) FI FI)"
   apply (rule not_stuck_If)
    apply (rule not_stuck_Seq)+
  apply (simp add: not_stuck_Basic)+
   apply (rule not_stuck_Seq, simp add: not_stuck_Basic)
  by (rule not_stuck_If, simp_all add: Skip_def not_stuck_Basic)

lemma register_unlock_awaitc: "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> register_post; lock\<^sub>c s\<^sub>c = Some (User_CPU uid);
       obs_st\<^sub>c s\<^sub>c = READY \<longrightarrow> max_bid\<^sub>c s\<^sub>c = (uid, qt) \<and> log_bid\<^sub>c s\<^sub>c = [(uid, qt)] \<and> status\<^sub>c s\<^sub>c = RUNNING;
       obs_st\<^sub>c s\<^sub>c \<noteq> READY \<longrightarrow> log_bid\<^sub>c s\<^sub>c = obs_log\<^sub>c s\<^sub>c @ [(uid, qt)] \<and>  status\<^sub>c s\<^sub>c = obs_st\<^sub>c s\<^sub>c \<and> 
      (snd (obs_max\<^sub>c s\<^sub>c) < qt \<longrightarrow> max_bid\<^sub>c s\<^sub>c = (uid, qt)) \<and> (qt \<le> snd (obs_max\<^sub>c s\<^sub>c) \<longrightarrow> max_bid\<^sub>c s\<^sub>c = obs_max\<^sub>c s\<^sub>c)\<rbrakk> 
       \<Longrightarrow> \<turnstile> ATOMIC \<acute>lock\<^sub>c := None;; \<acute>obs_log\<^sub>c := \<acute>log_bid\<^sub>c;; \<acute>obs_max\<^sub>c := \<acute>max_bid\<^sub>c;;
      \<acute>obs_st\<^sub>c := \<acute>status\<^sub>c END sat [{s\<^sub>c}, Id, register\<^sub>c_guar uid, 
      {s\<^sub>c\<lparr>lock\<^sub>c := None, obs_log\<^sub>c := log_bid\<^sub>c s\<^sub>c, obs_max\<^sub>c := max_bid\<^sub>c s\<^sub>c, obs_st\<^sub>c := status\<^sub>c s\<^sub>c\<rparr>}]"
  apply (rule Await, simp add: stable_def, simp add: stable_def, clarify)
  apply (case_tac "s\<^sub>c \<noteq> V", simp)
   apply (rule Seq[where mid = "{}"])+
      apply (rule Basic, simp_all add: stable_def)+
   apply (smt (verit, best))
  apply (rule Seq[where mid = "{s\<^sub>c\<lparr>lock\<^sub>c := None, obs_log\<^sub>c := log_bid\<^sub>c s\<^sub>c, obs_max\<^sub>c := max_bid\<^sub>c s\<^sub>c\<rparr>}"])
   apply (rule Seq[where mid = "{s\<^sub>c\<lparr>lock\<^sub>c := None, obs_log\<^sub>c := log_bid\<^sub>c s\<^sub>c\<rparr>}"])
    apply (rule Seq[where mid = "{s\<^sub>c\<lparr>lock\<^sub>c := None\<rparr>}"])
  by (rule Basic, simp_all add: stable_def)+

abbreviation "register_posta uid qt s\<^sub>a \<equiv> {s. status\<^sub>a s\<^sub>a = READY \<and> s = s\<^sub>a\<lparr>log_bid\<^sub>a := [(uid, qt)], max_bid\<^sub>a := (uid, qt), status\<^sub>a := RUNNING\<rparr>} \<union> 
                       {s. status\<^sub>a s\<^sub>a \<noteq> READY \<and> snd (max_bid\<^sub>a s\<^sub>a) < qt \<and> 
                        s = s\<^sub>a\<lparr>log_bid\<^sub>a := (log_bid\<^sub>a s\<^sub>a) @ [(uid, qt)], max_bid\<^sub>a := (uid, qt)\<rparr>} \<union> 
                       {s. status\<^sub>a s\<^sub>a \<noteq> READY \<and> snd (max_bid\<^sub>a s\<^sub>a) \<ge> qt \<and> 
                        s = s\<^sub>a\<lparr>log_bid\<^sub>a := (log_bid\<^sub>a s\<^sub>a) @ [(uid, qt)]\<rparr>}"

lemma register_unlock_awaita: "\<lbrakk>(s\<^sub>c, s\<^sub>a) \<in> register_post; lock\<^sub>c s\<^sub>c = Some (User_CPU uid);
       obs_st\<^sub>c s\<^sub>c = READY \<longrightarrow> max_bid\<^sub>c s\<^sub>c = (uid, qt) \<and> log_bid\<^sub>c s\<^sub>c = [(uid, qt)] \<and> status\<^sub>c s\<^sub>c = RUNNING;
       obs_st\<^sub>c s\<^sub>c \<noteq> READY \<longrightarrow> log_bid\<^sub>c s\<^sub>c = obs_log\<^sub>c s\<^sub>c @ [(uid, qt)] \<and>  status\<^sub>c s\<^sub>c = obs_st\<^sub>c s\<^sub>c \<and> 
      (snd (obs_max\<^sub>c s\<^sub>c) < qt \<longrightarrow> max_bid\<^sub>c s\<^sub>c = (uid, qt)) \<and> (qt \<le> snd (obs_max\<^sub>c s\<^sub>c) \<longrightarrow> max_bid\<^sub>c s\<^sub>c = obs_max\<^sub>c s\<^sub>c)\<rbrakk>
       \<Longrightarrow> \<turnstile> ATOMIC IF \<acute>status\<^sub>a = READY THEN \<acute>log_bid\<^sub>a := [(uid, qt)];; \<acute>max_bid\<^sub>a := (uid, qt);; \<acute>status\<^sub>a := RUNNING
                 ELSE \<acute>log_bid\<^sub>a := \<acute>log_bid\<^sub>a @ [(uid, qt)];; IF snd \<acute>max_bid\<^sub>a < qt THEN \<acute>max_bid\<^sub>a := (uid, qt) FI
                 FI END  sat [{s\<^sub>a}, Id, register\<^sub>a_guar, register_posta uid qt s\<^sub>a]"
  apply (rule Await, simp add: stable_def, simp add: stable_def, clarify)
  apply (case_tac "s\<^sub>a \<noteq> V", simp)
  apply (rule Cond, simp add: stable_def)
     apply (rule Seq[where mid = "{}"])+
       apply (rule Basic, simp_all add: stable_def)+
   apply (rule Seq[where mid = "{}"])
    apply (rule Basic, simp_all add: stable_def)
   apply (rule Cond, simp add: stable_def)
     apply (rule Basic, simp_all add: stable_def)
   apply (simp add: Skip_def, rule Basic, simp_all add: stable_def)
  apply (rule Cond, simp add: stable_def)
    apply (rule Seq[where mid = "{s. status\<^sub>a s\<^sub>a = READY \<and> s = s\<^sub>a\<lparr>log_bid\<^sub>a := [(uid, qt)], max_bid\<^sub>a := (uid, qt)\<rparr>}"])
     apply (rule Seq[where mid = "{s. status\<^sub>a s\<^sub>a = READY \<and> s = s\<^sub>a\<lparr>log_bid\<^sub>a := [(uid, qt)]\<rparr>}"])
      apply (rule Basic, simp_all add: stable_def)+
     apply auto[1]
    apply (rule Basic, simp_all add: stable_def)
    apply auto[1]
   apply (rule Basic, simp_all add: stable_def)
   apply auto[1]
  apply (rule Seq[where mid = "{s. status\<^sub>a s\<^sub>a \<noteq> READY \<and> s = s\<^sub>a\<lparr>log_bid\<^sub>a := (log_bid\<^sub>a s\<^sub>a) @ [(uid, qt)]\<rparr>}"])
   apply (rule Basic, simp_all add: stable_def)
   apply auto[1]
  apply (rule Cond, simp add: stable_def)
    apply (rule Basic, simp_all add: stable_def)
   apply auto[1]
  apply (simp add: Skip_def, rule Basic, simp_all add: stable_def)
  by auto

lemma register_sim_unlock: "prog_sim_pre
      (Some (ATOMIC \<acute>lock\<^sub>c := None;; \<acute>obs_log\<^sub>c := \<acute>log_bid\<^sub>c;; \<acute>obs_max\<^sub>c := \<acute>max_bid\<^sub>c;; \<acute>obs_st\<^sub>c := \<acute>status\<^sub>c END))
      (register\<^sub>c_rely uid) (register\<^sub>c_guar uid) state_inv (register_map uid qt) (register_mid1 uid qt) state_inv
      (Some (ATOMIC
        IF \<acute>status\<^sub>a = READY
        THEN
         \<acute>log_bid\<^sub>a := [(uid, qt)];;
         \<acute>max_bid\<^sub>a := (uid, qt) ;;
         \<acute>status\<^sub>a := RUNNING
        ELSE
         \<acute>log_bid\<^sub>a := \<acute>log_bid\<^sub>a @ [(uid, qt)] ;;
          IF qt > snd \<acute>max_bid\<^sub>a
          THEN
             \<acute>max_bid\<^sub>a := (uid, qt)
          FI
        FI
      END))
      register\<^sub>a_rely register\<^sub>a_guar"
  apply (rule Await_Await_Sound, simp add: rel_eq_def, simp add: register_map_def)
      apply (simp add: stable_alpha, simp)
    apply (simp add: Stable_def state_inv_def related_transitions_def)
    apply (smt (verit, best))
   apply (simp add: registera_not_stuck, clarify)
  apply (rule_tac x = "{s\<^sub>c\<lparr>lock\<^sub>c := None, obs_log\<^sub>c := log_bid\<^sub>c s\<^sub>c, obs_max\<^sub>c := max_bid\<^sub>c s\<^sub>c, 
         obs_st\<^sub>c := status\<^sub>c s\<^sub>c\<rparr>}" in exI)
  apply (rule_tac x = "register_posta uid qt s\<^sub>a" in exI)
  apply (rule conjI)
  using register_unlock_awaitc apply auto[1]
  apply (rule conjI)
  using register_unlock_awaita apply auto[1]
  apply (simp add: state_inv_def, clarsimp)
  apply (intro conjI)
  using is_max_def apply force
   apply (metis is_max_add_max prod.collapse)
  by (metis is_max_add_not_max prod.collapse)

lemma register_sim : "prog_sim_pre 
      (Some (AWAIT \<acute>lock\<^sub>c = None THEN 
        \<acute>lock\<^sub>c := Some (User_CPU uid) 
      END ;;
      IF \<acute>status\<^sub>c = READY
      THEN
         \<acute>max_bid\<^sub>c := (uid, qt) ;;
         \<acute>log_bid\<^sub>c := [(uid, qt)];;
         \<acute>status\<^sub>c := RUNNING
      ELSE
         \<acute>log_bid\<^sub>c := \<acute>log_bid\<^sub>c @ [(uid, qt)] ;;
          IF qt > snd \<acute>max_bid\<^sub>c
          THEN
             \<acute>max_bid\<^sub>c := (uid, qt)
          FI
      FI ;;
      ATOMIC
        \<acute>lock\<^sub>c := None ;;
        \<acute>obs_log\<^sub>c := \<acute>log_bid\<^sub>c ;;
        \<acute>obs_max\<^sub>c := \<acute>max_bid\<^sub>c ;;
        \<acute>obs_st\<^sub>c := \<acute>status\<^sub>c
      END))
      (register\<^sub>c_rely uid) (register\<^sub>c_guar uid)
      state_inv (register_map uid qt) register_pre register_post
      (Some (ATOMIC
        IF \<acute>status\<^sub>a = READY
        THEN
         \<acute>log_bid\<^sub>a := [(uid, qt)];;
         \<acute>max_bid\<^sub>a := (uid, qt) ;;
         \<acute>status\<^sub>a := RUNNING
        ELSE
         \<acute>log_bid\<^sub>a := \<acute>log_bid\<^sub>a @ [(uid, qt)] ;;
          IF qt > snd \<acute>max_bid\<^sub>a
          THEN
             \<acute>max_bid\<^sub>a := (uid, qt)
          FI
        FI
      END))
      register\<^sub>a_rely register\<^sub>a_guar"
  apply (rule_tac \<zeta>\<^sub>1 = Map.empty and \<gamma>\<^sub>1 = "register_mid1 uid qt" in Seq_Skip_Sound)
     apply (simp add: register_map_def, simp add: register_map_def)
   apply (rule_tac \<zeta>\<^sub>1 = Map.empty and \<gamma>\<^sub>1 = "register_mid2 uid" in Seq_Skip_Sound)
      apply simp+
  using register_sim_none1 apply auto[1]
  using register_sim_none2 apply auto[1]
  using register_sim_unlock[of uid qt] by auto

subsection \<open>Rely-guarantee Proof for event systems\<close>

lemma init_sat_inv: "(s0\<^sub>c, s0\<^sub>a) \<in> state_inv"
  by (simp add: state_inv_def is_max_def)


primrec evtsys_rely\<^sub>c :: "Core \<Rightarrow> (State\<^sub>c \<times> State\<^sub>c) set"
  where "evtsys_rely\<^sub>c (User_CPU uid) = (register\<^sub>c_rely uid)"
  | "evtsys_rely\<^sub>c Server_CPU = server\<^sub>c_rely"

primrec evtsys_guar\<^sub>c :: "Core \<Rightarrow> (State\<^sub>c \<times> State\<^sub>c) set"
  where "evtsys_guar\<^sub>c (User_CPU uid) = (register\<^sub>c_guar uid)"
  | "evtsys_guar\<^sub>c Server_CPU = server\<^sub>c_guar"

abbreviation "evtsys_rely\<^sub>a k \<equiv> UNIV"
abbreviation "evtsys_guar\<^sub>a k \<equiv> UNIV"

lemma evtsys_rely_guar_compat: "i \<noteq> j \<Longrightarrow> evtsys_guar\<^sub>c i \<subseteq> evtsys_rely\<^sub>c j"
  apply (case_tac i, case_tac j)
    apply auto[1]
   apply auto[1]
  apply (case_tac j)
  by auto

lemma start_e_sim: "(s\<^sub>c, s\<^sub>a) \<in> state_inv \<Longrightarrow> e_sim 
        \<Gamma>\<^sub>c (Start_Auction\<^sub>c qt, s\<^sub>c, x\<^sub>c) server\<^sub>c_rely server\<^sub>c_guar
        state_inv (zetaI (start_map qt)) state_inv 
        \<Gamma>\<^sub>a (Start_Auction\<^sub>a qt, s\<^sub>a, x\<^sub>a) UNIV UNIV"
  apply (simp add: Start_Auction\<^sub>c_def Start_Auction\<^sub>a_def)
  apply (rule_tac \<xi> = "state_inv" in PiCore_SIMP_Refine.BasicEvt_Rule')
       apply (simp add: state_inv_def rel_guard_eq_def)
       apply (smt (verit) Auc_Status.exhaust Collect_mono case_prodD split_cong)
      apply (simp, simp add: stable_e_alpha, simp, simp)
  apply clarsimp
  apply (rule_tac \<zeta> = "start_map qt" in sim_implies_simI)
   apply (rule_tac \<xi> = "start_pre" in prog_sim_pre_implies_sim)
  using start_sim apply auto[1]
   apply (simp add: state_inv_def rel_guard_and_def)
   apply metis
  by auto

lemma close_e_sim: "(s\<^sub>c, s\<^sub>a) \<in> state_inv \<Longrightarrow> e_sim 
        \<Gamma>\<^sub>c (Close_Auction\<^sub>c, s\<^sub>c, x\<^sub>c) server\<^sub>c_rely server\<^sub>c_guar
        state_inv (zetaI close_map) state_inv 
        \<Gamma>\<^sub>a (Close_Auction\<^sub>a, s\<^sub>a, x\<^sub>a) UNIV UNIV"
  apply (simp add: Close_Auction\<^sub>c_def Close_Auction\<^sub>a_def)
  apply (rule_tac \<xi> = "state_inv" in PiCore_SIMP_Refine.BasicEvt_Rule')
       apply (simp add: state_inv_def rel_guard_eq_def)
       apply fastforce
      apply simp
     apply (simp, simp add: stable_e_alpha, simp, simp)
  apply clarsimp
  apply (rule_tac \<zeta> = "close_map" in sim_implies_simI)
   apply (rule_tac \<xi> = "close_pre" in prog_sim_pre_implies_sim)
  using close_sim apply auto[1]
   apply (simp add: state_inv_def rel_guard_and_def)
   apply metis
  by auto

lemma publish_e_sim: "(s\<^sub>c, s\<^sub>a) \<in> state_inv \<Longrightarrow> e_sim 
        \<Gamma>\<^sub>c (Publish_Res\<^sub>c, s\<^sub>c, x\<^sub>c) server\<^sub>c_rely server\<^sub>c_guar
        state_inv (zetaI publish_map) state_inv 
        \<Gamma>\<^sub>a (Publish_Res\<^sub>a, s\<^sub>a, x\<^sub>a) UNIV UNIV"
  apply (simp add: Publish_Res\<^sub>c_def Publish_Res\<^sub>a_def)
  apply (rule_tac \<xi> = "state_inv" in PiCore_SIMP_Refine.BasicEvt_Rule')
       apply (simp add: state_inv_def rel_guard_eq_def)
       apply (smt (verit) Auc_Status.exhaust Collect_mono case_prodD split_cong)
      apply (simp, simp add: stable_e_alpha, simp, simp)
  apply clarsimp
  apply (rule_tac \<zeta> = "publish_map" in sim_implies_simI)
   apply (rule_tac \<xi> = "publish_pre" in prog_sim_pre_implies_sim)
  using publish_sim apply auto[1]
   apply (simp add: state_inv_def rel_guard_and_def)
   apply metis
  by auto


lemma register_e_sim: "(s\<^sub>c, s\<^sub>a) \<in> state_inv \<Longrightarrow> e_sim 
        \<Gamma>\<^sub>c (Register_Bid\<^sub>c uid qt, s\<^sub>c, x\<^sub>c) (register\<^sub>c_rely uid) (register\<^sub>c_guar uid)
        state_inv (zetaI (register_map uid qt)) state_inv 
        \<Gamma>\<^sub>a (Register_Bid\<^sub>a uid qt, s\<^sub>a, x\<^sub>a) UNIV UNIV"
  apply (simp add: Register_Bid\<^sub>c_def Register_Bid\<^sub>a_def)
  apply (rule_tac \<xi> = "state_inv" in PiCore_SIMP_Refine.BasicEvt_Rule')
       apply (simp add: state_inv_def rel_guard_eq_def)
       apply (smt (verit) Auc_Status.exhaust Collect_mono case_prodD split_cong)
      apply (simp, simp add: stable_e_alpha, simp, simp)
  apply clarsimp
  apply (rule_tac \<zeta> = "register_map uid qt" in sim_implies_simI)
   apply (rule_tac \<xi> = "register_pre" in prog_sim_pre_implies_sim)
  using register_sim by auto

lemma EvtSys_on_Core_sim : "es_sim 
      \<Gamma>\<^sub>c (Auction_Spec\<^sub>c k, s0\<^sub>c, x0\<^sub>c) (evtsys_rely\<^sub>c k) (evtsys_guar\<^sub>c k)
      k state_inv ev_map ev_prog_map
      \<Gamma>\<^sub>a (Auction_Spec\<^sub>a k, s0\<^sub>a, x0\<^sub>a) UNIV UNIV"
  apply (case_tac k, simp add: Auction_Spec\<^sub>c_def Auction_Spec\<^sub>a_def)
   apply (rule_tac \<gamma> = state_inv in PiCore_SIMP_Refine.EvtSys_rule, simp add: Register_Bid\<^sub>c_def, clarsimp)
  using ev_map_register apply blast
  using ev_prog_map_register ev_map_register register_e_sim apply auto[1]
     apply (simp add: state_inv_def is_max_def, simp)
  apply (simp add: stable_e_alpha)
   apply (simp add: Auction_Spec\<^sub>c_def Auction_Spec\<^sub>a_def)
   apply (rule_tac \<gamma> = state_inv in PiCore_SIMP_Refine.EvtSys_rule, 
          simp add: Publish_Res\<^sub>c_def Close_Auction\<^sub>c_def Start_Auction\<^sub>c_def)
  apply (simp add:  Publish_Res\<^sub>c_def Close_Auction\<^sub>c_def Start_Auction\<^sub>c_def get_evt_label_def label_def)
  using ev_map_close ev_map_register ev_map_start apply blast
      apply auto[1]
  using ev_prog_map_close ev_map_close close_e_sim apply auto[1]
  using ev_prog_map_publish ev_map_publish publish_e_sim apply auto[1]
  using ev_prog_map_start ev_map_start start_e_sim apply (smt (verit) Collect_cong)
  using init_sat_inv apply blast
  by (simp, simp add: stable_e_alpha)

theorem Arinc_sim: "pes_sim \<Gamma>\<^sub>c C0\<^sub>c state_inv ev_map ev_prog_map \<Gamma>\<^sub>a C0\<^sub>a"
  apply (rule_tac R\<^sub>c = evtsys_rely\<^sub>c and G\<^sub>c = evtsys_guar\<^sub>c and R\<^sub>a = evtsys_rely\<^sub>a and G\<^sub>a = evtsys_guar\<^sub>a 
        in PiCore_SIMP_Refine.Pes_rule)
  apply (simp add: EvtSys_on_Core_sim)
  using evtsys_rely_guar_compat by blast

subsection \<open>Refinement between implementation and Abstraction\<close>

interpretation ARINC_Sim_IFS: PiCore_Sim_IFS prog_simI
  ptranI\<^sub>c petranI\<^sub>c None Auc_Env\<^sub>c C0\<^sub>c "exec_step\<^sub>c Auc_Env\<^sub>c" interf state_equiv\<^sub>c state_obs\<^sub>c domevt\<^sub>c
  ptranI\<^sub>a petranI\<^sub>a None Auc_Env\<^sub>a C0\<^sub>a "exec_step\<^sub>a Auc_Env\<^sub>a" interf state_equiv\<^sub>a state_obs\<^sub>a domevt\<^sub>a
  state_inv ev_map ev_prog_map
proof
  show "pes_sim Auc_Env\<^sub>c C0\<^sub>c register_post ev_map ev_prog_map Auc_Env\<^sub>a C0\<^sub>a"
    by (simp add: Arinc_sim)
  show "\<And>s\<^sub>c s\<^sub>a e\<^sub>c e\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> register_post \<Longrightarrow> ev_map e\<^sub>c = e\<^sub>a \<Longrightarrow> domevt\<^sub>c s\<^sub>c e\<^sub>c = domevt\<^sub>a s\<^sub>a e\<^sub>a"
    by (simp add: Auction_dom_sim)
  show "interf \<preceq>\<^sub>p interf"
    by (simp add: policy_refine_refl)
  show "\<And>s\<^sub>c s\<^sub>a t\<^sub>c t\<^sub>a d. (s\<^sub>c, s\<^sub>a) \<in> register_post \<Longrightarrow> (t\<^sub>c, t\<^sub>a) \<in> register_post \<Longrightarrow> s\<^sub>a \<sim>\<^sub>ad\<sim>\<^sub>a t\<^sub>a = s\<^sub>c \<sim>\<^sub>cd\<sim>\<^sub>c t\<^sub>c"
    using Auction_sim_state_ifs by auto
qed

theorem ARINC_abs_lr_imp: "Auction\<^sub>a.local_respectC \<Longrightarrow> Auction\<^sub>c.local_respectC"
  by (simp add: ARINC_Sim_IFS.PiCore_abs_lr_imp)

theorem ARINC_abs_wsc_imp: "Auction\<^sub>a.weak_step_consistentC \<Longrightarrow> Auction\<^sub>c.weak_step_consistentC"
  by (simp add: ARINC_Sim_IFS.PiCore_abs_wsc_imp)

end