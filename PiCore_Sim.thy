theory PiCore_Sim
  imports PiCore_Refine
begin

locale event_sim_validity = 
   event\<^sub>c: event ptran\<^sub>c petran\<^sub>c fin_com\<^sub>c + 
   event\<^sub>a: event ptran\<^sub>a petran\<^sub>a fin_com\<^sub>a
for ptran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> (('s\<^sub>c,'prog\<^sub>c) pconf \<times> ('s\<^sub>c,'prog\<^sub>c) pconf) set" 
and petran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> ('s\<^sub>c,'prog\<^sub>c) pconf \<Rightarrow> ('s\<^sub>c,'prog\<^sub>c) pconf \<Rightarrow> bool"
and fin_com\<^sub>c :: "'prog\<^sub>c"
and ptran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> (('s\<^sub>a,'prog\<^sub>a) pconf \<times> ('s\<^sub>a,'prog\<^sub>a) pconf) set" 
and petran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> bool"
and fin_com\<^sub>a :: "'prog\<^sub>a"
+ fixes sim_s :: "'s\<^sub>c \<Rightarrow> 's\<^sub>a"
  and   prog_sim :: "['Env\<^sub>c, ('s\<^sub>c,'prog\<^sub>c) pconf, ('s\<^sub>c \<times> 's\<^sub>c) set, ('s\<^sub>c \<times> 's\<^sub>c) set, 
                      'Env\<^sub>a, ('s\<^sub>a,'prog\<^sub>a) pconf, ('s\<^sub>a \<times> 's\<^sub>a) set, ('s\<^sub>a \<times> 's\<^sub>a) set] \<Rightarrow> bool" 
  ("'(_,_,_,_')/ \<preceq>\<^sub>p /'(_,_,_,_')" [81,81,81,81,81,81,81,81] 100)
assumes prog_sim_validity: "(\<Gamma>\<^sub>c, (P\<^sub>c, s\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a) \<Longrightarrow> 
        sim_s s\<^sub>c = s\<^sub>a \<and> 
        (((P\<^sub>c, s\<^sub>c), (P'\<^sub>c, s'\<^sub>c)) \<in> ptran\<^sub>c \<Gamma>\<^sub>c  \<longrightarrow> (s\<^sub>c, s'\<^sub>c) \<in> G\<^sub>c \<longrightarrow>
        ((\<Gamma>\<^sub>c, (P'\<^sub>c, s'\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p (\<Gamma>\<^sub>a, (P\<^sub>a, s\<^sub>a), R\<^sub>a, G\<^sub>a) \<or> 
        ((P\<^sub>a, s\<^sub>a), (P'\<^sub>a, sim_s s'\<^sub>c)) \<in> ptran\<^sub>a \<Gamma>\<^sub>a \<and> (s\<^sub>a, sim_s s'\<^sub>c) \<in> G\<^sub>a \<and> 
        (\<Gamma>\<^sub>c, (P'\<^sub>c, s'\<^sub>c), R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p (\<Gamma>\<^sub>a, (P'\<^sub>a, sim_s s'\<^sub>c), R\<^sub>a, G\<^sub>a)))"
begin

abbreviation ptran\<^sub>c' :: "'Env\<^sub>c \<Rightarrow> ('s\<^sub>c,'prog\<^sub>c) pconf \<Rightarrow> ('s\<^sub>c,'prog\<^sub>c) pconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ -c\<rightarrow> _" [81,81] 80)
  where "ptran\<^sub>c' \<equiv> event\<^sub>c.ptran'"

abbreviation ptrans\<^sub>c :: "'Env\<^sub>c \<Rightarrow> ('s\<^sub>c,'prog\<^sub>c) pconf \<Rightarrow> ('s\<^sub>c,'prog\<^sub>c) pconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ c*\<rightarrow> _" [81,81] 80)
  where "ptrans\<^sub>c \<equiv> event\<^sub>c.ptrans"

abbreviation etran\<^sub>c ::  "'Env\<^sub>c \<Rightarrow> ('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) econf \<Rightarrow> ('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) actk \<Rightarrow> 
                        ('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) econf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ -et-_\<rightarrow> _" [81,81,81] 80)
  where "etran\<^sub>c \<equiv> event\<^sub>c.etran"

(*
abbreviation estran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> ('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) esconf \<Rightarrow> ('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) actk \<Rightarrow> 
                        ('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) esconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ -es-_\<rightarrow> _" [81,81] 80)
  where "estran\<^sub>c \<equiv> event\<^sub>c.estran"

abbreviation pestran\<^sub>c :: "'Env\<^sub>c \<Rightarrow> ('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) pesconf \<Rightarrow> ('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) actk \<Rightarrow> 
                        ('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) pesconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ -pes-_\<rightarrow> _" [70,70] 60)
  where "pestran\<^sub>c \<equiv> event\<^sub>c.pestran"
*)

abbreviation ptran\<^sub>a' :: "'Env\<^sub>a \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ -c\<rightarrow> _" [81,81] 80)
  where "ptran\<^sub>a' \<equiv> event\<^sub>a.ptran'"

abbreviation ptrans\<^sub>a :: "'Env\<^sub>a \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> ('s\<^sub>a,'prog\<^sub>a) pconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ c*\<rightarrow> _" [81,81] 80)
  where "ptrans\<^sub>a \<equiv> event\<^sub>a.ptrans"

abbreviation etran\<^sub>a ::  "'Env\<^sub>a \<Rightarrow> ('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) econf \<Rightarrow> ('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) actk \<Rightarrow> 
                        ('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) econf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ -et-_\<rightarrow> _" [81,81,81] 80)
  where "etran\<^sub>a \<equiv> event\<^sub>a.etran"

(*
abbreviation estran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> ('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) esconf \<Rightarrow> ('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) actk \<Rightarrow> 
                        ('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) esconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ -es-_\<rightarrow> _" [81,81] 80)
  where "estran\<^sub>a \<equiv> event\<^sub>a.estran"

abbreviation pestran\<^sub>a :: "'Env\<^sub>a \<Rightarrow> ('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) pesconf \<Rightarrow> ('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) actk \<Rightarrow> 
                        ('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) pesconf \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ -pes-_\<rightarrow> _" [70,70] 60)
  where "pestran\<^sub>a \<equiv> event\<^sub>a.pestran"
*)

inductive e_sim_validity :: "'Env\<^sub>c \<Rightarrow> ('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) econf \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>c) set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>c) set
    \<Rightarrow> 'Env\<^sub>a \<Rightarrow> ('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) econf \<Rightarrow> ('s\<^sub>a \<times> 's\<^sub>a) set \<Rightarrow> ('s\<^sub>a \<times> 's\<^sub>a) set \<Rightarrow> bool" 
    ("'(_,_,_,_')/ \<preceq>\<^sub>e /'(_,_,_,_')" [81,81,81,81,81,81,81,81] 100)
    where rgsim : "\<lbrakk>sim_s (gets_e econf\<^sub>c) = gets_e econf\<^sub>a ;
                   \<forall>econf\<^sub>c' \<delta>\<^sub>c. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c econf\<^sub>c -et-\<delta>\<^sub>c\<rightarrow>econf\<^sub>c') \<longrightarrow> 
                   ((\<Gamma>\<^sub>c, econf\<^sub>c', R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e (\<Gamma>\<^sub>a, econf\<^sub>a, R\<^sub>a, G\<^sub>a)) \<or> (
                    \<exists>econf\<^sub>a' \<delta>\<^sub>a. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a econf\<^sub>a -et-\<delta>\<^sub>a\<rightarrow>econf\<^sub>a') \<and> (gets_e econf\<^sub>a, gets_e econf\<^sub>a') \<in> G\<^sub>a
                    \<and> (\<Gamma>\<^sub>c, econf\<^sub>c', R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e (\<Gamma>\<^sub>a, econf\<^sub>a', R\<^sub>a, G\<^sub>a))\<rbrakk> \<Longrightarrow> (\<Gamma>\<^sub>c, econf\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e (\<Gamma>\<^sub>a, econf\<^sub>a, R\<^sub>a, G\<^sub>a)"


(*
inductive pes_sim_validity :: "'Env\<^sub>c \<Rightarrow> ('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) pesconf \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>c) set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>c) set
    \<Rightarrow> 'Env\<^sub>a \<Rightarrow> ('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) pesconf \<Rightarrow> ('s\<^sub>a \<times> 's\<^sub>a) set \<Rightarrow> ('s\<^sub>a \<times> 's\<^sub>a) set \<Rightarrow> bool" 
    ("'(_,_,_,_')/ \<preceq>\<^sub>p\<^sub>e\<^sub>s /'(_,_,_,_')" [81,81,81,81,81,81,81,81] 100)
    where rgsim : "\<lbrakk>sim_s (gets pesconf\<^sub>c) = gets pesconf\<^sub>a ;
                    \<forall>pesconf\<^sub>c' \<delta>\<^sub>c. (\<Gamma>\<^sub>c \<turnstile>\<^sub>c pesconf\<^sub>c -pes-\<delta>\<^sub>c\<rightarrow>pesconf\<^sub>c') \<longrightarrow> 
                    ((\<Gamma>\<^sub>c, pesconf\<^sub>c', R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p\<^sub>e\<^sub>s (\<Gamma>\<^sub>a, pesconf\<^sub>a, R\<^sub>a, G\<^sub>a)) \<or> (
                     \<exists>pesconf\<^sub>a' \<delta>\<^sub>a. (\<Gamma>\<^sub>a \<turnstile>\<^sub>a pesconf\<^sub>a -pes-\<delta>\<^sub>a\<rightarrow>pesconf\<^sub>a') \<and> (gets pesconf\<^sub>a, gets pesconf\<^sub>a') \<in> G\<^sub>a
                     \<and> (\<Gamma>\<^sub>c, pesconf\<^sub>c', R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p\<^sub>e\<^sub>s (\<Gamma>\<^sub>a, pesconf\<^sub>a', R\<^sub>a, G\<^sub>a)) 
                    \<rbrakk> \<Longrightarrow> (\<Gamma>\<^sub>c, pesconf\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p\<^sub>e\<^sub>s (\<Gamma>\<^sub>a, pesconf\<^sub>a, R\<^sub>a, G\<^sub>a)"
*)



(*
definition e_sim_validity :: "'Env\<^sub>c \<Rightarrow> ('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) econf \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>c) set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>c) set
    \<Rightarrow> 'Env\<^sub>a \<Rightarrow> ('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) econf \<Rightarrow> ('s\<^sub>a \<times> 's\<^sub>a) set \<Rightarrow> ('s\<^sub>a \<times> 's\<^sub>a) set \<Rightarrow> bool" 
    ("'(_,_,_,_')/ \<preceq>\<^sub>e /'(_,_,_,_')" [81,81,81,81,81,81,81,81] 100)
    where "(\<Gamma>\<^sub>c, econf\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e (\<Gamma>\<^sub>a, econf\<^sub>a, R\<^sub>a, G\<^sub>a) \<equiv> True"

definition es_sim_validity :: "'Env\<^sub>c \<Rightarrow> ('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) esconf \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>c) set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>c) set
    \<Rightarrow> 'Env\<^sub>a \<Rightarrow> ('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) esconf \<Rightarrow> ('s\<^sub>a \<times> 's\<^sub>a) set \<Rightarrow> ('s\<^sub>a \<times> 's\<^sub>a) set \<Rightarrow> bool" 
    ("'(_,_,_,_')/ \<preceq>\<^sub>e\<^sub>s /'(_,_,_,_')" [81,81,81,81,81,81,81,81] 100)
    where "(\<Gamma>\<^sub>c, esconf\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>e\<^sub>s (\<Gamma>\<^sub>a, esconf\<^sub>a, R\<^sub>a, G\<^sub>a) \<equiv> True"

definition pes_sim_validity :: "'Env\<^sub>c \<Rightarrow> ('l\<^sub>c,'k\<^sub>c,'s\<^sub>c,'prog\<^sub>c) pesconf \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>c) set \<Rightarrow> ('s\<^sub>c \<times> 's\<^sub>c) set
    \<Rightarrow> 'Env\<^sub>a \<Rightarrow> ('l\<^sub>a,'k\<^sub>a,'s\<^sub>a,'prog\<^sub>a) pesconf \<Rightarrow> ('s\<^sub>a \<times> 's\<^sub>a) set \<Rightarrow> ('s\<^sub>a \<times> 's\<^sub>a) set \<Rightarrow> bool" 
    ("'(_,_,_,_')/ \<preceq>\<^sub>p\<^sub>e\<^sub>s /'(_,_,_,_')" [81,81,81,81,81,81,81,81] 100)
    where "(\<Gamma>\<^sub>c, pesconf\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p\<^sub>e\<^sub>s (\<Gamma>\<^sub>a, pesconf\<^sub>a, R\<^sub>a, G\<^sub>a) \<equiv> 
            sim_s (gets pesconf\<^sub>c) = gets pesconf\<^sub>a \<and> 
            ((pesconf\<^sub>c, pesconf'\<^sub>c) \<in> pesetran \<Gamma>\<^sub>c  \<longrightarrow> (gets pesconf\<^sub>c, gets pesconf'\<^sub>c) \<in> G\<^sub>c \<longrightarrow>
            ((\<Gamma>\<^sub>c, pesconf\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p\<^sub>e\<^sub>s (\<Gamma>\<^sub>a, pesconf\<^sub>a, R\<^sub>a, G\<^sub>a) \<or> 
            (pesconf\<^sub>a, pesconf'\<^sub>a) \<in> pestran \<Gamma>\<^sub>a \<and> (gets pesconf\<^sub>a, gets pesconf'\<^sub>a) \<in> G\<^sub>a \<and> 
            (\<Gamma>\<^sub>c, pesconf'\<^sub>c, R\<^sub>c, G\<^sub>c) \<preceq>\<^sub>p\<^sub>e\<^sub>s (\<Gamma>\<^sub>a, pesconf'\<^sub>a, R\<^sub>a, G\<^sub>a)))"
*)


