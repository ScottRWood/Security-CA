section \<open>The Protocol\<close>

theory NS_Public imports Event begin

inductive_set ns_public :: "event list set" where
   Nil:  "[] \<in> ns_public" |
   NS1:  "\<lbrakk>evs1 \<in> ns_public; Nonce NA \<notin> used evs1\<rbrakk>
          \<Longrightarrow> \<lparr>Sender = A, Receiver = B, Message = Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>\<rparr> # evs1 \<in> ns_public" |
   NS2:  "\<lbrakk>evs2 \<in> ns_public;  Nonce NB \<notin> used evs2;
          \<lparr>Sender = A', Receiver = B, Message = (Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>)\<rparr> \<in> set evs2\<rbrakk>
          \<Longrightarrow> \<lparr>Sender = B, Receiver = A, Message =(Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace>)\<rparr> # evs2  \<in>  ns_public" |
   NS3:  "\<lbrakk>evs3 \<in> ns_public;
          \<lparr>Sender = A, Receiver = B, Message = (Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>)\<rparr> \<in> set evs3;
          \<lparr>Sender = B', Receiver = A, Message = (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace>)\<rparr> \<in> set evs3\<rbrakk>
          \<Longrightarrow> \<lparr>Sender = A, Receiver = B, Message = (Crypt (pubK B) (Nonce NB))\<rparr> # evs3 \<in> ns_public" |
   Fake: "\<lbrakk>evsf \<in> ns_public;  X \<in> synth (analz (knows evsf))\<rbrakk>
          \<Longrightarrow> \<lparr>Sender = Spy, Receiver = B, Message = X\<rparr> # evsf \<in> ns_public"

subsection "Exercise 1" (*{{{*)

(*Define the three events in Isabelle as e1, e2, and e3, using an abbreviation. {{{*)
abbreviation "e1 \<equiv> \<lparr>Sender = Friend 2, Receiver = Friend 8, Message = Crypt (pubK (Friend 8)) \<lbrace>Nonce 5, Agent (Friend 2)\<rbrace>\<rparr>"
abbreviation "e2 \<equiv> \<lparr>Sender = Friend 8, Receiver = Friend 2, Message = Crypt (pubK (Friend 2)) \<lbrace>Nonce 5, Nonce 7, Agent (Friend 8)\<rbrace>\<rparr>"
abbreviation "e3 \<equiv> \<lparr>Sender = Friend 2, Receiver = Friend 8, Message = Crypt (pubK (Friend 8)) (Nonce 7)\<rparr>"
(*}}}*)

(*Define a list ex1, which contains the three events in reverse order. {{{*)
abbreviation "ex1 \<equiv> [e3, e2, e1]"
(*}}}*)

(*Prove the following lemma e1*)
lemma e1: "[e1] \<in> ns_public" (*{{{*)
proof
  from ns_public.Nil show "[] \<in> ns_public" by simp
next
  show "Nonce 5 \<notin> used []" by simp
qed
(*}}}*)

(*Use lemma e1 to prove the following lemma e2*)
lemma e2: "[e2,e1] \<in> ns_public" (*{{{*)
proof
  from e1 show "[e1] \<in> ns_public" by simp
next
  show "Nonce 7 \<notin> used [e1]" by simp
next
  show "e1 \<in> set [e1]" by simp
qed
(*}}}*)

(*Use lemma e2 to prove the following theorem*)
theorem "ex1 \<in> ns_public" (*{{{*)
proof
  from e2 show "[e2,e1] \<in> ns_public" by simp
next
  show "e1 \<in> set [e2, e1]" by simp
next
  show "e2 \<in> set [e2, e1]" by simp
qed
(*}}}*)

(*}}}*)

subsection "Exercise 2" (*{{{*)

(*Create two additional events e4 and e5 and define the execution ex2 in terms of e1, e4, and e5 {{{*)
abbreviation "e4 \<equiv> \<lparr>Sender = Friend 8, Receiver = Friend 2, Message = Crypt (pubK (Friend 2)) \<lbrace>Nonce 5, Nonce 5, Agent (Friend 8)\<rbrace>\<rparr>"
abbreviation "e5 \<equiv> \<lparr>Sender = Friend 2, Receiver = Friend 8, Message = Crypt (pubK (Friend 8)) (Nonce 5)\<rparr>"
abbreviation "ex2 \<equiv> [e5, e4, e1]"
(*}}}*)

(*Use the same approach as in the previous exercise to try to verify that ex2
does follow the Needham-Schroeder protocol. Where does it fail? Why? {{{*)
lemma "[e4,e1] \<in> ns_public"
proof
  from e1 show "[e1] \<in> ns_public" by simp
next
  show "Nonce 5 \<notin> used [e1]" oops
(*}}}*)

(*Use the following commands to create two additional proof rules: {{{*)
inductive_cases r4: "e4 # evs \<in> ns_public"
inductive_cases r5: "e5 # evs \<in> ns_public"
(*}}}*)

(*Prove the following theorem by classical contradiction using rules r4 and r5*)
theorem "ex2 \<notin> ns_public" (*{{{*)
proof (rule ccontr)
  assume "\<not> ex2 \<notin> ns_public"
  hence "ex2 \<in> ns_public" by simp
  thus False
  proof (rule r5)
    assume "[e4, e1] \<in> ns_public"
    thus ?thesis
    proof (rule r4)
      assume "Nonce 5 \<notin> used [e1]"
      thus ?thesis by simp
    qed
  qed
qed
(*}}}*)

(*}}}*)

subsection "Exercise 3" (*{{{*)

(*Formulate a theorem spyKnowEnc which states that msg is indeed an
element of analz (knows ex1) and prove the theorem. {{{*)
theorem spyKnowEnc:
  defines "msg \<equiv> Crypt (pubK (Friend 2)) \<lbrace>Nonce 5, Nonce 7, Agent (Friend 8)\<rbrace>"
  shows "msg \<in> analz (knows ex1)" using msg_def by simp
(*}}}*)

(*Formulate a theorem spyNotAnalz which states that Nonce 5 is not an element of analz (knows ex1) and prove the theorem using lemma spyAnalz and
spyNotKnows. {{{*)
theorem spyNotAnalz:
  defines "msg \<equiv> Nonce 5"
  shows "msg \<notin> analz (knows ex1)" using msg_def by auto
(*}}}*)

(*}}}*)

subsection "Exercise 4" (*{{{*)

(*Verify in Isabelle that a spy cannot learn any private key of a honest participant for any execution of ns public:*)
theorem prikey:
assumes "A \<noteq> Spy"
shows "evs \<in> ns_public \<Longrightarrow> Key (priK A) \<notin> analz (knows evs)"
proof (induction rule: ns_public.induct)
  show "Key (priK A) \<notin> analz (knows [])" using assms by simp
next
  fix evs1 NA A' B
  assume "Key (priK A) \<notin> analz (knows evs1)"
  thus "Key (priK A) \<notin> analz (knows (\<lparr>Sender = A', Receiver = B, Message = Crypt (pubK B) \<lbrace>Nonce NA, Agent A'\<rbrace>\<rparr> # evs1))" by simp
next
  fix evs2 NB A' B NA A''
  assume "Key (priK A) \<notin> analz (knows evs2)"
  and "\<lparr>Sender = A', Receiver = B, Message = Crypt (pubK B) \<lbrace>Nonce NA, Agent A''\<rbrace>\<rparr> \<in> set evs2"
  thus "Key (priK A) \<notin> analz (knows (\<lparr>Sender = B, Receiver = A'', Message = Crypt (pubK A'') \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace>\<rparr> # evs2))" by simp
next
  fix evs3 A' B NA B' NB
  assume "Key (priK A) \<notin> analz (knows evs3)"
  thus "Key (priK A) \<notin> analz (knows (\<lparr>Sender = A', Receiver = B, Message = Crypt (pubK B) (Nonce NB)\<rparr> # evs3))" by simp
next
  fix evsf X B
  assume "Key (priK A) \<notin> analz (knows evsf)"
   and "X \<in> synth (analz (knows evsf))"
  thus "Key (priK A) \<notin> analz (knows (\<lparr>Sender = Spy, Receiver = B, Message = X\<rparr> # evsf))"
    using synth_analz_insert_eq by auto
qed

(*}}}*)

subsection "Correctness of NS" (*{{{*)

declare analz_subset_parts [THEN subsetD, dest]
declare Fake_parts_insert [THEN subsetD, dest]
declare knows_Spy_partsEs [elim]

lemma no_nonce_NS1_NS2:
    "\<lbrakk>Crypt (pubK C) \<lbrace>NA', Nonce NA, Agent D\<rbrace> \<in> parts (knows evs);
      Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace> \<in> parts (knows evs);
      evs \<in> ns_public\<rbrakk>
     \<Longrightarrow> Nonce NA \<in> analz (knows evs)"
apply (erule rev_mp, erule rev_mp)
apply (erule ns_public.induct, simp_all)
apply (blast intro: analz_insertI)+
done

lemma unique_NA:
     "\<lbrakk>Crypt(pubK B)  \<lbrace>Nonce NA, Agent A \<rbrace> \<in> parts(knows evs);
       Crypt(pubK B') \<lbrace>Nonce NA, Agent A'\<rbrace> \<in> parts(knows evs);
       Nonce NA \<notin> analz (knows evs); evs \<in> ns_public\<rbrakk>
      \<Longrightarrow> A=A' \<and> B=B'"
apply (erule rev_mp, erule rev_mp, erule rev_mp)
apply (erule ns_public.induct, simp_all)
apply (blast intro: analz_insertI)+
done

lemma unique_NA2:
     "\<lbrakk>Crypt(pubK B)  \<lbrace>Nonce NA, Nonce NB, Agent A\<rbrace> \<in> parts(knows evs);
       Crypt(pubK B') \<lbrace>Nonce NA', Nonce NB, Agent A'\<rbrace> \<in> parts(knows evs);
       Nonce NB \<notin> analz (knows evs); evs \<in> ns_public\<rbrakk>
      \<Longrightarrow> A=A' \<and> NA=NA'"
apply (erule rev_mp, erule rev_mp, erule rev_mp)
apply (erule ns_public.induct, simp_all)
apply (blast intro: analz_insertI)+
done

lemma honest_send_real_name:
  assumes "A \<noteq> Spy"
  shows "evs \<in> ns_public
    \<Longrightarrow> \<lparr>Sender = A, Receiver = B, Message = Crypt (pubK C) \<lbrace>Nonce NA, Agent A'\<rbrace>\<rparr> \<in> set evs 
    \<Longrightarrow> A = A'"
proof (induction rule: ns_public.induct)
  case Nil
  then show ?case by simp
next
  case (Fake evsf X B)
  then show ?case using assms by simp
next
  case (NS1 evs1 NA A B)
  then show ?case using assms by fastforce
next
  case (NS2 evs2 NB A' B NA A)
  then show ?case by simp
next
  case (NS3 evs3 A B NA B' NB)
  then show ?case by simp
qed

theorem Spy_not_see_NA:
defines send_def: "send A B NA \<equiv> \<lparr>Sender = A, Receiver = B, Message = Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>\<rparr>"
assumes "A \<noteq> Spy" and "B \<noteq> Spy"
shows "\<lbrakk>evs \<in> ns_public; send A B NA \<in> set evs\<rbrakk>
       \<Longrightarrow> Nonce NA \<notin> analz (knows evs)"
proof (induction rule: ns_public.induct)
  case Nil
  then show ?case by simp
next
  case (Fake evsf X Ba)
  hence "send A B NA = \<lparr>Sender = Spy, Receiver = Ba, Message = X\<rparr> \<or> send A B NA \<in> set evsf" by simp
  with `A \<noteq> Spy` send_def have "send A B NA \<in> set evsf" by simp
  with Fake.IH have "Nonce NA \<notin> analz (knows evsf)" by simp
  thus ?case
    by (metis Fake_analz_eq Nonce_synth \<open>X \<in> synth (analz (knows evsf))\<close> knows_Says synth.Inj)
next
  case (NS1 evs1 NAa Aa Ba)
  hence "send A B NA = \<lparr>Sender = Aa, Receiver = Ba, Message = Crypt (pubK Ba) \<lbrace>Nonce NAa, Agent Aa\<rbrace>\<rparr> \<or> send A B NA \<in> set evs1" by simp
  thus ?case
  proof
    assume asmp: "send A B NA = \<lparr>Sender = Aa, Receiver = Ba, Message = Crypt (pubK Ba) \<lbrace>Nonce NAa, Agent Aa\<rbrace>\<rparr>"
    with NS1.hyps(2) have "Nonce NA \<notin> used evs1" using send_def by simp
    moreover from asmp `B \<noteq> Spy` have "Ba \<noteq> Spy" using send_def by simp
    with prikey have "Key (priK Ba) \<notin> analz (knows evs1)" using `evs1 \<in> ns_public` by simp
    hence "analz (insert (Crypt (pubK Ba) \<lbrace>Nonce NAa, Agent Aa\<rbrace>) (knows evs1)) = insert (Crypt (pubK Ba) \<lbrace>Nonce NAa, Agent Aa\<rbrace>) (analz (knows evs1))" using analz_insert_Crypt by simp
    ultimately show ?thesis by auto
  next
    assume asmp: "send A B NA \<in> set evs1"
    with NS1.hyps(2) have "NA\<noteq>NAa" by (metis Says_imp_knows_Spy parts.simps select_convs(3) send_def usedI)
    moreover from NS1.IH asmp have "Nonce NA \<notin> analz (knows evs1)" by simp
    ultimately show ?thesis by simp
  qed
next
  case (NS2 evs2 NB A' Ba NAa Aa)
  hence asmp: "send A B NA \<in> set evs2" using send_def by simp
  show ?case
  proof cases
    assume "NA = NAa"
    with NS2.IH asmp have "Nonce NAa \<notin> analz (knows evs2)" by simp
    hence "Nonce NAa \<notin> analz (knows (\<lparr>Sender = Ba, Receiver = Aa, Message = Crypt (pubK Aa) \<lbrace>Nonce NAa, Nonce NB, Agent Ba\<rbrace>\<rparr> # evs2))"
    proof cases
      assume a1: "Nonce NAa \<notin> analz (knows evs2)" and "Aa = Spy"
      with NS2.hyps(3) have a2: "\<lparr>Sender = A', Receiver = Ba, Message = Crypt (pubK Ba) \<lbrace>Nonce NAa, Agent Spy\<rbrace>\<rparr> \<in> set evs2" by simp
      hence "A'=Spy" using honest_send_real_name \<open>evs2 \<in> ns_public\<close> by blast
      moreover have "A'\<noteq>Spy" by (metis Says_imp_analz_Spy \<open>Aa = Spy\<close> \<open>NA = NAa\<close> \<open>evs2 \<in> ns_public\<close> a1 asmp assms(2) NS2.hyps(3) not_parts_not_analz select_convs(3) send_def unique_NA)
      ultimately show ?thesis by simp
    next
      assume a1: "Nonce NAa \<notin> analz (knows evs2)" and "Aa \<noteq> Spy"
      thus ?thesis using \<open>evs2 \<in> ns_public\<close> prikey by simp
    qed
    thus ?thesis using \<open>NA = NAa\<close> by simp
  next
    assume "\<not>NA = NAa"
    moreover from NS2.IH asmp have "Nonce NA \<notin> analz (knows evs2)" by simp
    moreover from NS2.hyps(2) asmp have "NA\<noteq>NB" by (metis Says_imp_knows_Spy parts.simps select_convs(3) send_def usedI)
    ultimately show ?thesis using `NA\<noteq>NB` by simp
  qed
next
  case (NS3 evs3 Aa Ba NAa B' NB)
  hence "send A B NA \<in> set evs3" by (simp add: send_def)
  with NS3.IH have "Nonce NA \<notin> analz (knows evs3)" by simp
  thus ?case
  proof cases
    assume "Nonce NA \<notin> analz (knows evs3)" and "NA = NB"
    thus ?thesis
      by (metis Says_imp_knows_Spy \<open>\<lparr>Sender = B', Receiver = Aa, Message = Crypt (pubK Aa) \<lbrace>Nonce NAa, Nonce NB, Agent Ba\<rbrace>\<rparr> \<in> set evs3\<close> \<open>evs3 \<in> ns_public\<close> \<open>send A B NA \<in> set evs3\<close> no_nonce_NS1_NS2 parts.Inj select_convs(3) send_def)
  next
    assume "Nonce NA \<notin> analz (knows evs3)" and "\<not>NA = NB"
    thus ?thesis by simp
  qed
qed

lemma knows_parts:
  assumes "Y \<notin> parts {X}"
    and "Y \<notin> analz (knows evs)"
  shows "Y \<notin> knows (\<lparr>Sender = A, Receiver = B, Message = X\<rparr> # evs)"
  using assms(1) assms(2) by auto

theorem Spy_not_see_NB:
  defines send_def: "send B A NA NB \<equiv> \<lparr>Sender = B, Receiver = A, Message = Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace>\<rparr>"
  assumes "A \<noteq> Spy" and "B \<noteq> Spy"
  shows "\<lbrakk>evs \<in> ns_public; send B A NA NB \<in> set evs\<rbrakk>
  \<Longrightarrow> Nonce NB \<notin> analz (knows evs)"
proof (induction rule: ns_public.induct)
  case Nil
  then show ?case by simp
next
  case (Fake evsf X Ba)
  hence "send B A NA NB = \<lparr>Sender = Spy, Receiver = Ba, Message = X\<rparr> \<or> send B A NA NB \<in> set evsf" by simp
  with `B \<noteq> Spy` send_def have "send B A NA NB \<in> set evsf" by simp
  with Fake.IH have "Nonce NB \<notin> analz (knows evsf)" by simp
  thus ?case by (metis Fake.hyps(2) Fake_analz_eq Nonce_synth knows_Says synth.Inj)
next
  case (NS1 evs1 NAa Aa Ba)
  hence "send B A NA NB = \<lparr>Sender = Aa, Receiver = Ba, Message = Crypt (pubK Ba) \<lbrace>Nonce NAa, Agent Aa\<rbrace>\<rparr> \<or> send B A NA NB \<in> set evs1" by simp
  with `B \<noteq> Spy` send_def have "send B A NA NB \<in> set evs1" by simp
  hence "Nonce NB \<in> used evs1" using send_def by fastforce
  with NS1.hyps(2) have "\<not>NB=NAa" by auto
  hence "Nonce NB \<notin> parts ({Crypt (pubK Ba) \<lbrace>Nonce NAa, Agent Aa\<rbrace>})" by simp
  moreover from \<open>send B A NA NB \<in> set evs1\<close> have "Nonce NB \<notin> analz (knows evs1)" using NS1.IH by simp
  ultimately show ?case using knows_parts by simp
next
  case (NS2 evs2 NB' A'' B' NA' A')
  hence "send B A NA NB = \<lparr>Sender = B', Receiver = A', Message = Crypt (pubK A') \<lbrace>Nonce NA', Nonce NB', Agent B'\<rbrace>\<rparr> \<or> send B A NA NB \<in> set evs2" by simp
  then show ?case
  proof
    assume s_def: "send B A NA NB = \<lparr>Sender = B', Receiver = A', Message = Crypt (pubK A') \<lbrace>Nonce NA', Nonce NB', Agent B'\<rbrace>\<rparr>"
    hence "B \<noteq> Spy" and "A \<noteq> Spy" using assms by simp_all
    hence "analz(knows (\<lparr>Sender = B', Receiver = A', Message = Crypt (pubK A') \<lbrace>Nonce NA', Nonce NB', Agent B'\<rbrace>\<rparr> # evs2)) = insert (Crypt (pubK A') \<lbrace>Nonce NA', Nonce NB', Agent B'\<rbrace>) (analz(knows evs2))"
      using NS2.hyps(1) prikey s_def send_def by auto
    moreover from s_def have "NB = NB'" using send_def by simp
    with NS2.hyps(2) have "Nonce NB \<notin> analz(knows evs2)" by auto
    ultimately show ?thesis by simp
  next
    assume s_def: "send B A NA NB \<in> set evs2"
    moreover from \<open>send B A NA NB \<in> set evs2\<close> have IH: "Nonce NB \<notin> analz (knows evs2)" using NS2.IH by simp
    ultimately have "\<not>NB=NA'" using NS2.hyps(3) by (metis NS2.hyps(1) Says_imp_analz_Spy no_nonce_NS1_NS2 parts.Inj parts_analz select_convs(3) send_def)
    moreover from s_def have "Nonce NB \<in> used evs2" using send_def by fastforce
    with NS2.hyps(2) have "\<not>NB=NB'" by auto
    ultimately have "Nonce NB \<notin> parts {(Crypt (pubK A') \<lbrace>Nonce NA', Nonce NB', Agent B'\<rbrace>)}" by simp
    thus ?case using IH knows_parts by simp
  qed
next
  case (NS3 evs3 Aa Ba NAa Ba' NBa)
  hence "send B A NA NB = \<lparr>Sender = Aa, Receiver = Ba, Message = Crypt (pubK Ba) (Nonce NBa)\<rparr> \<or> send B A NA NB \<in> set evs3" by simp
  with `B \<noteq> Spy` send_def have "send B A NA NB \<in> set evs3" by simp
  with NS3.IH have IH: "Nonce NB \<notin> analz (knows evs3)" by simp
  show ?case
  proof cases
    assume "NB=NBa"
    show ?case
    proof cases
      assume "Ba=Spy"
      moreover have "Crypt (pubK Aa) \<lbrace>Nonce NAa, Nonce NBa, Agent Ba\<rbrace> \<in> parts(knows evs3)" using NS3.hyps(3) by auto
      with `NB=NBa` have "Ba = B"
        using NS3.hyps(1) \<open>send B A NA NB \<in> set evs3\<close> assms(3) calculation send_def unique_NA2 IH by auto
      ultimately show ?case using `B \<noteq> Spy` by simp
    next
      assume "\<not>Ba=Spy"
      thus ?case by (simp add: IH NS3.hyps(1) prikey)
    qed
  next
    assume "\<not>NB=NBa"
    thus ?case using IH by simp
  qed
qed

(*}}}*)

end