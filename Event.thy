section\<open>Events\<close>

theory Event imports Adversary begin

record event =
  Sender::agent
  Receiver::agent
  Message::msg

subsection\<open>Function knows\<close>

fun knows :: "event list \<Rightarrow> msg set"
where knows_Nil:   "knows [] = initState"
    | knows_Cons:  "knows (ev # evs) = insert (Message ev) (knows evs)"

(*
abbreviation "trace1 \<equiv> [Says (Friend 1) (Friend 2) (Key 0), Gets (Friend 1) (Key 1), Notes (Friend 2) (Key 2)]"
value "knows Spy trace1"
value "knows (Friend 1) trace1"
abbreviation "trace2 \<equiv> [Says (Friend 1) (Friend 2) (Key 0), Gets (Friend 1) (Key 1), Notes (Friend 2) (Key 2)]"
*)

lemmas parts_insert_knows_A = parts_insert [of _ "knows evs"] for A evs

lemma knows_Spy_subset_knows_Spy_Says:
     "knows evs \<subseteq> knows (ev # evs)"
by (simp add: subset_insertI)

lemmas analz_mono_contra =
       knows_Spy_subset_knows_Spy_Says [THEN analz_mono, THEN contra_subsetD]

lemma Says_imp_knows_Spy [rule_format]:
     "ev \<in> set evs \<longrightarrow> Message ev \<in> knows evs"
proof (induction rule: list.induct)
  case Nil
  then show ?case by simp
next
  case (Cons x1 x2)
  then show ?case by simp
qed

lemmas knows_Spy_partsEs =
     Says_imp_knows_Spy [THEN parts.Inj, elim_format] 
     parts.Body [elim_format]

lemmas Says_imp_analz_Spy = Says_imp_knows_Spy [THEN analz.Inj]

lemmas spies_partsEs = knows_Spy_partsEs
lemmas Says_imp_spies = Says_imp_knows_Spy
lemmas parts_insert_spies = parts_insert_knows_A [of _]

lemma knows_Says[simp]: "knows (\<lparr>Sender=A, Receiver=B, Message=X\<rparr> # evs) = insert X (knows evs)"
by simp

lemma Says_imp_knows [rule_format]: "\<lparr>Sender=A, Receiver=B, Message=X\<rparr> \<in> set evs \<longrightarrow> X \<in> knows evs"
proof (induction rule: list.induct)
  case Nil
  then show ?case by simp
next
  case (Cons x1 x2)
  show ?case
  proof
    assume "\<lparr>Sender = A, Receiver = B, Message = X\<rparr> \<in> set (x1 # x2)"
    hence "\<lparr>Sender = A, Receiver = B, Message = X\<rparr> = x1 \<or> \<lparr>Sender = A, Receiver = B, Message = X\<rparr> \<in> set x2" by simp
    thus "X \<in> knows (x1 # x2)"
    proof
      assume "\<lparr>Sender = A, Receiver = B, Message = X\<rparr> = x1"
      thus "X \<in> knows (x1 # x2)" by auto
    next
      assume "\<lparr>Sender = A, Receiver = B, Message = X\<rparr> \<in> set x2"
      with Cons.IH have "X \<in> knows x2" by simp
      thus "X \<in> knows (x1 # x2)" by auto
    qed
  qed
qed

lemma knows_Spy_imp_Says_Notes_initState [rule_format]:
     "[| X \<in> knows evs |] ==> \<exists>A B.
  \<lparr>Sender = A, Receiver = B, Message = X\<rparr> \<in> set evs \<or> X \<in> initState"
proof (erule rev_mp)
  show "X \<in> knows  evs \<longrightarrow> (\<exists>A B. \<lparr>Sender = A, Receiver = B, Message = X\<rparr> \<in> set evs \<or> X \<in> initState)"
  proof (induction rule: list.induct)
    case Nil
    then show ?case by simp
  next
    case (Cons x1 x2)
    show ?case
    proof
      assume "X \<in> knows (x1 # x2)"
      hence "X=Message x1 \<or> X\<in>(knows x2)" by simp
      thus "\<exists>A B. \<lparr>Sender = A, Receiver = B, Message = X\<rparr> \<in> set (x1 # x2) \<or> X \<in> initState"
      proof
        assume "X=Message x1"
        thus "\<exists>A B. \<lparr>Sender = A, Receiver = B, Message = X\<rparr> \<in> set (x1 # x2) \<or> X \<in> initState"
          by (metis list.set_intros(1) old.unit.exhaust surjective)
      next
        assume "X\<in>(knows x2)"
        thus "\<exists>A B. \<lparr>Sender = A, Receiver = B, Message = X\<rparr> \<in> set (x1 # x2) \<or> X \<in> initState"
          using Cons.IH by auto
      qed
    qed
  qed
qed

lemmas analz_impI = impI [where P = "Y \<notin> analz (knows evs)"] for Y evs

lemmas syan_impI = impI [where P = "Y \<notin> synth (analz (knows evs))"] for Y evs

lemma initState_subset_knows: "initState \<subseteq> knows evs"
apply (induct_tac evs, simp) 
apply (blast intro: knows_Spy_subset_knows_Spy_Says [THEN subsetD])
done

lemma spies_pubK[iff]: "Key (pubK A) \<in> knows evs"
  by (induct evs) (simp_all add: imageI)

lemmas [iff] = spies_pubK [THEN analz.Inj]

subsection\<open>Function used\<close>

fun used :: "event list \<Rightarrow> msg set" where
  used_Nil:   "used []         = parts initState" |
  used_Cons:  "used (ev # evs) = (parts {Message ev } \<union> used evs)"

lemma Nonce_notin_used_empty[simp]: "Nonce N \<notin> used []" by simp

lemma Says_imp_used [rule_format]: "ev \<in> set evs \<longrightarrow> Message ev \<in> used evs"
proof (induction rule: list.induct)
  case Nil
  then show ?case by simp
next
  case (Cons x1 x2)
  show ?case
  proof
    assume "ev \<in> set (x1 # x2)"
    hence "ev = x1 \<or> ev \<in> set x2" by simp
    thus "Message ev \<in> used (x1 # x2)"
    proof
      assume "ev = x1"
      thus "Message ev \<in> used (x1 # x2)" by auto
    next
      assume "ev \<in> set x2"
      with Cons.IH have "Message ev \<in> used x2" by simp
      thus "Message ev \<in> used (x1 # x2)" by auto
    qed
  qed
qed

lemma parts_knows_Spy_subset_used: "parts (knows evs) \<subseteq> used evs"
proof (induction rule: list.induct)
  case Nil
  then show ?case
  proof
    fix x assume "x \<in> parts (knows[])"
    hence "x \<in> parts initState" by simp
    moreover have "used [] = parts initState" by simp
    ultimately show "x\<in>used []" by blast
  qed
next
  case (Cons x1 x2)
  thus "parts (knows (x1 # x2)) \<subseteq> used (x1 # x2)"
    by (metis (no_types, lifting) Event.knows_Cons Event.used_Cons Un_assoc Un_upper1 parts_insert subset_Un_eq)
qed

lemmas usedI = parts_knows_Spy_subset_used [THEN subsetD, intro]

lemma Nonce_supply_lemma: "\<exists>N. \<forall>n. N\<le>n \<longrightarrow> Nonce n \<notin> used evs"
apply (induct_tac "evs")
apply (rule_tac x = 0 in exI)
apply (simp_all (no_asm_simp))
apply safe
apply (rule msg_Nonce_supply [THEN exE], blast elim!: add_leE)+
done

lemma Nonce_supply1: "\<exists>N. Nonce N \<notin> used evs"
by (rule Nonce_supply_lemma [THEN exE], blast)

lemma Nonce_supply: "Nonce (SOME N. Nonce N \<notin> used evs) \<notin> used evs"
apply (rule Nonce_supply_lemma [THEN exE])
apply (rule someI, fast)
done

end