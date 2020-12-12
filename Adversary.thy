section\<open>Modelling the Adversary\<close>

theory Adversary imports Message begin

subsection\<open>Analysis\<close>

inductive_set
  analz :: "msg set \<Rightarrow> msg set"
  for H :: "msg set"
  where
    Inj [intro,simp] : "X \<in> H \<Longrightarrow> X \<in> analz H"
  | Fst:     "\<lbrace>X,Y\<rbrace> \<in> analz H \<Longrightarrow> X \<in> analz H"
  | Snd:     "\<lbrace>X,Y\<rbrace> \<in> analz H \<Longrightarrow> Y \<in> analz H"
  | Decrypt [dest]: 
             "\<lbrakk>Crypt K X \<in> analz H; Key(invKey K) \<in> analz H\<rbrakk>
              \<Longrightarrow> X \<in> analz H"

lemma analz_mono: "G\<subseteq>H \<Longrightarrow> analz(G) \<subseteq> analz(H)"
apply auto
apply (erule analz.induct) 
apply (auto dest: analz.Fst analz.Snd) 
done

lemma MPair_analz [elim!]: "\<lbrakk> \<lbrace>X,Y\<rbrace> \<in> analz H; \<lbrakk>X \<in> analz H; Y \<in> analz H \<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (blast dest: analz.Fst analz.Snd)

lemma analz_increasing: "H \<subseteq> analz(H)"
by blast

lemma analz_subset_parts: "analz H \<subseteq> parts H"
apply (rule subsetI)
apply (erule analz.induct, blast+)
done

lemmas analz_into_parts = analz_subset_parts [THEN subsetD]

lemmas not_parts_not_analz = analz_subset_parts [THEN contra_subsetD]

lemma parts_analz [simp]: "parts (analz H) = parts H"
apply (rule equalityI)
apply (rule analz_subset_parts [THEN parts_mono, THEN subset_trans], simp)
apply (blast intro: analz_increasing [THEN parts_mono, THEN subsetD])
done

lemma analz_parts [simp]: "analz (parts H) = parts H"
apply auto
apply (erule analz.induct, auto)
done

lemmas analz_insertI = subset_insertI [THEN analz_mono, THEN [2] rev_subsetD]

lemma analz_empty [simp]: "analz{} = {}"
apply safe
apply (erule analz.induct, blast+)
done

lemma analz_Un: "analz(G) \<union> analz(H) \<subseteq> analz(G \<union> H)"
by (intro Un_least analz_mono Un_upper1 Un_upper2)

lemma analz_insert: "insert X (analz H) \<subseteq> analz(insert X H)"
by (blast intro: analz_mono [THEN [2] rev_subsetD])

lemmas analz_insert_eq_I = equalityI [OF subsetI analz_insert]

lemma analz_insert_Agent [simp]:
     "analz (insert (Agent agt) H) = insert (Agent agt) (analz H)"
apply (rule analz_insert_eq_I) 
apply (erule analz.induct, auto) 
done

lemma analz_insert_Nonce [simp]:
     "analz (insert (Nonce N) H) = insert (Nonce N) (analz H)"
apply (rule analz_insert_eq_I) 
apply (erule analz.induct, auto) 
done

lemma analz_insert_Key [simp]: 
    "K \<notin> keysFor (analz H) \<Longrightarrow>   
          analz (insert (Key K) H) = insert (Key K) (analz H)"
apply (unfold keysFor_def)
apply (rule analz_insert_eq_I) 
apply (erule analz.induct, auto) 
done

lemma analz_insert_MPair [simp]:
     "analz (insert \<lbrace>X,Y\<rbrace> H) =  
          insert \<lbrace>X,Y\<rbrace> (analz (insert X (insert Y H)))"
apply (rule equalityI)
apply (rule subsetI)
apply (erule analz.induct, auto)
apply (erule analz.induct)
apply (blast intro: analz.Fst analz.Snd)+
done

lemma analz_insert_Crypt:
     "Key (invKey K) \<notin> analz H 
      \<Longrightarrow> analz (insert (Crypt K X) H) = insert (Crypt K X) (analz H)"
apply (rule analz_insert_eq_I) 
apply (erule analz.induct, auto) 
done

lemma lemma1: "Key (invKey K) \<in> analz H \<Longrightarrow>   
               analz (insert (Crypt K X) H) \<subseteq>  
               insert (Crypt K X) (analz (insert X H))"
apply (rule subsetI)
apply (erule_tac x = x in analz.induct, auto)
done

lemma lemma2: "Key (invKey K) \<in> analz H \<Longrightarrow>   
               insert (Crypt K X) (analz (insert X H)) \<subseteq>  
               analz (insert (Crypt K X) H)"
apply auto
apply (erule_tac x = x in analz.induct, auto)
apply (blast intro: analz_insertI analz.Decrypt)
done

lemma analz_insert_Decrypt:
     "Key (invKey K) \<in> analz H \<Longrightarrow>   
               analz (insert (Crypt K X) H) =  
               insert (Crypt K X) (analz (insert X H))"
by (intro equalityI lemma1 lemma2)

lemma analz_Crypt_if [simp]:
     "analz (insert (Crypt K X) H) =                 
          (if (Key (invKey K) \<in> analz H)                 
           then insert (Crypt K X) (analz (insert X H))  
           else insert (Crypt K X) (analz H))"
by (simp add: analz_insert_Crypt analz_insert_Decrypt)

lemma analz_insert_Crypt_subset:
     "analz (insert (Crypt K X) H) \<subseteq>   
           insert (Crypt K X) (analz (insert X H))"
apply (rule subsetI)
apply (erule analz.induct, auto)
done

lemma analz_image_Key [simp]: "analz (Key`N) = Key`N"
apply auto
apply (erule analz.induct, auto)
done

lemma analz_analzD [dest!]: "X\<in> analz (analz H) \<Longrightarrow> X\<in> analz H"
by (erule analz.induct, blast+)

lemma analz_idem [simp]: "analz (analz H) = analz H"
by blast

lemma analz_subset_iff [simp]: "(analz G \<subseteq> analz H) = (G \<subseteq> analz H)"
apply (rule iffI)
apply (iprover intro: subset_trans analz_increasing)  
apply (frule analz_mono, simp) 
done

lemma analz_trans: "\<lbrakk>X\<in> analz G;  G \<subseteq> analz H \<rbrakk> \<Longrightarrow> X\<in> analz H"
by (drule analz_mono, blast)

lemma analz_cut: "\<lbrakk>Y\<in> analz (insert X H);  X\<in> analz H \<rbrakk> \<Longrightarrow> Y\<in> analz H"
by (erule analz_trans, blast)

lemma analz_insert_eq: "X\<in> analz H \<Longrightarrow> analz (insert X H) = analz H"
by (blast intro: analz_cut analz_insertI)

lemma analz_subset_cong:
     "\<lbrakk> analz G \<subseteq> analz G'; analz H \<subseteq> analz H'\<rbrakk>
      \<Longrightarrow> analz (G \<union> H) \<subseteq> analz (G' \<union> H')"
apply simp
apply (iprover intro: conjI subset_trans analz_mono Un_upper1 Un_upper2) 
done

lemma analz_cong:
     "\<lbrakk>analz G = analz G'; analz H = analz H'\<rbrakk> 
      \<Longrightarrow> analz (G \<union> H) = analz (G' \<union> H')"
by (intro equalityI analz_subset_cong, simp_all) 

lemma analz_insert_cong:
     "analz H = analz H' \<Longrightarrow> analz(insert X H) = analz(insert X H')"
by (force simp only: insert_def intro!: analz_cong)

lemma analz_trivial:
     "[| \<forall>X Y. \<lbrace>X,Y\<rbrace> \<notin> H;  \<forall>X K. Crypt K X \<notin> H |] ==> analz H = H"
apply safe
apply (erule analz.induct, blast+)
done

lemma analz_UN_analz_lemma:
     "X\<in> analz (\<Union>i\<in>A. analz (H i)) \<Longrightarrow> X\<in> analz (\<Union>i\<in>A. H i)"
apply (erule analz.induct)
apply (blast intro: analz_mono [THEN [2] rev_subsetD])+
done

lemma analz_UN_analz [simp]: "analz (\<Union>i\<in>A. analz (H i)) = analz (\<Union>i\<in>A. H i)"
by (blast intro: analz_UN_analz_lemma analz_mono [THEN [2] rev_subsetD])

lemma gen_analz_insert_eq [rule_format]:
     "X \<in> analz H \<Longrightarrow> \<forall>G. H \<subseteq> G \<longrightarrow> analz (insert X G) = analz G"
by (blast intro: analz_cut analz_insertI analz_mono [THEN [2] rev_subsetD])

lemma analz_analz_Un [simp]: "analz (analz G \<union> H) = analz (G \<union> H)"
apply (intro equalityI analz_subset_cong)+
apply simp_all
done

subsubsection\<open>Combinations of parts and analz\<close>

lemma analz_conj_parts [simp]:
     "(X \<in> analz H & X \<in> parts H) = (X \<in> analz H)"
by (blast intro: analz_subset_parts [THEN subsetD])

lemma analz_disj_parts [simp]:
     "(X \<in> analz H | X \<in> parts H) = (X \<in> parts H)"
by (blast intro: analz_subset_parts [THEN subsetD])

subsection\<open>Synthesis\<close>

inductive_set
  synth :: "msg set \<Rightarrow> msg set"
  for H :: "msg set"
  where
    Inj    [intro]: "X \<in> H \<Longrightarrow> X \<in> synth H"
  | Agent  [intro]: "Agent agt \<in> synth H"
  | MPair  [intro]:
              "\<lbrakk>X \<in> synth H;  Y \<in> synth H\<rbrakk> \<Longrightarrow> \<lbrace>X,Y\<rbrace> \<in> synth H"
  | Crypt  [intro]:
              "\<lbrakk>X \<in> synth H;  Key K \<in> H\<rbrakk> \<Longrightarrow> Crypt K X \<in> synth H"
lemma synth_mono: "G\<subseteq>H \<Longrightarrow> synth(G) \<subseteq> synth(H)"
  by (auto, erule synth.induct, auto)  

inductive_cases Key_synth   [elim!]: "Key K \<in> synth H"
inductive_cases MPair_synth [elim!]: "\<lbrace>X,Y\<rbrace> \<in> synth H"
inductive_cases Crypt_synth [elim!]: "Crypt K X \<in> synth H"
inductive_cases Nonce_synth [elim!]: "Nonce n \<in> synth H"

lemma synth_increasing: "H \<subseteq> synth(H)"
by blast

lemma synth_Un: "synth(G) \<union> synth(H) \<subseteq> synth(G \<union> H)"
by (intro Un_least synth_mono Un_upper1 Un_upper2)

lemma synth_insert: "insert X (synth H) \<subseteq> synth(insert X H)"
by (blast intro: synth_mono [THEN [2] rev_subsetD])

lemma synth_synthD [dest!]: "X\<in> synth (synth H) \<Longrightarrow> X\<in> synth H"
by (erule synth.induct, blast+)

lemma synth_idem: "synth (synth H) = synth H"
by blast

lemma synth_subset_iff [simp]: "(synth G \<subseteq> synth H) = (G \<subseteq> synth H)"
apply (rule iffI)
apply (iprover intro: subset_trans synth_increasing)  
apply (frule synth_mono, simp add: synth_idem) 
done

lemma synth_trans: "\<lbrakk>X\<in> synth G;  G \<subseteq> synth H\<rbrakk> \<Longrightarrow> X\<in> synth H"
by (drule synth_mono, blast)

lemma synth_cut: "\<lbrakk> Y\<in> synth (insert X H);  X\<in> synth H \<rbrakk> \<Longrightarrow> Y\<in> synth H"
by (erule synth_trans, blast)

lemma Nonce_synth_eq [simp]: "(Nonce N \<in> synth H) = (Nonce N \<in> H)"
by blast

lemma Key_synth_eq [simp]: "(Key K \<in> synth H) = (Key K \<in> H)"
by blast

lemma Crypt_synth_eq [simp]:
     "Key K \<notin> H \<Longrightarrow> (Crypt K X \<in> synth H) = (Crypt K X \<in> H)"
by blast

lemma keysFor_synth [simp]: 
    "keysFor (synth H) = keysFor H \<union> invKey`{K. Key K \<in> H}"
by (unfold keysFor_def, blast)

subsubsection\<open>Combinations of parts and synth\<close>

lemma parts_synth [simp]: "parts (synth H) = parts H \<union> synth H"
apply (rule equalityI)
apply (rule subsetI)
apply (erule parts.induct)
apply (blast intro: synth_increasing [THEN parts_mono, THEN subsetD] 
                    parts.Fst parts.Snd parts.Body)+
done

lemma keysFor_parts_insert:
     "[| K \<in> keysFor (parts (insert X G));  X \<in> synth (analz H) |] 
      ==> K \<in> keysFor (parts (G \<union> H)) | Key (invKey K) \<in> parts H" 
by (force 
    dest!: parts_insert_subset_Un [THEN keysFor_mono, THEN [2] rev_subsetD]
           analz_subset_parts [THEN keysFor_mono, THEN [2] rev_subsetD]
    intro: analz_subset_parts [THEN subsetD] parts_mono [THEN [2] rev_subsetD])

subsubsection\<open>Combinations of analz and synth\<close>

lemma analz_synth_Un [simp]: "analz (synth G \<union> H) = analz (G \<union> H) \<union> synth G"
apply (rule equalityI)
apply (rule subsetI)
apply (erule analz.induct)
prefer 5 apply (blast intro: analz_mono [THEN [2] rev_subsetD])
apply (blast intro: analz.Fst analz.Snd analz.Decrypt)+
done

lemma analz_synth [simp]: "analz (synth H) = analz H \<union> synth H"
apply (cut_tac H = "{}" in analz_synth_Un)
apply (simp (no_asm_use))
done

lemma Fake_analz_insert:
     "X \<in> synth (analz G) \<Longrightarrow>  
      analz (insert X H) \<subseteq> synth (analz G) \<union> analz (G \<union> H)"
apply (rule subsetI)
apply (subgoal_tac "x \<in> analz (synth (analz G) \<union> H) ")
prefer 2 apply (blast intro: analz_mono [THEN [2] rev_subsetD] analz_mono [THEN synth_mono, THEN [2] rev_subsetD])
apply (simp (no_asm_use))
apply blast
done

lemma MPair_synth_analz [iff]:
     "(\<lbrace>X,Y\<rbrace> \<in> synth (analz H)) =  
      (X \<in> synth (analz H) & Y \<in> synth (analz H))"
by blast

lemma synth_analz_mono: "G\<subseteq>H \<Longrightarrow> synth (analz(G)) \<subseteq> synth (analz(H))"
by (iprover intro: synth_mono analz_mono) 

lemma Fake_analz_eq [simp]:
     "X \<in> synth(analz H) \<Longrightarrow> synth (analz (insert X H)) = synth (analz H)"
apply (drule Fake_analz_insert[of _ _ "H"])
apply (simp add: synth_increasing[THEN Un_absorb2])
apply (drule synth_mono)
apply (simp add: synth_idem)
apply (rule equalityI)
apply (simp add: )
apply (rule synth_analz_mono, blast)   
done

lemma synth_analz_insert_eq [rule_format]:
     "X \<in> synth (analz H) 
      \<Longrightarrow> \<forall>G. H \<subseteq> G \<longrightarrow> (Key K \<in> analz (insert X G)) = (Key K \<in> analz G)"
apply (erule synth.induct) 
apply (simp_all add: gen_analz_insert_eq subset_trans [OF _ subset_insertI]) 
done

lemma synth_analz_idem [simp]: "synth (analz (synth (analz X)))=synth (analz X)"
  by (simp add: sup_absorb2 synth_idem synth_increasing)

subsubsection\<open>Combinations of parts, analz, and synth\<close>

lemma Fake_parts_insert: "X \<in> synth (analz H) \<Longrightarrow> parts (insert X H) \<subseteq> synth (analz H) \<union> parts H"
apply (drule parts_insert_subset_Un)
apply (simp (no_asm_use))
apply blast
done

lemma Fake_parts_insert_in_Un:
     "\<lbrakk>Z \<in> parts (insert X H);  X \<in> synth (analz H)\<rbrakk>
      \<Longrightarrow> Z \<in>  synth (analz H) \<union> parts H"
by (blast dest: Fake_parts_insert  [THEN subsetD])

lemma Crypt_synth_analz:
     "\<lbrakk> Key K \<in> analz H;  Key (invKey K) \<in> analz H \<rbrakk>
       \<Longrightarrow> (Crypt K X \<in> synth (analz H)) = (X \<in> synth (analz H))"
by blast

lemma Fake_parts_sing:
     "X \<in> synth (analz H) \<Longrightarrow> parts{X} \<subseteq> synth (analz H) \<union> parts H"
apply (rule subset_trans) 
 apply (erule_tac [2] Fake_parts_insert)
apply (rule parts_mono, blast)
  done

lemmas Fake_parts_sing_imp_Un = Fake_parts_sing [THEN [2] rev_subsetD]

declare parts.Body [rule del]

end