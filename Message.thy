section \<open>Agents and Messages\<close>

theory Message imports Main begin

datatype agent = Friend nat | Spy

subsection \<open>Public Key Cryptography\<close>

type_synonym key = nat

lemma insert_Key_singleton: "insert (Key K) H = Key ` {K} \<union> H" by blast

lemma insert_Key_image: "insert (Key K) (Key`KK \<union> C) = Key ` (insert K KK) \<union> C" by blast

consts pubK :: "agent \<Rightarrow> key"
axiomatization where
  inj_pubK:        "inj pubK"

lemmas [iff] = inj_pubK [THEN inj_eq]

lemma pubK_image_eq[simp]: "(pubK x \<in> pubK`A) = (x\<in>A)"
  by auto

consts invKey :: "key \<Rightarrow> key"
axiomatization where
  invKey [simp]: "invKey (invKey K) = K"

lemma inj_inv [simp]: "inj invKey"
proof (rule ccontr)
  assume "\<not> inj invKey"
  hence "\<exists>k k'. k\<noteq>k' \<and> invKey k=invKey k'" by (meson injI)
  then obtain k k' where "k\<noteq>k'" and "invKey k=invKey k'" by blast
  hence "invKey (invKey k) = invKey (invKey k')" by simp
  with invKey have "k=k'" by simp
  with `k\<noteq>k'` show False .. 
qed

lemmas [iff] = inj_inv [THEN inj_eq]

lemma invKey_image_eq[simp]: "(invKey x \<in> invKey ` A) = (x\<in>A)"
  by auto

abbreviation priK :: "agent \<Rightarrow> key"
  where "priK x  \<equiv>  invKey (pubK x)"
axiomatization where
  priK_neq_pubK:   "priK A \<noteq> pubK B"

declare o_def [simp]
lemma inj_priK: "inj priK" using inj_compose[OF inj_inv inj_pubK]
  by simp
lemmas [iff] = inj_priK [THEN inj_eq]
lemmas [iff] = priK_neq_pubK priK_neq_pubK [THEN not_sym]

lemma priK_pubK_image_eq[simp]: "(priK x \<notin> pubK`A)"
  by auto

subsection \<open>Messages\<close>

datatype msg = Agent  agent
             | Nonce  nat
             | Key    key
             | MPair  msg msg
             | Crypt  key msg

lemma Friend_image_eq [simp]: "(Friend x \<in> Friend`A) = (x\<in>A)"
  by auto

lemma Key_image_eq [simp]: "(Key x \<in> Key`A) = (x\<in>A)"
  by auto

lemma Nonce_Key_image_eq [simp]: "(Nonce x \<notin> Key`A)"
  by auto

lemma Crypt_notin_image_Key [simp]: "Crypt K X \<notin> Key ` A"
  by auto

abbreviation initState::"msg set" where
"initState \<equiv> insert (Key (priK Spy)) (Key ` range pubK)"

syntax
  "_MTuple"      :: "['a, args] \<Rightarrow> 'a * 'b"       ("(2\<lbrace>_,/ _\<rbrace>)")
translations
  "\<lbrace>x, y, z\<rbrace>"   == "\<lbrace>x, \<lbrace>y, z\<rbrace>\<rbrace>"
  "\<lbrace>x, y\<rbrace>"      == "CONST MPair x y"

subsubsection \<open>Keys useful for decryption\<close>

definition keysFor :: "msg set \<Rightarrow> key set" where
  "keysFor H == invKey ` {K. \<exists>X. Crypt K X \<in> H}"

lemma keysFor_empty [simp]: "keysFor {} = {}"
by (unfold keysFor_def, blast)

lemma keysFor_Un [simp]: "keysFor (H \<union> H') = keysFor H \<union> keysFor H'"
by (unfold keysFor_def, blast)

lemma keysFor_UN [simp]: "keysFor (\<Union>i\<in>A. H i) = (\<Union>i\<in>A. keysFor (H i))"
by (unfold keysFor_def, blast)

lemma keysFor_mono: "G \<subseteq> H \<Longrightarrow> keysFor(G) \<subseteq> keysFor(H)"
by (unfold keysFor_def, blast)

lemma keysFor_insert_Agent [simp]: "keysFor (insert (Agent A) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Nonce [simp]: "keysFor (insert (Nonce N) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Key [simp]: "keysFor (insert (Key K) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_MPair [simp]: "keysFor (insert \<lbrace>X,Y\<rbrace> H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Crypt [simp]: 
    "keysFor (insert (Crypt K X) H) = insert (invKey K) (keysFor H)"
by (unfold keysFor_def, auto)

lemma keysFor_image_Key [simp]: "keysFor (Key`E) = {}"
by (unfold keysFor_def, auto)

lemma Crypt_imp_invKey_keysFor: "Crypt K X \<in> H \<Longrightarrow> invKey K \<in> keysFor H"
by (unfold keysFor_def, blast)

subsubsection \<open>Parts\<close>

inductive_set
  parts :: "msg set \<Rightarrow> msg set"
  for H :: "msg set"
  where
    Inj [intro]:               "X \<in> H \<Longrightarrow> X \<in> parts H"
  | Fst:         "\<lbrace>X,Y\<rbrace>   \<in> parts H \<Longrightarrow> X \<in> parts H"
  | Snd:         "\<lbrace>X,Y\<rbrace>   \<in> parts H \<Longrightarrow> Y \<in> parts H"
  | Body:        "Crypt K X \<in> parts H \<Longrightarrow> X \<in> parts H"

lemma parts_mono:
  assumes "G \<subseteq> H"
  shows "parts(G) \<subseteq> parts(H)"
proof
  fix x
  assume "x \<in> parts(G)"
  then show "x \<in> parts(H)"
  proof (induction rule: parts.induct)
    case (Inj X)
    then show ?case using assms by auto
  next
    case (Fst X Y)
    then show ?case using parts.Fst by simp
  next
    case (Snd X Y)
    then show ?case using parts.Snd by simp
  next
    case (Body K X)
    then show ?case using parts.Body by simp
  qed
qed
  
lemma MPair_parts: "\<lbrakk> \<lbrace>X,Y\<rbrace> \<in> parts H; \<lbrakk> X \<in> parts H; Y \<in> parts H \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by (blast dest: parts.Fst parts.Snd) 

declare MPair_parts [elim!]  parts.Body [dest!]

lemma parts_increasing: "H \<subseteq> parts(H)" by blast

lemmas parts_insertI = subset_insertI [THEN parts_mono, THEN subsetD]

lemma parts_empty [simp]: "parts {} = {}"
proof
    show "parts {} \<subseteq> {}"
    proof
      fix x
      assume "x \<in> parts {}"
      hence False
      proof (induction rule: parts.induct)
        fix X assume "X \<in> {}" thus False by simp
      next
        fix X Y assume "\<lbrace>X, Y\<rbrace> \<in> parts {}" and False thus False ..
      next
        fix X Y assume "\<lbrace>X, Y\<rbrace> \<in> parts {}" and "False" thus False ..
      next 
        fix K X assume "Crypt K X \<in> parts {}" and False thus False ..
      qed
      thus "x \<in> {}" ..
    qed
  next
    show "{} \<subseteq> parts {}" ..
qed

lemma parts_emptyE [elim!]: "X\<in> parts{} \<Longrightarrow> P" by simp

lemma parts_singleton: "X\<in> parts H \<Longrightarrow> \<exists>Y\<in>H. X\<in> parts {Y}" by (erule parts.induct, fast+)

lemma parts_Un_subset1: "parts(G) \<union> parts(H) \<subseteq> parts(G \<union> H)"
by (intro Un_least parts_mono Un_upper1 Un_upper2)

lemma parts_Un_subset2: "parts(G \<union> H) \<subseteq> parts(G) \<union> parts(H)"
proof
  fix x
  assume "x \<in> parts (G \<union> H)"
  thus "x \<in> parts G \<union> parts H"
  proof (induction rule: parts.induct)
    case (Inj X)
    then show ?case by auto
  next
    case (Fst X Y)
    then show ?case by auto
  next
    case (Snd X Y)
    then show ?case by auto
  next
    case (Body K X)
    then show ?case by auto
  qed
qed

lemma parts_Un [simp]: "parts(G \<union> H) = parts(G) \<union> parts(H)"
by (intro equalityI parts_Un_subset1 parts_Un_subset2)

lemma parts_insert: "parts (insert X H) = parts {X} \<union> parts H"
proof -
  from insert_is_Un have "insert X H = {X} \<union> H" by simp
  thus ?thesis by (simp only: parts_Un)
qed

lemma parts_insert2: "parts (insert X (insert Y H)) = parts {X} \<union> parts {Y} \<union> parts H"
proof -
  have "parts (insert X (insert Y H)) = parts {X} \<union> parts (insert Y H)" using parts_insert[of "X" "insert Y H"] by simp
  moreover have "parts (insert Y H) = parts {Y} \<union> parts H" using parts_insert by blast
  ultimately show ?thesis by auto
qed

lemma parts_UN_subset1: "(\<Union>x\<in>A. parts(H x)) \<subseteq> parts(\<Union>x\<in>A. H x)"
by (intro UN_least parts_mono UN_upper)

lemma parts_UN_subset2: "parts(\<Union>x\<in>A. H x) \<subseteq> (\<Union>x\<in>A. parts(H x))"
proof
  fix x
  assume "x \<in> parts (\<Union> (H ` A))"
  thus "x \<in> (\<Union>x\<in>A. parts (H x))"
  proof (induction rule: parts.induct)
    case (Inj X)
    then show ?case by auto
  next
    case (Fst X Y)
    then show ?case by auto
  next
    case (Snd X Y)
    then show ?case by auto
  next
    case (Body K X)
    then show ?case by auto
  qed
qed

lemma parts_UN [simp]: "parts(\<Union>x\<in>A. H x) = (\<Union>x\<in>A. parts(H x))"
by (intro equalityI parts_UN_subset1 parts_UN_subset2)

lemmas in_parts_UnE = parts_Un [THEN equalityD1, THEN subsetD, THEN UnE] 

declare in_parts_UnE [elim!]

lemma parts_insert_subset: "insert X (parts H) \<subseteq> parts(insert X H)"
by (blast intro: parts_mono [THEN [2] rev_subsetD])

lemma parts_partsD [dest!]: "X \<in> parts (parts H) \<Longrightarrow> X\<in> parts H"
by (erule parts.induct, blast+)

lemma parts_idem [simp]: "parts (parts H) = parts H"
by blast

lemma parts_subset_iff [simp]: "(parts G \<subseteq> parts H) = (G \<subseteq> parts H)"
proof
    assume "parts G \<subseteq> parts H"
    thus "G \<subseteq> parts H" by auto
  next
    assume "G \<subseteq> parts H"
    show "parts G \<subseteq> parts H"
      using \<open>G \<subseteq> parts H\<close> parts_mono by auto
qed

lemma parts_trans: "[| X\<in> parts G;  G \<subseteq> parts H |] ==> X\<in> parts H"
by (drule parts_mono, blast)

lemma parts_cut: "\<lbrakk> Y\<in> parts (insert X G);  X\<in> parts H \<rbrakk> \<Longrightarrow> Y\<in> parts (G \<union> H)" 
by (blast intro: parts_trans) 

lemma parts_cut_eq [simp]: "X\<in> parts H ==> parts (insert X H) = parts H"
by (force dest!: parts_cut intro: parts_insertI)

lemmas parts_insert_eq_I = equalityI [OF subsetI parts_insert_subset]

lemma parts_insert_Agent [simp]: "parts (insert (Agent agt) H) = insert (Agent agt) (parts H)"
proof (rule parts_insert_eq_I)
  fix x
  assume "x \<in> parts (insert (Agent agt) H)"
  thus "x \<in> insert (Agent agt) (parts H)"
  proof (induction rule:parts.induct)
    case (Inj X)
    then show ?case by auto
  next
    case (Fst X Y)
    then show ?case by auto
  next
    case (Snd X Y)
    then show ?case by auto
  next
    case (Body K X)
    then show ?case by auto
  qed
qed

lemma parts_insert_Nonce [simp]: "parts (insert (Nonce N) H) = insert (Nonce N) (parts H)"
proof (rule parts_insert_eq_I)
  fix x
  assume "x \<in> parts (insert (Nonce N) H)"
  thus "x \<in> insert (Nonce N) (parts H)"
  proof (induction rule:parts.induct)
    case (Inj X)
    then show ?case by auto
  next
    case (Fst X Y)
    then show ?case by auto
  next
    case (Snd X Y)
    then show ?case by auto
  next
    case (Body K X)
    then show ?case by auto
  qed
qed

lemma parts_insert_Key [simp]: "parts (insert (Key K) H) = insert (Key K) (parts H)"
proof (rule parts_insert_eq_I)
  fix x
  assume "x \<in> parts (insert (Key K) H)"
  thus "x \<in> insert (Key K) (parts H)"
  proof (induction rule:parts.induct)
    case (Inj X)
    then show ?case by auto
  next
    case (Fst X Y)
    then show ?case by auto
  next
    case (Snd X Y)
    then show ?case by auto
  next
    case (Body K X)
    then show ?case by auto
  qed
qed

lemma parts_insert_Crypt [simp]: "parts (insert (Crypt K X) H) = insert (Crypt K X) (parts (insert X H))"
proof
  show "parts (insert (Crypt K X) H) \<subseteq> insert (Crypt K X) (parts (insert X H))"
  proof
    fix x
    assume "x \<in> parts (insert (Crypt K X) H)"
    thus "x \<in> insert (Crypt K X) (parts (insert X H))"
    proof (induction rule:parts.induct)
      case (Inj X)
      then show ?case by auto
    next
      case (Fst X Y)
      then show ?case by auto
    next
      case (Snd X Y)
      then show ?case by auto
    next
      case (Body K X)
      then show ?case by auto
    qed
  qed
next 
  show "insert (Crypt K X) (parts (insert X H)) \<subseteq> parts (insert (Crypt K X) H)"
  proof
    fix x
    assume "x \<in> insert (Crypt K X) (parts (insert X H))"
    thus "x \<in> parts (insert (Crypt K X) H)"
    proof
      assume "x = Crypt K X"
      thus "x \<in> parts (insert (Crypt K X) H)" by (simp add: parts.Inj)
    next
      assume "x \<in> parts (insert X H)"
      thus "x \<in> parts (insert (Crypt K X) H)"
      proof (induction rule:parts.induct)
        case (Inj X)
        then show ?case by (metis insert_iff parts.simps)
      next
        case (Fst X Y)
        then show ?case by auto
      next
        case (Snd X Y)
        then show ?case by auto
      next
        case (Body K X)
        then show ?case by auto
      qed
    qed
  qed
qed

lemma parts_insert_MPair [simp]: "parts (insert \<lbrace>X,Y\<rbrace> H) = insert \<lbrace>X,Y\<rbrace> (parts (insert X (insert Y H)))"
proof
  show "parts (insert \<lbrace>X,Y\<rbrace> H) \<subseteq> insert \<lbrace>X,Y\<rbrace> (parts (insert X (insert Y H)))"
  proof
    fix x
    assume "x \<in>parts (insert \<lbrace>X,Y\<rbrace> H)"
    thus "x \<in> insert \<lbrace>X,Y\<rbrace> (parts (insert X (insert Y H)))"
    proof (induction rule:parts.induct)
      case (Inj X)
      then show ?case by auto
    next
      case (Fst X Y)
      then show ?case by auto
    next
      case (Snd X Y)
      then show ?case by auto
    next
      case (Body K X)
      then show ?case by auto
    qed
  qed
next 
  show "insert \<lbrace>X,Y\<rbrace> (parts (insert X (insert Y H))) \<subseteq> parts (insert \<lbrace>X,Y\<rbrace> H)"
  proof
    fix x
    assume "x \<in> insert \<lbrace>X,Y\<rbrace> (parts (insert X (insert Y H)))"
    thus "x \<in> parts (insert \<lbrace>X,Y\<rbrace> H)"
    proof
      assume "x = \<lbrace>X,Y\<rbrace>"
      thus "x \<in> parts (insert \<lbrace>X,Y\<rbrace> H)" by (simp add: parts.Inj)
    next
      assume "x \<in> parts (insert X (insert Y H))"
      thus "x \<in> parts (insert \<lbrace>X,Y\<rbrace> H)"
      proof (induction rule:parts.induct)
        case (Inj X)
        then show ?case by (metis insert_iff parts.simps)
      next
        case (Fst X Y)
        then show ?case by auto
      next
        case (Snd X Y)
        then show ?case by auto
      next
        case (Body K X)
        then show ?case by auto
      qed
    qed
  qed
qed

lemma parts_image_Key [simp]: "parts (Key`N) = Key`N"
proof
  show "parts (Key ` N) \<subseteq> Key ` N"
  proof
    fix x
    assume "x \<in> parts (Key ` N)"
    thus "x \<in> Key ` N"
    proof (induction rule:parts.induct)
      case (Inj X)
      then show ?case by simp
    next
      case (Fst X Y)
      then show ?case by auto
    next
      case (Snd X Y)
      then show ?case by auto
    next
      case (Body K X)
      then show ?case by auto
    qed
  qed
  next
  show "Key ` N \<subseteq> parts (Key ` N)" by auto
qed

lemma msg_Nonce_supply: "\<exists>N. \<forall>n. N\<le>n \<longrightarrow> Nonce n \<notin> parts {msg}"
proof (induction)
  case (Agent x)
  then show ?case by simp
next
  case (Nonce x)
  have "\<forall>n\<ge>Suc x. Nonce n \<notin> parts {Nonce x}" by simp
  thus ?case by blast
next
  case (Key x)
  then show ?case by simp
next
  case (MPair x1a x2a)
  then obtain n1 n2 where "\<forall>n\<ge>n1. Nonce n \<notin> parts {x1a}"
  and "\<forall>n\<ge>n2. Nonce n \<notin> parts {x2a}" by auto
  hence "\<forall>n\<ge>n1 + n2. Nonce n \<notin> parts {x1a} \<and> Nonce n \<notin> parts {x2a}" by simp
  moreover have "parts {x1a, x2a} = parts {x1a} \<union> parts {x2a}" using parts_insert by blast
  ultimately show ?case by auto
next
  case (Crypt x1a x2a)
  then show ?case by simp
qed

lemma parts_insert_subset_Un: "X \<in> G \<Longrightarrow> parts(insert X H) \<subseteq> parts G \<union> parts H"
by (rule subset_trans [OF parts_mono parts_Un_subset2], blast)

end