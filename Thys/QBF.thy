theory QBF
imports Main
begin

  section \<open>Shallow Matrix\<close>
  
  type_synonym 'a valuation = "'a \<Rightarrow> bool"
  type_synonym 'a afml = "'a valuation \<Rightarrow> bool"

  definition sForall ("\<^bold>\<forall>_. _" 80) where "\<^bold>\<forall>x. \<phi> \<equiv> \<lambda>\<sigma>. \<forall>v. \<phi> (\<sigma>(x:=v))"
  definition sExists ("\<^bold>\<exists>_. _" 80) where "\<^bold>\<exists>x. \<phi> \<equiv> \<lambda>\<sigma>. \<exists>v. \<phi> (\<sigma>(x:=v))"
  definition sAnd (infixr "\<^bold>\<and>" 95) where "\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2 \<equiv> \<lambda>\<sigma>. \<phi>\<^sub>1 \<sigma> \<and> \<phi>\<^sub>2 \<sigma>"
  definition sOr (infixr "\<^bold>\<or>" 90) where "\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2 \<equiv> \<lambda>\<sigma>. \<phi>\<^sub>1 \<sigma> \<or> \<phi>\<^sub>2 \<sigma>"
  definition sNot ("\<^bold>\<not>_" [100] 100) where "sNot \<phi>\<^sub>1 \<equiv> \<lambda>\<sigma>. \<not> \<phi>\<^sub>1 \<sigma>"
  
  definition "Pos x \<equiv> \<lambda>\<sigma>::_ \<Rightarrow> bool. \<sigma> x"
  abbreviation "Neg x \<equiv> \<^bold>\<not>Pos x"
  
  
  lemma not_not[simp]:
    "\<^bold>\<not>\<^bold>\<not>\<phi> = \<phi>" 
    by (auto simp: sNot_def)
  
  lemma push_not_qs: 
    "\<^bold>\<not>(\<^bold>\<forall>x. \<phi>) = \<^bold>\<exists>x. \<^bold>\<not>\<phi>"
    "\<^bold>\<not>(\<^bold>\<exists>x. \<phi>) = \<^bold>\<forall>x. \<^bold>\<not>\<phi>"
    unfolding sNot_def sForall_def sExists_def by auto
  
  lemma push_not_cd:   
    "\<^bold>\<not>(\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) = \<^bold>\<not>\<phi>\<^sub>1 \<^bold>\<or> \<^bold>\<not>\<phi>\<^sub>2"
    unfolding sNot_def sAnd_def sOr_def by auto

  lemmas to_nnf = push_not_qs push_not_cd
  lemmas to_nnf' = not_not push_not_qs push_not_cd

  lemma or_assoc[simp]: "(a \<^bold>\<or> b) \<^bold>\<or> c = a \<^bold>\<or> b \<^bold>\<or> c"
    by (auto simp: sAnd_def sOr_def)

  lemma and_assoc[simp]: "(a \<^bold>\<and> b) \<^bold>\<and> c = a \<^bold>\<and> b \<^bold>\<and> c"
    by (auto simp: sAnd_def sOr_def)
    
  lemma or_commute[simp]: "(a \<^bold>\<or> b) = (b \<^bold>\<or> a)"  
    by (auto simp: sAnd_def sOr_def)
    
  lemma and_commute[simp]: "(a \<^bold>\<and> b) = (b \<^bold>\<and> a)"  
    by (auto simp: sAnd_def sOr_def)
    
  thm add.left_commute        

  lemma de_morgan_cnf: 
    "a \<^bold>\<or> (b \<^bold>\<and> c) = (a \<^bold>\<or> b) \<^bold>\<and> (a \<^bold>\<or> c)"
    "(a \<^bold>\<and> b) \<^bold>\<or> c = (a \<^bold>\<or> c) \<^bold>\<and> (b \<^bold>\<or> c)"
    by (auto simp: sAnd_def sOr_def)
  
  lemma de_morgan_dnf: 
    "a \<^bold>\<and> (b \<^bold>\<or> c) = (a \<^bold>\<and> b) \<^bold>\<or> (a \<^bold>\<and> c)"
    "(a \<^bold>\<or> b) \<^bold>\<and> c = (a \<^bold>\<and> c) \<^bold>\<or> (b \<^bold>\<and> c)"
    by (auto simp: sAnd_def sOr_def)
    
  lemmas to_cnf = to_nnf de_morgan_cnf
  lemmas to_dnf = to_nnf de_morgan_dnf

  lemma forall_distrib_and: "(\<^bold>\<forall>x. \<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) = (\<^bold>\<forall>x. \<phi>\<^sub>1) \<^bold>\<and> (\<^bold>\<forall>x. \<phi>\<^sub>2)"
    by (auto simp: sAnd_def sForall_def)
  
  lemma exists_distrib_or: "(\<^bold>\<exists>x. \<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) = (\<^bold>\<exists>x. \<phi>\<^sub>1) \<^bold>\<or> (\<^bold>\<exists>x. \<phi>\<^sub>2)"
    by (auto simp: sOr_def sExists_def)
  
  lemma forall_commute[simp]: "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<phi>) = (\<^bold>\<forall>y. \<^bold>\<forall>x. \<phi>)"  
    apply (auto simp: sForall_def)
    by (metis fun_upd_twist)
  
  lemma exists_commute[simp]: "(\<^bold>\<exists>x. \<^bold>\<exists>y. \<phi>) = (\<^bold>\<exists>y. \<^bold>\<exists>x. \<phi>)"  
    apply (auto simp: sExists_def)
    by (metis fun_upd_twist)
    
  lemma quant_dup[simp]: 
    "(\<^bold>\<forall>x. \<^bold>\<forall>x. \<phi>) = \<^bold>\<forall>x. \<phi>"
    "(\<^bold>\<exists>x. \<^bold>\<exists>x. \<phi>) = \<^bold>\<exists>x. \<phi>"
    "(\<^bold>\<exists>x. \<^bold>\<forall>x. \<phi>) = \<^bold>\<forall>x. \<phi>"  
    "(\<^bold>\<forall>x. \<^bold>\<exists>x. \<phi>) = \<^bold>\<exists>x. \<phi>"
    by (auto simp: sForall_def sExists_def)
    
    
  term "\<^bold>\<forall>x. \<^bold>\<exists>y. Pos x \<^bold>\<and> Neg y"
  
  
  definition "is_dep X \<phi> \<equiv> \<forall>\<sigma>\<^sub>1 \<sigma>\<^sub>2. (\<forall>x\<in>X. \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x) \<longrightarrow> \<phi> \<sigma>\<^sub>1 = \<phi> \<sigma>\<^sub>2"
  
  abbreviation "closed \<phi> \<equiv> is_dep {}"

  lemma is_deps_mono: "X \<subseteq> X' \<Longrightarrow> is_dep X \<phi> \<Longrightarrow> is_dep X' \<phi>"
    unfolding is_dep_def
    apply auto
    by blast
  
  lemma is_deps_not_eq[simp]: "is_dep X (\<^bold>\<not>\<phi>) \<longleftrightarrow> is_dep X \<phi>"    
    unfolding is_dep_def sNot_def by auto
  
  lemma is_deps_Pos[simp]: "is_dep X (Pos x) \<longleftrightarrow> x\<in>X"  
    unfolding is_dep_def Pos_def
    by auto

  (* Syntactic procedure to compute (overapproximation) of dependent variables *)    
  lemma is_depsI:
    "is_dep X \<phi> \<Longrightarrow> is_dep (X-{x}) (\<^bold>\<forall>x. \<phi>)"
    "is_dep X \<phi> \<Longrightarrow> is_dep (X-{x}) (\<^bold>\<exists>x. \<phi>)"
    "\<lbrakk>is_dep X\<^sub>1 \<phi>\<^sub>1; is_dep X\<^sub>2 \<phi>\<^sub>2 \<rbrakk> \<Longrightarrow> is_dep (X\<^sub>1\<union>X\<^sub>2) (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2)"
    "\<lbrakk>is_dep X\<^sub>1 \<phi>\<^sub>1; is_dep X\<^sub>2 \<phi>\<^sub>2 \<rbrakk> \<Longrightarrow> is_dep (X\<^sub>1\<union>X\<^sub>2) (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2)"
    "is_dep X \<phi> \<Longrightarrow> is_dep X (\<^bold>\<not>\<phi>)"
    "is_dep {x} (Pos x)"
    apply simp_all
    unfolding is_dep_def sForall_def sExists_def sAnd_def sOr_def
    subgoal by clarsimp (smt fun_upd_def insert_Diff_single insert_iff)
    subgoal by clarsimp (smt DiffD2 Diff_iff Diff_insert0 Diff_insert2 fun_upd_eqD fun_upd_other fun_upd_triv insert_Diff insert_iff)
    subgoal by clarsimp blast
    subgoal by clarsimp blast
    done

  
  definition is_indep1 :: "'a \<Rightarrow> 'a afml \<Rightarrow> bool" 
    where "is_indep1 x \<phi> \<equiv> \<forall>\<sigma> v. \<phi> (\<sigma>(x:=v)) = \<phi> \<sigma>"
  definition "is_indep X \<phi> \<equiv> \<forall>x\<in>X. is_indep1 x \<phi>"
  
  lemma is_indep1_upd[simp]: "is_indep1 x \<phi> \<Longrightarrow> \<phi>(\<sigma>(x:=v)) = \<phi> \<sigma>"
    unfolding is_indep1_def is_indep_def is_dep_def by auto
  
  lemma is_indep_simps[simp]:
    "is_indep {} \<phi>"
    "is_indep (insert x X) \<phi> \<longleftrightarrow> is_indep1 x \<phi> \<and> is_indep X \<phi>"
    "is_indep (X\<^sub>1 \<union> X\<^sub>2) \<phi> \<longleftrightarrow> is_indep X\<^sub>1 \<phi> \<and> is_indep X\<^sub>2 \<phi>"
    by (auto simp: is_indep_def is_dep_def is_indep1_def)


  lemma is_indep1_elim_all_conv: "is_indep1 x \<phi> \<longleftrightarrow> (\<^bold>\<forall>x. \<phi>) = \<phi>"  
    apply (auto simp: is_indep1_def sForall_def)
    apply (smt fun_upd_upd)
    by metis
    
      
  
  lemma is_indep1_Pos[simp]: "is_indep1 x (Pos y) \<longleftrightarrow> x\<noteq>y"  
    unfolding is_indep1_def Pos_def
    by auto
    
  lemma is_indep1_Not[simp]: "is_indep1 x (\<^bold>\<not>\<phi>) \<longleftrightarrow> is_indep1 x \<phi>"  
    unfolding is_indep1_def sNot_def
    by auto
    
  lemma is_indep1_ForallI: "is_indep1 x \<phi> \<Longrightarrow> is_indep1 x (\<^bold>\<forall>y. \<phi>)"
    unfolding is_indep1_elim_all_conv
    by (metis forall_commute)
    
  lemma is_indep1_ExistsI: "is_indep1 x \<phi> \<Longrightarrow> is_indep1 x (\<^bold>\<exists>y. \<phi>)"
    by (metis is_indep1_ForallI is_indep1_Not push_not_qs(2))

  lemma is_indep1_conjI: "\<lbrakk> is_indep1 x \<phi>\<^sub>1; is_indep1 x \<phi>\<^sub>2 \<rbrakk> \<Longrightarrow> is_indep1 x (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2)"
    by (simp add: forall_distrib_and is_indep1_elim_all_conv)
  
  lemma is_indep1_disjI: "\<lbrakk> is_indep1 x \<phi>\<^sub>1; is_indep1 x \<phi>\<^sub>2 \<rbrakk> \<Longrightarrow> is_indep1 x (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2)"
    by (simp add: is_indep1_def sOr_def)
    
  lemma is_indep_Forall_same[simp]: "is_indep1 x (\<^bold>\<forall>x. \<phi>)" 
    unfolding is_indep1_elim_all_conv by simp
    
  lemma is_indep_Exists_same[simp]: "is_indep1 x (\<^bold>\<exists>x. \<phi>)"
    unfolding is_indep1_elim_all_conv by simp
    
                
  lemma is_indep_Pos[simp]: "is_indep X (Pos x) \<longleftrightarrow> x\<notin>X" 
    unfolding is_indep_def by auto
    
  lemma is_indep_Not[simp]: "is_indep X (\<^bold>\<not>\<phi>) \<longleftrightarrow> is_indep X \<phi>" 
    unfolding is_indep_def by auto

    
  lemma is_indep_subst_conv[simp]: "is_indep X f \<Longrightarrow> x\<in>X \<Longrightarrow> f (\<sigma>(x:=v)) = f \<sigma>"  
    unfolding is_indep_def is_dep_def by simp
    

  lemma is_indep1_forall[simp]: "is_indep1 x \<phi> \<Longrightarrow> (\<^bold>\<forall>x. \<phi>) = \<phi>"
    by (auto simp: sForall_def fun_eq_iff)
    
  lemma is_indep1_exists[simp]: "is_indep1 x \<phi> \<Longrightarrow> (\<^bold>\<exists>x. \<phi>) = \<phi>"
    by (auto simp: sExists_def fun_eq_iff)
    
  lemma is_indep_forall_disj: 
    "is_indep1 x \<phi>\<^sub>1 \<Longrightarrow> (\<^bold>\<forall>x. \<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) = (\<phi>\<^sub>1 \<^bold>\<or> (\<^bold>\<forall>x. \<phi>\<^sub>2))"
    "is_indep1 x \<phi>\<^sub>1 \<Longrightarrow> (\<^bold>\<forall>x. \<phi>\<^sub>2 \<^bold>\<or> \<phi>\<^sub>1) = ((\<^bold>\<forall>x. \<phi>\<^sub>2) \<^bold>\<or> \<phi>\<^sub>1)"    
    by (auto simp: sForall_def fun_eq_iff sOr_def)
    
  lemma is_indep_exists_conj: 
    "is_indep1 x \<phi>\<^sub>1 \<Longrightarrow> (\<^bold>\<exists>x. \<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) = (\<phi>\<^sub>1 \<^bold>\<and> (\<^bold>\<exists>x. \<phi>\<^sub>2))"
    "is_indep1 x \<phi>\<^sub>1 \<Longrightarrow> (\<^bold>\<exists>x. \<phi>\<^sub>2 \<^bold>\<and> \<phi>\<^sub>1) = ((\<^bold>\<exists>x. \<phi>\<^sub>2) \<^bold>\<and> \<phi>\<^sub>1)"
    by (auto simp: sExists_def fun_eq_iff sAnd_def)
    

  (* Arbitrary Quantifiers *)  
  datatype quantifier = Forall | Exists
  datatype 'a quantification = Q quantifier (qvar: 'a)
  
  fun quant :: "'a quantification \<Rightarrow> 'a afml \<Rightarrow> 'a afml" where
    "quant (Q Forall x) = sForall x"
  | "quant (Q Exists x) = sExists x"
    
  definition quants :: "'a quantification list \<Rightarrow> 'a afml \<Rightarrow> 'a afml" where "quants = foldr quant"
  
  lemma quants_simp[simp]:
    "quants [] \<phi> = \<phi>"
    "quants (q#qs) \<phi> = quant q (quants qs \<phi>)"
    "quants (qs\<^sub>1@qs\<^sub>2) \<phi> = quants qs\<^sub>1 (quants qs\<^sub>2 \<phi>)"
    unfolding quants_def by auto

  fun quants_induction_scheme :: "'a quantification list \<Rightarrow> unit" where
    "quants_induction_scheme [] = ()"
  | "quants_induction_scheme (Q Forall _ # qs) = quants_induction_scheme qs"
  | "quants_induction_scheme (Q Exists _ # qs) = quants_induction_scheme qs"
  
  lemmas quants_induct = quants_induction_scheme.induct[case_names Empty Forall Exists]
    
      
  lemma quants_bound_indep1: "x\<in>qvar`set qs \<Longrightarrow> is_indep1 x (quants qs \<phi>)"  
    apply (induction qs rule: quants_induct)
    apply (auto simp: is_indep1_ForallI is_indep1_ExistsI)
    done
    
  lemma quants_bound_indep: "is_indep (qvar`set qs) (quants qs \<phi>)"
    by (auto simp: is_indep_def quants_bound_indep1)
    
  lemma quant_indep1_pull: 
    "is_indep1 (qvar q) \<phi>\<^sub>1 \<Longrightarrow> quant q (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) = \<phi>\<^sub>1 \<^bold>\<and> quant q \<phi>\<^sub>2"
    "is_indep1 (qvar q) \<phi>\<^sub>2 \<Longrightarrow> quant q (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) = quant q \<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2"
    "is_indep1 (qvar q) \<phi>\<^sub>1 \<Longrightarrow> quant q (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) = \<phi>\<^sub>1 \<^bold>\<or> quant q \<phi>\<^sub>2"
    "is_indep1 (qvar q) \<phi>\<^sub>2 \<Longrightarrow> quant q (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) = quant q \<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2"
    by (cases q rule: quant.cases; 
      auto simp: forall_distrib_and is_indep_exists_conj exists_distrib_or is_indep_forall_disj)+
    
  lemma quants_indep_pull: 
    "is_indep (qvar`set qs) \<phi>\<^sub>1 \<Longrightarrow> quants qs (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) = \<phi>\<^sub>1 \<^bold>\<and> quants qs \<phi>\<^sub>2"
    "is_indep (qvar`set qs) \<phi>\<^sub>2 \<Longrightarrow> quants qs (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) = quants qs \<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2"
    "is_indep (qvar`set qs) \<phi>\<^sub>1 \<Longrightarrow> quants qs (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) = \<phi>\<^sub>1 \<^bold>\<or> quants qs \<phi>\<^sub>2"
    "is_indep (qvar`set qs) \<phi>\<^sub>2 \<Longrightarrow> quants qs (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) = quants qs \<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2"
    by (induction qs; auto simp: quant_indep1_pull)+
    
    
  lemma forall_reduction: 
    assumes I: "is_indep (qvar`set qs\<^sub>2) C"  
    shows "quants (qs\<^sub>1@Q Forall x#qs\<^sub>2) (C \<^bold>\<and> \<phi>) 
         = quants (qs\<^sub>1@Q Forall x#qs\<^sub>2) ((\<^bold>\<forall>x. C) \<^bold>\<and> \<phi>)"
  proof -
    have "quants (qs\<^sub>1@Q Forall x#qs\<^sub>2) (C \<^bold>\<and> \<phi>)
        = quants qs\<^sub>1 ((\<^bold>\<forall>x. C) \<^bold>\<and> quants (Q Forall x#qs\<^sub>2) \<phi>)"       
      by (simp add: forall_distrib_and quants_indep_pull(1) I)
    also have "\<dots> = quants (qs\<^sub>1@Q Forall x#qs\<^sub>2) ((\<^bold>\<forall>x. C) \<^bold>\<and> \<phi>)"
      using I
      by (simp add: forall_distrib_and is_indep1_ForallI is_indep_def quants_indep_pull(2))
    finally show ?thesis .
  qed
    
    
    
end xxx
    
        
    
  fun quants :: "'a quantifier list \<Rightarrow> 'a afml \<Rightarrow> 'a afml" where  
    "quants [] \<phi> = \<phi>"
  | "sem_qbf (q # qs) m = sem_quant q (sem_qbf qs m)"

  fun sem_qbf_induction_scheme :: "'a quantifier list \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "sem_qbf_induction_scheme [] _ = True"
  | "sem_qbf_induction_scheme (Forall _ # qs) \<sigma> = (\<forall>\<sigma>. sem_qbf_induction_scheme qs \<sigma>)"
  | "sem_qbf_induction_scheme (Exists _ # qs) \<sigma> = (\<forall>\<sigma>. sem_qbf_induction_scheme qs \<sigma>)"
  
  lemmas sem_qbf_induct = sem_qbf_induction_scheme.induct[case_names Matrix Forall Exists]
    
  definition "closed Q m \<equiv> is_deps m (qvar`set Q)"
    
  lemma sem_qbf_closed_aux: 
    "(is_deps m (qvar`set qs \<union> {x. \<sigma>1 x = \<sigma>2 x})) \<Longrightarrow> sem_qbf qs m \<sigma>1 = sem_qbf qs m \<sigma>2"
  proof (induction qs arbitrary: \<sigma>1 \<sigma>2)
    case Nil
    then show ?case by (auto simp: is_deps_def)
  next
    case (Cons a qs)
    
    have [simp]: "(insert x (X \<union> {x. \<sigma>1 x = \<sigma>2 x})) = (X \<union> {xa. xa \<noteq> x \<longrightarrow> \<sigma>1 xa = \<sigma>2 xa})" for x X
      by blast
      
    have "sem_qbf qs m (\<sigma>1(qvar a := v)) = sem_qbf qs m (\<sigma>2(qvar a := v))" for v
      apply (rule Cons.IH)
      using Cons.prems by auto
      
    then show ?case by (cases a) auto
  qed
      
  lemma sem_qbf_closed: "closed Q m \<Longrightarrow> sem_qbf Q m \<sigma>\<^sub>1 = sem_qbf Q m (\<lambda>_. False)"
    unfolding closed_def
    using sem_qbf_closed_aux is_deps_mono 
    by blast
  
    
  lemma sem_qbf_matrix_mono: "(\<forall>\<sigma>. m \<sigma> \<longrightarrow> m' \<sigma>) \<Longrightarrow> 
    sem_qbf Q m \<sigma> \<Longrightarrow> sem_qbf Q m' \<sigma>"
    by (induction Q \<sigma> rule: sem_qbf_induct) auto
    
  lemma sem_qbf_mono: 
    assumes "\<forall>\<sigma>. sem_qbf Q\<^sub>2 m \<sigma> \<longrightarrow> sem_qbf Q\<^sub>2' m' \<sigma>"  
    assumes "sem_qbf (Q\<^sub>1@Q\<^sub>2) m \<sigma>"
    shows "sem_qbf (Q\<^sub>1@Q\<^sub>2') m' \<sigma>"
    using assms by (induction Q\<^sub>1 \<sigma> rule: sem_qbf_induct) auto
    
  lemma sem_qbf_append[simp]: "sem_qbf (Q\<^sub>1@Q\<^sub>2) m = sem_qbf Q\<^sub>1 (sem_qbf Q\<^sub>2 m)"
    by (induction Q\<^sub>1) auto
    
    
  lemma fun_upd_twist_cases:
    "f(x\<^sub>1:=y\<^sub>1, x\<^sub>2:=y\<^sub>2) = (if x\<^sub>1=x\<^sub>2 then f(x\<^sub>2:=y\<^sub>2) else f(x\<^sub>2:=y\<^sub>2, x\<^sub>1:=y\<^sub>1))" by auto
    
  lemma move_forall: "sem_qbf Q (sem_quant (Forall x) m) \<sigma> \<Longrightarrow> sem_qbf (Forall x # Q) m \<sigma>"
    apply (induction Q \<sigma> rule: sem_qbf_induct)
    subgoal by simp
    subgoal by (fastforce simp: fun_upd_twist_cases[where x\<^sub>1=x])
    subgoal by (fastforce simp: fun_upd_twist_cases[where x\<^sub>1=x])
    done
  
    
  lemma sem_qbf_reorder_quant:
    assumes "sem_qbf (filter is_Exists Q @ filter is_Forall Q) m \<sigma>"  
    shows "sem_qbf Q m \<sigma>"
    using assms
    apply (induction Q \<sigma> rule: sem_qbf_induct)
    apply (auto dest: move_forall)
    done
  
  lemma eq_on_except_conv: "(\<forall>x\<in>- {x}. \<sigma> x = \<sigma>' x) \<longleftrightarrow> (\<exists>v. \<sigma> = \<sigma>'(x:=v))"    
    by (auto split: if_splits intro!: exI[where x="\<sigma> x"])
    
  definition "indep f x \<equiv> is_deps f (-{x})"  
    
  lemma indep_sng_conv: "indep f x \<longleftrightarrow> (\<forall>\<sigma> v. f (\<sigma>(x:=v)) = f \<sigma>)"  
    unfolding is_deps_def indep_def
    by (auto simp: eq_on_except_conv)
    
  lemma sem_quant_drop_indep: 
    assumes "indep m\<^sub>1 (qvar q)"
    shows "sem_quant q (\<lambda>\<sigma>. m\<^sub>1 \<sigma> \<and> m\<^sub>2 \<sigma>) = (\<lambda>\<sigma>. m\<^sub>1 \<sigma> \<and> sem_quant q m\<^sub>2 \<sigma>)"
    using assms 
    by (cases q) (auto simp: fun_eq_iff indep_sng_conv)
    
         
  lemma forall_distrib_and: "sem_quant (Forall x) (\<lambda>\<sigma>. m\<^sub>1 \<sigma> \<and> m\<^sub>2 \<sigma>) 
    = (\<lambda>\<sigma>. sem_quant (Forall x) m\<^sub>1 \<sigma> \<and> sem_quant (Forall x) m\<^sub>2 \<sigma>)"
    by auto
        
    
  lemma qbf_pull_indep:
    assumes "\<forall>x\<in>qvar`set Q\<^sub>2. indep m\<^sub>1 x"
    shows "sem_qbf Q\<^sub>2 (\<lambda>\<sigma>. m\<^sub>1 \<sigma> \<and> m\<^sub>2 \<sigma>) = (\<lambda>\<sigma>. m\<^sub>1 \<sigma> \<and> sem_qbf Q\<^sub>2 m\<^sub>2 \<sigma>)"    
    using assms
    by (induction Q\<^sub>2) (auto simp: sem_quant_drop_indep)

  lemma
    assumes "\<forall>x\<in>qvar`set Q\<^sub>2. indep m\<^sub>1 x"
    shows "sem_qbf (Q\<^sub>1@Forall x#Q\<^sub>2) (\<lambda>\<sigma>. m\<^sub>1 \<sigma> \<and> m\<^sub>2 \<sigma>)
      = sem_qbf (Q\<^sub>1@Forall x#Q\<^sub>2) (\<lambda>\<sigma>. (\<forall>v. m\<^sub>1 (\<sigma>(x:=v))) \<and> m\<^sub>2 \<sigma>)"  
    proof -
      from assms have 1: "\<forall>x\<in>qvar`set Q\<^sub>2. indep (\<lambda>\<sigma>. (\<forall>v. m\<^sub>1 (\<sigma>(x := v)))) x"
        by (auto simp: indep_sng_conv)
    
      then show ?thesis
        using assms
        apply (simp add: qbf_pull_indep fun_eq_iff forall_distrib_and sem_quant.simps[abs_def])
        thm qbf_pull_indep[where m\<^sub>1 = "(\<lambda>\<sigma>. \<forall>v. m\<^sub>1 (\<sigma>(x := v)))"]
      
      
      
        
    
  definition "rem_forall_Q Q = filter is_Exists Q"
  definition "rem_forall_m Q m = "
    
  lemma sem_qbf_rem_forall:
    assumes "sem_qbf_aux (filter is_Exists Q) m \<sigma>"
    shows "sem_qbf_aux Q m \<sigma>"
    
    
        
    
    
section \<open>CNF/DNF Matrix\<close>    
        
  datatype 'a literal = is_pos: Pos (lvar: 'a) | Neg (lvar: 'a)
  type_synonym 'a clause = "'a literal set"
  type_synonym 'a matrix = "'a clause set"

  fun sem_lit :: "'a literal \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "sem_lit (Pos x) \<sigma> = \<sigma> x"
  | "sem_lit (Neg x) \<sigma> = (\<not> \<sigma> x)"

  lemma sem_lit_alt: "sem_lit l \<sigma> = (case l of Pos x \<Rightarrow> \<sigma> x | Neg x \<Rightarrow> \<not>\<sigma> x)"
    by (auto split: literal.split)

  definition sem_clause_cnf :: "'a clause \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "sem_clause_cnf C \<sigma> \<equiv> \<exists>l\<in>C. sem_lit l \<sigma>"

  definition sem_cnf :: "'a matrix \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "sem_cnf F \<sigma> \<equiv> \<forall>C\<in>F. sem_clause_cnf C \<sigma>"

  definition sem_clause_dnf :: "'a clause \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "sem_clause_dnf C \<sigma> \<equiv> \<forall>l\<in>C. sem_lit l \<sigma>"

  definition sem_dnf :: "'a matrix \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "sem_dnf F \<sigma> \<equiv> \<exists>C\<in>F. sem_clause_dnf C \<sigma>"

  lemma sem_clause_cnf_simps:  
    "\<not>sem_clause_cnf {} \<sigma>"
    "sem_clause_cnf (insert l C) \<sigma> \<longleftrightarrow> sem_lit l \<sigma> \<or> sem_clause_cnf C \<sigma>"
    "sem_clause_cnf (C\<^sub>1 \<union> C\<^sub>2) \<sigma> \<longleftrightarrow> sem_clause_cnf C\<^sub>1 \<sigma> \<or> sem_clause_cnf C\<^sub>2 \<sigma>"
    by (auto simp: sem_clause_cnf_def)
    
  lemma sem_clause_dnf_simps:  
    "sem_clause_dnf {} \<sigma>"
    "sem_clause_dnf (insert l C) \<sigma> \<longleftrightarrow> sem_lit l \<sigma> \<and> sem_clause_dnf C \<sigma>"
    "sem_clause_dnf (C\<^sub>1 \<union> C\<^sub>2) \<sigma> \<longleftrightarrow> sem_clause_dnf C\<^sub>1 \<sigma> \<and> sem_clause_dnf C\<^sub>2 \<sigma>"
    by (auto simp: sem_clause_dnf_def)
    
  lemma sem_cnf_simps:
    "sem_cnf {} = (\<lambda>_. True)"
    "sem_cnf (insert C F) = (\<lambda>\<sigma>. sem_clause_cnf C \<sigma> \<and> sem_cnf F \<sigma>)"  
    "sem_cnf (F\<^sub>1 \<union> F\<^sub>2) = (\<lambda>\<sigma>. sem_cnf F\<^sub>1 \<sigma> \<and> sem_cnf F\<^sub>2 \<sigma>)"
    by (auto simp: sem_cnf_def fun_eq_iff)
    
  lemma sem_dnf_simps:
    "\<not>sem_dnf {} \<sigma>"
    "sem_dnf (insert C F) \<sigma> \<longleftrightarrow> sem_clause_dnf C \<sigma> \<or> sem_dnf F \<sigma>"  
    "sem_dnf (F\<^sub>1 \<union> F\<^sub>2) \<sigma> \<longleftrightarrow> sem_dnf F\<^sub>1 \<sigma> \<or> sem_dnf F\<^sub>2 \<sigma>"  
    by (auto simp: sem_dnf_def)

    
  fun var_of_lit :: "'a literal \<Rightarrow> 'a" where
    "var_of_lit (Pos x) = x" | "var_of_lit (Neg x) = x"
  lemma var_of_lit_alt: "var_of_lit l = (case l of Pos x \<Rightarrow> x | Neg x \<Rightarrow> x)"
    by (cases l) auto
  definition vars_of_clause :: "'a clause \<Rightarrow> 'a set" 
    where "vars_of_clause C = var_of_lit ` C"
  definition vars_of_matrix :: "'a matrix \<Rightarrow> 'a set" where "vars_of_matrix F \<equiv> \<Union>(vars_of_clause`F)"

  lemma vars_of_clause_simps[simp]:
    "vars_of_clause {} = {}"
    "vars_of_clause (insert l C) = insert (var_of_lit l) (vars_of_clause C)"
    "vars_of_clause (C\<^sub>1 \<union> C\<^sub>2) = vars_of_clause C\<^sub>1 \<union> vars_of_clause C\<^sub>2"
    by (auto simp: vars_of_clause_def)

  lemma vars_of_matrix_simps[simp]: 
    "vars_of_matrix {} = {}"
    "vars_of_matrix (insert C F) = vars_of_clause C \<union> vars_of_matrix F"
    "vars_of_matrix (F\<^sub>1\<union>F\<^sub>2) = vars_of_matrix F\<^sub>1 \<union> vars_of_matrix F\<^sub>2"
    by (auto simp: vars_of_matrix_def)

  lemma vars_of_clause_empty_iff[simp]: "vars_of_clause C = {} \<longleftrightarrow> C={}"  
    by (auto simp: vars_of_clause_def)

  lemma vars_of_matrix_empty_iff[simp]: "vars_of_matrix F = {} \<longleftrightarrow> (F={} \<or> F={{}})"
    by (auto simp: vars_of_matrix_def)

  lemma sem_lit_dep: "\<sigma>1 (var_of_lit l) = \<sigma>2 (var_of_lit l) \<longleftrightarrow> sem_lit l \<sigma>1 = sem_lit l \<sigma>2"
    by (cases l) auto
  
  lemma sem_clause_cnf_dep: "\<forall>x\<in>vars_of_clause c. \<sigma>1 x = \<sigma>2 x \<Longrightarrow> sem_clause_cnf c \<sigma>1 = sem_clause_cnf c \<sigma>2"
    by (auto simp: sem_clause_cnf_def vars_of_clause_def sem_lit_dep)
    
  lemma sem_clause_dnf_dep: "\<forall>x\<in>vars_of_clause c. \<sigma>1 x = \<sigma>2 x \<Longrightarrow> sem_clause_dnf c \<sigma>1 = sem_clause_dnf c \<sigma>2"
    by (auto simp: sem_clause_dnf_def vars_of_clause_def sem_lit_dep)
  
  lemma sem_cnf_dep: "\<forall>x\<in>vars_of_matrix F. \<sigma>1 x = \<sigma>2 x \<Longrightarrow> sem_cnf F \<sigma>1 = sem_cnf F \<sigma>2"
    apply (auto simp: sem_cnf_def vars_of_matrix_def) 
    using sem_clause_cnf_dep apply force
    using sem_clause_cnf_dep apply force
    done
  
  lemma sem_dnf_dep: "\<forall>x\<in>vars_of_matrix F. \<sigma>1 x = \<sigma>2 x \<Longrightarrow> sem_dnf F \<sigma>1 = sem_dnf F \<sigma>2"
    apply (auto simp: sem_dnf_def vars_of_matrix_def) 
    using sem_clause_dnf_dep apply force
    using sem_clause_dnf_dep apply force
    done
    
  lemma sem_cnf_deps: "is_deps (sem_cnf m) (vars_of_matrix m)"  
    unfolding is_deps_def
    using sem_cnf_dep by blast
    
  lemma sem_dnf_deps: "is_deps (sem_dnf m) (vars_of_matrix m)"  
    unfolding is_deps_def
    using sem_dnf_dep by blast
    
    
  lemma cnf_resolution: "sem_cnf ({ {Pos x} \<union> C\<^sub>1, {Neg x} \<union> C\<^sub>2 } \<union> R) 
    = sem_cnf ({ {Pos x} \<union> C\<^sub>1, {Neg x} \<union> C\<^sub>2, C\<^sub>1 \<union> C\<^sub>2 } \<union> R)"
    by (auto simp: sem_cnf_simps fun_eq_iff sem_clause_cnf_simps)

  lemma dnf_resolution: "sem_dnf ({ {Pos x} \<union> C\<^sub>1, {Neg x} \<union> C\<^sub>2 } \<union> R) 
    = sem_dnf ({ {Pos x} \<union> C\<^sub>1, {Neg x} \<union> C\<^sub>2, C\<^sub>1 \<union> C\<^sub>2 } \<union> R)"
    by (auto simp: sem_dnf_simps fun_eq_iff sem_clause_dnf_simps)
    
        
  fun lit_of where "lit_of x True = Pos x" | "lit_of x False = Neg x" 
    
  definition "subst F x v \<equiv> { C - {lit_of x (\<not>v)} | C. C\<in>F \<and> lit_of x v \<notin> C }"  
    
  
  lemma sem_clause_subst: "sem_clause_cnf C (\<sigma>(x := v)) 
    \<longleftrightarrow> lit_of x v \<in> C \<or> sem_clause_cnf (C - {lit_of x (\<not>v)}) \<sigma>"
    unfolding sem_clause_cnf_def 
    apply (cases v)
    apply safe
    apply (auto simp: sem_lit_alt split: literal.splits if_split_asm)
    done
  
  lemma sem_cnf_subst: "sem_cnf F (\<sigma>(x:=v)) \<longleftrightarrow> sem_cnf (subst F x v) \<sigma>"
    unfolding sem_cnf_def subst_def
    by (auto simp: sem_clause_subst)
    
  lemma subst_removes_var: "x \<notin> vars_of_matrix (subst F x v)"
    apply (cases v)
    apply (auto simp: vars_of_matrix_def subst_def vars_of_clause_def)
    apply (metis (full_types) var_of_lit.elims)+
    done
      
    
    
  lemma sem_qbf_aux_subst:
    "x\<notin>qvar`set qs \<Longrightarrow> sem_qbf_aux qs (sem_cnf F) (\<sigma>(x:=v)) = sem_qbf_aux qs (sem_cnf (subst F x v)) \<sigma>"  
  proof (induction qs arbitrary: \<sigma>)
    case Nil
    
    then show ?case 
      apply (subst eta_contract_eq)
      apply (simp add: sem_cnf_subst)
      done
      
  next
    case (Cons a qs)
    then show ?case 
      apply (subst eta_contract_eq)
      apply (subst (asm) eta_contract_eq)
      apply (cases a)
      apply (auto simp: fun_upd_twist[of x])
      done
    
  qed
  
    
  lemma subst_simps: 
    "NO_MATCH {} R \<Longrightarrow> subst (insert C R) x v = subst {C} x v \<union> subst R x v"
    "subst {C} x v = (if lit_of x v \<in> C then {} else {C - {lit_of x (\<not>v)}})"
    by (auto simp: subst_def)
  
  lemma sem_qbf_aux_const: "sem_qbf_aux qs (\<lambda>_. c) \<sigma> = c"  
    apply (induction qs "(\<lambda>_::'a valuation. c)" \<sigma> rule: sem_qbf_aux.induct)
    by auto
        
  lemma lvar_lit_of[simp]: "lvar (lit_of x v) = x" by (cases v) auto
    
  lemma cnf_univ_reduction:  
    assumes DIST: "distinct (map qvar qs)"
    assumes QSFMT: "qs = qs\<^sub>1@Forall (lvar l)#qs\<^sub>2"
    assumes SS: "vars_of_clause C \<subseteq> qvar`set qs\<^sub>1"
    shows "sem_qbf (QBF qs (sem_cnf ({ {l} \<union> C } \<union> R))) = sem_qbf (QBF qs (sem_cnf ({C} \<union> R)))"
  proof -

    have 1: "subst {{l}} (lvar l) v = (if v = is_pos l then {} else {{}})" for v
      by (cases l) (simp_all add: subst_def)
      
    have 2: "\<exists>v. sem_cnf (subst (insert {l} R) (lvar l) v) = (\<lambda>_. False)" for R
      apply (simp add: 1 subst_simps(1))
      by (meson sem_clause_cnf_simps(1) sem_cnf_simps(2))
  
    have 3: "\<exists>v. \<not>sem_qbf_aux qs\<^sub>2 (sem_cnf (subst (insert {l} R) (lvar l) v)) \<sigma>" for R \<sigma>  
      by (smt "2" sem_qbf_aux_const[where c=False])
      
    have "sem_qbf_aux qs (sem_cnf (insert (insert l C) R)) \<sigma> =
      sem_qbf_aux qs (sem_cnf (insert C R)) \<sigma>" for \<sigma>
      using DIST SS
      apply (simp add: QSFMT)
    proof (induction qs\<^sub>1 arbitrary: C R \<sigma>)
      case Nil
      then show ?case 
        apply (safe;clarsimp simp: sem_qbf_aux_subst)
        subgoal using 3 by blast
        subgoal by (simp add: subst_simps sem_cnf_simps sem_clause_cnf_simps sem_qbf_aux_const)
        done
      
    next
      case (Cons a qs\<^sub>1)
      
      show ?case 
        (* TODO: CLEAN UP THIS MESS! *)
        using Cons.prems
        apply (cases a; simp)
        subgoal for x
          apply (auto)
          subgoal for v
            apply (subst sem_qbf_aux_subst)
            apply auto []
            apply (subst (asm) sem_qbf_aux_subst)
            apply auto []
            apply (drule spec[of _ v])
            apply (cases "lit_of x v \<in> C")
            subgoal by (simp add: subst_simps)
            subgoal
              apply (auto simp add: subst_simps split: if_splits) []
              apply (smt Cons.IH Diff_insert0 Diff_insert_absorb UnCI insert_Diff insert_Diff1 insert_Diff_if insert_absorb insert_subset subset_insert_iff subst_removes_var subst_simps(2) vars_of_clause_simps(2) vars_of_matrix_simps(2))
              done
            done  
          subgoal for v
            apply (subst sem_qbf_aux_subst)
            apply auto []
            apply (subst (asm) sem_qbf_aux_subst)
            apply auto []
            apply (drule spec[of _ v])
            apply (cases "lit_of x v \<in> C")
            subgoal by (simp add: subst_simps)
            subgoal
              apply (auto simp add: subst_simps split: if_splits) []
              apply (smt Cons.IH Diff_insert0 Diff_insert_absorb UnCI insert_Diff insert_Diff1 insert_Diff_if insert_absorb insert_subset subset_insert_iff subst_removes_var subst_simps(2) vars_of_clause_simps(2) vars_of_matrix_simps(2))
              done
            done  
          done
          
        subgoal for x
          apply (auto)
          subgoal for v
            apply (subst sem_qbf_aux_subst)
            apply auto []
            apply (subst (asm) sem_qbf_aux_subst)
            apply auto []
            apply (rule exI[of _ v])
            apply (cases "lit_of x v \<in> C")
            subgoal by (simp add: subst_simps)
            subgoal
              apply (auto simp add: subst_simps split: if_splits) []
              apply (smt Cons.IH Diff_insert0 Diff_insert_absorb UnCI insert_Diff insert_Diff1 insert_Diff_if insert_absorb insert_subset subset_insert_iff subst_removes_var subst_simps(2) vars_of_clause_simps(2) vars_of_matrix_simps(2))
              done
            done  
          subgoal for v
            apply (subst sem_qbf_aux_subst)
            apply auto []
            apply (subst (asm) sem_qbf_aux_subst)
            apply auto []
            apply (rule exI[of _ v])
            apply (cases "lit_of x v \<in> C")
            subgoal by (simp add: subst_simps)
            subgoal
              apply (auto simp add: subst_simps split: if_splits) []
              apply (smt Cons.IH Diff_insert0 Diff_insert_absorb UnCI insert_Diff insert_Diff1 insert_Diff_if insert_absorb insert_subset subset_insert_iff subst_removes_var subst_simps(2) vars_of_clause_simps(2) vars_of_matrix_simps(2))
              done
            done  
          done
        done
    qed
      
    then show ?thesis
      by (simp add: sem_qbf_def)
  qed
       

  xxx, ctd here: towards abstract proof checker
  
  map: ids \<rightharpoonup> clauses
  
  map = empty
  
  foreach (STEP id C antecedents) \<in> butlast cert
    @invariant: range map \<union> orig_clauses  equisat  orig_clauses
    check step
    map = map(id\<mapsto>C)
  
  check last step of cert
    assert that C={}  
    
  
  
      
    
oops    
  xxx, 
    describe resolution syntactically (on matrix)
    then describe \<forall>-reduction syntactically       
      

  lemma "
    (x \<or> C1) \<and> (\<not>x \<or> C2) \<and> R
  \<longleftrightarrow> (x \<or> C1) \<and> (\<not>x \<or> C2) \<and> (C1 \<or> C2) \<and> R  
    " by blast 
      
  lemma 
    "(\<forall>x. (x \<or> C) \<and> R x) \<longleftrightarrow> (\<forall>x. C \<and> R x)" 
    "(\<forall>x. (\<not>x \<or> C) \<and> R x) \<longleftrightarrow> (\<forall>x. C \<and> R x)" 
    by blast+
  
  lemma 
    "(\<forall>x. (x \<or> C x) \<and> R x) \<longleftrightarrow> (\<forall>x. C x \<and> R x)" oops
  
  
  
oops end end end
  
  
  
  
  datatype 'a literal = is_pos: Pos 'a | Neg 'a

  type_synonym 'a clause = "'a literal set"

  type_synonym 'a matrix = "'a clause set"

  datatype 'a qbf = Forall 'a "'a qbf" | Exists 'a "'a qbf" | Matrix "'a matrix" 
  
  type_synonym 'a valuation = "'a \<Rightarrow> bool"

  
  
  subsection \<open>Used Variables\<close>
  fun var_of_lit :: "'a literal \<Rightarrow> 'a" where
    "var_of_lit (Pos x) = x" | "var_of_lit (Neg x) = x"
  lemma var_of_lit_alt: "var_of_lit l = (case l of Pos x \<Rightarrow> x | Neg x \<Rightarrow> x)"
    by (cases l) auto
  definition vars_of_clause :: "'a clause \<Rightarrow> 'a set" 
    where "vars_of_clause C = var_of_lit ` C"
  definition vars_of_matrix :: "'a matrix \<Rightarrow> 'a set" where "vars_of_matrix F \<equiv> \<Union>(vars_of_clause`F)"

  lemma vars_of_clause_simps[simp]:
    "vars_of_clause {} = {}"
    "vars_of_clause (insert l C) = insert (var_of_lit l) (vars_of_clause C)"
    "vars_of_clause (C\<^sub>1 \<union> C\<^sub>2) = vars_of_clause C\<^sub>1 \<union> vars_of_clause C\<^sub>2"
    by (auto simp: vars_of_clause_def)

  lemma vars_of_matrix_simps[simp]: 
    "vars_of_matrix {} = {}"
    "vars_of_matrix (insert C F) = vars_of_clause C \<union> vars_of_matrix F"
    "vars_of_matrix (F\<^sub>1\<union>F\<^sub>2) = vars_of_matrix F\<^sub>1 \<union> vars_of_matrix F\<^sub>2"
    by (auto simp: vars_of_matrix_def)

  lemma vars_of_clause_empty_iff[simp]: "vars_of_clause C = {} \<longleftrightarrow> C={}"  
    by (auto simp: vars_of_clause_def)

  lemma vars_of_matrix_empty_iff[simp]: "vars_of_matrix F = {} \<longleftrightarrow> (F={} \<or> F={{}})"
    by (auto simp: vars_of_matrix_def)
  
  
  fun sem_lit :: "'a literal \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "sem_lit (Pos x) \<sigma> = \<sigma> x"
  | "sem_lit (Neg x) \<sigma> = (\<not> \<sigma> x)"

  lemma sem_lit_alt: "sem_lit l \<sigma> = (case l of Pos x \<Rightarrow> \<sigma> x | Neg x \<Rightarrow> \<not>\<sigma> x)"
    by (auto split: literal.split)

  definition sem_clause_cnf :: "'a clause \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "sem_clause_cnf C \<sigma> \<equiv> \<exists>l\<in>C. sem_lit l \<sigma>"

  definition sem_cnf :: "'a matrix \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "sem_cnf F \<sigma> \<equiv> \<forall>C\<in>F. sem_clause_cnf C \<sigma>"

  definition sem_clause_dnf :: "'a clause \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "sem_clause_dnf C \<sigma> \<equiv> \<forall>l\<in>C. sem_lit l \<sigma>"

  definition sem_dnf :: "'a matrix \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "sem_dnf F \<sigma> \<equiv> \<exists>C\<in>F. sem_clause_dnf C \<sigma>"
    
      

  fun sem_qbf_cnf_aux :: "'a qbf \<Rightarrow> 'a valuation \<Rightarrow> bool" where  
    "sem_qbf_cnf_aux (Matrix F) \<sigma> = sem_cnf F \<sigma>"
  | "sem_qbf_cnf_aux (Forall x F) \<sigma> \<longleftrightarrow> (\<forall>v. sem_qbf_cnf_aux F (\<sigma>(x:=v)))"  
  | "sem_qbf_cnf_aux (Exists x F) \<sigma> \<longleftrightarrow> (\<exists>v. sem_qbf_cnf_aux F (\<sigma>(x:=v)))"  
      
  definition "sem_qbf_cnf F \<equiv> (sem_qbf_cnf_aux F) (\<lambda>_. False)"
  
  fun sem_qbf_dnf_aux :: "'a qbf \<Rightarrow> 'a valuation \<Rightarrow> bool" where  
    "sem_qbf_dnf_aux (Matrix F) \<sigma> = sem_dnf F \<sigma>"
  | "sem_qbf_dnf_aux (Forall x F) \<sigma> \<longleftrightarrow> (\<forall>v. sem_qbf_dnf_aux F (\<sigma>(x:=v)))"  
  | "sem_qbf_dnf_aux (Exists x F) \<sigma> \<longleftrightarrow> (\<exists>v. sem_qbf_dnf_aux F (\<sigma>(x:=v)))"  
      
  definition "sem_qbf_dnf F \<equiv> (sem_qbf_dnf_aux F) (\<lambda>_. False)"

  
  
    
  fun bound_vars where
    "bound_vars (Matrix _) = {}"
  | "bound_vars (Forall x F) = insert x (bound_vars F)"  
  | "bound_vars (Exists x F) = insert x (bound_vars F)"  
  
  fun matrix_of where
    "matrix_of (Matrix F) = F"
  | "matrix_of (Forall _ F) = matrix_of F"
  | "matrix_of (Exists _ F) = matrix_of F"
  
  definition "closed F \<longleftrightarrow> vars_of_matrix (matrix_of F) \<subseteq> bound_vars F"  
  
  lemma sem_lit_dep: "\<sigma>1 (var_of_lit l) = \<sigma>2 (var_of_lit l) \<longleftrightarrow> sem_lit l \<sigma>1 = sem_lit l \<sigma>2"
    by (cases l) auto
  
  lemma sem_clause_cnf_dep: "\<forall>x\<in>vars_of_clause c. \<sigma>1 x = \<sigma>2 x \<Longrightarrow> sem_clause_cnf c \<sigma>1 = sem_clause_cnf c \<sigma>2"
    by (auto simp: sem_clause_cnf_def vars_of_clause_def sem_lit_dep)
    
  lemma sem_clause_dnf_dep: "\<forall>x\<in>vars_of_clause c. \<sigma>1 x = \<sigma>2 x \<Longrightarrow> sem_clause_dnf c \<sigma>1 = sem_clause_dnf c \<sigma>2"
    by (auto simp: sem_clause_dnf_def vars_of_clause_def sem_lit_dep)
  
  lemma sem_cnf_dep: "\<forall>x\<in>vars_of_matrix F. \<sigma>1 x = \<sigma>2 x \<Longrightarrow> sem_cnf F \<sigma>1 = sem_cnf F \<sigma>2"
    apply (auto simp: sem_cnf_def vars_of_matrix_def) 
    using sem_clause_cnf_dep apply force
    using sem_clause_cnf_dep apply force
    done
  
  lemma sem_dnf_dep: "\<forall>x\<in>vars_of_matrix F. \<sigma>1 x = \<sigma>2 x \<Longrightarrow> sem_dnf F \<sigma>1 = sem_dnf F \<sigma>2"
    apply (auto simp: sem_dnf_def vars_of_matrix_def) 
    using sem_clause_dnf_dep apply force
    using sem_clause_dnf_dep apply force
    done
  
  
  lemma sem_closed_qbf_cnf_aux: 
    "(\<forall>x\<in>vars_of_matrix (matrix_of F) - bound_vars F. \<sigma>1 x = \<sigma>2 x) \<Longrightarrow> (sem_qbf_cnf_aux F) \<sigma>1 = (sem_qbf_cnf_aux F) \<sigma>2"
    apply (induction F arbitrary: \<sigma>1 \<sigma>2)
    apply (auto simp: sem_cnf_dep)
    apply (drule_tac x=v in spec; smt DiffE DiffI fun_upd_apply insert_iff)
    apply (drule_tac x=v in spec; smt DiffE DiffI fun_upd_apply insert_iff)
    apply (rule_tac x=v in exI; smt DiffE DiffI fun_upd_apply insert_iff)
    apply (rule_tac x=v in exI; smt DiffE DiffI fun_upd_apply insert_iff)
    done
    
  lemma sem_closed_qbf_cnf: 
    "closed F \<Longrightarrow> sem_qbf_cnf_aux F \<sigma>1 = sem_qbf_cnf F"
    unfolding closed_def sem_qbf_cnf_def using sem_closed_qbf_cnf_aux[of F \<sigma>1 "\<lambda>_. False"]
    by blast

  lemma sem_closed_qbf_dnf_aux: 
    "(\<forall>x\<in>vars_of_matrix (matrix_of F) - bound_vars F. \<sigma>1 x = \<sigma>2 x) \<Longrightarrow> (sem_qbf_dnf_aux F) \<sigma>1 = (sem_qbf_dnf_aux F) \<sigma>2"
    apply (induction F arbitrary: \<sigma>1 \<sigma>2)
    apply (auto simp: sem_dnf_dep)
    apply (drule_tac x=v in spec; smt DiffE DiffI fun_upd_apply insert_iff)
    apply (drule_tac x=v in spec; smt DiffE DiffI fun_upd_apply insert_iff)
    apply (rule_tac x=v in exI; smt DiffE DiffI fun_upd_apply insert_iff)
    apply (rule_tac x=v in exI; smt DiffE DiffI fun_upd_apply insert_iff)
    done
    
  lemma sem_closed_qbf_dnf: 
    "closed F \<Longrightarrow> sem_qbf_dnf_aux F \<sigma>1 = sem_qbf_dnf F"
    unfolding closed_def sem_qbf_dnf_def using sem_closed_qbf_dnf_aux[of F \<sigma>1 "\<lambda>_. False"]
    by blast
    
    
        
  fun skolem_sem :: "('a \<Rightarrow> 'a valuation \<Rightarrow> bool) \<Rightarrow> 'a qbf \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "skolem_sem SKF (Matrix F) \<sigma> = sem_dnf F \<sigma>"
  | "skolem_sem SKF (Exists x F) \<sigma> = (skolem_sem SKF F (\<sigma>(x:=SKF x \<sigma>)))"  
  | "skolem_sem SKF (Forall x F) \<sigma> = (\<forall>v. skolem_sem SKF F (\<sigma>(x:=v)))"  
  
  lemma skolem_cert_aux: "skolem_sem SKF F \<sigma> \<Longrightarrow> sem_qbf_dnf_aux F \<sigma>"
    apply (induction F arbitrary: \<sigma>)
    apply auto
    done

  lemma skolem_cert: "closed F \<Longrightarrow> skolem_sem SKF F (\<lambda>_. False) \<Longrightarrow> sem_qbf_dnf F"
    by (simp add: sem_qbf_dnf_def skolem_cert_aux)
    
  fun herbrandt_sem :: "('a \<Rightarrow> 'a valuation \<Rightarrow> bool) \<Rightarrow> 'a qbf \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "herbrandt_sem HBF (Matrix F) \<sigma> = sem_cnf F \<sigma>"
  | "herbrandt_sem HBF (Forall x F) \<sigma> = (herbrandt_sem HBF F (\<sigma>(x:=HBF x \<sigma>)))"  
  | "herbrandt_sem HBF (Exists x F) \<sigma> = (\<exists>v. herbrandt_sem HBF F (\<sigma>(x:=v)))"
  
  lemma herbrandt_cert_aux: "sem_qbf_cnf_aux F \<sigma> \<Longrightarrow> herbrandt_sem HBF F \<sigma>"
    apply (induction F arbitrary: \<sigma>)
    apply auto
    done
    
  lemma herbrandt_cert: "closed F \<Longrightarrow> \<not>herbrandt_sem HBF F (\<lambda>_. False) \<Longrightarrow> \<not>sem_qbf_cnf F"  
    using herbrandt_cert_aux sem_closed_qbf_cnf by blast

        
    
    
    
  lemma "sem_qbf_aux F \<sigma> \<Longrightarrow> \<exists>SKF. skolem_sem SKF F \<sigma>"  
    apply (induction F arbitrary: \<sigma>)
    apply auto
    oops  
    
    
  convert matrix to aig, then merge!  

  semantics of both steps together should match skolemization semantics.
  
      
  fun merge :: "aig \<Rightarrow> idx qbf \<Rightarrow> aig"  
    
    
    
  
  

end


end
