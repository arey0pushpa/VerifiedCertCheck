theory QBF
imports Main "HOL-Library.Monad_Syntax" "List-Index.List_Index"
  "HOL-Eisbach.Eisbach_Tools"
begin

  section \<open>Shallow Matrix\<close>
  
  type_synonym 'a valuation = "'a \<Rightarrow> bool"
  type_synonym 'a afml = "'a valuation \<Rightarrow> bool"

  definition sForall ("\<^bold>\<forall>_. _" [1000,55] 80) where "\<^bold>\<forall>x. \<phi> \<equiv> \<lambda>\<sigma>. \<forall>v. \<phi> (\<sigma>(x:=v))"
  definition sExists ("\<^bold>\<exists>_. _" [1000,55] 80) where "\<^bold>\<exists>x. \<phi> \<equiv> \<lambda>\<sigma>. \<exists>v. \<phi> (\<sigma>(x:=v))"
  definition sAnd (infixr "\<^bold>\<and>" 95) where "\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2 \<equiv> \<lambda>\<sigma>. \<phi>\<^sub>1 \<sigma> \<and> \<phi>\<^sub>2 \<sigma>"
  definition sOr (infixr "\<^bold>\<or>" 90) where "\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2 \<equiv> \<lambda>\<sigma>. \<phi>\<^sub>1 \<sigma> \<or> \<phi>\<^sub>2 \<sigma>"
  definition sNot ("\<^bold>\<not>_" [100] 100) where "sNot \<phi>\<^sub>1 \<equiv> \<lambda>\<sigma>. \<not> \<phi>\<^sub>1 \<sigma>"
  
  definition "sVar x \<equiv> \<lambda>\<sigma>::_ \<Rightarrow> bool. \<sigma> x"
  
  definition sTop ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>_. True"
  definition sBot ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>_. False"
  
  lemma top_simps[simp]:
    "\<^bold>\<forall>x. \<^bold>\<top> = \<^bold>\<top>"
    "\<^bold>\<exists>x. \<^bold>\<top> = \<^bold>\<top>"
    "\<phi> \<^bold>\<and> \<^bold>\<top> = \<phi>"
    "\<^bold>\<top> \<^bold>\<and> \<phi> = \<phi>"
    "\<phi> \<^bold>\<or> \<^bold>\<top> = \<^bold>\<top>"
    "\<^bold>\<top> \<^bold>\<or> \<phi> = \<^bold>\<top>"
    "\<^bold>\<not>\<^bold>\<top> = \<^bold>\<bottom>"
    and bot_simps[simp]:
    "\<^bold>\<forall>x. \<^bold>\<bottom> = \<^bold>\<bottom>"
    "\<^bold>\<exists>x. \<^bold>\<bottom> = \<^bold>\<bottom>"
    "\<phi> \<^bold>\<and> \<^bold>\<bottom> = \<^bold>\<bottom>"
    "\<^bold>\<bottom> \<^bold>\<and> \<phi> = \<^bold>\<bottom>"
    "\<phi> \<^bold>\<or> \<^bold>\<bottom> = \<phi>"
    "\<^bold>\<bottom> \<^bold>\<or> \<phi> = \<phi>"
    "\<^bold>\<not>\<^bold>\<bottom> = \<^bold>\<top>"
    by (auto simp: sForall_def sExists_def sAnd_def sOr_def sNot_def sTop_def sBot_def)
    
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
    
  lemma and_left_commute[simp]: "a \<^bold>\<and> (b \<^bold>\<and> c) = b\<^bold>\<and>(a\<^bold>\<and>c)"  
    by (auto simp: sAnd_def sOr_def)
  
  lemma or_left_commute[simp]: "a \<^bold>\<or> (b \<^bold>\<or> c) = b\<^bold>\<or>(a\<^bold>\<or>c)"  
    by (auto simp: sAnd_def sOr_def)
    

  lemma de_morgan_cnf: 
    "a \<^bold>\<or> (b \<^bold>\<and> c) = (a \<^bold>\<or> b) \<^bold>\<and> (a \<^bold>\<or> c)"
    "(a \<^bold>\<and> b) \<^bold>\<or> c = (a \<^bold>\<or> c) \<^bold>\<and> (b \<^bold>\<or> c)"
    by (auto simp: sAnd_def sOr_def)
  
  lemma de_morgan_dnf: 
    "a \<^bold>\<and> (b \<^bold>\<or> c) = (a \<^bold>\<and> b) \<^bold>\<or> (a \<^bold>\<and> c)"
    "(a \<^bold>\<or> b) \<^bold>\<and> c = (a \<^bold>\<and> c) \<^bold>\<or> (b \<^bold>\<and> c)"
    by (auto simp: sAnd_def sOr_def)
  
  lemma and_idem[simp]: "a \<^bold>\<and> a = a" "a \<^bold>\<and> (a \<^bold>\<and> b) = a \<^bold>\<and> b" 
    and or_idem[simp]: "a \<^bold>\<or> a = a" "a \<^bold>\<or> (a \<^bold>\<or> b) = a \<^bold>\<or> b"
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
    
    
  term "\<^bold>\<forall>x. \<^bold>\<exists>y. sVar x \<^bold>\<and> \<^bold>\<not>sVar y"
  
  
  definition "is_dep X \<phi> \<equiv> \<forall>\<sigma>\<^sub>1 \<sigma>\<^sub>2. (\<forall>x\<in>X. \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x) \<longrightarrow> \<phi> \<sigma>\<^sub>1 = \<phi> \<sigma>\<^sub>2"
  
  abbreviation "closed \<phi> \<equiv> is_dep {}"

  lemma is_deps_mono: "X \<subseteq> X' \<Longrightarrow> is_dep X \<phi> \<Longrightarrow> is_dep X' \<phi>"
    unfolding is_dep_def
    apply auto
    by blast
  
  lemma is_deps_not_eq[simp]: "is_dep X (\<^bold>\<not>\<phi>) \<longleftrightarrow> is_dep X \<phi>"    
    unfolding is_dep_def sNot_def by auto
  
  lemma is_deps_var[simp]: "is_dep X (sVar x) \<longleftrightarrow> x\<in>X"  
    unfolding is_dep_def sVar_def
    by auto

  (* Syntactic procedure to compute (overapproximation) of dependent variables *)    
  lemma is_depsI:
    "is_dep X \<phi> \<Longrightarrow> is_dep (X-{x}) (\<^bold>\<forall>x. \<phi>)"
    "is_dep X \<phi> \<Longrightarrow> is_dep (X-{x}) (\<^bold>\<exists>x. \<phi>)"
    "\<lbrakk>is_dep X\<^sub>1 \<phi>\<^sub>1; is_dep X\<^sub>2 \<phi>\<^sub>2 \<rbrakk> \<Longrightarrow> is_dep (X\<^sub>1\<union>X\<^sub>2) (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2)"
    "\<lbrakk>is_dep X\<^sub>1 \<phi>\<^sub>1; is_dep X\<^sub>2 \<phi>\<^sub>2 \<rbrakk> \<Longrightarrow> is_dep (X\<^sub>1\<union>X\<^sub>2) (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2)"
    "is_dep X \<phi> \<Longrightarrow> is_dep X (\<^bold>\<not>\<phi>)"
    "is_dep {x} (sVar x)"
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
    
      
  
  lemma is_indep1_var[simp]: "is_indep1 x (sVar y) \<longleftrightarrow> x\<noteq>y"  
    unfolding is_indep1_def sVar_def
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
    
                
  lemma is_indep_var[simp]: "is_indep X (sVar x) \<longleftrightarrow> x\<notin>X" 
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
  datatype 'a quantifier = is_Forall: Forall (qvar: 'a) | is_Exists: Exists (qvar: 'a)
  
  fun quant :: "'a quantifier \<Rightarrow> 'a afml \<Rightarrow> 'a afml" where
    "quant (Forall x) = sForall x"
  | "quant (Exists x) = sExists x"
    
  definition quants :: "'a quantifier list \<Rightarrow> 'a afml \<Rightarrow> 'a afml" where "quants = foldr quant"
  
  lemma quants_simp[simp]:
    "quants [] \<phi> = \<phi>"
    "quants (q#qs) \<phi> = quant q (quants qs \<phi>)"
    "quants (qs\<^sub>1@qs\<^sub>2) \<phi> = quants qs\<^sub>1 (quants qs\<^sub>2 \<phi>)"
    unfolding quants_def by auto

  fun quants_induction_scheme :: "'a quantifier list \<Rightarrow> unit" where
    "quants_induction_scheme [] = ()"
  | "quants_induction_scheme (Forall _ # qs) = quants_induction_scheme qs"
  | "quants_induction_scheme (Exists _ # qs) = quants_induction_scheme qs"
  
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
    shows "quants qs\<^sub>1(\<^bold>\<forall>x. quants qs\<^sub>2 (C \<^bold>\<and> \<phi> \<^bold>\<and> (\<^bold>\<forall>x. C))) 
         = quants qs\<^sub>1(\<^bold>\<forall>x. quants qs\<^sub>2 (C \<^bold>\<and> \<phi>))"
  proof -
    from I have [simp]: "is_indep (qvar`set qs\<^sub>2) (\<^bold>\<forall>x. C)"
      by (simp add: is_indep1_ForallI is_indep_def) 

    show ?thesis  
      by (simp add: I quants_indep_pull forall_distrib_and)
        
  qed

  lemma exists_reduction: 
    assumes I: "is_indep (qvar`set qs\<^sub>2) C"  
    shows "quants qs\<^sub>1(\<^bold>\<exists>x. quants qs\<^sub>2 ((\<^bold>\<exists>x. C) \<^bold>\<or> C \<^bold>\<or> \<phi>))
         = quants qs\<^sub>1(\<^bold>\<exists>x. quants qs\<^sub>2 (C \<^bold>\<or> \<phi>))"
  proof -
    from I have [simp]: "is_indep (qvar`set qs\<^sub>2) (\<^bold>\<exists>x. C)"
      by (simp add: is_indep1_ExistsI is_indep_def) 

    show ?thesis  
      by (simp add: I quants_indep_pull exists_distrib_or)
        
  qed
  
    
  lemma resolution1: "(x \<^bold>\<and> r) \<^bold>\<or> (\<^bold>\<not>x \<^bold>\<and> r) = r"
    by (rule ext) (auto simp: sAnd_def sOr_def sNot_def)
  
  lemma resolution2: "(x \<^bold>\<or> r) \<^bold>\<and> (\<^bold>\<not>x \<^bold>\<or> r) = r"
    by (rule ext) (auto simp: sAnd_def sOr_def sNot_def)


  lemma resolution1': "R \<^bold>\<and> (x \<^bold>\<or> C\<^sub>1) \<^bold>\<and> (\<^bold>\<not>x \<^bold>\<or> C\<^sub>2) 
    = R \<^bold>\<and> (x \<^bold>\<or> C\<^sub>1) \<^bold>\<and> (\<^bold>\<not>x \<^bold>\<or> C\<^sub>2) \<^bold>\<and> (C\<^sub>1 \<^bold>\<or> C\<^sub>2)"
    by (rule ext) (auto simp: sAnd_def sOr_def sNot_def)
  
  lemma resolution2': "R \<^bold>\<or> (x \<^bold>\<and> C\<^sub>1) \<^bold>\<or> (\<^bold>\<not>x \<^bold>\<and> C\<^sub>2) 
    = R \<^bold>\<or> (x \<^bold>\<and> C\<^sub>1) \<^bold>\<or> (\<^bold>\<not>x \<^bold>\<and> C\<^sub>2) \<^bold>\<or> (C\<^sub>1 \<^bold>\<and> C\<^sub>2)"
    by (rule ext) (auto simp: sAnd_def sOr_def sNot_def)
    
    
    
  (* TODO: Move, and add appropriate sequent calculus rules! *)  
  definition entails (infix "\<turnstile>" 50) where "\<phi>\<turnstile>\<psi> \<equiv> \<forall>\<sigma>. \<phi> \<sigma> \<longrightarrow> \<psi> \<sigma>"  

  lemma fml_eqI[intro?]: "\<phi> \<turnstile> \<psi> \<Longrightarrow> \<psi> \<turnstile> \<phi> \<Longrightarrow> \<phi> = \<psi>"
    by (auto simp: entails_def)
  
  lemma ent_trans[trans]: 
    "\<phi>\<^sub>1 \<turnstile> \<phi>\<^sub>2 \<Longrightarrow> \<phi>\<^sub>2 \<turnstile> \<phi>\<^sub>3 \<Longrightarrow> \<phi>\<^sub>1 \<turnstile> \<phi>\<^sub>3" 
    "\<phi>\<^sub>1 \<turnstile> \<phi>\<^sub>2 \<Longrightarrow> \<phi>\<^sub>2 = \<phi>\<^sub>3 \<Longrightarrow> \<phi>\<^sub>1 \<turnstile> \<phi>\<^sub>3" 
    "\<phi>\<^sub>1 = \<phi>\<^sub>2 \<Longrightarrow> \<phi>\<^sub>2 \<turnstile> \<phi>\<^sub>3 \<Longrightarrow> \<phi>\<^sub>1 \<turnstile> \<phi>\<^sub>3" 
    by (auto simp: entails_def)
    
  lemma entails_same[simp,intro!]: "\<phi> \<turnstile> \<phi>"
    by (auto simp: entails_def)
    
  
  lemma forall_mono: "\<phi> \<turnstile> \<psi> \<Longrightarrow> \<^bold>\<forall>x. \<phi> \<turnstile> \<^bold>\<forall>x. \<psi>"
    and exists_mono: "\<phi> \<turnstile> \<psi> \<Longrightarrow> \<^bold>\<exists>x. \<phi> \<turnstile> \<^bold>\<exists>x. \<psi>"
    by (auto simp: sForall_def sExists_def entails_def)
  
  lemma quant_mono: "\<phi> \<turnstile> \<psi> \<Longrightarrow> quant q \<phi> \<turnstile> quant q \<psi>"
    using forall_mono exists_mono by (cases q) auto
    
  lemma quants_mono: "\<phi> \<turnstile> \<psi> \<Longrightarrow> quants qs \<phi> \<turnstile> quants qs \<psi>"  
    by (induction qs) (auto simp: quant_mono)
  
  lemma ent_and_red: 
    "\<phi> \<turnstile> \<phi>' \<Longrightarrow> \<phi> \<^bold>\<and> \<phi>' = \<phi>"  
    "\<phi> \<turnstile> \<phi>' \<Longrightarrow> \<phi>' \<^bold>\<and> \<phi> = \<phi>"  
    by (auto simp: entails_def sAnd_def)
    
  lemma ent_and_iff: "\<phi> \<turnstile> \<phi> \<^bold>\<and> \<phi>' \<longleftrightarrow> \<phi> \<turnstile> \<phi>'"
    by (auto simp: entails_def sAnd_def)

  lemmas ent_andI = ent_and_iff[THEN iffD1]  
        
  lemma ent_or_iff: "\<phi>' \<turnstile> \<phi> \<longleftrightarrow> \<phi> \<^bold>\<or> \<phi>' = \<phi>"
    by (auto simp: entails_def sOr_def) metis
    
  lemmas ent_orI = ent_or_iff[THEN iffD1]  
    
  lemma swap_ex_forall: "x\<noteq>y \<Longrightarrow> \<^bold>\<exists>x. \<^bold>\<forall>y. \<phi> \<turnstile> \<^bold>\<forall>y. \<^bold>\<exists>x. \<phi>"
    by (auto simp: entails_def sExists_def sForall_def fun_upd_twist)
    
  lemma swap_exs_forall: "quants (filter is_Exists qs) (\<^bold>\<forall>x. \<phi>) \<turnstile> \<^bold>\<forall>x. quants (filter is_Exists qs) \<phi>"
    apply (induction qs rule: quants_induct)
    apply auto
    by (smt ent_trans(1) entails_def exists_mono quant_dup(3) quant_dup(4) sExists_def sForall_def swap_ex_forall)
    
    
  lemma quants_reorder_ex_forall:
    assumes "distinct (map qvar qs)"  
    shows "quants (filter is_Exists qs) (quants (filter is_Forall qs) \<phi>) \<turnstile> quants qs \<phi>"
    using assms
    apply (induction qs rule: quants_induct)
    apply (auto simp: exists_mono)
    by (meson ent_trans(1) forall_mono swap_exs_forall)
  
    
  lemma model_generation_aux:
    assumes "is_indep (qvar`set qs\<^sub>2) C"
    assumes "C \<turnstile> quants qs\<^sub>2 C'"
    assumes "C \<^bold>\<and> C' \<turnstile> \<phi>"
    shows "quants (qs\<^sub>1@qs\<^sub>2) (\<phi> \<^bold>\<or> C) = quants (qs\<^sub>1@qs\<^sub>2) \<phi>"  
  proof -
    have 1: "C \<turnstile> quants qs\<^sub>2 \<phi>"
    proof -
      have "C = C \<^bold>\<and> quants qs\<^sub>2 C'" 
        using ent_and_red[OF assms(2)]
        by (auto)  
      also have "\<dots> = quants qs\<^sub>2 (C \<^bold>\<and> C')"  
        by (simp add: assms(1) quants_indep_pull)
      also have "\<dots> \<turnstile> quants qs\<^sub>2 \<phi>"
        by (simp add: assms(3) quants_mono)
      finally show ?thesis .
    qed  
      
    have "quants (qs\<^sub>2) (\<phi> \<^bold>\<or> C) = quants qs\<^sub>2 \<phi> \<^bold>\<or> C"
      by (simp add: assms(1) quants_indep_pull(3))
    also note ent_orI[OF 1]
    finally show ?thesis by simp
  qed    
  
  lemma model_generation_v1:
    assumes "distinct (map qvar qs\<^sub>2)"
    assumes "is_indep (qvar`set qs\<^sub>2) C"
    assumes "C \<turnstile> quants (filter is_Exists qs\<^sub>2) (quants (filter is_Forall qs\<^sub>2) C')"
    assumes "C \<^bold>\<and> C' \<turnstile> \<phi>"
    shows "quants (qs\<^sub>1@qs\<^sub>2) (\<phi> \<^bold>\<or> C) = quants (qs\<^sub>1@qs\<^sub>2) \<phi>"  
    using assms ent_trans(1) model_generation_aux quants_reorder_ex_forall 
    by blast
  
  
  
    
    
    
section \<open>CNF/DNF Matrix\<close>    
        
  datatype 'a literal = is_pos: Pos (lvar: 'a) | Neg (lvar: 'a)
  type_synonym 'a clause = "'a literal set"
  type_synonym 'a matrix = "'a clause set"

  fun sem_lit :: "'a literal \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "sem_lit (Pos x) = sVar x"
  | "sem_lit (Neg x) = \<^bold>\<not> sVar x"

  lemma sem_lit_alt: "sem_lit l = (case l of Pos x \<Rightarrow> sVar x | Neg x \<Rightarrow> \<^bold>\<not> sVar x)"
    by (auto split: literal.split simp: sVar_def sNot_def)

  lemma sem_lit_alt': "sem_lit l \<sigma> = (case l of Pos x \<Rightarrow> \<sigma> x | Neg x \<Rightarrow> \<not> \<sigma> x)"
    by (auto split: literal.split simp: sVar_def sNot_def)
    
  definition sem_clause_cnf :: "'a clause \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "sem_clause_cnf C \<sigma> \<equiv> \<exists>l\<in>C. sem_lit l \<sigma>"

  definition sem_cnf :: "'a matrix \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "sem_cnf F \<sigma> \<equiv> \<forall>C\<in>F. sem_clause_cnf C \<sigma>"

  definition sem_clause_dnf :: "'a clause \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "sem_clause_dnf C \<sigma> \<equiv> \<forall>l\<in>C. sem_lit l \<sigma>"

  definition sem_dnf :: "'a matrix \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "sem_dnf F \<sigma> \<equiv> \<exists>C\<in>F. sem_clause_dnf C \<sigma>"

  lemma sem_clause_cnf_simps[simp]:  
    "sem_clause_cnf {} = \<^bold>\<bottom>"
    "sem_clause_cnf (insert l C) = sem_lit l \<^bold>\<or> sem_clause_cnf C"
    "sem_clause_cnf (C\<^sub>1 \<union> C\<^sub>2) = sem_clause_cnf C\<^sub>1 \<^bold>\<or> sem_clause_cnf C\<^sub>2"
    by (auto simp: sem_clause_cnf_def sOr_def fun_eq_iff sBot_def)
    
  lemma sem_clause_dnf_simps[simp]:  
    "sem_clause_dnf {} = \<^bold>\<top>"
    "sem_clause_dnf (insert l C) = sem_lit l \<^bold>\<and> sem_clause_dnf C"
    "sem_clause_dnf (C\<^sub>1 \<union> C\<^sub>2) = sem_clause_dnf C\<^sub>1 \<^bold>\<and> sem_clause_dnf C\<^sub>2"
    by (auto simp: sem_clause_dnf_def sAnd_def fun_eq_iff sTop_def)
    
  lemma sem_cnf_simps[simp]:
    "sem_cnf {} = \<^bold>\<top>"
    "sem_cnf (insert C F) = sem_clause_cnf C \<^bold>\<and> sem_cnf F"
    "sem_cnf (F\<^sub>1 \<union> F\<^sub>2) = sem_cnf F\<^sub>1 \<^bold>\<and> sem_cnf F\<^sub>2"
    by (auto simp: sem_cnf_def fun_eq_iff sAnd_def sTop_def)
    
  lemma sem_dnf_simps[simp]:
    "sem_dnf {} = \<^bold>\<bottom>"
    "sem_dnf (insert C F) = sem_clause_dnf C \<^bold>\<or> sem_dnf F"  
    "sem_dnf (F\<^sub>1 \<union> F\<^sub>2) = sem_dnf F\<^sub>1 \<^bold>\<or> sem_dnf F\<^sub>2"  
    by (auto simp: sem_dnf_def sOr_def fun_eq_iff sBot_def)

    
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
    by (auto simp: sem_lit_alt' split: literal.split)
  
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
    

  lemma sem_cnf_indep1I: "x\<notin>vars_of_matrix F \<Longrightarrow> is_indep1 x (sem_cnf F)"  
    by (clarsimp simp: is_indep1_def) (metis fun_upd_other sem_cnf_dep)
        
  lemma sem_dnf_indep1I: "x\<notin>vars_of_matrix F \<Longrightarrow> is_indep1 x (sem_dnf F)"  
    by (clarsimp simp: is_indep1_def) (metis fun_upd_other sem_dnf_dep)
    
  lemma sem_cnf_indepI: "vars_of_matrix F \<inter> X = {} \<Longrightarrow> is_indep X (sem_cnf F)"  
    by (meson disjoint_iff_not_equal is_indep_def sem_cnf_indep1I)
    
  lemma sem_dnf_indepI: "vars_of_matrix F \<inter> X = {} \<Longrightarrow> is_indep X (sem_dnf F)"  
    by (meson disjoint_iff_not_equal is_indep_def sem_dnf_indep1I)
    
  corollary sem_clause_cnf_indepI: "vars_of_clause C \<inter> X = {} \<Longrightarrow> is_indep X (sem_clause_cnf C)"
    using sem_cnf_indepI[of "{C}" X]
    by simp
    
  corollary sem_clause_dnf_indepI: "vars_of_clause C \<inter> X = {} \<Longrightarrow> is_indep X (sem_clause_dnf C)"
    using sem_dnf_indepI[of "{C}" X]
    by simp
    
    
  definition "filter_clause P C \<equiv> { l\<in>C. P (lvar l) }"
  definition "filter_matrix P F \<equiv> filter_clause P ` F"

  
  definition "taut_free_clause C \<equiv> \<nexists>x. Pos x \<in> C \<and> Neg x \<in> C"
  definition "taut_free F \<equiv> \<forall>C\<in>F. taut_free_clause C"
  
  lemma taut_free_empty[simp]: "taut_free {}" by (auto simp: taut_free_def)
  
  
  lemma filter_forall_clause_cnf: "taut_free_clause C \<Longrightarrow> sem_clause_cnf (filter_clause (\<lambda>y. y\<noteq>x) C) = \<^bold>\<forall>x. sem_clause_cnf C"
    apply (auto simp: fun_eq_iff sForall_def filter_clause_def sem_clause_cnf_def)
    apply (auto simp: taut_free_clause_def sem_lit_alt' split: literal.splits)
    by metis

  lemma filter_exists_clause_dnf: "taut_free_clause C \<Longrightarrow> sem_clause_dnf (filter_clause (\<lambda>y. y\<noteq>x) C) = \<^bold>\<exists>x. sem_clause_dnf C"
    apply (intro ext iffI)
    unfolding fun_eq_iff sExists_def filter_clause_def sem_clause_dnf_def taut_free_clause_def sem_lit_alt'
    subgoal
      apply (simp split: literal.splits)
      by smt
    subgoal by (auto split: literal.splits)
    done
    
        
  lemma filter_forall_cnf: "taut_free F \<Longrightarrow> sem_cnf (filter_matrix (\<lambda>y. y\<noteq>x) F) = \<^bold>\<forall>x. sem_cnf F"
    unfolding taut_free_def sem_cnf_def filter_matrix_def
    apply (auto simp: filter_forall_clause_cnf)
    apply (auto simp: sForall_def) 
      (* TODO: Commute sForall over set-based-forall. 
        Or, probably, use quantification over sets rather than single variables
        as abstraction *)
    done
    

definition "assert \<Phi> \<equiv> if \<Phi> then Some () else None"    
lemma assert_simps[simp]: 
  "assert True = Some ()" 
  "assert False = None"
  "assert \<Phi> = Some x \<longleftrightarrow> \<Phi>"
  "assert \<Phi> = None \<longleftrightarrow> \<not>\<Phi>"
  by (auto simp: assert_def)
    
        

type_synonym ('i,'a) cmap = "'i \<rightharpoonup> 'a clause"  


lemma ran_split2:
  fixes m :: "'k \<rightharpoonup> 'v"
  assumes "m k = Some v" "m k' = Some v'"
  obtains m' :: "'k \<rightharpoonup> 'v"  where "ran m = insert v (insert v' (ran m'))"
  using assms ran_def by fastforce
  
  
(* TODO: Move *)
lemma quant_top[simp]: "quant q \<^bold>\<top> = \<^bold>\<top>" by (cases q; auto)
lemma quant_bot[simp]: "quant q \<^bold>\<bottom> = \<^bold>\<bottom>" by (cases q; auto)

lemma quants_top[simp]: "quants qs \<^bold>\<top> = \<^bold>\<top>" by (induction qs; auto)
lemma quants_bot[simp]: "quants qs \<^bold>\<bottom> = \<^bold>\<bottom>" by (induction qs; auto)

lemma is_indep_cancel: "is_indep (qvar`set qs) \<phi> \<Longrightarrow> quants qs \<phi> = \<phi>"
  using quants_indep_pull(1)[where \<phi>\<^sub>2="\<^bold>\<top>", simplified] by simp

  
lemma split_by_indexes:
  assumes "\<forall>x'\<in>C'. \<forall>x\<in>C. index xs x < index xs x'"
  assumes "C' \<subseteq> set xs"
  assumes "distinct xs"
  obtains xs\<^sub>1 xs\<^sub>2 where "xs = xs\<^sub>1@xs\<^sub>2" "C \<inter> set xs\<^sub>2 = {}" "C' \<subseteq> set xs\<^sub>2"
proof -  
  have "finite C'" using assms(2) finite_subset by blast
  then have "\<exists>xs\<^sub>1 xs\<^sub>2. xs = xs\<^sub>1@xs\<^sub>2 \<and> C \<inter> set xs\<^sub>2 = {} \<and> C' \<subseteq> set xs\<^sub>2" 
    using assms(1,2) 
  proof induction
    case empty
    then show ?case apply auto
      by (metis append_Nil2 inf_bot_right list.set(1))
  next
    case (insert x C')
    
    then obtain xs\<^sub>1 xs\<^sub>2 where [simp]: "xs = xs\<^sub>1 @ xs\<^sub>2" and IH: "C \<inter> set xs\<^sub>2 = {}" "C' \<subseteq> set xs\<^sub>2"
      by blast
    
    from insert.prems consider "x\<in>set xs\<^sub>1" | "x\<in>set xs\<^sub>2" by auto
    then show ?case proof cases
      case 1
      then obtain xs11 xs12 where [simp]: "xs\<^sub>1 = xs11@x#xs12" by (auto simp: in_set_conv_decomp)
      
      have "x\<notin>C" using insert.prems(1) by auto
      
      moreover have "y\<notin>set xs12" if "y\<in>C" for y
      proof  
        assume "y\<in>set xs12"
        then obtain xsa xsb xsc where XSF: "xs = xsa@x#xsb@y#xsc"
          by (auto simp: in_set_conv_decomp)
        with \<open>distinct xs\<close> have "index xs x < index xs y"
          unfolding XSF
          by (auto simp: index_append) 
        thus False
          using insert.prems(1) less_asym that by auto  
      qed    
      ultimately show ?thesis
        apply -
        apply (rule exI[where x="xs11"])
        apply (rule exI[where x="x#xs12@xs\<^sub>2"])
        using IH by auto
    next
      case 2
      then show ?thesis using IH by auto
    qed  
  qed
  then show ?thesis using that by blast
qed  
  
  


  
  
  
  
  

locale qbf_formula =
  fixes qs :: "'a quantifier list"
  fixes m :: "'a matrix"

  assumes no_taut: "taut_free m"
  assumes closed: "qvar`set qs = vars_of_matrix m"  
  assumes no_dup_quant: "distinct (map qvar qs)"
begin

  definition "index_of_var \<equiv> index (map qvar qs)"
  definition "is_ex_var x \<equiv> Exists x \<in> set qs"
  definition "is_all_var x \<equiv> Forall x \<in> set qs"

  definition "resolve x c1 c2 \<equiv> do {
    assert (Pos x \<in> c1);
    assert (Neg x \<in> c2);
    let resolvent = (c1 - {Pos x}) \<union> (c2 - {Neg x});
    Some resolvent
  }"

  
  (* Unsat Proofs *)
    
  lemma resolve_cnf_correct:
    assumes F: "C1 \<in> F" "C2 \<in> F" 
        and R: "resolve x C1 C2 = Some cN"
    shows "sem_cnf (insert cN F) = sem_cnf F"
    using R
    unfolding resolve_def
    apply (clarsimp split: Option.bind_splits)
  proof -
  
    from F obtain F' where [simp]: "F = insert C1 (insert C2 F')" by blast
  
    assume C: "Pos x \<in> C1" "Neg x \<in> C2" and "cN = C1 - {Pos x} \<union> (C2 - {Neg x})"
    
    from C obtain C1' C2' where [simp]: "C1 = insert (Pos x) C1'" "C2 = insert (Neg x) C2'"
      by blast

    show "sem_cnf F \<^bold>\<and>
        (sem_clause_cnf (C1 - {Pos x}) \<^bold>\<or> sem_clause_cnf (C2 - {Neg x})) =
        sem_cnf F" 
      apply simp
      by (smt insert_Diff_single or_commute resolution1' sem_clause_cnf_simps(2) sem_lit.simps(1) sem_lit.simps(2))         
  qed      
  
  definition unsat_invar :: "('i,'a) cmap \<Rightarrow> bool"
    where "unsat_invar cmap \<equiv> 
      taut_free (ran cmap) 
    \<and> quants qs (sem_cnf m) = quants qs (sem_cnf (ran cmap))"

    
  lemma unsat_invar_init: "ran cmap = m \<Longrightarrow> unsat_invar cmap"  
    unfolding unsat_invar_def using no_taut by auto
    
  lemma unsat_invar_final: 
    "\<lbrakk>unsat_invar cmap; {} \<in> ran cmap\<rbrakk> \<Longrightarrow> quants qs (sem_cnf m) = \<^bold>\<bottom>"
    unfolding unsat_invar_def
    by (auto elim: Set.set_insert)
  
    
    
  definition "resolution_step idN x id1 id2 cmap  \<equiv> do {
    c1 \<leftarrow> cmap id1;
    c2 \<leftarrow> cmap id2;
    assert (cmap idN = None);
    resolvent \<leftarrow> resolve x c1 c2;
    assert (taut_free_clause resolvent);
    let cmap = cmap(idN \<mapsto> resolvent);
    Some cmap
  }"
  
  lemma resolution_step_unsat:
    "\<lbrakk>unsat_invar cmap; resolution_step idN x id1 id2 cmap  = Some cmap'\<rbrakk> 
      \<Longrightarrow> unsat_invar cmap'"
    unfolding resolution_step_def
    apply (auto simp: unsat_invar_def taut_free_def split: Option.bind_splits)
    by (metis ranI resolve_cnf_correct sem_cnf_simps(2))
    

  definition "reduce_all x c \<equiv> do {
    assert (is_all_var x);
    let i = index_of_var x;
    assert (\<forall>y\<in>vars_of_clause c. index_of_var y \<le> i);
    let c = filter_clause (\<lambda>y. y\<noteq>x) c;
    Some c
  }"  
    
  (* TODO: Move *)
  lemma taut_free_clause_mono: "C\<subseteq>C' \<Longrightarrow> taut_free_clause C' \<Longrightarrow> taut_free_clause C"
    by (auto simp: taut_free_clause_def)
  
  lemma filter_clause_ss: "filter_clause P C \<subseteq> C"  
    by (auto simp: filter_clause_def)
    
  
  
  lemma reduce_all_correct:
    assumes "reduce_all x c = Some c'"  
    assumes "taut_free_clause c" "c \<in> F" 
    shows "taut_free_clause c' \<and> quants qs (sem_clause_cnf c' \<^bold>\<and> sem_cnf F) = quants qs (sem_cnf F)"
    using assms unfolding reduce_all_def
    apply (clarsimp split: Option.bind_splits simp: filter_forall_clause_cnf elim!: Set.set_insert)
  proof (intro conjI)
    assume "is_all_var x"
    then obtain qs\<^sub>1 qs\<^sub>2 where [simp]: "qs = qs\<^sub>1 @ Forall x # qs\<^sub>2"
      unfolding is_all_var_def by (auto simp: in_set_conv_decomp)
  
    assume "\<forall>y\<in>vars_of_clause c. index_of_var y \<le> index_of_var x"  
    then have V: "vars_of_clause c \<inter> qvar ` set qs\<^sub>2 = {}"  
      unfolding index_of_var_def using no_dup_quant
      by (auto 0 3 simp: in_set_conv_decomp index_append)
      
      
    fix B  
    show "quants qs (sem_clause_cnf c \<^bold>\<and> sem_cnf B \<^bold>\<and> (\<^bold>\<forall>x. sem_clause_cnf c)) =
             quants qs (sem_clause_cnf c \<^bold>\<and> sem_cnf B)"  
      apply simp
      apply (rule forall_reduction)
      apply (rule sem_clause_cnf_indepI)
      by fact
      
    assume "taut_free_clause c"  
    then show "taut_free_clause (filter_clause (\<lambda>y. y \<noteq> x) c)"
      by (rule taut_free_clause_mono[OF filter_clause_ss])
      
  qed      
      
  definition "reduction_step_cnf idN x id1 cmap \<equiv> do {
    c \<leftarrow> cmap id1;
    assert (cmap idN = None);
    c' \<leftarrow> reduce_all x c;
    let cmap = cmap(idN \<mapsto> c');
    Some cmap
  }"    
    
  lemma reduction_step_unsat:
    "\<lbrakk>unsat_invar cmap; reduction_step_cnf idN x id1 cmap  = Some cmap'\<rbrakk> 
      \<Longrightarrow> unsat_invar cmap'"
    unfolding reduction_step_cnf_def
    apply (auto simp: unsat_invar_def taut_free_def split: Option.bind_splits)
    apply (auto dest!: ranI[of cmap] reduce_all_correct)
    done
    
  (* SAT Proofs *)    
    
  lemma resolve_dnf_correct:
    assumes F: "C1 \<in> F" "C2 \<in> F" 
        and R: "resolve x C1 C2 = Some cN"
    shows "sem_dnf (insert cN F) = sem_dnf F"
    using R
    unfolding resolve_def
    apply (clarsimp split: Option.bind_splits)
  proof -
  
    from F obtain F' where [simp]: "F = insert C1 (insert C2 F')" by blast
  
    assume C: "Pos x \<in> C1" "Neg x \<in> C2" and "cN = C1 - {Pos x} \<union> (C2 - {Neg x})"
    
    from C obtain C1' C2' where [simp]: "C1 = insert (Pos x) C1'" "C2 = insert (Neg x) C2'"
      by blast

    show "sem_dnf F \<^bold>\<or>
        (sem_clause_dnf (C1 - {Pos x}) \<^bold>\<and> sem_clause_dnf (C2 - {Neg x})) =
        sem_dnf F" 
      apply simp
      by (smt and_commute insert_Diff_single resolution2' sem_clause_dnf_simps(2) sem_lit.simps(1) sem_lit.simps(2))         
      
  qed      
  
  definition sat_invar :: "('i,'a) cmap \<Rightarrow> bool"
    where "sat_invar cmap \<equiv> 
      taut_free (ran cmap) 
    \<and> quants qs (sem_cnf m) = quants qs (sem_cnf m \<^bold>\<or> sem_dnf (ran cmap))"

  lemma sat_invar_init: "cmap = Map.empty \<Longrightarrow> sat_invar cmap"  
    unfolding sat_invar_def using no_taut by auto
    
  lemma sat_invar_final: 
    "\<lbrakk>sat_invar cmap; {} \<in> ran cmap\<rbrakk> \<Longrightarrow> quants qs (sem_cnf m) = \<^bold>\<top>"
    unfolding sat_invar_def
    by (auto elim: Set.set_insert)
    
    
  lemma resolution_step_sat:
    "\<lbrakk>sat_invar cmap; resolution_step idN x id1 id2 cmap  = Some cmap'\<rbrakk> 
      \<Longrightarrow> sat_invar cmap'"
    unfolding resolution_step_def
    apply (auto simp: sat_invar_def taut_free_def split: Option.bind_splits)
    by (smt or_left_commute ranI resolve_dnf_correct sem_dnf_simps(2))
    

  definition "reduce_ex x c \<equiv> do {
    assert (is_ex_var x);
    let i = index_of_var x;
    assert (\<forall>y\<in>vars_of_clause c. index_of_var y \<le> i);
    let c = filter_clause (\<lambda>y. y\<noteq>x) c;
    Some c
  }"  
  
  
  thm filter_forall_clause_cnf
  thm filter_exists_clause_dnf
  
  thm exists_reduction
  
  lemma reduce_ex_correct:
    assumes "reduce_ex x c = Some c'"  
    assumes "taut_free_clause c" "c \<in> F" 
    shows "taut_free_clause c' \<and> quants qs (sem_clause_dnf c' \<^bold>\<or> sem_dnf F \<^bold>\<or> \<phi>) = quants qs (sem_dnf F \<^bold>\<or> \<phi>)"
    using assms unfolding reduce_ex_def
    apply (clarsimp split: Option.bind_splits simp: filter_exists_clause_dnf elim!: Set.set_insert)
  proof (intro conjI)
    assume "is_ex_var x"
    then obtain qs\<^sub>1 qs\<^sub>2 where [simp]: "qs = qs\<^sub>1 @ Exists x # qs\<^sub>2"
      unfolding is_ex_var_def by (auto simp: in_set_conv_decomp)
  
    assume "\<forall>y\<in>vars_of_clause c. index_of_var y \<le> index_of_var x"  
    then have V: "vars_of_clause c \<inter> qvar ` set qs\<^sub>2 = {}"  
      unfolding index_of_var_def using no_dup_quant
      by (auto 0 3 simp: in_set_conv_decomp index_append)
    hence [simp]: "is_indep (qvar ` set qs\<^sub>2) (sem_clause_dnf c)"
      by (simp add: sem_clause_dnf_indepI) 
      
    fix B  
    show "quants qs (\<phi> \<^bold>\<or> sem_clause_dnf c \<^bold>\<or> sem_dnf B \<^bold>\<or> (\<^bold>\<exists>x. sem_clause_dnf c)) =
             quants qs (\<phi> \<^bold>\<or> sem_clause_dnf c \<^bold>\<or> sem_dnf B)"
      using exists_reduction[of qs\<^sub>2 "sem_clause_dnf c" qs\<^sub>1 x "\<phi> \<^bold>\<or> sem_dnf B"]
      by simp
      
    assume "taut_free_clause c"  
    then show "taut_free_clause (filter_clause (\<lambda>y. y \<noteq> x) c)"
      by (rule taut_free_clause_mono[OF filter_clause_ss])
      
  qed      
      
  definition "reduction_step_dnf idN x id1 cmap \<equiv> do {
    c \<leftarrow> cmap id1;
    assert (cmap idN = None);
    c' \<leftarrow> reduce_ex x c;
    let cmap = cmap(idN \<mapsto> c');
    Some cmap
  }"    
    
  lemma reduction_step_sat:
    "\<lbrakk>sat_invar cmap; reduction_step_dnf idN x id1 cmap  = Some cmap'\<rbrakk> 
      \<Longrightarrow> sat_invar cmap'"
    unfolding reduction_step_dnf_def
    apply (auto simp: sat_invar_def taut_free_def split: Option.bind_splits)
    apply (auto dest!: ranI[of cmap] reduce_ex_correct[where \<phi> = "sem_cnf m"])
    done

  definition "check_initial_cube C C' \<equiv> do {
    assert (taut_free_clause C \<and> taut_free_clause C');
    assert (\<forall>x\<in>vars_of_clause C'. is_ex_var x \<and> (\<forall>y\<in>vars_of_clause C. index_of_var y < index_of_var x));
    assert (sem_clause_dnf C \<^bold>\<and> sem_clause_dnf C' \<turnstile> sem_cnf m);
    Some ()
  }"
  
  lemma vars_of_filter_clause[simp]: "vars_of_clause (filter_clause P C) = {x \<in> vars_of_clause C. P x}"
    by (auto simp: vars_of_clause_def filter_clause_def lvar_def var_of_lit_alt)
  
  
  (* TODO: Move *)  
  lemma entails_top_simps[simp]:
    "C \<turnstile> \<^bold>\<top>"
    "\<^bold>\<top> \<turnstile> C \<longleftrightarrow> C=\<^bold>\<top>"
    and entails_bot_simps[simp]:
    "C \<turnstile> \<^bold>\<bottom> \<longleftrightarrow> C=\<^bold>\<bottom>"
    "\<^bold>\<bottom> \<turnstile> C"
    by (auto simp: entails_def sBot_def sTop_def)
  
    

  (* TODO: Move *)      
  lemma map_eq_append_conv: "map f xs = fxs\<^sub>1@fxs\<^sub>2 \<longleftrightarrow> (\<exists>xs\<^sub>1 xs\<^sub>2. xs=xs\<^sub>1@xs\<^sub>2 \<and> fxs\<^sub>1 = map f xs\<^sub>1 \<and> fxs\<^sub>2 = map f xs\<^sub>2)"
    apply auto
    by (metis append_eq_conv_conj append_take_drop_id drop_map take_map)
  
  
  
  lemma check_initial_cube_correct:
    assumes "check_initial_cube C C' = Some ()"
    shows "quants qs (sem_cnf m \<^bold>\<or> cubes \<^bold>\<or> sem_clause_dnf C) = quants qs (sem_cnf m \<^bold>\<or> cubes)"
      and "taut_free_clause C"
    using assms unfolding check_initial_cube_def
  proof (all \<open>clarsimp split: Option.bind_splits\<close>)
    assume 
      IDXS: "\<forall>x\<in>vars_of_clause C'. is_ex_var x \<and> (\<forall>y\<in>vars_of_clause C. index_of_var y < index_of_var x)"
      and
      IMPL: "sem_clause_dnf C \<^bold>\<and> sem_clause_dnf C' \<turnstile> sem_cnf m"
  
    assume TF_C: "taut_free_clause C" 
      and TF_C': "taut_free_clause C'"
      
    obtain qs\<^sub>1 qs\<^sub>2 where 
      [simp]: "qs = qs\<^sub>1@qs\<^sub>2" 
      and C_djv: "vars_of_clause C \<inter> qvar`set qs\<^sub>2 = {}"
      and VC'ex: "vars_of_clause C' \<subseteq> qvar`set (filter is_Exists qs\<^sub>2)"
    proof -
      from IDXS have 
        "\<forall>x'\<in>vars_of_clause C'. \<forall>x\<in>vars_of_clause C. index (map qvar qs) x < index (map qvar qs) x'"
        "vars_of_clause C' \<subseteq> set (map qvar qs)"
        unfolding index_of_var_def is_ex_var_def
        by force+
      from split_by_indexes[OF this no_dup_quant] obtain qqs\<^sub>1 qqs\<^sub>2 where
        1: "map qvar qs = qqs\<^sub>1 @ qqs\<^sub>2" 
        and 2: "vars_of_clause C \<inter> set qqs\<^sub>2 = {}" "vars_of_clause C' \<subseteq> set qqs\<^sub>2"
        .
      from 1 obtain qs\<^sub>1 qs\<^sub>2 where QSEQ[simp]: "qs = qs\<^sub>1@qs\<^sub>2" and [simp]: "qqs\<^sub>1 = map qvar qs\<^sub>1" "qqs\<^sub>2 = map qvar qs\<^sub>2" 
        by (auto simp: map_eq_append_conv) 
        
      from 2 have "vars_of_clause C \<inter> qvar`set qs\<^sub>2 = {}" by auto 
      moreover from 2 IDXS have "vars_of_clause C' \<subseteq> qvar`set (filter is_Exists qs\<^sub>2)" 
        using no_dup_quant
        unfolding is_ex_var_def
        apply (auto)
        by (smt IntI empty_iff imageI mem_Collect_eq quantifier.disc(4) quantifier.sel(2) set_map subset_eq)
      ultimately show ?thesis using that by simp
    qed    
      
    from IMPL have IMPL': "sem_clause_dnf C \<^bold>\<and> sem_clause_dnf C' \<turnstile> sem_cnf m \<^bold>\<or> cubes"
      by (simp add: ent_or_iff)
      
    from C_djv have INDEP_C: "is_indep (qvar`set qs\<^sub>2) (sem_clause_dnf C)" 
      by (rule sem_clause_dnf_indepI)
      
      
    from VC'ex TF_C' have QEC': "quants (filter is_Exists qs\<^sub>2) (sem_clause_dnf C') = \<^bold>\<top>"  
      apply (induction qs\<^sub>2 arbitrary: C' rule: rev_induct)
      apply (auto simp: is_Exists_def filter_exists_clause_dnf[symmetric])
      using taut_free_clause_mono[OF filter_clause_ss]
      by (smt insertE mem_Collect_eq subset_eq vars_of_filter_clause)
      
    have "set (filter is_Exists qs\<^sub>2) \<inter> set (filter is_Forall qs\<^sub>2) = {}" by auto
    with no_dup_quant have "qvar`set (filter is_Exists qs\<^sub>2) \<inter> qvar`set (filter is_Forall qs\<^sub>2) = {}" 
      apply (simp; safe)
      by (metis (no_types, hide_lams) distinct_map inj_on_def quantifier.distinct_disc(2))
    with VC'ex have "vars_of_clause C' \<inter> qvar`set (filter is_Forall qs\<^sub>2) = {}"
      by blast
    hence "is_indep (qvar`set (filter is_Forall qs\<^sub>2)) (sem_clause_dnf C')"  
      by (rule sem_clause_dnf_indepI)
    from is_indep_cancel[OF this] have 
      1: "sem_clause_dnf C \<turnstile> quants (filter is_Exists qs\<^sub>2) (quants (filter is_Forall qs\<^sub>2) (sem_clause_dnf C'))"
      by (simp add: QEC')
        
      
    from model_generation_v1[OF _ INDEP_C 1 IMPL', of qs\<^sub>1] no_dup_quant 
    show "quants qs (cubes \<^bold>\<or> sem_clause_dnf C \<^bold>\<or> sem_cnf m) = quants qs (cubes \<^bold>\<or> sem_cnf m)"
      by auto
      
  qed
      
  definition "initial_cube_step idN C C' cmap \<equiv> do {
    assert (cmap idN = None);
    check_initial_cube C C';
    let cmap = cmap(idN \<mapsto> C);
    Some cmap
  }"    
  
  lemma initial_cube_step:
    "\<lbrakk>sat_invar cmap; initial_cube_step idN C C' cmap = Some cmap'\<rbrakk> 
      \<Longrightarrow> sat_invar cmap'"
    unfolding initial_cube_step_def
    apply (auto simp: sat_invar_def taut_free_def check_initial_cube_correct(2) split: Option.bind_splits)
    by (smt check_initial_cube_correct(1) or_commute or_left_commute)
      
    
  (* Summary *)  
  
  (* Unsat proofs *)
  thm unsat_invar_init reduction_step_unsat resolution_step_unsat unsat_invar_final
  
  (* Sat proofs *)
  thm sat_invar_init reduction_step_sat resolution_step_sat initial_cube_step sat_invar_final
  
end  
    
    
    
oops
  xxx, ctd here: We have formalized the correctness of the basic proof steps. 
  
  Next, think about implementation. In particular:
    Shall we automatically reduce all clauses/cubes
    Implement a proof preprocessor that generates a proof that
      * uses internal IDs, for
        UNSAT: First IDs to original clauses, then increment ids with every proof step
        SAT: Start with 0, increment IDs
  
      * contains full witnesses (C' part) for initial cubes
      
      * uses a binary format that can easily be mmap'ed. 
    
    other ideas:
      if clauses are sorted, tautology check becomes simpler
      alternatively, we can sort clauses by quantifier index, then reduction
      becomes simpler?
  
  
  

end
