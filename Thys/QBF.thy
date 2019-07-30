theory QBF
imports Main
begin

  section \<open>Shallow Matrix\<close>
  
  type_synonym 'a valuation = "'a \<Rightarrow> bool"
  type_synonym 'a afml = "'a valuation \<Rightarrow> bool"
  
  definition "is_deps F X \<equiv> \<forall>\<sigma> \<sigma>'. (\<forall>x\<in>X. \<sigma> x = \<sigma>' x) \<longrightarrow> F \<sigma> = F \<sigma>'"
  
  lemma is_deps_mono: "is_deps F X \<Longrightarrow> X\<subseteq>X' \<Longrightarrow> is_deps F X'"
    by (auto simp: is_deps_def)
  
  
  datatype 'a quant = Forall (qvar: 'a) | Exists (qvar: 'a)
  datatype 'a qbf = QBF (quants: "'a quant list") (matrix: "'a afml")

  fun sem_qbf_aux :: "'a quant list \<Rightarrow> 'a afml \<Rightarrow> 'a valuation \<Rightarrow> bool" where  
    "sem_qbf_aux [] m \<sigma> \<longleftrightarrow> m \<sigma>"
  | "sem_qbf_aux (Forall x # qs) m \<sigma> \<longleftrightarrow> (\<forall>v. sem_qbf_aux qs m (\<sigma>(x:=v)))"  
  | "sem_qbf_aux (Exists x # qs) m \<sigma> \<longleftrightarrow> (\<exists>v. sem_qbf_aux qs m (\<sigma>(x:=v)))"  

  definition "sem_qbf F \<equiv> sem_qbf_aux (quants F) (matrix F) (\<lambda>_. False)"
    
  definition "bound_vars F \<equiv> qvar`set (quants F)"
  definition "closed F \<equiv> is_deps (matrix F) (bound_vars F)"
    
  lemma sem_qbf_closed_aux: 
    "(is_deps m (qvar`set qs \<union> {x. \<sigma>1 x = \<sigma>2 x})) \<Longrightarrow> sem_qbf_aux qs m \<sigma>1 = sem_qbf_aux qs m \<sigma>2"
  proof (induction qs arbitrary: \<sigma>1 \<sigma>2)
    case Nil
    then show ?case by (auto simp: is_deps_def)
  next
    case (Cons a qs)
    
    have [simp]: "(insert x (X \<union> {x. \<sigma>1 x = \<sigma>2 x})) = (X \<union> {xa. xa \<noteq> x \<longrightarrow> \<sigma>1 xa = \<sigma>2 xa})" for x X
      by blast
      
    have "sem_qbf_aux qs m (\<sigma>1(qvar a := v)) = sem_qbf_aux qs m (\<sigma>2(qvar a := v))" for v
      apply (rule Cons.IH)
      using Cons.prems by auto
      
    then show ?case by (cases a) auto
  qed
      
  lemma sem_qbf_closed: "closed F \<Longrightarrow> sem_qbf_aux (quants F) (matrix F) \<sigma> = sem_qbf F"
    unfolding closed_def sem_qbf_def bound_vars_def
    using sem_qbf_closed_aux[of "matrix F" "quants F" \<sigma> "\<lambda>_. False"]
    using is_deps_mono 
    by blast
  
    
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
