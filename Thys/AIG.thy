theory AIG
imports Main
begin
  section \<open>AIGs\<close>

  type_synonym idx = nat
  datatype lit = Pos (sym: idx) | Neg (sym: idx)
  datatype symdef = Input | And lit lit


  type_synonym aig = "symdef list"

  definition wf_aig :: "aig \<Rightarrow> bool" where
    "wf_aig defs \<equiv> (\<forall>l\<^sub>1 l\<^sub>2 i. i<length defs \<and> defs!i = And l\<^sub>1 l\<^sub>2 \<longrightarrow> sym l\<^sub>1 < i \<and> sym l\<^sub>2 < i)"
  
    (*
  typedef aig = "{defs . wf_aig defs}" 
    by (auto simp: wf_aig_def intro: exI[where x="[]"])
  setup_lifting type_definition_aig  
    *)
  
    
  context 
    fixes g :: aig
      and v :: "idx \<Rightarrow> bool"
      assumes WF: "wf_aig g"
  begin    
  
    definition "lit_ord l \<equiv> case l of (Pos i) \<Rightarrow> 2*i | Neg i \<Rightarrow> 2*i+1"
    
(*    fun lit_ord :: "lit \<Rightarrow> nat" where
      "lit_ord (Pos i) = 2*i"
    | "lit_ord (Neg i) = 2*i+1"
*)  
  
    lemma wf_aigD: assumes "i<length g" "g!i=And l\<^sub>1 l\<^sub>2" shows "sym l\<^sub>1 < i" "sym l\<^sub>2 < i"
      using assms WF unfolding wf_aig_def by auto

    function sem :: "lit \<Rightarrow> bool" where
      "sem (Neg i) \<longleftrightarrow> \<not>sem (Pos i)"
    | "sem (Pos i) \<longleftrightarrow> (
        if i<length g then 
          case g!i of
            Input \<Rightarrow> v i
          | And l\<^sub>1 l\<^sub>2 \<Rightarrow> sem l\<^sub>1 \<and> sem l\<^sub>2
        else False)"
      by pat_completeness auto
    termination
      apply (relation "measure lit_ord")
      apply (auto simp: lit_ord_def split: lit.split)
      apply (drule (1) wf_aigD; auto)+
      done
  
  end


end
