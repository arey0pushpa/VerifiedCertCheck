section \<open>Types of Cardinality 2 or Greater
  Inspired by from AFP/Optics
\<close>

theory Two
imports Main
begin

text \<open>The two class states that a type's carrier is either infinite, or else it has a finite 
  cardinality of at least 2. It is needed when we depend on having at least two distinguishable
  elements.\<close>
  
lemma card_two_eq_diff: "(infinite (UNIV :: 'a set) \<or> card (UNIV :: 'a set) \<ge> 2) \<longleftrightarrow> (\<exists>a b::'a. a\<noteq>b)"  
  apply auto
  subgoal
    by (metis (full_types) ex_new_if_finite finite.emptyI finite_insert insert_iff)
  subgoal
    by (metis (full_types) One_nat_def Suc_1 Suc_le_mono UNIV_I UNIV_eq_I card.empty card.insert card_UNIV_bool card_eq_UNIV_imp_eq_UNIV empty_iff finite_imageI finite_insert infinite_arbitrarily_large insert_iff le_0_eq)
  subgoal
    by (smt Suc_leI Suc_less_eq UNIV_I card.empty card.infinite card.insert card_UNIV_bool card_mono empty_iff equalityI finite finite.intros(1) finite_insert insertCI insert_iff le_simps(2) linorder_not_le mem_Collect_eq nat.simps(3) nat_numeral order_antisym_conv singleton_conv2 subsetI top.extremum zero_order(1))
  done
    
    
class two =
  assumes two_diff: "\<exists>a b::'a. a\<noteq>b"
begin
  lemma card_two: "infinite (UNIV :: 'a set) \<or> card (UNIV :: 'a set) \<ge> 2"
    using card_two_eq_diff two_diff by auto
    
end

instance bool :: two
  by (intro_classes, auto)

instance nat :: two
  by (intro_classes, auto)

instance int :: two
  by (intro_classes, fastforce intro: exI[where x="1::int"] exI[where x="0::int"])

instance list :: (type) two
  by (intro_classes, auto simp add: infinite_UNIV_listI)

instance option :: (type) two
  by intro_classes auto
  
  
end
