theory Sorting
imports Main "~~/src/HOL/Library/Multiset"
begin

inductive sorted :: "'a::linorder list \<Rightarrow> bool" where
empty: "sorted []" |
single: "sorted [x]" |
cons: "x\<^sub>1 \<le> x\<^sub>2 \<Longrightarrow> sorted (x\<^sub>2 # xs) \<Longrightarrow> sorted (x\<^sub>1 # x\<^sub>2 # xs)"

code_pred sorted .

lemma sorted_cons_dest[dest]: "sorted (x # xs) \<Longrightarrow> sorted xs"
by (ind_cases "sorted (x # xs)") (auto intro: sorted.intros)

locale sorting =
  fixes sort :: "'a::linorder list \<Rightarrow> 'a list"
  assumes sorted: "sorted (sort xs)" and permutation: "multiset_of (sort xs) = multiset_of xs"



end
