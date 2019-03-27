theory Quick_Sort
imports Sorting
begin

lemma multiset_partition:
  "mset (fst (partition f xs)) + mset (snd (partition f xs)) = mset xs"
by (induction xs) (auto simp: algebra_simps)

fun quicksort :: "'a::linorder list \<Rightarrow> 'a list" where
"quicksort [] = []" |
"quicksort (x # xs) = (let (as, bs) = partition (\<lambda>y. y \<le> x) xs in quicksort as @ x # quicksort bs)"

declare sorted.empty[simp]
declare sorted.single[simp]

lemma sorted_cons_iff: "sorted (x # xs) \<longleftrightarrow> (\<forall>x' \<in> set xs. x \<le> x') \<and> sorted xs"
sorry

lemma sorted_appI: "sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> \<forall>x \<in> set xs. \<forall>y \<in> set ys. x \<le> y \<Longrightarrow> sorted (xs @ ys)"
  sorry

global_interpretation quick_sort: sorting quicksort
proof
  fix xs :: "'a::linorder list"
  show "mset (quicksort xs) = mset xs"
    by (induction xs rule: quicksort.induct)
       (auto simp: multiset_partition[simplified] algebra_simps)

  show "sorted (quicksort xs)"
    apply (induction xs rule: quicksort.induct)
     apply simp
    unfolding quicksort.simps
    apply (case_tac "partition (\<lambda>y. y \<le> x) xs")
    apply (simp only: Let_def)
    unfolding prod.case
    apply (rule sorted_appI)
      apply simp
     apply (subst sorted_cons_iff)
     apply (rule conjI)
    subgoal sorry
     apply simp
    subgoal sorry
    done
qed

end