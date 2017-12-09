theory Quick_Sort
imports Sorting
begin

lemma multiset_partition:
  "multiset_of (fst (partition f xs)) + multiset_of (snd (partition f xs)) = multiset_of xs"
by (induction xs) (auto simp: algebra_simps)

fun quicksort :: "'a::linorder list \<Rightarrow> 'a list" where
"quicksort [] = []" |
"quicksort (x # xs) = (let (as, bs) = partition (\<lambda>y. y \<le> x) xs in quicksort as @ x # quicksort bs)"

interpretation quick_sort!: sorting quicksort
proof
  fix xs :: "'a::linorder list"
  show "multiset_of (quicksort xs) = multiset_of xs"
    by (induction xs rule: quicksort.induct)
       (auto simp: multiset_partition[simplified] algebra_simps)

  show "sorted (quicksort xs)"
    sorry
qed

end