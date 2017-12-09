theory Merge_Sort
imports Sorting
begin

context begin

qualified fun merge :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"merge [] ys = ys" |
"merge xs [] = xs" |
"merge (x # xs) (y # ys) = (if x \<le> y then x # merge xs (y # ys) else y # merge (x # xs) ys)"

qualified lemma merge_sorted: "sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> sorted (merge xs ys)"
proof (induction xs ys rule: merge.induct)
  case (3 x xs y ys)
  thus ?case
    (*by (smt Sorting.sorted.simps le_cases list.inject merge.simps(1) merge.simps(2) merge.simps(3))*)
    apply (auto intro: sorted.intros)
    apply (cases xs)
    apply (auto intro: sorted.intros)
    apply (metis Sorting.sorted.simps list.distinct(1) list.sel(3) nth_Cons_0)
    apply (auto intro: sorted.intros)
    apply (cases ys)
    apply (auto intro: sorted.intros)
    apply (meson cons le_cases sorted_cons_dest)
    by (metis Sorting.sorted.simps list.distinct(1) list.sel(3) nth_Cons_0)
qed (auto intro: sorted.intros)

qualified lemma merge_permutation: "multiset_of (merge xs ys) = multiset_of xs + multiset_of ys"
by (induction xs ys rule: merge.induct) (auto simp: algebra_simps)

qualified fun split :: "'a list \<Rightarrow> ('a list \<times> 'a list)" where
"split [] = ([], [])" |
"split [x] = ([x], [])" |
"split (x\<^sub>1 # x\<^sub>2 # xs) = map_prod (op # x\<^sub>1) (op # x\<^sub>2) (split xs)"

lemmas split_induct = split.induct[case_names nil single cons]

qualified lemma split_permutation: "multiset_of (fst (split xs)) + multiset_of (snd (split xs)) = multiset_of xs"
by (induction xs rule: split.induct) (auto simp: algebra_simps)

qualified lemma split_length:
  "length (fst (split xs)) \<le> length xs" (is ?fst)
  "length (snd (split xs)) \<le> length xs" (is ?snd)
proof -
  show ?fst
    by (induction xs rule: split_induct) auto

  show ?snd
    by (induction xs rule: split_induct) auto
qed

context
  notes [simp] = map_prod_def split_beta split_length less_Suc_eq_le
begin

fun mergesort :: "'a::linorder list \<Rightarrow> 'a list" where
"mergesort [] = []" |
"mergesort [x] = [x]" |
"mergesort xs = (let (as, bs) = split xs in merge (mergesort as) (mergesort bs))"

end

end

interpretation merge_sort!: sorting mergesort
proof
  fix xs :: "'a::linorder list"
  show "sorted (mergesort xs)"
    proof (induction xs taking: length rule: measure_induct_rule)
      case (less xs)
      thus ?case
        by (cases xs rule: mergesort.cases)
           (auto simp: split_beta less_Suc_eq_le Merge_Sort.split_length
                 intro: Merge_Sort.merge_sorted sorted.intros)
    qed

  show "multiset_of (mergesort xs) = multiset_of xs"
    proof (induction xs taking: length rule: measure_induct_rule)
      case (less xs)
      thus ?case
        by (cases xs rule: mergesort.cases)
           (auto simp: split_beta less_Suc_eq_le algebra_simps
                       Merge_Sort.merge_permutation Merge_Sort.split_permutation Merge_Sort.split_length)
    qed
qed

export_code mergesort in Scala

end