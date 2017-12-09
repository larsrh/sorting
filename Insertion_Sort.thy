theory Insertion_Sort
imports Sorting
begin

context begin

qualified primrec insert :: "'a::linorder \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"insert x [] = [x]" |
"insert x (y # ys) = (if x \<le> y then x # y # ys else y # insert x ys)"

qualified lemma insert_sorted: "sorted xs \<Longrightarrow> sorted (insert x xs)"
proof (induction xs rule: sorted.induct)
  case empty
  show ?case
    by (auto intro: single)
next
  case (single y)
  show ?case
    by (cases "x \<le> y") (auto intro: sorted.intros) (* if_splits *)
next
  case (cons x\<^sub>1 x\<^sub>2 xs)
  show ?case
    proof (cases "x \<le> x\<^sub>1")
      case True
      hence "insert x (x\<^sub>1 # x\<^sub>2 # xs) = x # x\<^sub>1 # x\<^sub>2 # xs"
        by simp
      moreover have "sorted (x # x\<^sub>1 # x\<^sub>2 # xs)"
        apply (rule sorted.intros)
        apply fact
        apply (rule sorted.intros)
        apply fact+
        done
      ultimately show ?thesis
        by simp
    next
      case False
      hence "insert x (x\<^sub>1 # x\<^sub>2 # xs) = x\<^sub>1 # insert x (x\<^sub>2 # xs)"
        by simp
      moreover have "sorted (x\<^sub>1 # insert x (x\<^sub>2 # xs))"
        apply (cases "x \<le> x\<^sub>2")
        using cons apply (auto intro: sorted.intros)
        apply (rule sorted.cons)
        using False apply simp
        apply assumption
        done
      ultimately show ?thesis
        by simp
    qed
qed

qualified lemma insert_permutation: "multiset_of (insert x xs) = {#x#} + multiset_of xs"
proof (induction xs)
  case Nil
  show ?case
    by simp
next
  case (Cons y ys)
  show ?case
    proof (cases "x \<le> y")
      case True
      thus ?thesis
        by (simp add: union_commute)
    next
      case False
      thus ?thesis
        apply simp
        apply (subst Cons)
        by (simp add: union_assoc)
    qed
qed

primrec insort :: "'a::linorder list \<Rightarrow> 'a list" where
"insort [] = []" |
"insort (x # xs) = insert x (insort xs)"

end

interpretation insertion_sort!: sorting insort
proof
  fix xs :: "'a::linorder list"
  show "sorted (insort xs)"
    proof (induction xs)
      case Nil
      show ?case
        apply simp
        apply (rule sorted.empty)
        done
    next
      case (Cons y ys)
      show ?case
        apply simp
        apply (rule Insertion_Sort.insert_sorted)
        apply (rule Cons)
        done
  qed

  show "multiset_of (insort xs) = multiset_of xs"
    by (induction xs) (auto simp: Insertion_Sort.insert_permutation union_commute)
qed

end