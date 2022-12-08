theory coursework
  imports Main
begin


text \<open>\Coursework{1}{}\<close>

text \<open>

  

  \<^item> Recall the binary search tree which we discussed in the lecture, and the functions \<open>tree_set\<close>,
    \<open>bst\<close>, \<open>isin\<close>, \<open>ins\<close>, and their properties which we proved earlier, and which are repeated 
    below.\footnote{We only repeat the properties here. However, in the template, you will find all
    the function definitions from the lecture as well as the theorems and their proofs.}


\<close>


datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"  

fun tree_set where
"tree_set Leaf = {}"
| "tree_set (Node l a r) = insert a (tree_set l) \<union> (tree_set r)"


fun bst where
"bst Leaf = True"
| "bst (Node l a r) = ((\<forall>x\<in>tree_set l. x < a) \<and> bst l \<and> (\<forall>x\<in>tree_set r. a < x) \<and> bst r)"

  
fun isin :: "('a::linorder) tree \<Rightarrow> 'a \<Rightarrow> bool" where
"isin Leaf x = False" |
"isin (Node l a r) x =
  (if x < a then isin l x else
   if x > a then isin r x
  else True)"

fun ins :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"ins x Leaf = Node Leaf x Leaf" |
"ins x (Node l a r) =
  (if x < a then Node (ins x l) a r else
   if x > a then Node l a (ins x r)
   else Node l a r)"


text "Functional Correctness"

lemma tree_set_isin: "bst (t::nat tree) \<Longrightarrow> isin t x = (x \<in> tree_set t)"
  apply (induction t)
  apply (auto)
  done

lemma tree_set_ins: "tree_set (ins x t) = {x} \<union> tree_set t"
apply(induction t)
apply auto
  done



text "Preservation of Invariant"

lemma bst_ins: "bst t \<Longrightarrow> bst (ins x t)"
apply(induction t)
apply (auto simp: tree_set_ins)
done

text \<open>
  \<^item> Define a new function \<open>bst_eq\<close> that is like @{const bst} but allows duplicate in the tree.
  \<^item> Show that @{const isin} and @{const ins} are also correct for \<open>bst_eq\<close>.
\<close>

fun bst_eq :: "(nat) tree \<Rightarrow>  bool" where
"bst_eq Leaf = True"
| "bst_eq (Node l a r) = ((\<forall>x\<in>tree_set l. x \<le> a) \<and> bst_eq l \<and> (\<forall>x\<in>tree_set r. a \<le> x) \<and> bst_eq r)"

lemma "bst_eq t \<Longrightarrow> isin t x = (x \<in> tree_set t)"
apply (induction t)
apply (auto)
done
  
lemma bst_eq_ins: "bst_eq t \<Longrightarrow> bst_eq (ins x t)"
apply(induction t)
apply (auto simp: tree_set_ins)
done

text \<open>  
Define a function \<open>ins_eq\<close> to insert into a BST with duplicates.
\<close>

value "bst_eq (Node (Node Leaf 1 Leaf) 1 (Node Leaf 1 Leaf)) = True"
value "bst_eq (Node (Node Leaf 2 Leaf) 1 (Node Leaf 1 Leaf)) = False"
value "bst_eq (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)) = True"


fun ins_eq :: "nat \<Rightarrow> nat tree \<Rightarrow> nat tree" 
  where
   "ins_eq x Leaf = Node Leaf x Leaf" |
   "ins_eq x (Node l a r) =
  (if x \<le> a then Node (ins_eq x l) a r else
   if x \<ge>  a then Node l a (ins_eq  x r)
   else Node l a r)"

value "ins_eq 1 Leaf = Node Leaf 1 Leaf"
value "(ins_eq 1 (Node Leaf 1 Leaf) = Node Leaf 1 (Node Leaf 1 Leaf) \<or> 
       ins_eq 1 (Node Leaf 1 Leaf) = Node (Node Leaf 1 Leaf) 1 Leaf) = True"

lemma tree_set_ins_eq: "tree_set (ins_eq x t) = {x} \<union> tree_set t"
apply(induction t)
apply auto
done
  
text \<open>  
Show that \<open>ins_eq\<close> preserves the invariant @{const \<open>bst_eq\<close>}
\<close>
  
lemma bst_eq_ins_eq: "bst_eq t \<Longrightarrow> bst_eq (ins_eq x t)"
apply(induction t)
apply (auto simp: tree_set_ins_eq)
done


text \<open>  
Define a function \<open>count_tree\<close> to count how often a given element occurs in a tree
\<close>
fun count_tree :: "nat \<Rightarrow>  nat tree \<Rightarrow> nat" 
  where
"count_tree x Leaf = 0" |
"count_tree x (Node l a r) =
  (if x = a then 1 + count_tree x l else
  if x < a then count_tree x l else
  count_tree x r)"

  
text \<open>  
Show that the \<open>ins_eq\<close> function inserts the desired element, and does not affect other elements.
\<close>


value  "count_tree 1 (Node Leaf 1 Leaf) = 1"
value  "count_tree 1 (Node Leaf 0 Leaf) = 0"
value  "count_tree 0 (Node (Node Leaf 0 Leaf) 1 Leaf) = 1"
value  "count_tree 1 (Node (Node Leaf 1 Leaf) 1 Leaf) = 2"

lemma "count_tree x (ins_eq x t) = Suc (count_tree x t)"  
apply(induction t)
apply (auto)
done

lemma "x\<noteq>y \<Longrightarrow> count_tree y (ins_eq x t) = count_tree y t"  
apply(induction t)
apply (auto)
done

end