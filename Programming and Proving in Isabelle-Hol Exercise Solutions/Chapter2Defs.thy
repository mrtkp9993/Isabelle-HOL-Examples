theory Chapter2Defs
imports Main
begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

lemma add_02[simp] : "add m 0 = m"
  apply(induction m)
  apply(auto)
  done

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror:: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

end
