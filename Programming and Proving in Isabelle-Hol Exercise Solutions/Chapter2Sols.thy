theory Chapter2Sols
imports Main Chapter2Defs
begin

(*  Exercise 2.1  *)
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(*  Exercise 2.2  *)
lemma add_assoc[simp]: "add x (add y z) = add (add x y) z"
  apply(induction x)
   apply(auto)
  done

lemma suc_add[simp]: "Suc (add m n) = add m (Suc n)"
  apply(induction m)
   apply(auto)
  done 

lemma add_commu[simp]: "add x y = add y x"
  apply(induction x)
   apply(auto)
  done

fun double:: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc n) = 2 + double n"

lemma "double m = add m m"
  apply(induction m)
   apply(auto)
  done

(*  Exercise 2.3  *)
fun count:: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count n [] = 0" |
"count n (x#xs) = (if x=n then (1 + count n xs) else count n xs)"

theorem count_len [simp]: "count x xs \<le> length xs"
  apply(induction xs)
   apply(auto)
  done

(*  Exercise 2.4  *)
fun snoc:: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] elem = (Cons elem Nil)" |
"snoc (Cons x xs) elem = (Cons x (snoc xs elem))"

fun reverse:: "'a list \<Rightarrow> 'a list" where
"reverse Nil = Nil" |
"reverse (Cons x xs) = snoc (reverse xs) x"

lemma snoc_rev[simp]: "reverse (snoc xs a) = a # reverse xs"
  apply(induction xs)
   apply(auto)
  done

lemma rev_rev[simp]: "reverse (reverse xs) = xs"
  apply(induction xs)
   apply(auto)
  done

(*  Exercise 2.5  *)
fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" | 
"sum_upto n = n + sum_upto (n - 1)"

lemma "sum_upto n = (n * (n+1)) div 2"
  apply(induction n)
   apply(auto)
  done

(*  Exercise 2.6  *)
fun contents:: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l a r) = (Cons a (contents l))@(contents r)"

fun sum_tree:: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l a r) = a + sum_tree l + sum_tree r"

lemma "sum_tree t = sum_list(contents t)"
  apply(induction t)
   apply(auto)
  done

(*  Exercise 2.7  *)
fun pre_order:: "'a tree \<Rightarrow> 'a list" where
"pre_order Tip = []" |
"pre_order (Node l a r) = [a]@(pre_order l)@(pre_order r)"

fun post_order:: "'a tree \<Rightarrow> 'a list" where
"post_order Tip = []" |
"post_order (Node l a r) = (post_order l)@(post_order r)@[a]"

lemma "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
  apply(auto)
  done

(*  Exercise 2.8  *)
fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse elem [] = [elem]" |
"intersperse elem (x#xs) = [x] @ [elem] @ (intersperse elem xs)"

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs)
   apply(auto)
  done

(*  Exercise 2.9  *)
fun itadd:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

(* proof is incomplete *)

end