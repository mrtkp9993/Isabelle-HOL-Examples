theory Chapter3Sols
imports Main Chapter3Defs
begin

(*  Exercise 3.1  *)
fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node l a r) = {a} \<union> (set l) \<union> (set r)"

(* not complete *)

(*  Exercise 3.2  *)
inductive palindrome:: "'a list \<Rightarrow> bool" where
emptyP: "palindrome []" |
singlP: "palindrome [x]" |
indctP: "palindrome xs \<Longrightarrow> palindrome(a # xs @ [a])"

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply(induction xs rule: palindrome.induct)
    apply(simp_all)
  done
  
end