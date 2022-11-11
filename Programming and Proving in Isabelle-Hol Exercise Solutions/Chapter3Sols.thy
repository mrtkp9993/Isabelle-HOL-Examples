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

(*  Exercise 3.3  *)
(* not complete *)

(*  Exercise 3.4  *)
(* not complete *)

(*  Exercise 3.5  *)
(* Adapted from: https://isabelle.in.tum.de/exercises/logic/parentheses/sol.pdf *)
datatype alpha = a | b

inductive S:: "alpha list \<Rightarrow> bool" where
S1: "S []" |
S2: "S [v] \<Longrightarrow> S (a # [v] @ [b])" |
S3: "S [v] \<Longrightarrow> S [w] \<Longrightarrow> S([v] @ [w])"

declare S1 [iff] S2 [intro!, simp]

inductive T:: "alpha list \<Rightarrow> bool" where
T1: "T []" |
T2: "T [v] \<Longrightarrow> T[w] \<Longrightarrow> T([v] @ a # [w] @ [b])"

declare T1 [iff]

lemma T2S:"T w \<Longrightarrow> S w"
  apply(erule T.induct)
   apply(simp)
  (* found by sledgehammer *)
  using S.cases by auto

lemma S2T:"S w \<Longrightarrow> T w"
  apply(erule S.induct)
    apply(simp)
  (* found by sledgehammer *)
  using S.cases by auto

lemma "S w == T w"
  by (smt (verit) S2T T2S)
  
end