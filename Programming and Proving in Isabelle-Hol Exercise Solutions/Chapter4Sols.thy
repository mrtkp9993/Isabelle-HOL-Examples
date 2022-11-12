theory Chapter4Sols
imports Main
begin

(*  Exercise 4.1  *)
lemma assumes T: "\<forall>x y. T x y \<or> T y x"
  and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall>x y. T x y \<longrightarrow> A x y" and "A x y"
shows "T x y"
  using A T TA assms(4) by blast

(*  Exercise 4.2  *)
lemma "\<exists>ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"

(* not complete *)

end