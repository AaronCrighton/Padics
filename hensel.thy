theory hensel
  imports Main "~~/src/HOL/Algebra/UnivPoly" "~~/src/HOL/Algebra/Valued_Fields/padic_construction"
begin

definition p_UP :: "nat \<Rightarrow> (nat \<Rightarrow> int, nat \<Rightarrow> nat \<Rightarrow> int) up_ring" where
  "p_UP p = UP (padic_int p)"

fun shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "shift b n = b (n + 1)"

fun mult :: "('a, 'b) ring_scheme \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "mult R b n = add_pow R n (b n)"

definition deriv :: "('a, 'b) ring_scheme \<Rightarrow> (nat \<Rightarrow> 'a ) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "deriv R b = shift (mult R b)"

lemma(in domain) shift_in_up_ring:
  assumes "b \<in> up R"
  shows "shift  b \<in> up R" 
proof
  show "\<And>n. shift b n \<in> carrier R" 
    by (simp add: assms mem_upD)
  show "\<exists>n. bound \<zero> n (shift b)" 
  proof- 
    obtain n where Bb: "bound \<zero> n b"
      using assms(1) by auto
    have "bound \<zero> n (shift b)"
    proof
      fix m
      assume A: "n < m"
      have P0: "shift b m = b (m + 1)" 
        by auto
      have P1: "n < m + 1" using A by auto 
      then show "shift b m = \<zero>"
        using Bb A P0 P1 by fastforce 
    qed
    then show ?thesis by blast 
  qed
qed

lemma(in domain) mult_in_up_ring:
  assumes "b \<in> up R"
  shows "mult R b \<in> up R" 
proof
  show "\<And>n. mult R b n \<in> carrier R"
  proof-
    fix n
    show "mult R b n \<in> carrier R" 
      by (simp add: assms mem_upD)
  qed
  show "\<exists>n. bound \<zero> n (hensel.mult R b)"
    using assms by fastforce
qed

(* deriv also returns a polynomial *)
lemma(in domain) deriv_in_up_ring:
  assumes "p \<in> up R"
  shows "(deriv R p) \<in> up R" 
  by (simp add: assms deriv_def mult_in_up_ring shift_in_up_ring)


(*
  obtain n where "deg R p = n" by simp
  then have "n = (LEAST n. bound \<zero>\<^bsub>R\<^esub> n (coeff (UP R) p))" using deg_def  sledgehammer*)