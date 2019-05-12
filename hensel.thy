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

lemma(in domain) gt_deg_is_zero:
  assumes "p \<in> up R"
  shows "\<And>m. \<lbrakk>m > deg R p\<rbrakk> \<Longrightarrow> p m = \<zero>"
proof-
  fix k
  obtain n where 1: "deg R p = n" by simp
  have 2: "deg R p = (LEAST n. bound (zero R) n (coeff (UP R) p))" using deg_def by auto
  then have 3: "\<lbrakk> k > n \<rbrakk> \<Longrightarrow> k > (LEAST n. bound (zero R) n (coeff (UP R) p))"
    using "1" by linarith
  then have "\<lbrakk>k > deg R p\<rbrakk> \<Longrightarrow> p k = \<zero>"
    by (smt LeastI UP_def \<open>deg R p = (LEAST n. bound \<zero> n (coeff (UP R) p))\<close> assms(1) bound_def bound_upD deg_def mem_Collect_eq restrict_apply up_def up_ring.simps(2))
  then show "\<And>m. \<lbrakk>m > deg R p\<rbrakk> \<Longrightarrow> p m = \<zero>" using 1 2 3 assms(1) bound_def bound_upD deg_def mem_Collect_eq up_def up_ring.simps(2) 
    by (smt UP_def cring_def domain_axioms domain_def restrict_apply ring.bound_upD wellorder_Least_lemma(1))
qed

lemma(in domain) bound_is_zero:
  assumes "p \<in> up R"
  assumes "deg R p = n"
  shows "p n = \<zero>"
proof-
  obtain n where "n = (LEAST n. bound \<zero> n (coeff (UP R) p))"
    by simp
  have "n \<le> n+1" by simp
  have "\<lbrakk>deg R p = n
  then have "coeff (UP R) p (n+1) = \<zero>"




lemma(in domain) deg_shift_lt:
  assumes "p \<in> up R"
  shows "deg R (shift p) = deg R p - 1" 
proof-
  have "\<exists>n. deg R p = n" by simp
  obtain n where 1: "deg R p = n"
    by auto
  have "shift p n = p (n+1)"
    by simp
  have "p n = \<zero>" using 1 assms deg_def  sledgehammer

lemma(in domain) deg_deriv_lt:
  assumes "p \<in> up R"
  assumes "deg R p = n"
  shows "deg R (deriv R p) = n - 1" 


(*
  obtain n where "deg R p = n" by simp
  then have "n = (LEAST n. bound \<zero>\<^bsub>R\<^esub> n (coeff (UP R) p))" using deg_def  sledgehammer*)