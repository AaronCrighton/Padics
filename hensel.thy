theory hensel
  imports Main "~~/src/HOL/Algebra/UnivPoly" "~~/src/HOL/Algebra/Valued_Fields/padic_construction"
begin

definition p_UP :: "nat \<Rightarrow> (nat \<Rightarrow> int, nat \<Rightarrow> nat \<Rightarrow> int) up_ring" where
  "p_UP p = UP (padic_int p)"

fun shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "shift b n = b (n + 1)"

fun multc :: "('a, 'b) ring_scheme \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "multc R b n = add_pow R n (b n)"

definition deriv :: "('a, 'b) ring_scheme \<Rightarrow> (nat \<Rightarrow> 'a ) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "deriv R b = shift (multc R b)"

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
    thus ?thesis by blast 
  qed
qed

lemma(in domain) multc_in_up_ring:
  assumes "b \<in> up R"
  shows "multc R b \<in> up R" 
proof
  show "\<And>n. multc R b n \<in> carrier R"
  proof-
    fix n
    show "multc R b n \<in> carrier R" 
      by (simp add: assms mem_upD)
  qed
  show "\<exists>n. bound \<zero> n (hensel.multc R b)"
    using assms by fastforce
qed

(* deriv also returns a polynomial *)
lemma(in domain) deriv_in_up_ring:
  assumes "p \<in> up R"
  shows "(deriv R p) \<in> up R" 
  by (simp add: assms deriv_def multc_in_up_ring shift_in_up_ring)

lemma degr: "deg R p = (LEAST n. bound (zero R) n (coeff (UP R) p))" using deg_def by auto

lemma(in domain) coeff_simp:
  assumes "p \<in> up R"
  shows "coeff (UP R) p = p" 
proof-
  have "coeff (UP R) = (\<lambda>p \<in> (up R). p)" 
    by (simp add: UP_def)
  then show  "coeff (UP R) p = p" using assms by auto 
qed



lemma(in domain) deg_simp_0:
  assumes "p \<in> up R"
  assumes "n = deg R p"
  shows " bound (zero R) n (coeff (UP R) p)"
proof
  show "\<And>m. n < m \<Longrightarrow> coeff (UP R) p m = \<zero>"
  proof-
    fix m
    assume "n < m"
    show "coeff (UP R) p m = \<zero>" 
    proof-
      obtain f where f_def: "f = (coeff (UP R) p)"
        by simp
      obtain P where P_def: "P = (\<lambda> m. bound (zero R) m (coeff (UP R) p))" 
        by simp
      have "\<exists>n. bound \<zero> n f" 
        using assms(1) up_def f_def coeff_simp by auto
      then have "\<exists>m. P m" 
        using P_def f_def by auto 
      then have 0: "P (LEAST m. P m)"
        using LeastI  by auto
      have "P m =  bound (zero R) m (coeff (UP R) p)"
        by (simp add: P_def)
      then have 1: "(LEAST m. P m) = (LEAST m. ( bound (zero R) m (coeff (UP R) p)))"
        by (simp add: P_def)
      have 2: "deg R p = (LEAST m. ( bound (zero R) m (coeff (UP R) p)))"
        using deg_def by auto
      then have "(LEAST m. P m) = deg R p" 
        using 1 2 by auto 
      then have "P n" using 0 assms by auto
      then show ?thesis using P_def 
        using \<open>n < m\<close> by blast 
    qed
  qed
qed

(*
lemma(in domain) deg_simp_1:
  assumes "p \<in> up R"
  assumes "n \<ge> deg R p"
  shows " bound (zero R) n (coeff (UP R) p)"
proof(cases "n=0")
  case True
  then show ?thesis 
    using assms(1) assms(2) deg_simp_0 by force
next
  case False
  then show ?thesis sorry
qed
*)

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

lemma(in domain) deg_neq_0:
  assumes "p \<in> up R"
  assumes "deg R p = n"
  assumes "n > 0"
  shows "p n \<noteq> \<zero>"
proof(rule ccontr)
  assume "\<not> (p n \<noteq> \<zero>)"
  have cont1: "n = (LEAST n. bound (zero R) n (coeff (UP R) p))" using assms(1) assms(2) deg_def degr
    by blast
  have "n-1 < n"
    using assms(2) assms(3) diff_less less_numeral_extra(1)
    by (simp add: assms(3))
  have "\<And>m. \<lbrakk>m > (n-1)\<rbrakk> \<Longrightarrow> p m = \<zero>"
    by (metis One_nat_def Suc_lessI Suc_pred \<open>\<not> p n \<noteq> \<zero>\<close> assms(1) assms(2) assms(3) gt_deg_is_zero)
  then have 2: "bound (zero R) (n-1) (coeff (UP R) p)"
    by (simp add: UP_def assms(1) bound_def)
  then have cont: "n-1 = (LEAST n. bound (zero R) n (coeff (UP R) p))" using 2  \<open>n-1 < n\<close> assms(1)
    by (metis One_nat_def \<open>n = (LEAST n. bound \<zero> n (coeff (UP R) p))\<close>  neq0_conv not_less_Least zero_less_diff)
  then have "n \<noteq> (LEAST n. bound (zero R) n (coeff (UP R) p))" using 2  assms(1) UP_def cont
        not_less_Least order.asym neq0_conv lessI diff_less
    using \<open>n - 1 < n\<close> by linarith
  hence "n \<noteq> deg R p"
    using cont1 by blast
  thus False
    using assms(2) by blast
qed

lemma(in domain) deg_shift_lt:
  assumes "p \<in> up R"
  assumes "deg R p > 0"
  shows "deg R (shift p) < deg R p" 
proof-
  have "\<exists>n. deg R p = n" by simp
  obtain n where 1: "deg R p = n"
    by auto
  have "shift p n = p (n+1)"
    by simp
  have 1: "p (n+1) = \<zero>" using 1 assms deg_def gt_deg_is_zero
    by simp
  then have 2: "shift p n = p (n+1)" by simp
  then have 3: "shift p n = \<zero>" using 1 by auto
  thus "deg R (shift p) < deg R p" using degr 1 2 3 assms(1) assms(2) deg_neq_0
    by (metis (no_types, lifting)  dual_order.strict_trans2
          gt_deg_is_zero less_add_one not_le_imp_less shift.elims shift_in_up_ring)
qed


  
(*lemma(in domain) multc_neq_0:
  assumes "p \<in> up R"
  assumes "p n \<noteq> \<zero>"
  shows "multc R p n \<noteq> \<zero>" sledgehammer*)

(*lemma(in domain) deg_multc_eq:
  assumes "p \<in> up R"
  shows "deg R p \<le> deg R (multc R p)" 
proof-
  have "\<lbrakk> p m \<noteq> \<zero> \<rbrakk> \<Longrightarrow> multc R p m \<noteq> \<zero>" using multc_def add_pow_def *)

(*lemma(in domain) deg_deriv_lt:
  assumes "p \<in> up R"
  assumes "deg R p > 0"
  shows "deg R (deriv R p) < deg R p" using deriv_def shift_def multc_def 
proof-
  have "deriv R p = shift (multc R p)" 
    using deriv_def by blast
  have "deg R (shift (multc R p)) < deg R p" using deg_def shift_def deg_shift_lt *)
