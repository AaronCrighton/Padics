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

lemma(in UP_ring) shift_in_up_ring:
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

lemma(in UP_ring) multc_in_up_ring:
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

fun trunc :: "('a, 'b) ring_scheme \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "trunc R f = (\<lambda>i. (if i < (deg R f) then  f i else \<zero>\<^bsub>R\<^esub>))"

lemma(in UP_ring) monom_simp:
  assumes "a \<in> carrier R"
  shows "(monom (UP R) a m) n = (if m=n then a else \<zero>)"
proof-
  have "(\<lambda>n. if n = m then a else \<zero>) \<in> up R"
    using up_def assms(1) by force
  with assms(1) show ?thesis by (simp add: UP_def)
qed

lemma(in UP_ring) trunc_is_poly:
  assumes "f \<in> up R"
  shows "trunc R f \<in> up R"
proof
  show "\<exists>n. bound \<zero>\<^bsub>R\<^esub> n (trunc R f)" 
    by (meson bound_def less_le less_trans trunc.elims)
  show "\<And>n. trunc R f n \<in> carrier R"
  proof-
    fix n
    show "trunc R f n \<in> carrier R"
    proof(cases "n < deg R f")
      case True
      then have "trunc R f n = f n"
        by simp
      
      then show "trunc R f n \<in> carrier R"
        by (simp add: assms mem_upD)
    next
      case False
      then have "trunc R f n = \<zero>\<^bsub>R\<^esub>"
        by simp
      then show ?thesis
        by (smt assms bound_def lessI mem_Collect_eq mem_upD up_def)
    qed
  qed
qed

fun lc :: "('a,'b) ring_scheme \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "lc R p = p (deg R p)"

lemma(in UP_ring) monom_eq_deg:
  assumes "deg R p = n"
  assumes "m \<ge> n"
  shows "monom (UP R) (p n) n m = p m"
  proof(cases "m \<noteq> n")
    case True
    then show ?thesis 
  next
    case False
    then show ?thesis using assms(1) assms(2) monom_simp UP_def 
  qed

lemma(in UP_ring) trunc_monom_0:
  assumes "p \<in> up R"
  assumes "deg R p > 0"
  assumes "deg R p = n"
  shows "p x = (trunc R p x) \<oplus>\<^bsub>R\<^esub> (monom (UP R) (p n) n x)"
proof-
  fix m
  have "p m = trunc R p m \<oplus>\<^bsub>R\<^esub> monom (UP R) (p n) n m"
  proof(cases "m < n")
    case True
    have "p m = p m \<oplus>\<^bsub>R\<^esub> \<zero>" 
      by (simp add: assms(1) mem_upD)
    then have 1: "monom (UP R) (p n) n m = \<zero>" using monom_simp
      by (metis True assms(1) mem_upD nat_neq_iff)
    then have 2: "trunc R p m = p m" 
      by (simp add: True assms(3))
    then have 3: "trunc R p m \<oplus>\<^bsub>R\<^esub> monom (UP R) (p n) n m = p m \<oplus>\<^bsub>R\<^esub> \<zero>"
      by (simp add: \<open>monom (UP R) (p n) n m = \<zero>\<close>)
    then show ?thesis using 1 2 3 assms(2) assms(3) \<open>p m = p m \<oplus> \<zero>\<close> by auto
  next
    case False
    then have "\<not> (m < n)"
      by simp
    show ?thesis
    proof(cases "n = m")
      case False
      then have "trunc R p m = \<zero>" sledgehammer
        by (simp add: \<open>\<not> m < n\<close> assms(3))
  qed

lemma(in UP_ring) monom_simp:
  assumes "a \<in> carrier R"
  shows "(monom (UP R) a m) n = (if m=n then a else \<zero>)"
proof-
  have "(\<lambda>n. if n = m then a else \<zero>) \<in> up R"
    using up_def assms(1) by force
  with assms(1) show ?thesis by (simp add: UP_def)
qed

lemma(in UP_ring) monom_deriv:
  assumes "p \<in> up R"
  shows "deriv R (monom (UP R) p) = shift (multc R (monom (UP R) p))"

(* deriv also returns a polynomial *)
lemma(in UP_ring) deriv_in_up_ring:
  assumes "p \<in> up R"
  shows "(deriv R p) \<in> up R" 
    by (simp add: assms deriv_def multc_in_up_ring shift_in_up_ring)

lemma(in UP_ring) degr: "deg R p = (LEAST n. bound (zero R) n (coeff (UP R) p))" using deg_def by auto

lemma(in UP_ring) coeff_simp:
  assumes "p \<in> up R"
  shows "coeff (UP R) p = p" 
proof-
  have "coeff (UP R) = (\<lambda>p \<in> (up R). p)" 
    by (simp add: UP_def)
  then show  "coeff (UP R) p = p" using assms by auto 
qed



lemma(in UP_ring) deg_simp_0:
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

lemma(in UP_ring) gt_deg_is_zero:
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
    by (metis coeff_simp deg_simp_0)
qed

lemma(in UP_ring) deg_neq_0:
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

lemma(in UP_ring) deg_shift_lt:
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

(*fun mult :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "mult p q = *) 
lemma(in UP_ring) prod_of_poly_is_poly:
  assumes "p \<in> up R" "q \<in> up R"
  shows "(p \<otimes>\<^bsub>UP R\<^esub> q) \<in> up R" using up_mult_closed
  by (metis (no_types, lifting) UP_def UP_ring.UP_mult_closed UP_ring_axioms assms(1) assms(2) partial_object.select_convs(1))

lemma(in UP_ring) add_of_poly_is_poly:
  assumes "p \<in> up R" "q \<in> up R"
  shows "(p \<oplus>\<^bsub>UP R\<^esub> q) \<in> up R"
  by (metis (no_types, lifting) UP_def UP_ring.UP_a_closed UP_ring_axioms assms(1) assms(2) partial_object.select_convs(1))

lemma(in UP_ring) deriv_mult_in_up:
  assumes "q \<in> up R" "p \<in> up R"
  shows "deriv R p \<otimes>\<^bsub>UP R\<^esub> q \<in> up R" using prod_of_poly_is_poly deriv_in_up_ring
  by (simp add: assms(1) assms(2))

lemma(in UP_ring) prod_monom_poly_in_up_0:
  assumes "p \<in> up R" "q \<in> up R"
  shows "p \<otimes>\<^bsub>UP R\<^esub> monom (UP R) (q n) (deg R q) \<in> up R" 
  by (metis (no_types, lifting) UP_def UP_ring.monom_closed UP_ring_axioms assms(1) assms(2) mem_upD partial_object.select_convs(1) prod_of_poly_is_poly)

lemma(in UP_ring) prod_monom_poly_in_up_1:
  assumes "p \<in> up R" "q \<in> up R"
  shows "monom (UP R) (q n) (deg R q) \<otimes>\<^bsub>UP R\<^esub> p \<in> up R" 
  by (metis (no_types, lifting) UP_def UP_ring.monom_closed UP_ring.prod_of_poly_is_poly UP_ring_axioms assms(1) assms(2) mem_upD partial_object.select_convs(1))

lemma(in UP_ring) deriv_add_comm:
  shows "deriv R (p \<oplus>\<^bsub>UP R\<^esub> q) = deriv R p \<oplus>\<^bsub>UP R\<^esub> deriv R q"
proof


lemma(in UP_ring) deg_0_deriv_zero:
  assumes "deg R q = 0"
  assumes "q \<in> carrier P"
  shows "deriv R q = \<zero>\<^bsub>P\<^esub>"
  sorry

lemma(in UP_ring) deg_0_is_monom:
  assumes "deg R p = 0"
  shows "\<exists>a. (p = monom P a 0)"
  sorry

lemma(in UP_cring) deg_0_smult:
  assumes "deg R q = 0"
  shows "p \<otimes>\<^bsub>P\<^esub> q = a \<odot>\<^bsub>P\<^esub> p" 
proof
  have "\<exists>a. (q = monom P a 0)" using deg_0_is_monom assms(1) by blast
  then have "coeff (UP R) q 0 = a" 

definition(in UP_ring) to_poly where
"to_poly  = (\<lambda>a. monom P a 0)"

lemma(in UP_ring) to_poly_is_ring_hom:
"to_poly \<in> ring_hom R P"
  unfolding P_def
  unfolding to_poly_def
  unfolding P_def
  using UP_ring.const_ring_hom[of R]
  UP_ring_axioms by blast

lemma(in UP_cring) product_deg_0_cons:
  assumes "p \<in> carrier P" "q \<in> carrier P"
  assumes "deg R q = 0"
  shows "(p \<otimes>\<^bsub>P\<^esub> q) n = (p n)\<otimes>(q 0)"
proof-
  have "(p \<otimes>\<^bsub>P\<^esub> q) n = (q \<otimes>\<^bsub>P\<^esub> p) n" 
    by (simp add: P.m_comm assms(1) assms(2))
  then have "(p \<otimes>\<^bsub>P\<^esub> q) n = (\<Oplus>\<^bsub>R\<^esub>i \<in> {..n}. q i \<otimes>\<^bsub>R\<^esub> p (n-i))"
    using assms(1) assms (2) UP_def 

    have

(*
  obtain n where ndef: "deg R p = n" by simp
  have "(\<Oplus>k \<in> {..n + 0}. \<Oplus>i \<in> {..k}. p i \<otimes> q (k - i)) =
    (\<Oplus>i \<in> {..n}. p i) \<otimes> (\<Oplus>i \<in> {..0}. q i)"
  proof-
    have 0:"bound \<zero> n p" using ndef 
      by (metis (no_types, lifting) P_def UP_def assms(1) bound_def gt_deg_is_zero partial_object.select_convs(1))
    have 1:"bound \<zero> 0 q"
      by (metis (no_types, lifting) P_def UP_def UP_ring.gt_deg_is_zero UP_ring_axioms assms(2) assms(3) bound_def partial_object.select_convs(1))
    have 2:"p \<in> {..n} \<rightarrow> carrier R" 
      by (metis (no_types, lifting) P_def Pi_I UP_def assms(1) mem_upD partial_object.select_convs(1))
    have 3:"q \<in> {..0} \<rightarrow> carrier R" 
      by (metis (no_types, lifting) P_def Pi_I UP_def assms(2) mem_upD partial_object.select_convs(1))
    show ?thesis using cauchy_product[of n p 0 q] 0 1 2 3 by auto

*)

lemma(in UP_ring) product_rule_deg_0:
  assumes "p \<in> carrier P"
  shows "\<And> q. q \<in> carrier P \<Longrightarrow> (deg R q) = 0 \<Longrightarrow> deriv R (p \<otimes>\<^bsub>UP R\<^esub> q) =  ((deriv R p) \<otimes>\<^bsub>UP R\<^esub> q) \<oplus>\<^bsub>UP R\<^esub> (p \<otimes>\<^bsub>(UP R)\<^esub> (deriv R q))"
proof-
  fix q
  assume C: "q \<in> carrier P" 
  assume A: "(deg R q) = 0 "
  then have 1: "deriv R q = \<zero>\<^bsub>P\<^esub>" 
    using deg_0_deriv_zero A C by auto
  then have "(p \<otimes>\<^bsub>(UP R)\<^esub> (deriv R q)) =  \<zero>\<^bsub>P\<^esub>" using UP_ring.UP_ring C assms(1)
    using P.r_null P_def by auto
  then have 1:"((deriv R p) \<otimes>\<^bsub>UP R\<^esub> q) \<oplus>\<^bsub>UP R\<^esub> (p \<otimes>\<^bsub>P\<^esub> (deriv R q)) = ((deriv R p) \<otimes>\<^bsub>P\<^esub> q) \<oplus>\<^bsub>UP R\<^esub> \<zero>\<^bsub>P\<^esub>" 
    by simp
  have "deriv R (p \<otimes>\<^bsub>UP R\<^esub> q) =  ((deriv R p) \<otimes>\<^bsub>UP R\<^esub> q)"
  proof

definition(in UP_ring) is_monomial where
"is_monomial q = (\<exists> n. \<exists> c. q = monom P c n)"


lemma(in UP_ring) product_rule_monom:
  shows "\<And> q. (deg R q) \<le> n \<and> (is_monomial q)\<Longrightarrow> deriv R (p \<otimes>\<^bsub>UP R\<^esub> q) =  ((deriv R p) \<otimes>\<^bsub>UP R\<^esub> q) \<oplus>\<^bsub>UP R\<^esub> (p \<otimes>\<^bsub>(UP R)\<^esub> (deriv R q))"
proof(induction n)
  case 0
  then show ?case sorry
next
  case (Suc n)
  then show ?case sorry
qed


lemma(in UP_ring) product_rule1:
  shows "\<And> q. (deg R q) \<le> n \<Longrightarrow> deriv R (p \<otimes>\<^bsub>UP R\<^esub> q) =  ((deriv R p) \<otimes>\<^bsub>UP R\<^esub> q) \<oplus>\<^bsub>UP R\<^esub> (p \<otimes>\<^bsub>(UP R)\<^esub> (deriv R q))"
proof(induction n)
  (*This proof seems difficult to do without talking explicitly about limits*)
  have "deriv R (p \<otimes>\<^bsub>UP R\<^esub> q) = shift(multc R (p \<otimes>\<^bsub>UP R\<^esub> q))"
    by (simp add: deriv_def)
  
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
