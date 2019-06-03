theory hensel
  imports Main "~~/src/HOL/Algebra/UnivPoly" "~~/src/HOL/Algebra/Valued_Fields/padic_construction" "~~/src/HOL/Algebra/Valued_Fields/cring_poly"
begin

definition p_UP :: "nat \<Rightarrow> (nat \<Rightarrow> int, nat \<Rightarrow> nat \<Rightarrow> int) up_ring" where
  "p_UP p = UP (padic_int p)"

definition shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "shift b n = b (n + 1)"

definition multc :: "('a, 'b) ring_scheme \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "multc R b n = add_pow R n (b n)"

definition deriv :: "('a, 'b) ring_scheme \<Rightarrow> (nat \<Rightarrow> 'a ) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "deriv R b = shift (multc R b)"

definition lc :: "('a,'b) ring_scheme \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "lc R p = p (deg R p)"

lemma(in UP_domain) multc_simp[simp]:
  assumes "p \<in> carrier P"
  shows "multc R p n = [n]\<cdot>(p n)" 
  by (simp add: multc_def)

lemma(in UP_ring) shift_in_up_ring:
  assumes "b \<in> up R"
  shows "shift  b \<in> up R" 
proof
  show "\<And>n. shift b n \<in> carrier R" 
    by (simp add: assms hensel.shift_def mem_upD)
 show "\<exists>n. bound \<zero> n (shift b)" 
  proof- 
    obtain n where Bb: "bound \<zero> n b"
      using assms(1) by auto
    have "bound \<zero> n (shift b)"
    proof
      fix m
      assume A: "n < m"
      have P0: "shift b m = b (m + 1)" 
        by (simp add: hensel.shift_def)
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
      by (simp add: assms mem_upD multc_def)
    qed
  show "\<exists>n. bound \<zero> n (hensel.multc R b)"
    by (smt R.add.nat_pow_one R.bound_upD assms bound_def multc_def)
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



(*lemma(in UP_ring) monom_eq_deg:
  assumes "deg R p = n"
  assumes "m \<ge> n"
  shows "monom P (p n) n m = p m"
  proof(cases "m \<noteq> n")
    case True
    have "m > n" sledgehammer
      using True assms(2) le_neq_implies_less by blast
    have "bound \<zero> (deg R p) p" sledgehammer
    have "monom P (p n) n m = \<zero>" sledgehammer
    then show ?thesis 
  next
    case False
    then show ?thesis using assms(1) assms(2) monom_simp UP_def 
  qed*)

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
      then have "` R p m = \<zero>" 
        by (simp add: \<open>\<not> m < n\<close> assms(3))
  qed

lemma(in UP_ring) trunc_deg_lt:
  assumes "p \<in> up R"
  assumes "deg R p > 0"
  shows "deg R (trunc R p) < deg R p" 
proof-
  have "\<And>n. n < deg R p \<Longrightarrow> trunc R p n = p n"
    by simp
  have "trunc R p (deg R p) = \<zero>" by simp
  obtain n where ndef: "deg R p = n" by simp
  have "deg R p = (LEAST n. bound \<zero> n (coeff (UP R) p))" using deg_def by auto
  then have "bound \<zero> n (coeff (UP R) p)" using LeastI 
    by (smt P_def UP_def \<open>deg R p = n\<close> assms(1) bound_def deg_aboveD partial_object.select_convs(1))
  then have "\<And>m. m > n \<Longrightarrow> p m = \<zero>"
    using \<open>deg R p = n\<close>
    by (smt UP_def assms(1) bound.bound restrict_apply up_ring.simps(2))
  have A1: "\<And>m. m > n \<Longrightarrow> trunc R p m = \<zero>"
    using \<open>deg R p = n\<close> by auto
  hence "bound \<zero> n (trunc R p)" using bound_def LeastI
    by blast
  have "trunc R p n = \<zero>"
    by (simp add: \<open>deg R p = n\<close>)
  hence B1: "bound \<zero> (n-1) (trunc R p)" using A1 
    using \<open>deg R p = n\<close> less_trans by auto
  have "(n-1) < n"
    using \<open>deg R p = n\<close> assms(2) by auto
  hence "deg R (trunc R p) \<noteq> n" using deg_def Least_def LeastI B1 
    by (smt P_def UP_def UP_ring.trunc_is_poly UP_ring_axioms \<open>deg R p = n\<close> \<open>trunc R p n = \<zero>\<close> assms(1) assms(2) lcoeff_nonzero_deg 
        neq0_conv partial_object.select_convs(1) restrict_apply up_ring.simps(2))
  hence "deg R (trunc R p) < n" using deg_def LeastI 
    by (smt A1 UP_def UP_ring.deg_zero UP_ring.lcoeff_nonzero2 UP_ring.trunc_is_poly UP_ring_axioms assms(1) assms(2) linorder_neqE_nat ndef 
        partial_object.select_convs(1) restrict_apply up_ring.simps(2))
  thus ?thesis using ndef by simp
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
  shows "deriv R (monom (UP R) a p) = shift (multc R (monom (UP R) a p))" sledgehammer

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
  then show "\<And>m. \<lbrakk>m > deg R p\<rbrakk> \<Longrightarrow> p m = \<zero>" using 1 2 3 assms(1) bound_def bound_upD 
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
    using hensel.shift_def by auto
  have 1: "p (n+1) = \<zero>" using 1 assms deg_def gt_deg_is_zero
    by simp
  then have 2: "shift p n = p (n+1)" using hensel.shift_def 
    by (simp add: hensel.shift_def)
  then have 3: "shift p n = \<zero>" using 1 by auto
  thus "deg R (shift p) < deg R p" using degr 1 2 3 assms(1) assms(2) deg_neq_0
    by (smt One_nat_def add.commute add.left_neutral add_Suc_right add_mono_thms_linordered_field(5) gt_deg_is_zero hensel.shift_def lessI less_imp_add_positive linorder_neqE_nat shift_in_up_ring)
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

definition(in UP_ring) to_poly where
"to_poly  = (\<lambda>a. monom P a 0)"

lemma(in UP_ring) to_poly_is_ring_hom:
"to_poly \<in> ring_hom R P"
  unfolding P_def
  unfolding to_poly_def
  unfolding P_def
  using UP_ring.const_ring_hom[of R]
  UP_ring_axioms by blast


lemma(in UP_ring) deg_0_deriv_zero:
  assumes "deg R q = 0"
  assumes "q \<in> carrier P"
  shows "deriv R q = \<zero>\<^bsub>P\<^esub>"
proof-
  have B0: "deg R q = 0 \<Longrightarrow> bound \<zero> 0 q"
    by (metis (no_types, lifting) P_def UP_def UP_ring.gt_deg_is_zero UP_ring_axioms assms(2) bound_def partial_object.select_convs(1))
  have "shift q n = q (n+1)" 
    by (simp add: hensel.shift_def)
  have "q n = \<zero> \<Longrightarrow> multc R q n = \<zero>"
    by (simp add: multc_def)
  hence "\<And>n. n > 0 \<Longrightarrow> multc R q n = \<zero>" using B0 assms(1) assms(2)
    by (metis R.add.nat_pow_one bound.bound multc_def)
  hence A1: "\<And>n. shift (multc R q) n = \<zero>" using B0 assms(1) assms(2)
    by (simp add: hensel.shift_def)
  have "deriv R q = shift (multc R q)" using deriv_def by auto
  hence "\<And>n. deriv R q n = \<zero>"
    by (simp add: A1)
  thus "deriv R q = \<zero>\<^bsub>P\<^esub>"
    by (metis (no_types, lifting) P_def UP_def UP_ring.deriv_in_up_ring UP_ring.lcoeff_nonzero 
        UP_ring_axioms assms(2) coeff_simp partial_object.select_convs(1))
qed

lemma(in UP_ring) deg_0_implies_0_coeffs:
  assumes "p \<in> up R"
  assumes "deg R p = 0"
  shows "\<And>n. n > 0 \<Longrightarrow> coeff P p n = \<zero>"
  by (simp add: P_def UP_ring.coeff_simp UP_ring.gt_deg_is_zero UP_ring_axioms assms(1) assms(2))

lemma(in UP_ring) deg_0_is_monom:
  assumes "p \<in> up R"
  assumes "deg R p = 0"
  shows "\<exists>a. (monom P a 0 = p)" 
  by (metis (no_types, lifting) P_def UP_def assms(1) assms(2) deg_zero_impl_monom partial_object.select_convs(1))

lemma(in UP_ring) monom_coeff_simp:
  assumes "p \<in> up R"
  assumes "a \<in> carrier R"
  shows "coeff P (monom P a n) n = a"
  by (simp add: assms(2))

lemma(in UP_cring) deg_0_smult:
  assumes "p \<in> up R" "q \<in> up R"
  assumes "a \<in> carrier R"
  assumes "deg R q = 0"
  assumes "q 0 = a"
  shows "q \<otimes>\<^bsub>P\<^esub> p= a \<odot>\<^bsub>P\<^esub> p"
proof- 
  have bdef: "\<exists>b \<in> carrier R. monom P b 0 = q"
    using assms(2) assms(4) deg_zero_impl_monom
    by (metis (no_types, lifting) P_def UP_def lcoeff_closed partial_object.select_convs(1))
   have "deg R (monom P a 0) = 0"
    using assms(4) by
  by (simp add: assms(3))
  have " (monom P a 0) 0 = a" using UP_def bdef monom_coeff_simp 
  using assms(2) assms(3) 
  by (simp add: P_def UP_ring.monom_simp UP_ring_axioms)
  have "monom P a 0 \<otimes>\<^bsub>P\<^esub> p = a \<odot>\<^bsub>P\<^esub> p" using monom_mult_is_smult
    by (simp add: P_def UP_def assms(1) assms(3))
  have A1: "\<And>n. n > 0 \<Longrightarrow> q n = \<zero>" using assms(3) assms(1)
    by (simp add: assms(2) assms(4) gt_deg_is_zero)
  have A2: "\<And>n. n > 0 \<Longrightarrow> monom P a 0 n = \<zero>"
    by (simp add: P_def UP_ring.monom_simp UP_ring_axioms assms(3))
  have "q 0 = monom P a 0 0"
    by (simp add: \<open>monom P a 0 0 = a\<close> assms(5))
  thus ?thesis
    using P_def UP_ring.monom_simp UP_ring_axioms \<open>monom P a 0 \<otimes>\<^bsub>P\<^esub> p = a \<odot>\<^bsub>P\<^esub> p\<close> assms(5) bdef by fastforce
qed

lemma(in UP_ring) deg_0_monom_simp_0:
  assumes "q \<in> carrier P"
  assumes "deg R q = 0"
  assumes "is_monomial q"
  shows "\<And>i. \<lbrakk>i > 0\<rbrakk> \<Longrightarrow> q i = \<zero>"
  by (metis (no_types, lifting) P_def UP_def assms(1) assms(2) gt_deg_is_zero partial_object.select_convs(1))
  

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
lemma(in UP_ring) deriv_cons_mult:
  assumes "a \<in> carrier R"
  assumes "p \<in> carrier P"
  shows "\<And>n. deriv R (a \<odot>\<^bsub>P\<^esub> p) n = a \<otimes>\<^bsub>R\<^esub> deriv R p n"
proof-
  fix n
  have A1: "\<And>m. (a \<odot>\<^bsub>P\<^esub> p) m = a \<otimes>\<^bsub>R\<^esub> p m" 
    by (smt P_def UP_def UP_ring.coeff_simp UP_ring_axioms UP_smult_closed assms(1) assms(2) coeff_smult partial_object.select_convs(1)) 
  then have "\<And>m. shift (a \<odot>\<^bsub>P\<^esub> p) m = a \<otimes>\<^bsub>R\<^esub> p (m+1)"
    by (simp add: hensel.shift_def)
  have "multc R (a \<odot>\<^bsub>P\<^esub> p) n = a \<otimes>\<^bsub>R\<^esub> multc R p n" 
    by (smt A1 P_def R.add_pow_rdistr UP_def assms(1) assms(2) mem_upD multc_def partial_object.select_convs(1))
  hence "\<And>m. multc R (a \<odot>\<^bsub>P\<^esub> p) m = a \<otimes>\<^bsub>R\<^esub> multc R p m" 
    by (metis (no_types, lifting) A1 P_def R.add_pow_rdistr UP.coeff_closed UP_def assms(1) assms(2) coeff_simp multc_def partial_object.select_convs(1))
  thus "\<And>n. deriv R (a \<odot>\<^bsub>P\<^esub> p) n = a \<otimes>\<^bsub>R\<^esub> deriv R p n"
    by (simp add: deriv_def hensel.shift_def)
qed

lemma(in UP_ring) poly_is_sum_monom:
  shows "\<lbrakk> p \<in> carrier P \<and> deg R p = n \<rbrakk> \<Longrightarrow> p = (\<Oplus>\<^bsub>P\<^esub>i \<in>{..n}. (monom P (p i) i))" 
proof(induction n)
  case 0
  then have "deg R p = 0"
    by simp
  have "coeff P p 0 = monom P (p 0) 0 0" 
    by (metis (no_types, lifting) "0" P_def UP_def UP_ring.coeff_simp UP_ring_axioms deg_zero_impl_monom partial_object.select_convs(1))
  have "\<And>n. n > 0 \<Longrightarrow> monom P (p 0) 0 n = \<zero>" 
    by (metis (no_types, lifting) "0" P_def UP_def UP_ring.coeff_simp UP_ring_axioms deg_zero_impl_monom gt_deg_is_zero partial_object.select_convs(1))
  have "\<And>m. m > 0 \<Longrightarrow> coeff P p m = \<zero>" 
    by (simp add: "0" deg_aboveD)
  then show ?case 
  proof -
    have "carrier P = up R"
      by (simp add: P_def UP_def)
    then show ?thesis
      by (metis (no_types) "0.prems" P_def UP_ring.coeff_simp UP_ring_axioms up_repr)
  qed
next
  case (Suc n)
  assume "p \<in> carrier P \<and> deg R p = n \<Longrightarrow> p = (\<Oplus>\<^bsub>P\<^esub>i\<in>{..n}. monom P (p i) i)" 
  then show ?case 
   
  proof -
    have "carrier P = up R"
      by (simp add: P_def UP_def)
    then have "coeff P p = p"
      using P_def Suc.prems UP_ring.coeff_simp UP_ring_axioms by auto
    then show ?thesis
      using Suc.prems up_repr by fastforce
  qed
qed

lemma(in UP_cring) product_rule_deg_0:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "deg R q = 0"
  shows "deriv R (q \<otimes>\<^bsub>UP R\<^esub> p) =  ((deriv R q) \<otimes>\<^bsub>UP R\<^esub> p) \<oplus>\<^bsub>UP R\<^esub> (q \<otimes>\<^bsub>(UP R)\<^esub> (deriv R p))"
proof-
  obtain a where adef: "q 0 = a" by simp
   have 1: "deriv R q = \<zero>\<^bsub>P\<^esub>" 
    using  P_def UP_ring.deg_0_deriv_zero UP_ring_axioms assms(2) assms(3) by blast
  then have "((deriv R q) \<otimes>\<^bsub>(UP R)\<^esub> p) =  \<zero>\<^bsub>P\<^esub>" 
    using P.l_null P_def assms(1)  assms(2) assms(3) deg_0_deriv_zero by auto
  then have 1:"((deriv R p) \<otimes>\<^bsub>UP R\<^esub> q) \<oplus>\<^bsub>UP R\<^esub> (p \<otimes>\<^bsub>P\<^esub> (deriv R q)) = (q \<otimes>\<^bsub>P\<^esub> (deriv R p)) \<oplus>\<^bsub>UP R\<^esub> \<zero>\<^bsub>P\<^esub>" 
    using "1" P.r_null P_def assms(1)
    by (smt P.m_comm UP_def assms(2) deriv_in_up_ring partial_object.select_convs(1))
  then have "deriv R (q \<otimes>\<^bsub>UP R\<^esub> p) = deriv R (a \<odot>\<^bsub>P\<^esub> p)" using P_def P_fact0 UP_ring_deg_zero_impl_monom assms(1) assms(2) assms(3) assms(4)
      by (metis (no_types, lifting) P_def P_fact0 UP_def adef assms(1) assms(2) assms(3) deg_0_smult partial_object.select_convs(1))
   then have "\<And>n. deriv R (a \<odot>\<^bsub>P\<^esub> p) n = (a \<odot>\<^bsub>P\<^esub> deriv R p) n" using deriv_cons_mult assms (1) assms(4)  
    by (smt P_def P_fact0 UP_def UP_ring.coeff_simp UP_ring.coeff_smult UP_ring.deriv_in_up_ring UP_ring.prod_of_poly_is_poly UP_ring_axioms adef
        assms(1) assms(2) assms(3) deg_0_smult deriv_cons_mult partial_object.select_convs(1)) 
  hence "deriv R (a \<odot>\<^bsub>P\<^esub> p) = a \<odot>\<^bsub>P\<^esub> deriv R p" 
    by (simp add: ext)
  thus ?thesis 
    by (smt P_def P_fact0 UP_def UP_l_zero UP_mult_closed UP_ring.deriv_in_up_ring UP_ring_axioms \<open>deriv R q \<otimes>\<^bsub>UP R\<^esub> p = \<zero>\<^bsub>P\<^esub>\<close> adef assms(1) assms(2) 
         assms(3) deg_0_smult partial_object.select_convs(1))
qed
(*  then have "deriv R (q \<otimes>\<^bsub>UP R\<^esub> p) =  (q \<otimes>\<^bsub>UP R\<^esub>(deriv R p) )"
  proof-
    have "\<exists>a \<in> carrier R. q = monom P a 0"
      using assms(2) assms(3) deg_zero_impl_monom by fastforce
    (*then obtain a where adef: "q = monom P a 0"
      by blast*)
    hence "q \<otimes>\<^bsub>UP R\<^esub> p =  a \<odot>\<^bsub>P\<^esub> p" using deg_0_smult
      using P_def UP_ring.monom_simp UP_ring_axioms assms(1) assms(4) monom_mult_is_smult by fastforce*)
    


definition(in UP_ring) is_monomial where
"is_monomial q = (\<exists> n. \<exists> c. q = monom P c n)"

definition(in UP_ring) is_const where
"is_const q = (is_monomial q) \<and> deg R q = 0"

lemma(in UP_ring) deg_0_deriv_is_zero:
  assumes "deg R p = 0"
  assumes "p \<in> carrier P"
  shows "\<And>n. deriv R p n = \<zero>" using UP_smult_zero deg_0_smult deg_one 
  by (metis (no_types, lifting) One_nat_def P_def R.add.nat_pow_one UP_def UP_ring add.left_neutral assms(1) assms(2) deg_0_deriv_zero deg_zero 
      deriv_def gr0I gt_deg_is_zero hensel.shift_def lessI multc_def partial_object.select_convs(1) ring.ring_simprules(2))

lemma(in UP_ring) shift_additive:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "shift (p \<oplus>\<^bsub>P\<^esub> q) = shift p \<oplus>\<^bsub>P\<^esub> shift q"
proof
  have A1: "\<And>n. shift (p \<oplus>\<^bsub>P\<^esub> q) n = (p \<oplus>\<^bsub>P\<^esub> q) (n+1)" using shift_def by simp
  have A2: "\<And>n. (p  \<oplus>\<^bsub>P\<^esub> q) n = p n \<oplus> q n" 
    by (smt P_def UP_a_closed UP_def UP_ring.coeff_simp UP_ring_axioms assms(1) assms(2) coeff_add partial_object.select_convs(1))
  then have "\<And>n. (p \<oplus>\<^bsub>P\<^esub> q) (n+1) = p (n+1) \<oplus>\<^bsub>R\<^esub> q (n+1)"
    by simp
  hence "\<And>n. shift (p \<oplus>\<^bsub>P\<^esub> q) n =  p (n+1) \<oplus>\<^bsub>R\<^esub> q (n+1)" 
    by (simp add: A1)
  hence A3: "\<And>n. shift (p \<oplus>\<^bsub>P\<^esub> q) n = shift p n  \<oplus>\<^bsub>R\<^esub> shift q n"
    by (simp add: A2 hensel.shift_def)
  have "\<And>n. shift p n \<oplus>\<^bsub>R\<^esub> shift q n = (shift p \<oplus>\<^bsub>P\<^esub> shift q ) n" 
    by (smt P_def UP_def UP_ring.UP_a_closed UP_ring.coeff_add UP_ring_axioms assms(1) assms(2) coeff_simp partial_object.select_convs(1) shift_in_up_ring)
  thus "\<And>n. shift (p \<oplus>\<^bsub>P\<^esub> q) n = (shift p \<oplus>\<^bsub>P\<^esub> shift q ) n" 
    by (simp add: \<open>\<And>n. shift (p \<oplus>\<^bsub>P\<^esub> q) n = shift p n \<oplus> shift q n\<close>)
qed

lemma(in UP_ring) multc_additive:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "multc R (p \<oplus>\<^bsub>P\<^esub> q) = multc R p \<oplus>\<^bsub>P\<^esub> multc R q" 
proof
  have A1: "\<And>n. multc R (p \<oplus>\<^bsub>P\<^esub> q) n = [n]\<cdot>(p \<oplus>\<^bsub>P\<^esub> q) n"
    by (simp add: multc_def)
  have A2: "\<And>n. [n]\<cdot>(p \<oplus>\<^bsub>P\<^esub> q) n = [n]\<cdot>(p n) \<oplus>\<^bsub>R\<^esub> [n]\<cdot>(q n)" 
    by (smt P_def R.add.nat_pow_distr UP_a_closed UP_def UP_ring.coeff_add UP_ring.coeff_simp UP_ring_axioms assms(1) assms(2) 
         mem_upD partial_object.select_convs(1))
  have A3: "\<And>n. [n]\<cdot>(p n) \<oplus>\<^bsub>R\<^esub> [n]\<cdot>(q n) = multc R p n \<oplus>\<^bsub>R\<^esub> multc R q n" 
    by (simp add: multc_def)
  have "\<And>n. multc R p n \<oplus>\<^bsub>R\<^esub> multc R q n = (multc R p \<oplus>\<^bsub>P\<^esub> multc R q) n" 
    by (smt P_def UP_def UP_ring.UP_a_closed UP_ring.coeff_add UP_ring.coeff_simp UP_ring_axioms assms(1) assms(2) multc_in_up_ring 
        partial_object.select_convs(1))
  thus "\<And>n. multc R (p \<oplus>\<^bsub>P\<^esub> q) n = (multc R p \<oplus>\<^bsub>P\<^esub> multc R q) n" using A1 A2 A3 assms(1) assms(2) by simp
qed

lemma(in UP_ring) deriv_additive_0:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "deriv R ( p \<oplus>\<^bsub>P\<^esub> q ) = deriv R p \<oplus>\<^bsub>P\<^esub> deriv R q"  using deriv_def shift_additive multc_additive assms(1) assms(2)
  by (simp add: deriv_def P_def UP_def multc_in_up_ring partial_object.select_convs(1))

lemma(in UP_ring) deriv_additive_1:
  assumes fin: "finite A"
  assumes "A \<noteq> {}"
  assumes "(p \<in> A) \<Longrightarrow> (p \<in> carrier P)"
  shows "deriv R (\<Oplus>\<^bsub>P\<^esub> p \<in> A. p) = (\<Oplus>\<^bsub>P\<^esub> p \<in> A. deriv R p)"
proof(induct "card A")
  case C1: 0
  show ?case
    apply(rule ccontr)
  proof(rule ccontr)
    assume "deriv R (\<Oplus>\<^bsub>P\<^esub>p\<in>A. p) \<noteq> finsum P (deriv R) A"
    have "card A = 0" using C1 by simp
    have "finite A \<and> A \<noteq> {}" using assms(1) assms(2) by simp
    have "card A \<noteq> 0" using assms(2) assms(1) card_gt_0_iff 
      by simp
    thus False
    by (simp add: C1.hyps)
next
  case (Suc x)
  assume "x = card A \<Longrightarrow> deriv R (\<Oplus>\<^bsub>P\<^esub>p\<in>A. p) = finsum P (deriv R) A"
  assume "Suc x = card A"
  then show ?case sorry
qed

lemma(in UP_domain) product_rule_monom:
  assumes "p \<in> carrier P"
  shows "\<And>q. \<lbrakk>q \<in> carrier P \<and> deg R q \<le> n \<and> is_monomial q \<rbrakk> \<Longrightarrow> deriv R (q \<otimes>\<^bsub>UP R\<^esub> p) = ((deriv R q) \<otimes>\<^bsub>UP R\<^esub> p) \<oplus>\<^bsub>UP R\<^esub> (q \<otimes>\<^bsub>(UP R)\<^esub> (deriv R p))"
proof(induction n)
  case 0
    then have 1: "deg R q = 0" 
      by simp
    have 2: "q \<in> carrier P"
      by (simp add: "0.prems")
    show ?case using product_rule_deg_0 1 2 assms(1) by auto
  next
  case (Suc n)
    fix n
    assume A1: "(\<And>q. q \<in> carrier P \<and> deg R q \<le> n \<and> is_monomial q \<Longrightarrow> deriv R (q \<otimes>\<^bsub>P\<^esub> p) = deriv R q \<otimes>\<^bsub>P\<^esub> p \<oplus>\<^bsub>UP R\<^esub> q \<otimes>\<^bsub>P\<^esub> deriv R p)"
    assume A2: "q \<in> carrier P \<and> deg R q \<le> Suc n \<and> is_monomial q"
    show "deriv R (q \<otimes>\<^bsub>P\<^esub> p) = deriv R q \<otimes>\<^bsub>P\<^esub> p \<oplus>\<^bsub>UP R\<^esub> q \<otimes>\<^bsub>P\<^esub> deriv R p"
    proof
      have "q \<in> carrier P \<and> deg R q \<le> Suc n \<and> is_monomial q \<Longrightarrow> is_monomial q" by simp
      then have "is_monomial q" using A2 by simp 
      obtain a where "q (deg R q) = a"
        then have "q \<otimes>\<^bsub>P\<^esub> p = a \<odot>\<^bsub>P\<^esub> p" sledgehammer


lemma(in UP_domain) product_rule1:
  shows "\<And> q. (deg R q) = n \<Longrightarrow> deriv R (p \<otimes>\<^bsub>UP R\<^esub> q) =  ((deriv R p) \<otimes>\<^bsub>UP R\<^esub> q) \<oplus>\<^bsub>UP R\<^esub> (p \<otimes>\<^bsub>(UP R)\<^esub> (deriv R q))"
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
