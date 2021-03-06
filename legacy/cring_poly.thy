theory cring_poly
imports "~~/src/HOL/Algebra/UnivPoly" 
begin

(*The composition of two ring homomorphisms is a ring homomorphism*)
lemma ring_hom_compose:
  assumes "ring R"
  assumes "ring S"
  assumes "ring T"
  assumes "h \<in> ring_hom R S"
  assumes "g \<in> ring_hom S T"
  assumes "\<And>c. c \<in> carrier R \<Longrightarrow> f c = g (h c)"
  shows "f \<in>  ring_hom R T"
proof(rule ring_hom_memI)
  show "\<And>x. x \<in> carrier R \<Longrightarrow> f x \<in> carrier T"
    using assms  by (metis ring_hom_closed)
  show " \<And>x y. x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> f (x \<otimes>\<^bsub>R\<^esub> y) = f x \<otimes>\<^bsub>T\<^esub> f y"
  proof-
    fix x y
    assume A: "x \<in>  carrier R" "y \<in>  carrier R"
    show "f (x \<otimes>\<^bsub>R\<^esub> y) = f x \<otimes>\<^bsub>T\<^esub> f y"
    proof-
      have  "f (x \<otimes>\<^bsub>R\<^esub> y) = g (h (x \<otimes>\<^bsub>R\<^esub> y))"
        by (simp add: A(1) A(2) assms(1) assms(6) ring.ring_simprules(5))
      then have  "f (x \<otimes>\<^bsub>R\<^esub> y) = g ((h x) \<otimes>\<^bsub>S\<^esub> (h y))"
        using A(1) A(2) assms(4) ring_hom_mult by fastforce
      then have  "f (x \<otimes>\<^bsub>R\<^esub> y) = g (h x) \<otimes>\<^bsub>T\<^esub> g (h y)"
        using A(1) A(2) assms(4) assms(5) ring_hom_closed ring_hom_mult by fastforce
      then show ?thesis 
        by (simp add: A(1) A(2) assms(6))
    qed
  qed
  show "\<And>x y. x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> f (x \<oplus>\<^bsub>R\<^esub> y) = f x \<oplus>\<^bsub>T\<^esub> f y"
  proof-
    fix x y
    assume A: "x \<in>  carrier R" "y \<in>  carrier R"
    show "f (x \<oplus>\<^bsub>R\<^esub> y) = f x \<oplus>\<^bsub>T\<^esub> f y"
    proof-
      have  "f (x \<oplus>\<^bsub>R\<^esub> y) = g (h (x \<oplus>\<^bsub>R\<^esub> y))"
        by (simp add: A(1) A(2) assms(1) assms(6) ring.ring_simprules(1))
      then have  "f (x \<oplus>\<^bsub>R\<^esub> y) = g ((h x) \<oplus>\<^bsub>S\<^esub> (h y))"
        using A(1) A(2) assms(4) ring_hom_add by fastforce
      then have  "f (x \<oplus>\<^bsub>R\<^esub> y) = g (h x) \<oplus>\<^bsub>T\<^esub> g (h y)"
        by (metis (no_types, hide_lams) A(1) A(2) assms(4) assms(5) ring_hom_add ring_hom_closed)
      then show ?thesis
        by (simp add: A(1) A(2) assms(6))
    qed
  qed
  show "f \<one>\<^bsub>R\<^esub> = \<one>\<^bsub>T\<^esub>" 
    by (metis assms(1) assms(4) assms(5) assms(6) ring.ring_simprules(6) ring_hom_one)
qed


context UP_domain
begin

(*rings are closed under monomial terms*)
lemma monom_term_car:
  assumes "c \<in> carrier R"
  assumes "x \<in> carrier R"
  shows "c \<otimes> x[^](n::nat) \<in> carrier R"
  using assms monoid.nat_pow_closed 
  by blast

(*Univariate polynomial ring over R*)

lemma P_is_UP_ring[simp]:
"UP_ring R"
  by (simp add: UP_ring_axioms)

(*Degree function*)
abbreviation degree  where
"degree f \<equiv>  deg R f"
end 

(*Bound on the degree of a sum*)
lemma bound_deg_sum_UP_ring[simp]:
  assumes "UP_ring R"
  assumes " f \<in> carrier (UP R)"
  assumes "g \<in> carrier (UP R)"
  assumes "deg R f  \<le> n"
  assumes "deg R g \<le> n"
  shows "deg R(f \<oplus>\<^bsub>UP R\<^esub> g) \<le>n"
  by (meson UP_ring.deg_add assms(1) assms(2) assms(3) 
      assms(4) assms(5) dual_order.trans le_max_iff_disj)

lemma(in UP_domain) bound_deg_sum[simp]:
  assumes " f \<in> carrier P"
  assumes "g \<in> carrier P"
  assumes "degree f  \<le> n"
  assumes "degree g \<le> n"
  shows "degree (f \<oplus>\<^bsub>P\<^esub> g) \<le>n"
  using P_def UP_ring_axioms assms(1) assms(2) assms(3) assms(4) bound_deg_sum_UP_ring 
  by blast

lemma bound_deg_sum'_UP_ring[simp]:
  assumes "UP_ring R"
  assumes " f \<in> carrier (UP R)"
  assumes "g \<in> carrier (UP R)"
  assumes "deg R f < n"
  assumes "deg R g < n"
  shows "deg R (f \<oplus>\<^bsub>UP R\<^esub> g) <n"
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) bound_deg_sum_UP_ring le_less_trans nat_le_linear)

lemma(in UP_domain) bound_deg_sum'[simp]:
  assumes " f \<in> carrier P"
  assumes "g \<in> carrier P"
  assumes "degree f < n"
  assumes "degree g < n"
  shows "degree (f \<oplus>\<^bsub>P\<^esub> g) <n"
  using P_def UP_ring_axioms assms(1) assms(2) 
        assms(3) assms(4) bound_deg_sum'_UP_ring by blast

lemma(in UP_domain) equal_deg_sum[simp]:
  assumes " f \<in> carrier P"
  assumes "g \<in> carrier P"
  assumes "degree f < n"
  assumes "degree g = n"
  shows "degree (f \<oplus>\<^bsub>P\<^esub> g) = n"
proof-
  have 0: "degree (f \<oplus>\<^bsub>P\<^esub> g) \<le>n"
    using assms bound_deg_sum 
          P_def UP_ring_axioms by auto
  show "degree (f \<oplus>\<^bsub>P\<^esub> g) = n"
  proof(rule ccontr)
    assume "degree (f \<oplus>\<^bsub>P\<^esub> g) \<noteq> n "
    then have 1: "degree (f \<oplus>\<^bsub>P\<^esub> g) < n"
      using 0 by auto 
    have 2: "degree (\<ominus>\<^bsub>P\<^esub> f) < n"
      using assms by simp
    have 3: "g = (f \<oplus>\<^bsub>P\<^esub> g) \<oplus>\<^bsub>P\<^esub> (\<ominus>\<^bsub>P\<^esub> f)"
      using assms cring  
      by (simp add: P.add.m_comm P.r_neg1)
    then show False using 1 2 3 assms 
      by (metis UP_a_closed UP_a_inv_closed deg_add leD le_max_iff_disj)
  qed
qed

lemma equal_deg_sum_UP_ring[simp]:
  assumes "UP_domain R"
  assumes " f \<in> carrier (UP R)"
  assumes "g \<in> carrier (UP R)"
  assumes "deg R f < n"
  assumes "deg R g = n"
  shows "deg R (f \<oplus>\<^bsub>UP R\<^esub> g) = n"
  by (simp add: UP_domain.equal_deg_sum assms(1) assms(2) assms(3) assms(4) assms(5))

lemma(in UP_domain) equal_deg_sum'[simp]:
  assumes "f \<in> carrier P"
  assumes "g \<in> carrier P"
  assumes "degree g < n"
  assumes "degree f = n"
  shows "degree (f \<oplus>\<^bsub>P\<^esub> g) = n"
  using P.add.m_comm assms(1) assms(2) assms(3) assms(4) by fastforce

context UP_domain
begin

(*Coefficient function*)
abbreviation cf  where
"cf  \<equiv> coeff P "

(*This function is redundant*)
lemma cf_f:
  assumes "f \<in> carrier P"
  shows "cf f = f"
proof-
  have "cf = (\<lambda>f \<in> up R. f)"
    using  P_def  by (simp add: UP_def)
  then show ?thesis using assms P_def by (simp add: UP_def) 
qed

(*So is coeff from UNIVPOLY*)

lemma coeff_simp1:
  assumes "f \<in> carrier P"
  shows "coeff (UP R)  f = f "
  using cf_f  P_def assms by auto

(*Coefficients are in R*)
lemma cfs_closed[simp]:
  assumes "f \<in> carrier P"
  shows "f n \<in> carrier R"
proof-
  have "coeff P f n \<in> carrier R"
    using assms P_def by (simp add: UP.coeff_closed)
  then show ?thesis 
    using assms cf_f by auto  
qed

(*closure under smult*)


lemma cfs_closed_UP_domain[simp]:
  assumes "UP_domain R"
  assumes "f \<in> carrier (UP R)"
  shows "f n \<in> carrier R"
  by (simp add: UP_domain.cfs_closed assms(1) assms(2))
end 

context UP_domain
begin

(*Coefficients are additive *)
lemma cf_add[simp]:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "(p \<oplus>\<^bsub>P\<^esub> q) n = (p n) \<oplus> (q n)"
proof-
  have 0: "(p \<oplus>\<^bsub>P\<^esub> q) n = coeff P (p \<oplus>\<^bsub>P\<^esub> q) n" 
    by (simp add: assms(1) assms(2) cf_f)
  have 1: "(p n) \<oplus> (q n) = (coeff P p) n \<oplus> (coeff P q) n"
    by (simp add: assms(1) assms(2) cf_f)
  then show ?thesis 
    by (simp add: "0" assms(1) assms(2))
qed

end

definition leading_term where 
"leading_term R f = monom (UP R) (f (deg R f)) (deg R f)"

context UP_domain 
begin

(*Leading term function*) 
abbreviation lt  where
"lt f \<equiv> leading_term R f"

(*leading term is a polynomial*)
lemma lt_closed:
  assumes "f \<in> carrier P"
  shows "lt f \<in> carrier P"
  unfolding leading_term_def
  using UP_ring.monom_closed P_is_UP_ring  UP.coeff_closed 
    UP_ring.monom_closed P_def P_is_UP_ring assms cf_f 
  by (simp add: UP_ring.monom_closed)

(*Simplified coefficient function description for leading term*)
lemma lt_coeffs0:
  assumes "f \<in> carrier P"
  shows "coeff P (lt f) n  = (if (n = degree f) then (f (degree f)) else \<zero>)"
    unfolding leading_term_def
    apply(simp add: UP_ring.coeff_monom)
    using UP_ring.coeff_monom UP_ring.lcoeff_closed P_def P_is_UP_ring
      assms cf_f  by (simp add: UP_ring.coeff_monom)

lemma lt_coeffs:
  assumes "f \<in> carrier P"
  shows "(lt f) n  = (if (n = degree f) then (f (degree f)) else \<zero>)"
proof-
  have "coeff P (lt f) n  = (if (n = degree f) then (f (degree f)) else \<zero>)"
    using assms lt_coeffs0 by blast
  then have "cf (lt f) n  = (if (n = degree f) then (f (degree f)) else \<zero>)"
     by auto 
  then show ?thesis 
    by (simp add: assms cf_f lt_closed)
qed

lemma lt_coeff_above:
  assumes "f \<in> carrier P"
  assumes "n > degree f"
  shows "lt f n = \<zero>"
proof-
  have "coeff P  (lt f) n = (if (n = degree f) then (f (degree f)) else \<zero>)"
    using lt_coeffs0 assms by auto 
  then have "coeff P  (lt f) n = \<zero>"
    using assms(2) by auto 
  then have "cf (lt f) n = \<zero>"
    by auto 
  then show ?thesis
    using cf_f assms lt_closed by simp
qed

(*leading term of f has the same degree as f*)
lemma degree_lt[simp]:
  assumes "f \<in> carrier P"
  shows "degree (lt f) = degree f"
  using UP_ring.deg_monom 
  by (metis UP_ring.deg_zero_impl_monom UP_ring.lcoeff_closed
      UP_ring.lcoeff_nonzero_deg P_def P_is_UP_ring assms cf_f  leading_term_def)

(*f minus its leading term has smaller degree*)
lemma lt_decomp0:
  assumes "f \<in> carrier P"
  assumes "degree f = Suc n"
  shows "degree (f \<ominus>\<^bsub>P\<^esub> (lt f)) \<le> n"
proof(rule UP_ring.deg_aboveI)
  show C0: "UP_ring R" 
    by simp
  show C1: "f \<ominus>\<^bsub>P\<^esub> lt f \<in> carrier (UP R)"
    using assms lt_closed 
    by (simp add: UP_ring.UP_ring P_def ring.ring_simprules(4))
  show C2: "\<And>m. n < m \<Longrightarrow> coeff (UP R) (f \<ominus>\<^bsub>P\<^esub> lt f) m = \<zero>"
  proof-
    fix m
    assume A: "n<m"
    show "coeff (UP R) (f \<ominus>\<^bsub>P\<^esub> lt f) m = \<zero>"
      apply(auto  simp: P_def)
    proof(cases " m = Suc n")
      case True
      have B: "f m \<in> carrier R" 
        using UP.coeff_closed P_def assms(1) cf_f by fastforce
      have "m = degree f"
        using True by (simp add: assms(2))
      then have "f m = (lt f) m" 
        using lt_coeffs assms(1) by auto 
      then have "(f m) \<ominus>\<^bsub>R\<^esub>( lt f) m = \<zero>"
        using B UP_ring_def P_is_UP_ring 
          B R.add.r_inv R.is_abelian_group abelian_group.minus_eq by fastforce
      then have "(f \<ominus>\<^bsub>UP R\<^esub> lt f) m = \<zero>"
        using  UP_ring.coeff_minus coeff_simp1 
        by (metis C1 P_def P_is_UP_ring assms(1) lt_closed)
      then show  "coeff (UP R) (f \<ominus>\<^bsub>UP R\<^esub> lt f) m = \<zero>"
        using coeff_simp1 
        using C1 P_def by auto
    next
      case False
      have D0: "m > degree f" using False 
        using A assms(2) by linarith
       have B: "f m \<in> carrier R" 
        using UP.coeff_closed P_def assms(1)  cf_f by fastforce
      have "f m = (lt f) m" 
      proof-
        have "coeff (UP R) f m = \<zero>" 
          using D0 
            P_is_UP_ring assms(1) UP_ring.deg_aboveD[of R f m]  
          by (simp add: P_def)
        then have 0: "f m = \<zero>" 
          using assms coeff_simp1 by auto 
        have "(lt f) m = \<zero>" 
          using D0 assms(1) lt_coeff_above by auto  
        then show ?thesis using 0 by auto 
      then have "(f m) \<ominus>\<^bsub>R\<^esub>( lt f) m = \<zero>"
        using B UP_ring_def P_is_UP_ring 
        by (simp add: R.add.r_inv R.is_abelian_group abelian_group.minus_eq)
      then have "(f \<ominus>\<^bsub>UP R\<^esub> lt f) m = \<zero>"
        using  UP_ring.coeff_minus coeff_simp1 
        by (metis C1 P_def P_is_UP_ring assms(1) lt_closed)
    qed
      then show "coeff (UP R) (f \<ominus>\<^bsub>UP R\<^esub> lt f) m = \<zero>" 
        using coeff_simp1  C1 P_def 
        by (metis B D0 R.is_abelian_group UP_cring_axioms UP_cring_def abelian_group.minus_eq 
            assms(1) coeff_minus cring.cring_simprules(22) cring.cring_simprules(8) 
            lt_coeff_above lt_closed)
    qed
  qed
qed

lemma lt_decomp:
  assumes "f \<in> carrier P"
  assumes "degree f >(0::nat)"
  obtains g where "g \<in> carrier P \<and> f = g \<oplus>\<^bsub>P\<^esub> (lt f) \<and> degree g < degree f"
proof-
  obtain k where k_def: "Suc k = degree f" 
    using assms  by (metis gr0_implies_Suc)
  obtain g where g_def: "g = (f \<ominus>\<^bsub>P\<^esub> (lt f))" 
    by simp
  have 0:  "degree g \<le> k"
    using assms lt_decomp0 k_def g_def by auto  
  have 1: "g \<in> carrier P" 
    using assms g_def lt_closed 
    by (simp add: UP_ring.UP_ring P_def ring.ring_simprules(4))
  have 2: "f = g \<oplus>\<^bsub>P\<^esub> (lt f)" 
  proof-
    have P0: "ring P" 
      using P_is_UP_ring UP_ring.UP_ring P_def UP_ring 
      by linarith 
    have P1: " g \<oplus>\<^bsub>P\<^esub> (lt f) = (f \<ominus>\<^bsub>P\<^esub> (lt f)) \<oplus>\<^bsub>P\<^esub> (lt f)" 
      using g_def by auto 
    have P2: " g \<oplus>\<^bsub>P\<^esub> (lt f) = (f \<oplus>\<^bsub>P\<^esub> ((\<ominus>\<^bsub>P\<^esub> (lt f)) \<oplus>\<^bsub>P\<^esub> (lt f)))"    
      by (simp add: P0 a_minus_def assms(1) g_def lt_closed ring.ring_simprules(3)
          ring.ring_simprules(7))
    then show ?thesis 
      using assms(1) lt_closed[of f] 1 P0 
      by (metis (no_types, lifting) ring.ring_simprules(10) 
          ring.ring_simprules(18) ring.ring_simprules(3) ring.ring_simprules(7))
  qed
  show ?thesis 
    using 0 1 2 k_def  that by fastforce
qed

(*leading term of a sum*)
lemma coeff_of_sum_diff_degree0:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "degree q < n"
  shows "(p \<oplus>\<^bsub>P\<^esub> q) n = p n"
proof-
  have 0:"q n = \<zero>"
    using assms  P_def  UP_cring_axioms coeff_simp1 deg_aboveD by fastforce
  have 1:"(p \<oplus>\<^bsub>P\<^esub> q) n = (p n) \<oplus> (q n)" 
    using P_def UP_a_closed assms(1) assms(2) coeff_add coeff_simp1 by auto
  show ?thesis using 0 1 
    by (simp add: assms(1))
qed

lemma coeff_of_sum_diff_degree1:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "degree q < degree p"
  shows "(p \<oplus>\<^bsub>P\<^esub> q) (degree p) = p (degree p)"
  using assms(1) assms(2) assms(3) coeff_of_sum_diff_degree0 by blast

lemma degree_of_sum_diff_degree:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "degree q < degree p"
  shows "degree (p \<oplus>\<^bsub>P\<^esub> q) = degree p" 
proof-
  have 0: "degree (p \<oplus>\<^bsub>P\<^esub> q) \<le> degree p" using assms 
    by (metis P.add.m_comm 
        deg_add dual_order.strict_implies_order max_def)
  have 1: "degree (p \<oplus>\<^bsub>P\<^esub> q) \<ge> degree p"
    using P_def UP_a_closed assms(1) assms(2) assms(3) coeff_of_sum_diff_degree1 
      coeff_simp1 deg_belowI lcoeff_nonzero_deg by auto
  then show ?thesis 
    by (simp add: "0" eq_iff)
qed

lemma degree_of_difference_diff_degree:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "degree q < degree p"
  shows "degree (p \<ominus>\<^bsub>P\<^esub> q) = degree p" 
proof-
  have A: "(p \<ominus>\<^bsub>P\<^esub> q) = p \<oplus>\<^bsub>P\<^esub> (\<ominus>\<^bsub>P\<^esub> q)" 
    by (simp add: P.minus_eq)
  have "degree (\<ominus>\<^bsub>P\<^esub> q) = degree q " 
    by (simp add: assms(2))
  then show ?thesis 
    using assms A 
    by (simp add: degree_of_sum_diff_degree)
qed


lemma lt_of_sum_diff_degree:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "degree p > degree q"
  shows "lt (p \<oplus>\<^bsub>P\<^esub> q) = lt p"
  unfolding leading_term_def 
  using assms(1) assms(2) assms(3) coeff_of_sum_diff_degree1 degree_of_sum_diff_degree 
  by presburger

(*leading term of a monomial*)

lemma lt_monom:
  assumes "a \<in> carrier R"
  assumes "f = monom P a n"
  shows "lt f = f"
  unfolding leading_term_def
  by (metis P_def UP_ring.deg_monom UP_ring.monom_closed UP_ring.monom_zero
      UP_ring_axioms assms(1) assms(2) coeff_monom coeff_simp1)

lemma lt_monom_simp[simp]:
  assumes "a \<in> carrier R"
  shows "lt (monom P a n) = monom P a n"
  using assms lt_monom by auto

lemma lt_inv_simp[simp]:
  assumes "f \<in> carrier P"
  shows "lt (lt f) = lt f"
  by (metis assms degree_lt leading_term_def lt_coeffs)

lemma lt_deg_0[simp]:
  assumes "p \<in> carrier P"
  assumes "degree p = 0"
  shows "lt p = p"
  using lt_monom assms 
  using P_def  UP_cring_axioms coeff_simp1 deg_zero_impl_monom leading_term_def 
  by (simp add: leading_term_def)

end 

(*lead coefficient function*)

definition leading_coefficient where 
"leading_coefficient R p = p (deg R p)"

abbreviation(in UP_domain) lc where
"lc \<equiv> leading_coefficient R"

lemma(in UP_domain) lc_lt:
"lt p = monom P (lc p) (degree p)"
  by (simp add: P_def leading_coefficient_def leading_term_def)

lemma(in UP_domain) lc_closed:
  assumes "f \<in> carrier P"
  shows "lc f \<in> carrier R"
  by (metis P_def assms coeff_simp1 lcoeff_closed leading_coefficient_def)

lemma(in UP_domain) lc_monom[simp]:
  assumes "a \<in> carrier R"
  shows "lc (monom P a n) = a"
  unfolding leading_coefficient_def 
  by (metis P_def UP_ring.monom_closed UP_ring_axioms assms coeff_monom coeff_simp1 deg_monom)

(*monomial predicate*)
definition is_monom_poly where
"is_monom_poly R = (\<lambda>f. f \<in> carrier (UP R) \<and> f = leading_term R f)"

context UP_domain 
begin

abbreviation is_monom where
"is_monom \<equiv> is_monom_poly R"

lemma is_monom_prop0:
  assumes "a \<in> carrier R"
  assumes "p = monom P a n"
  shows "is_monom p"
  using assms(1) assms(2) is_monom_poly_def lt_monom 
  by (metis P_def UP_ring.monom_closed UP_ring_axioms)

lemma is_monom_id:
  assumes "is_monom f"
  shows "f = monom P (lc f) (degree f)"
proof-
  obtain a where "a = f (degree f)"
    by simp
  have "f \<in> carrier P" 
    using assms unfolding is_monom_poly_def P_def by auto  
  then have 0: "a \<in> carrier R"
    by (simp add: \<open>a = f (degree f)\<close>)
  have 1: "f = monom P a (degree f)"
    by (metis P_def \<open>a = f (degree f)\<close> assms is_monom_poly_def leading_term_def)
  then have "a = lc f" 
    by (simp add: \<open>a = f (degree f)\<close> leading_coefficient_def)
  then show ?thesis
    using 1 by blast
qed


(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)

lemma poly_induct:
  assumes "p \<in> carrier P"
  assumes Deg_0: "\<And>p. p \<in> carrier P \<Longrightarrow> degree p = 0 \<Longrightarrow> Q p"
  assumes IH: "\<And>p. (\<And>q. q \<in> carrier P \<Longrightarrow> degree q < degree p \<Longrightarrow> Q q) \<Longrightarrow> p \<in> carrier P \<Longrightarrow> degree p > 0 \<Longrightarrow> Q p"
  shows "Q p"
proof-
  have "\<And>n. \<And>p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> Q p"
  proof-
    fix n
    show "\<And>p. p \<in> carrier P \<Longrightarrow>  degree p \<le> n \<Longrightarrow> Q p"
    proof(induction n)
      case 0
      then show ?case 
        using Deg_0  by simp
    next
      case (Suc n)
      fix n 
      assume I:  "\<And>p. p \<in> carrier P \<Longrightarrow>  degree p \<le> n \<Longrightarrow> Q p"
      show  "\<And>p. p \<in> carrier P \<Longrightarrow>  degree p \<le> (Suc n) \<Longrightarrow> Q p"
      proof-
        fix p
        assume A0: " p \<in> carrier P "
        assume A1: "degree p \<le>Suc n"
        show "Q p"
        proof(cases "degree p < Suc n")
          case True
          then show ?thesis 
            using I  A0 by auto
        next
          case False
          then have D: "degree p = Suc n" 
            by (simp add: A1 nat_less_le)
          then  have "(\<And>q. q \<in> carrier P \<Longrightarrow> degree q < degree p \<Longrightarrow> Q q)" 
              using I   by simp
            then show "Q p" 
                  using IH D A0 A1 Deg_0 by blast
        qed
      qed
    qed
  qed
  then show ?thesis using assms by blast 
qed



(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)


lemma is_monom_prop1:
  assumes "p \<in> carrier P"
  shows "is_monom (lt p)"
  by (metis P_def assms is_monom_poly_def lt_closed lt_inv_simp)

lemma is_monom_mult:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "is_monom p"
  assumes "is_monom q"
  shows "is_monom (p \<otimes>\<^bsub>P\<^esub> q)"
proof-
  have "p \<otimes>\<^bsub>P\<^esub> q = (lt p) \<otimes>\<^bsub>P\<^esub> (lt q)"
    using assms(3) assms(4) is_monom_poly_def by metis
  then have "p \<otimes>\<^bsub>P\<^esub> q = monom P ((p (degree p)) \<otimes> (q (degree q))) (degree p + degree q)"
    unfolding leading_term_def using monom_mult
    using P_def cfs_closed assms(1) assms(2) by auto
  then show ?thesis 
    by (metis P_def cfs_closed R.m_closed UP_domain.is_monom_prop0 UP_domain_axioms assms(1) assms(2))
qed

lemma lt_prod_lt[simp]:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "lt ((lt p) \<otimes>\<^bsub>P\<^esub> (lt q)) = (lt p) \<otimes>\<^bsub>P\<^esub> (lt q)"
proof-
  have "is_monom ((lt p) \<otimes>\<^bsub>P\<^esub> (lt q))"
    by (simp add: assms(1) assms(2) is_monom_mult is_monom_prop1 lt_closed)
  then show ?thesis 
    by (simp add: is_monom_poly_def)
qed

end

(*Relation for functions which are equal on the carrier*)

definition equal_on_carrier where
"equal_on_carrier R f g = (\<forall>x. x \<in> carrier R \<longrightarrow> f x = g x)"

abbreviation(in UP_domain) eq_on_car (infixl "\<sim>" 70) where
"eq_on_car \<equiv> equal_on_carrier R "

lemma(in UP_domain) eq_on_car_simp:
  assumes "f \<sim> g"
  assumes "x \<in> carrier R"
  shows "f x = g x"
  using equal_on_carrier_def assms 
  by (simp add: equal_on_carrier_def)

definition function_sum where
"function_sum R f g = (\<lambda>x. (f x) \<oplus>\<^bsub>R\<^esub> (g x))"

abbreviation(in UP_domain) fun_sum where
"fun_sum \<equiv> function_sum R"

definition function_prod where
"function_prod R f g = (\<lambda>x. (f x) \<otimes>\<^bsub>R\<^esub> (g x))"

abbreviation(in UP_domain) fun_prod where
"fun_prod \<equiv> function_prod R"

(*Turning a polynomial into a function on R*)
definition function_of  where
"function_of S f  = (\<lambda>s .eval S S (\<lambda>x. x) s f)"

context UP_domain 
begin
abbreviation fun_of where
"fun_of f \<equiv> function_of R f"

(*Explicit formula for evaluating a polynomial function*)


lemma fun_of_formula:
  assumes "f \<in> carrier P"
  assumes "x \<in> carrier R"
  shows "fun_of f x = (\<Oplus>i \<in> {..degree f}. (cf f i) \<otimes> x [^] i)"
proof-
  have "f \<in> carrier (UP R)"
    using assms P_def by auto 
  then  have "eval R R (\<lambda>x. x) x f =  (\<Oplus>\<^bsub>R\<^esub>i\<in>{..deg R f}. (\<lambda>x. x) (coeff (UP R) f i) \<otimes>\<^bsub>R\<^esub> x [^]\<^bsub>R\<^esub> i)"
    apply(simp add:UnivPoly.eval_def) done
  then have "fun_of f x = (\<Oplus>\<^bsub>R\<^esub>i\<in>{..deg R f}. (\<lambda>x. x) (coeff (UP R) f i) \<otimes>\<^bsub>R\<^esub> x [^]\<^bsub>R\<^esub> i)"
    using function_of_def assms 
    by (simp add: function_of_def)
  then show ?thesis  by (simp add: P_def)
qed

lemma fun_of_formula':
  assumes "f \<in> carrier P"
  assumes "x \<in> carrier R"
  shows "fun_of f x = (\<Oplus>i \<in> {..degree f}. (f i) \<otimes> x [^] i)"
proof-
  have 0: "fun_of f x = (\<Oplus>i \<in> {..degree f}. (cf f i) \<otimes> x [^] i)"
    using fun_of_formula assms by auto 
  have 1: "\<And>i. f i= cf f i" using cf_f assms(1) by auto 
  have "(\<Oplus>i \<in> {..degree f}. (f i) \<otimes> x [^] i) = (\<Oplus>i \<in> {..degree f}. (cf f i) \<otimes> x [^] i)"
    apply(simp add: 1)
    done
  then show ?thesis using 0 by auto 
qed

lemma eval_ring_hom:
  assumes "a \<in> carrier R"
  shows "eval R R (\<lambda>x. x) a \<in> ring_hom P R"
proof-
  have "(\<lambda>x. x) \<in> ring_hom R R"
    apply(rule ring_hom_memI)
    apply auto done
  then have "UP_pre_univ_prop R R (\<lambda>x. x)"
    using R_cring UP_pre_univ_propI by blast
  then show ?thesis 
    by (simp add: P_def UP_pre_univ_prop.eval_ring_hom assms)
qed

lemma fun_of_plus[simp]:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "x \<in> carrier R"
  shows "fun_of (f \<oplus>\<^bsub>P\<^esub> g) x = (fun_of f x) \<oplus> (fun_of g x)"
  unfolding function_of_def 
  using assms  eval_ring_hom[of x] ring_hom_add[of "eval R R (\<lambda>x. x) x" P R f g]
  by auto 

lemma fun_of_mult[simp]:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "x \<in> carrier R"
  shows "fun_of (f \<otimes>\<^bsub>P\<^esub> g) x = (fun_of f x) \<otimes> (fun_of g x)"
  unfolding function_of_def 
  using assms  eval_ring_hom[of x] ring_hom_mult[of "eval R R (\<lambda>x. x) x" P R f g]
  by auto 


(*technical lemmas for reasoning about fun_of*)
lemma id_is_hom:
"ring_hom_cring R R (\<lambda>x. x)"
proof(rule ring_hom_cringI)
  show "cring R" 
    by (simp add: R_cring )
  show "cring R" 
    by (simp add: R_cring ) 
  show "(\<lambda>x. x) \<in> ring_hom R R"
    unfolding ring_hom_def
    apply(auto)
    done
qed

lemma UP_pre_univ_prop_fact:
"UP_pre_univ_prop R R (\<lambda>x. x)"
  unfolding UP_pre_univ_prop_def
  by (simp add: UP_cring_def R_cring  id_is_hom)

lemma fun_of_closed[simp]:
  assumes "p \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "fun_of p a \<in> carrier R"
  unfolding function_of_def
  proof-
    have "(eval R R (\<lambda>x. x)) a \<in> (ring_hom P R)"
      using UP_pre_univ_prop_fact UP_pre_univ_prop.eval_ring_hom[of R R "(\<lambda>x. x)" a] 
      using P_def assms(2) by blast
    then show "eval R R (\<lambda>x. x) a p \<in> carrier R"
      using assms(1) ring_hom_closed by fastforce
  qed

end

lemma fun_of_closed_UP_domain[simp]:
  assumes "UP_domain R" 
  assumes "p \<in> carrier (UP R)"
  assumes "a \<in> carrier R"
  shows "function_of R p a \<in> carrier R"
  by (simp add: UP_domain.fun_of_closed assms(1) assms(2) assms(3))

context UP_domain
begin
(*P addition commutes with evaluation addition*)
lemma fun_of_fun_sum:
  assumes "f \<in> carrier P"
  assumes "g \<in> carrier P"
  assumes "h = f \<oplus>\<^bsub>P\<^esub> g"
  shows "fun_sum (fun_of f) (fun_of g) \<sim> fun_of h" 
  unfolding equal_on_carrier_def
  apply(auto)
proof-
  fix x
  assume A: "x \<in> carrier R"
  show "fun_sum (fun_of f) (fun_of g) x = fun_of h x "
    unfolding function_sum_def
    unfolding function_of_def
  proof-
    have "(eval R R (\<lambda>x. x)) x \<in> (ring_hom P R)"
      using UP_pre_univ_prop_fact A UP_pre_univ_prop.eval_ring_hom[of R R "(\<lambda>x. x)" x]  P_def by auto   
    then show "eval R R (\<lambda>x. x) x f \<oplus> eval R R (\<lambda>x. x) x g = eval R R (\<lambda>x. x) x h "
      using assms ring_hom_add by fastforce
  qed
qed

(*explicit description of monomial functions*)
lemma fun_of_monom:
  assumes "c \<in> carrier R"
  assumes "c \<noteq>\<zero>"
  assumes "x \<in> carrier R"
  shows "fun_of (monom P c (n::nat)) x = c \<otimes> x [^] n"
proof-
  have 0: "(monom P c n) \<in> carrier P "
    using P_def UP_ring.intro UP_ring.monom_closed R_cring  assms cring_def by fastforce
  then have 1: "fun_of (monom P c n) x =  (\<Oplus>i \<in> {..degree (monom P c n) }. (cf (monom P c n)  i) \<otimes> x [^] i)"
    using assms fun_of_formula by simp 
  have 2: "\<And>i. (cf (monom P c n)  i) = (if i=n then c else \<zero>)" 
  proof-
    fix i
    show "(cf (monom P c n)  i) = (if i=n then c else \<zero>)" 
    proof-
      have 0: "cf (monom P c n) = (monom P c n)" 
        using 0 cf_f by auto 
      have "monom P = (\<lambda>a\<in>(carrier R). \<lambda>n i. if i = n then a else \<zero>)"
        by (simp add: UP_def P_def)
      then have "monom P c = (\<lambda>n i. if i = n then c else \<zero>)"
        using assms by auto 
      then show ?thesis 
        using 0 by auto 
    qed
  qed
  have 3: "degree (monom P c n) = n" 
    using assms P_is_UP_ring P_def by (simp add: UP_ring.deg_monom)
  then have 4: "fun_of (monom P c n) x =  (\<Oplus>i \<in> {..n}. (cf (monom P c n)  i) \<otimes> x [^] i)"
    using 1 by auto
  then have 5: "fun_of (monom P c n) x =  (\<Oplus>i \<in> {..n}. (if i=n then c else \<zero>) \<otimes> x [^] i)"
    using 2 by auto 
  show ?thesis 
  proof(cases "n=0")
    case True
    then have A0: "fun_of (monom P c n) x = (\<Oplus>i \<in> {(0::nat)}. (if i=n then c else \<zero>) \<otimes> x [^] i)"
      using 5  by simp
    have A1:"abelian_monoid R" 
      using R_cring  abelian_group_def cring_def ring_def by blast
    have "\<And>i.( (cf (monom P c n)  i) \<otimes> x [^] i) \<in> carrier R"
    proof-
      fix i
      have P0: "(cf (monom P c n)  i) \<in> carrier R" 
        using assms  "2" R_cring  cring.cring_simprules(2) by auto
      have P1: " (x [^] i) \<in> carrier R" 
        using assms R_cring  monoid.nat_pow_closed  by (metis cring.axioms(1) ring_def)
      show "( (cf (monom P c n)  i) \<otimes> x [^] i) \<in> carrier R"
        using assms P0 P1 R_cring    by (simp add: cring.cring_simprules(5))
    qed
    then have A2: "(\<lambda>i. (cf (monom P c n)  i) \<otimes> x [^] i) \<in> ({0::nat} \<rightarrow> carrier R)" 
      by blast
    have A3: "(\<Oplus>i \<in> {0}.  (cf (monom P c n) i) \<otimes> x [^] i) = finsum R (\<lambda>i. (cf (monom P c n)  i) \<otimes> x [^] i) {..0}"
      by simp
    have "finsum R (\<lambda>i. (cf (monom P c n)  i) \<otimes> x [^] i) {..0} = (\<lambda>i. (cf (monom P c n)  i) \<otimes> x [^] i) 0"
      using A1 A2 abelian_monoid.finsum_0  by blast
    then have A4: "(\<Oplus>i \<in> {0}.  (cf (monom P c n) i) \<otimes> x [^] i) = (\<lambda>i. (cf (monom P c n)  i) \<otimes> x [^] i) 0"
      using A3  True by auto
    have "(\<lambda>i. (cf (monom P c n)  i) \<otimes> x [^] i) (0::nat) = (cf (monom P c n)  (0::nat)) \<otimes> x [^] (0::nat)"
      by auto
    then have "(\<Oplus>i \<in> {0::nat}.  (cf (monom P c n) i) \<otimes> x [^] i) =(cf (monom P c n) ( 0::nat)) \<otimes> x [^] (0::nat)"
      using A4  by blast
    then show ?thesis using A0  "2" True by auto
  next
    case False
    then obtain k where k_def: "n = Suc k" 
      by (meson lessI less_Suc_eq_0_disj)
    have A0: "abelian_monoid R" 
      using R_cring  abelian_group_def cring_def ring_def by auto
    have A1: "(\<lambda>i. (if i=n then c else \<zero>) \<otimes> x [^] i) \<in> ({..Suc k} \<rightarrow> (carrier R))"
    proof 
      fix a
      assume "a \<in> {..Suc k}"  
      show "(if a = n then c else \<zero>) \<otimes> x [^] a \<in> carrier R"
      proof-
        have P0: "(if a = n then c else \<zero>) \<in> carrier R"
          by (simp add: A0 abelian_monoid.zero_closed assms(1))
        have P1: " x [^] a \<in> carrier R" 
          by (meson R_cring assms(3) cring_def monoid.nat_pow_closed ring_def)
        show ?thesis using P0 P1 
          by (simp add: R_cring cring.cring_simprules(5))
      qed
    qed
    obtain g where g_def: "g = (\<lambda>i. (if i=n then c else \<zero>) \<otimes> x [^] i)"
      by simp
    have "g \<in>  ({..Suc k} \<rightarrow> (carrier R))" 
      using A1 g_def by simp
    then have A2:"(\<Oplus>(i::nat) \<in> {..Suc k}. g i) = (g (Suc k)) \<oplus>(\<Oplus>(i::nat) \<in> {..k}. g i) "
      using A0 abelian_monoid.finsum_Suc by auto  
    have A3:"(\<Oplus>(i::nat) \<in> {..k}. g i) = (\<Oplus>(i::nat) \<in> {..k}. \<zero> )"
    proof-
      have "\<And>(i::nat). i \<in> {..k} \<Longrightarrow> g i=\<zero>"
      proof-
        fix i::nat
        assume " i \<in> {..k} "
        then have I: "i \<noteq> n" 
          using k_def by auto 
        show "g i=\<zero>"
        proof-
          have B0: "g i= \<zero>  \<otimes> x [^] i" 
            using g_def I by simp
          have B1: "x [^] (i::nat) \<in> carrier R" 
            using R_cring assms(3)   by (simp add: monoid.nat_pow_closed cring_def ring_def)
          then show " g i=\<zero>" 
            using B0 B1  by (simp add: R_cring cring.cring_simprules(26)) 
        qed
      qed
      then show ?thesis 
        using  A0 abelian_monoid.finsum_cong'[of R "{..k}" "{..k}" "(\<lambda>i. \<zero>)" g ]    
        by (simp add: abelian_monoid.zero_closed finsum_def)
    qed
    then have "(\<Oplus>(i::nat) \<in> {..Suc k}. g i) = (g (Suc k)) \<oplus> \<zero>" 
      using A0 A2 abelian_monoid.finsum_zero[of R "{..k}"] by auto  
    then have "(\<Oplus>(i::nat) \<in> {..Suc k}. g i) = (g (Suc k))" 
      by (metis A0 PiE Suc_le_eq \<open>g \<in> {..Suc k} \<rightarrow> carrier R\<close> abelian_monoid.r_zero atMost_iff lessI)
    then show ?thesis using 5 k_def g_def  by simp
  qed
qed


lemma degree_0_imp_constant0:
  assumes "f \<in> carrier (UP R)"
  assumes "degree f = 0"
  obtains c where "c \<in> carrier R" and  "\<And>x.  x \<in> carrier R \<Longrightarrow> (fun_of f) x = c"
proof-
  obtain c where c_def: "c = f 0"
    by simp
  have 0: "c \<in> carrier R" using c_def assms(1) 
    using UP_domain.cfs_closed  UP_domain_axioms by blast
  have 1:  "\<And>x.  x \<in> carrier R \<Longrightarrow> (fun_of f) x = c"
  proof-
    fix x
    assume A: "x \<in> carrier R"
    have ab: "abelian_monoid R" 
      by (simp add: R.abelian_monoid_axioms)
    have d: "(\<lambda>i. f i \<otimes> x [^] i) \<in> {0::nat} \<rightarrow> carrier R "
    proof
      fix a
      assume "a \<in> {0::nat}"
      show "((f a) \<otimes> (x[^] a)) \<in> carrier R"
        using "0" A \<open>a \<in> {0}\<close> c_def monom_term_car by blast      
    qed
    have "(fun_of f) x = (\<Oplus>i\<in>{..degree f}. f i \<otimes> x [^] i)"
      using fun_of_formula' assms A  P_def by blast
    then have P0: "(fun_of f) x = (\<Oplus>i\<in>{..0}. f i \<otimes> x [^] i)"
      by(simp add: assms)
    have "(\<Oplus>i\<in>{..0}. f i \<otimes> x [^] i) =  f 0 \<otimes> x [^] (0::nat)" 
      using ab d abelian_monoid.finsum_0[of R "(\<lambda>i::nat. f i \<otimes> x [^] i)"] by auto  
    then have "(fun_of f) x = f 0 \<otimes> x [^] (0::nat)" 
      using P0   by simp
    then have P1: "(fun_of f) x = c\<otimes> x [^] (0::nat)" 
      by(simp add: c_def)
    then have "(fun_of f) x = c\<otimes> \<one>" 
    proof-
      have "\<one> =  x [^] (0::nat)"  
        using A   by (simp add: monoid.nat_pow_0 cring_def ring_def)
      then show ?thesis using P1  by simp
    qed
    then show "(fun_of f) x = c" 
      by (simp add: "0")
  qed
  then show ?thesis 
    using 0 1 that by auto
qed


end


(**************************************************************************************************)
(**************************************************************************************************)
(**********************************    Polynomial Substitution   **********************************)
(**************************************************************************************************)
(**************************************************************************************************)

(*Inclusion of R into P*)

definition to_polynomial where
"to_polynomial R  =  (\<lambda>a. monom (UP R) a 0)"

abbreviation(in UP_ring) to_poly where
"to_poly  \<equiv> to_polynomial R "

lemma to_poly_mult_simp[simp]:
  assumes "UP_domain R"
  assumes "b \<in> carrier R"
  assumes "f \<in> carrier (UP R)"
  shows "(to_polynomial R b) \<otimes>\<^bsub>UP R\<^esub> f = b \<odot>\<^bsub>UP R\<^esub> f"
        "f  \<otimes>\<^bsub>UP R\<^esub> (to_polynomial R b) = b \<odot>\<^bsub>UP R\<^esub> f"   
  unfolding to_polynomial_def
  using assms 
  apply (simp add: UP_domain.P_is_UP_ring UP_ring.monom_mult_is_smult)
proof-
  have "monom (UP R) b 0 \<otimes>\<^bsub>UP R\<^esub> f = f \<otimes>\<^bsub>UP R\<^esub> monom (UP R) b 0"
    by (meson UP_cring.UP_m_comm UP_cring.intro UP_domain.P_is_UP_ring 
        UP_domain_def UP_ring.monom_closed assms(1) assms(2) assms(3) domain_def)
  then show "f \<otimes>\<^bsub>UP R\<^esub> monom (UP R) b 0 = b \<odot>\<^bsub>UP R\<^esub> f"
    using UP_domain.P_is_UP_ring UP_ring.monom_mult_is_smult assms(1) assms(2) assms(3) by fastforce
qed

(**************************************************************************************************)
context UP_domain
begin 

lemma fun_of_to_poly[simp]:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "fun_of (to_poly a) b = a"
  unfolding function_of_def to_polynomial_def 
  by (simp add: UP_pre_univ_prop.eval_const UP_pre_univ_prop_fact assms(1) assms(2))

lemma to_poly_inverse:
  assumes "f \<in> carrier P"
  assumes "degree f = 0"
  shows "f = to_poly (f 0)"
  using P_def assms(1) assms(2) coeff_simp1 deg_zero_impl_monom 
  by (simp add: to_polynomial_def)

lemma to_poly_is_poly:
  assumes "a \<in> carrier R"
  shows "to_poly a \<in> carrier P"
  by (metis P_def assms monom_closed to_polynomial_def)

lemma degree_to_poly[simp]:
  assumes "a \<in> carrier R"
  shows "degree (to_poly a) = 0"
  by (metis P_def assms deg_const to_polynomial_def)

lemma(in UP_domain) to_poly_is_ring_hom:
"to_poly \<in> ring_hom R P"
  unfolding to_polynomial_def
  unfolding P_def
  using UP_ring.const_ring_hom[of R]
  UP_ring_axioms by simp 

lemma(in UP_domain) to_poly_add[simp]:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "to_poly (a \<oplus> b) = to_poly a \<oplus>\<^bsub>P\<^esub> to_poly b"
  by (simp add: assms(1) assms(2) ring_hom_add to_poly_is_ring_hom)

lemma(in UP_domain) to_poly_mult[simp]:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "to_poly (a \<otimes> b) = to_poly a \<otimes>\<^bsub>P\<^esub> to_poly b"
  by (simp add: assms(1) assms(2) ring_hom_mult to_poly_is_ring_hom)

lemma(in UP_domain) to_poly_minus[simp]:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "to_poly (a \<ominus> b) = to_poly a \<ominus>\<^bsub>P\<^esub> to_poly b"
  by (metis P.minus_eq P_def R.add.inv_closed R.ring_axioms UP_ring.monom_add 
      UP_ring_axioms assms(1) assms(2) monom_a_inv ring.ring_simprules(14) to_polynomial_def)

lemma(in UP_domain) to_poly_ominus[simp]:
  assumes "a \<in> carrier R"
  shows "to_poly (\<ominus> a) =  \<ominus>\<^bsub>P\<^esub> to_poly a"
  by (metis P_def assms monom_a_inv to_polynomial_def)

end
(*Substitution of one polynomial into another*)


definition compose where
"compose R f g = eval R (UP R) (to_polynomial R) g f"

abbreviation(in UP_domain) sub  (infixl "of" 70) where
"sub f g \<equiv> compose R f g"


definition rev_compose  where
"rev_compose R = eval R (UP R) (to_polynomial R)"

abbreviation(in UP_domain) rev_sub  where
"rev_sub \<equiv> rev_compose R"


context UP_domain
begin

lemma(in UP_domain) sub_rev_sub:
"sub f g = rev_sub g f"
  unfolding compose_def rev_compose_def by simp

lemma(in UP_domain) to_poly_UP_pre_univ_prop:
"UP_pre_univ_prop R P to_poly"
proof 
  show "to_poly \<in> ring_hom R P" 
    by (simp add: to_poly_is_ring_hom)
qed

lemma rev_sub_is_hom:
  assumes "g \<in> carrier P"
  shows "rev_sub g \<in> ring_hom P P"
  unfolding rev_compose_def
  using to_poly_UP_pre_univ_prop assms(1) UP_pre_univ_prop.eval_ring_hom[of R P to_poly g] 
  unfolding P_def apply auto 
  done

lemma rev_sub_closed:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "rev_sub q p \<in> carrier P"
  using rev_sub_is_hom[of q] assms ring_hom_closed[of "rev_sub q" P P p] by auto  

lemma sub_closed[simp]:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "sub q p \<in> carrier P"
  by (simp add: assms(1) assms(2) rev_sub_closed sub_rev_sub)

lemma rev_sub_add:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "h \<in>carrier P"
  shows "rev_sub g (f \<oplus>\<^bsub>P\<^esub> h) = (rev_sub g f) \<oplus>\<^bsub>P\<^esub> (rev_sub g h)"
  using rev_sub_is_hom assms ring_hom_add by fastforce

lemma sub_add: 
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "h \<in>carrier P"
  shows "((f \<oplus>\<^bsub>P\<^esub> h) of g) = ((f of g) \<oplus>\<^bsub>P\<^esub> (h of g))"
  by (simp add: assms(1) assms(2) assms(3) rev_sub_add sub_rev_sub)

lemma rev_sub_mult:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "h \<in>carrier P"
  shows "rev_sub g (f \<otimes>\<^bsub>P\<^esub> h) = (rev_sub g f) \<otimes>\<^bsub>P\<^esub> (rev_sub g h)"
  using rev_sub_is_hom assms ring_hom_mult  by fastforce

lemma sub_mult: 
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "h \<in>carrier P"
  shows "((f \<otimes>\<^bsub>P\<^esub> h) of g) = ((f of g) \<otimes>\<^bsub>P\<^esub> (h of g))"
  by (simp add: assms(1) assms(2) assms(3) rev_sub_mult sub_rev_sub)

(*Subbing into a constant does nothing*)
lemma rev_sub_to_poly:
  assumes "g \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "rev_sub g (to_poly a) = to_poly a"
  unfolding to_polynomial_def rev_compose_def
  using to_poly_UP_pre_univ_prop 
  unfolding to_polynomial_def 
     using P_def UP_pre_univ_prop.eval_const assms(1) assms(2) by fastforce

lemma sub_to_poly[simp]:
  assumes "g \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "(to_poly a) of g  = to_poly a"
  by (simp add: assms(1) assms(2) rev_sub_to_poly sub_rev_sub)

lemma sub_const[simp]:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "degree f = 0"
  shows "f of g = f"
proof-
  obtain a where a_def: "a \<in> carrier R \<and> f = to_poly a"
    using assms(2) assms(3) deg_zero_impl_monom to_polynomial_def 
    by (metis P_def lcoeff_closed)
  then show ?thesis 
    by (simp add: assms(1))
qed

end 
(*Function which truncates a polynomial by removing the leading term*)
definition truncate where
"truncate R f = f \<ominus>\<^bsub>(UP R)\<^esub> (leading_term R f)"


context UP_domain
begin 

abbreviation trunc where
"trunc \<equiv> truncate R"

lemma trunc_simps:
  assumes "f \<in> carrier P"
  shows "f = (trunc f) \<oplus>\<^bsub>P\<^esub> (lt f)"
        "f \<ominus>\<^bsub>P\<^esub> (trunc f) = lt f"   
        "trunc f \<in> carrier P"
  unfolding truncate_def
  apply (metis P.add.inv_solve_right P.minus_closed P_def a_minus_def assms lt_closed)
  apply (metis (no_types, hide_lams) P.add.inv_solve_right 
        P.minus_closed P_def UP_a_comm a_minus_def assms lt_closed)
  using P.minus_closed P_def assms lt_closed by blast



lemma trunc_zero:
  assumes "f \<in> carrier P"
  assumes "degree f = 0"
  shows "trunc f = \<zero>\<^bsub>P\<^esub>"
  unfolding truncate_def 
  using assms lt_deg_0[of f] 
  by (metis P.r_neg P_def a_minus_def)

lemma trunc_degree:
  assumes "f \<in> carrier P"
  assumes "degree f > 0"
  shows "degree (trunc f) < degree f"
  unfolding truncate_def using assms 
  by (metis P.add.inv_solve_right P_def a_minus_def lt_decomp lt_closed)

(**************************************************************************************************)
(**************************************************************************************************)
(**************************  Alternate Polynomial Induction  **************************************)
(**************************************************************************************************)
(**************************************************************************************************)


lemma poly_induct2:
  assumes "p \<in> carrier P"
  assumes Deg_0: "\<And>p. p \<in> carrier P \<Longrightarrow> degree p = 0 \<Longrightarrow> Q p"
  assumes IH: "\<And>p. degree p > 0  \<Longrightarrow> p \<in> carrier P \<Longrightarrow> Q (trunc p)  \<Longrightarrow> Q p"
  shows "Q p"
proof(rule poly_induct)
  show "p \<in> carrier P" 
    by (simp add: assms(1))
  show "\<And>p. p \<in> carrier P \<Longrightarrow> degree p = 0 \<Longrightarrow> Q p" 
      by (simp add: Deg_0)
    show "\<And>p. (\<And>q. q \<in> carrier P \<Longrightarrow> degree q < degree p \<Longrightarrow> Q q) \<Longrightarrow> p \<in> carrier P \<Longrightarrow> 0 < degree p \<Longrightarrow> Q p"
    proof-
      fix p
      assume A0: "(\<And>q. q \<in> carrier P \<Longrightarrow> degree q < degree p \<Longrightarrow> Q q)"
      assume A1: " p \<in> carrier P"
      assume A2: "0 < degree p" 
      show "Q p"
      proof-
        have "degree (trunc p) < degree p"
          by (simp add: A1 A2 trunc_degree)
        have "Q (trunc p)"
          by (simp add: A0 A1 \<open>degree (trunc p) < degree p\<close> trunc_simps(3))
        then show ?thesis 
          by (simp add: A1 A2 IH)
      qed
    qed
qed



(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)


(*leading term is multiplicative*)

lemma lt_id:
  assumes "q \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "a \<noteq>\<zero>"
  assumes "degree q < n"
  assumes "p = q \<oplus>\<^bsub>P\<^esub> (monom P a n)"
  shows "lt p =  (monom P a n)"
proof-
  have 0: "degree  (monom P a n) = n" 
    by (simp add: assms(2) assms(3))
  have 1: "(monom P a n) \<in> carrier P"
    using assms(2) by auto
  have 2: "lt ((monom P a n) \<oplus>\<^bsub>P\<^esub> q) = lt (monom P a n)"
    using assms lt_of_sum_diff_degree[of "(monom P a n)" q] 1  "0" by linarith
  then show ?thesis 
    using UP_a_comm assms(1) assms(2) assms(5) lt_monom by auto
qed

lemma lt_smult:
  assumes "p \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "lt (a \<odot>\<^bsub>P\<^esub>p) = a\<odot>\<^bsub>P\<^esub>(lt p)"
proof(cases "a = \<zero>")
  case True
  then show ?thesis 
    by (metis P_def UP_smult_zero UP_zero_closed assms(1)
        coeff_simp1 deg_nzero_nzero deg_zero_impl_monom leading_term_def lt_closed)
next
  case False
  show ?thesis 
  proof(cases "degree p = 0")
    case True
    then show ?thesis 
      by (simp add: assms(1) assms(2))
  next
    case F: False
    then show ?thesis 
    proof-
      have P0: "(a \<odot>\<^bsub>P\<^esub>p) = (trunc (a \<odot>\<^bsub>P\<^esub>p)) \<oplus>\<^bsub>P\<^esub> lt (a \<odot>\<^bsub>P\<^esub>p)"
        by (simp add: assms(1) assms(2) trunc_simps(1))
      have P1: "(a \<odot>\<^bsub>P\<^esub>p) = (a \<odot>\<^bsub>P\<^esub> ((trunc p) \<oplus>\<^bsub>P\<^esub> lt p))"
        using assms(1) trunc_simps(1) by auto
      have P2: "(a \<odot>\<^bsub>P\<^esub>p) = (a \<odot>\<^bsub>P\<^esub>(trunc p)) \<oplus>\<^bsub>P\<^esub> (a \<odot>\<^bsub>P\<^esub>(lt p))"
        by (simp add: P1 assms(1) assms(2) lt_closed smult_r_distr trunc_simps(3))
      have P3: "degree (lt (a \<odot>\<^bsub>P\<^esub>p)) = degree (a \<odot>\<^bsub>P\<^esub>(lt p))" 
        using assms(1) assms(2)  degree_lt lt_closed by auto
      have P4: "degree (a \<odot>\<^bsub>P\<^esub>(lt p)) = degree p"
        by (metis False P3 assms(1) assms(2) deg_smult  degree_lt smult_closed)
      have P5: "degree (a \<odot>\<^bsub>P\<^esub>(trunc p)) = degree (trunc p)"
        using False by (simp add: assms(1) assms(2)  trunc_simps(3))
      have P6: "degree (a \<odot>\<^bsub>P\<^esub>(trunc p)) < degree (a \<odot>\<^bsub>P\<^esub>(lt p))"
        using F P4 P5 P_def UP_domain.trunc_degree UP_domain_axioms assms(1) by auto
      have  P7: "(a \<odot>\<^bsub>P\<^esub>(lt p)) = monom P (a \<otimes> (p (degree p))) (degree p)" 
        unfolding leading_term_def 
        using P_def cfs_closed assms(1) assms(2) monom_mult_smult by auto
      have P8: "(a \<otimes> (p (degree p))) \<noteq>\<zero>" 
        using F P4 P_def cfs_closed R.integral assms(1) assms(2) coeff_simp1 deg_smult
          deg_zero  lcoeff_nonzero2 lt_closed by fastforce
      show ?thesis 
        using P6 P2 P7 P8 lt_id  P4 cfs_closed assms(1) assms(2) trunc_simps(3) by auto
    qed
  qed
qed

lemma lt_mult:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "lt (p \<otimes>\<^bsub>P\<^esub> q) = (lt p) \<otimes>\<^bsub>P\<^esub> (lt q)"
proof(cases "degree p = 0 \<or> degree q = 0")
  case True
  then show ?thesis
  proof(cases "degree p = 0")
    case True
    then have L: "p = lt p"
      by (simp add: assms(1))
    have LHS: "lt (p \<otimes>\<^bsub>P\<^esub> q) = lt( (p 0) \<odot>\<^bsub>P\<^esub>q)"
      using L True 
      by (metis P_def cfs_closed assms(1) assms(2) coeff_simp1
          deg_zero_impl_monom monom_mult_is_smult)
    have RHS: "(lt p) \<otimes>\<^bsub>P\<^esub> (lt q) = (p 0) \<odot>\<^bsub>P\<^esub> (lt q)"
      using L True cfs_closed assms(1) assms(2) leading_term_def lt_closed monom_mult_is_smult 
      by (metis P_def)
    then show ?thesis using LHS RHS lt_smult  cfs_closed assms(1) assms(2) by auto
  next
    case False
    then have "degree q = 0" 
      using True by linarith
    then show ?thesis 
      by (metis P.m_comm P_def cfs_closed UP_domain.lt_smult UP_domain_axioms assms(1)
          assms(2) leading_term_def lt_deg_0 lt_closed monom_mult_is_smult)
  qed
next
  case False
  then show ?thesis 
  proof-
    obtain q0 where q0_def: "q0 = trunc q" 
      by simp
    obtain p0 where p0_def: "p0 = trunc p" 
      by simp
    have Pq: "degree q0 < degree q"
      using False P_def UP_domain.trunc_degree UP_domain_axioms assms(2) q0_def by blast
    have Pp: "degree p0 < degree p"
      using False P_def UP_domain.trunc_degree UP_domain_axioms assms(1) p0_def by blast
    have "p \<otimes>\<^bsub>P\<^esub> q = (p0 \<oplus>\<^bsub>P\<^esub> lt(p)) \<otimes>\<^bsub>P \<^esub>(q0 \<oplus>\<^bsub>P\<^esub> lt(q))"
      using assms(1) assms(2) p0_def q0_def trunc_simps(1) by auto
    then have P0: "p \<otimes>\<^bsub>P\<^esub> q = ((p0 \<oplus>\<^bsub>P\<^esub> lt(p)) \<otimes>\<^bsub>P \<^esub>q0) \<oplus>\<^bsub>P\<^esub> ((p0 \<oplus>\<^bsub>P\<^esub> lt(p))\<otimes>\<^bsub>P \<^esub>lt(q))"
      by (simp add: P.r_distr assms(1) assms(2) lt_closed p0_def q0_def trunc_simps(3))
    have P1: "degree ((p0 \<oplus>\<^bsub>P\<^esub> lt(p)) \<otimes>\<^bsub>P \<^esub>q0) < degree ((p0 \<oplus>\<^bsub>P\<^esub> lt(p))\<otimes>\<^bsub>P \<^esub>lt(q))"
    proof-
      have LHS: "degree ((p0 \<oplus>\<^bsub>P\<^esub> lt(p)) \<otimes>\<^bsub>P \<^esub>q0) \<le> degree p + degree q0 "
      proof(cases "q0 = \<zero>\<^bsub>P\<^esub>")
        case True
        then show ?thesis 
          using assms(1) p0_def trunc_simps(1) by auto
      next
        case False
        then show ?thesis 
          using assms(1) assms(2) deg_mult_ring  p0_def 
            q0_def trunc_simps(1) trunc_simps(3) by auto
      qed
      have RHS: "degree ((p0 \<oplus>\<^bsub>P\<^esub> lt(p))\<otimes>\<^bsub>P \<^esub>lt(q)) = degree p + degree q"
        by (metis False assms(1) assms(2) deg_mult deg_zero 
            degree_lt lt_closed p0_def trunc_simps(1))
      then show ?thesis using RHS LHS 
        using Pq by linarith
    qed
    then have P2: "lt (p \<otimes>\<^bsub>P\<^esub> q) = lt ((p0 \<oplus>\<^bsub>P\<^esub> lt(p))\<otimes>\<^bsub>P \<^esub>lt(q))"
      using P0 P1  
      by (simp add: UP_a_comm assms(1) assms(2) lt_closed 
          lt_of_sum_diff_degree p0_def q0_def trunc_simps(3))
    have P3: " lt ((p0 \<oplus>\<^bsub>P\<^esub> lt(p))\<otimes>\<^bsub>P \<^esub>lt(q)) = lt p \<otimes>\<^bsub>P\<^esub> lt q"
    proof-
      have Q0: "((p0 \<oplus>\<^bsub>P\<^esub> lt(p))\<otimes>\<^bsub>P \<^esub>lt(q)) = (p0 \<otimes>\<^bsub>P \<^esub>lt(q)) \<oplus>\<^bsub>P\<^esub>  (lt(p))\<otimes>\<^bsub>P \<^esub>lt(q)"
        by (simp add: P.l_distr assms(1) assms(2) lt_closed p0_def trunc_simps(3))
      have Q1: "degree ((p0 \<otimes>\<^bsub>P \<^esub>lt(q)) ) < degree ((lt(p))\<otimes>\<^bsub>P \<^esub>lt(q))"
      proof(cases "p0 = \<zero>\<^bsub>P\<^esub>")
        case True
        then show ?thesis 
          using P1 assms(1) assms(2)  lt_closed by auto
      next
        case F: False
        then show ?thesis
          proof-
            have LHS: "degree ((p0 \<otimes>\<^bsub>P \<^esub>lt(q))) < degree p + degree q"
              using False F deg_mult Pp assms(1) assms(2) deg_nzero_nzero 
                 degree_lt lt_closed p0_def trunc_simps(3) by auto
            have RHS: "degree ((lt(p))\<otimes>\<^bsub>P \<^esub>lt(q)) = degree p + degree q" 
               by (metis False  assms(1) assms(2) deg_mult deg_zero 
                     degree_lt lt_closed)
            then show ?thesis using LHS RHS by auto 
        qed
      qed
      have Q2: "lt ((p0 \<oplus>\<^bsub>P\<^esub> lt(p))\<otimes>\<^bsub>P \<^esub>lt(q)) = lt ((lt(p))\<otimes>\<^bsub>P \<^esub>lt(q))" 
        using Q0 Q1 by (simp add: UP_a_comm assms(1) assms(2) 
            lt_closed lt_of_sum_diff_degree p0_def trunc_simps(3))
      show ?thesis using lt_prod_lt Q0 Q1 Q2 
        by (simp add: assms(1) assms(2))
    qed
    then show ?thesis 
      by (simp add: P2)
  qed
qed

lemma lc_deg_0:
  assumes "degree p = 0"
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "(p \<otimes>\<^bsub>P\<^esub> q) = (lc p)\<odot>\<^bsub>P\<^esub>q" 
  using P_def assms(1) assms(2) assms(3) coeff_simp1 deg_zero_impl_monom 
    leading_coefficient_def lcoeff_closed monom_mult_is_smult 
     by (metis cfs_closed cf_f)

(*leading term powers*)

lemma (in domain) nonzero_pow_nonzero:
  assumes "a \<in> carrier R"
  assumes "a \<noteq>\<zero>"
  shows "a[^](n::nat) \<noteq> \<zero>"  
proof(induction n)
  case 0
  then show ?case 
    by auto
next
  case (Suc n)
  fix n::nat
  assume IH: "a[^] n \<noteq> \<zero>" 
  show "a[^] (Suc n) \<noteq> \<zero>" 
  proof-
    have "a[^] (Suc n) = a[^] n \<otimes> a"
      by simp
    then show ?thesis using assms IH 
      using IH assms(1) assms(2) local.integral by auto
  qed
qed

lemma monom_degree:
  assumes "a \<noteq>\<zero>"
  assumes "a \<in> (carrier R)"
  assumes "p = monom P a m"
  shows "degree (p[^]\<^bsub>P\<^esub> n) = n*m"
  using P_def R.nonzero_pow_nonzero UP_cring.monom_pow 
    UP_cring_axioms assms(1) assms(2) assms(3) deg_monom  by fastforce

lemma pow_sum0:
"\<And> p q. p \<in> carrier P \<Longrightarrow> q \<in> carrier P \<Longrightarrow> degree q < degree p \<Longrightarrow> degree ((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) = (degree p)*n"
proof(induction n)
  case 0
  then show ?case 
    by (metis P_def UP_domain_axioms UP_domain_def UP_ring.UP_ring UP_ring.intro coeff_simp1 
        cring_def deg_nzero_nzero  domain_def lcoeff_closed lcoeff_nonzero2 
        less_nat_zero_code monoid.nat_pow_0 monom_degree mult_zero_left mult_zero_right ring_def )
next
  case (Suc n)
  fix n
  assume IH: "\<And> p q. p \<in> carrier P \<Longrightarrow> q \<in> carrier P \<Longrightarrow> 
              degree q < degree p \<Longrightarrow> degree ((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) = (degree p)*n"
  then show "\<And> p q. p \<in> carrier P \<Longrightarrow> q \<in> carrier P \<Longrightarrow> 
             degree q < degree p \<Longrightarrow> degree ((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>(Suc n)) = (degree p)*(Suc n)"
  proof-
    fix p q
    assume A0: "p \<in> carrier P" and 
           A1: "q \<in> carrier P" and 
           A2:  "degree q < degree p"
    show "degree ((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>(Suc n)) = (degree p)*(Suc n)"
    proof(cases "q = \<zero>\<^bsub>P\<^esub>")
      case True
      then show ?thesis 
        by (metis A0 A1 A2 IH P.nat_pow_Suc2 P.nat_pow_closed P.r_zero deg_mult 
            domain.nonzero_pow_nonzero local.domain_axioms mult_Suc_right nat_neq_iff)
    next
      case False
      then show ?thesis 
      proof-
        have P0: "degree ((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) = (degree p)*n" 
          using A0 A1 A2 IH by auto 
        have P1: "(p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>(Suc n) = ((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) \<otimes>\<^bsub>P\<^esub> (p \<oplus>\<^bsub>P\<^esub> q )"
          by simp
        then have P2: "(p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>(Suc n) = (((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) \<otimes>\<^bsub>P\<^esub> p) \<oplus>\<^bsub>P\<^esub> (((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) \<otimes>\<^bsub>P\<^esub> q)"
          by (simp add: A0 A1 UP_r_distr)
        have P3: "degree (((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) \<otimes>\<^bsub>P\<^esub> p) = (degree p)*n + (degree p)" 
          using P0 A0 A1 A2 deg_nzero_nzero  degree_of_sum_diff_degree local.nonzero_pow_nonzero by auto
        have P4: "degree (((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) \<otimes>\<^bsub>P\<^esub> q) = (degree p)*n + (degree q)" 
          using P0 A0 A1 A2 deg_nzero_nzero  degree_of_sum_diff_degree local.nonzero_pow_nonzero False deg_mult 
          by simp
        have P5: "degree (((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) \<otimes>\<^bsub>P\<^esub> p) > degree (((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) \<otimes>\<^bsub>P\<^esub> q)"
          using P3 P4 A2 by auto 
        then show ?thesis using P5 P3 P2 
          by (simp add: A0 A1 degree_of_sum_diff_degree)
      qed
    qed
  qed
qed

lemma pow_sum:
  assumes "p \<in> carrier P" 
  assumes "q \<in> carrier P"
  assumes "degree q < degree p"
  shows "degree ((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) = (degree p)*n"
  using assms(1) assms(2) assms(3) pow_sum0 by blast

lemma deg_pow0:
 "\<And> p. p \<in> carrier P \<Longrightarrow> n \<ge> degree p \<Longrightarrow> degree (p [^]\<^bsub>P\<^esub> m) = m*(degree p)"
proof(induction n)
  case 0
  show "p \<in> carrier P \<Longrightarrow> 0 \<ge> degree p \<Longrightarrow> degree (p [^]\<^bsub>P\<^esub> m) = m*(degree p)"
  proof-
    assume B0:"p \<in> carrier P"
    assume B1: "0 \<ge> degree p"
    then obtain a where a_def: "a \<in> carrier R \<and> p = monom P a 0"
      using B0 deg_zero_impl_monom  by fastforce
    show "degree (p [^]\<^bsub>P\<^esub> m) = m*(degree p)"  using UP_cring.monom_pow 
      by (metis P_def R.nat_pow_closed UP_cring_axioms a_def deg_const  
        mult_0_right mult_zero_left)
  qed
next
  case (Suc n)
  fix n
  assume IH: "\<And>p. (p \<in> carrier P \<Longrightarrow> n \<ge>degree p \<Longrightarrow> degree (p [^]\<^bsub>P\<^esub> m) = m * (degree p))"
  show "p \<in> carrier P \<Longrightarrow> Suc n \<ge> degree p \<Longrightarrow> degree (p [^]\<^bsub>P\<^esub> m) = m * (degree p)"
  proof-
    assume A0: "p \<in> carrier P"
    assume A1: "Suc n \<ge> degree p"
    show "degree (p [^]\<^bsub>P\<^esub> m) = m * (degree p)"
    proof(cases "Suc n > degree p")
      case True
      then show ?thesis using IH A0 by simp
    next
      case False
      then show ?thesis 
      proof-
        obtain q where q_def: "q = trunc p"
          by simp
        obtain k where k_def: "k = degree q"
          by simp
        have q_is_poly: "q \<in> carrier P" 
          by (simp add: A0 q_def trunc_simps(3))
        have k_bound0: "k <degree p" 
          using k_def q_def trunc_degree[of p] A0 False by auto
        have k_bound1: "k \<le> n" 
          using k_bound0 A0 A1 by auto  
        have P_q:"degree (q [^]\<^bsub>P\<^esub> m) = m * k" 
          using IH[of "q"] k_bound1 k_def q_is_poly by auto  
        have P_lt: "degree ((lt p) [^]\<^bsub>P\<^esub> m) = m*(degree p)"
        proof-
          have "degree p = degree (lt p)" 
            by (simp add: A0)
          then show ?thesis using monom_degree 
            using A0 P_def coeff_simp1 deg_nzero_nzero 
              k_bound0 lcoeff_closed lcoeff_nonzero2 leading_term_def 
               by (metis k_def nat_neq_iff q_def trunc_zero)
        qed
        have "p = q \<oplus>\<^bsub>P\<^esub> (lt p)" 
          by (simp add: A0 q_def trunc_simps(1))
        then show ?thesis 
          using P_q pow_sum[of "(lt p)" q m] A0 UP_a_comm 
            degree_lt k_bound0 k_def lt_closed q_is_poly by auto
      qed
    qed
  qed
qed

lemma deg_pow:
  assumes "p \<in> carrier P"
  shows "degree (p [^]\<^bsub>P\<^esub> m) = m*(degree p)"
  using deg_pow0 assms by blast

lemma lt_pow0:
"\<And>f. f \<in> carrier P \<Longrightarrow> lt (f [^]\<^bsub>P\<^esub> (n::nat)) = (lt f) [^]\<^bsub>P\<^esub> n"
proof(induction n)
  case 0
  then show ?case 
    by (metis P.nat_pow_0 P_def R.one_closed R_cring UP_cring.monom_pow 
        UP_cring_axioms cring_def lt_monom monoid.nat_pow_0 ring_def)
next
  case (Suc n)
  fix n::nat
  assume IH: "\<And>f. f \<in> carrier P \<Longrightarrow> lt (f [^]\<^bsub>P\<^esub> n) = (lt f) [^]\<^bsub>P\<^esub> n"
  then show "\<And>f. f \<in> carrier P \<Longrightarrow> lt (f [^]\<^bsub>P\<^esub> (Suc n)) = (lt f) [^]\<^bsub>P\<^esub> (Suc n)"
  proof-
    fix f
    assume A: "f \<in> carrier P"
    show " lt (f [^]\<^bsub>P\<^esub> (Suc n)) = (lt f) [^]\<^bsub>P\<^esub> (Suc n)"
    proof-
      have 0: "lt (f [^]\<^bsub>P\<^esub> n) = (lt f) [^]\<^bsub>P\<^esub> n" 
        using A IH  by blast
      have 1: "lt (f [^]\<^bsub>P\<^esub> (Suc n)) = lt ((f [^]\<^bsub>P\<^esub> n)\<otimes>\<^bsub>P\<^esub> f)" 
        by auto then 
      show ?thesis using lt_mult 0 1 
        by (simp add: A)
    qed
  qed
qed

lemma lt_pow:
  assumes "f \<in> carrier P"
  shows " lt (f [^]\<^bsub>P\<^esub> (n::nat)) = (lt f) [^]\<^bsub>P\<^esub> n"
  using assms lt_pow0 by blast

(*The coefficients of trunc agree with f for small degree*)
lemma trunc_cfs0:
  assumes "p \<in> carrier P"
  assumes "n < degree p"
  shows "coeff P p n = coeff P (trunc p) n"
proof-
  have "coeff P (lt p) n = \<zero>"
    using assms lt_coeffs0 by auto
  then show ?thesis 
    using trunc_simps 
    by (metis P_def R.add.l_cancel_one UP.coeff_closed assms(1) coeff_add lt_closed)
qed

lemma trunc_cfs[simp]:
  assumes "p \<in> carrier P"
  assumes "n < degree p"
  shows " (trunc p) n = p n"
  using P_def assms(1) assms(2) coeff_simp1 trunc_cfs0 trunc_simps(3) by auto

(*Substitution into a monomial*)

lemma sub_monom:
  assumes "a \<in> carrier R"
  assumes "a \<noteq>\<zero>"
  assumes "f = monom P a n"
  assumes "g \<in> carrier P"
  shows "degree (f of g) = n*(degree g)"
proof-
  have "f of g = (to_poly a) \<otimes>\<^bsub>P\<^esub> (g[^]\<^bsub>P\<^esub>n)"
    unfolding compose_def
    using assms UP_pre_univ_prop.eval_monom[of R P to_poly a g] to_poly_UP_pre_univ_prop 
    unfolding P_def  
    by blast
  then show ?thesis using deg_pow deg_mult 
    by (metis P.nat_pow_closed P_def assms(1) assms(2) 
        assms(4) deg_smult monom_mult_is_smult to_polynomial_def)
qed

(*Subbing a constant into a polynomial yields a constant*)
lemma sub_in_const:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "degree g = 0"
  shows "degree (f of g) = 0"
proof-
  have "\<And>n. (\<And>p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> degree (p of g) = 0)"
  proof-
    fix n
    show "\<And>p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> degree (p of g) = 0"
    proof(induction n)
      case 0
      then show ?case 
        by (simp add: assms(1))
    next
      case (Suc n)
      fix n
      assume IH: "\<And>p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> degree (p of g) = 0"
      show  "\<And>p. p \<in> carrier P \<Longrightarrow> degree p \<le> (Suc n) \<Longrightarrow> degree (p of g) = 0"
      proof-
        fix p
        assume A0: "p \<in> carrier P"
        assume A1: "degree p \<le> (Suc n)"
        show "degree (p of g) = 0"
        proof(cases "degree p < Suc n")
          case True
          then show ?thesis using IH 
            using A0 by auto
        next
          case False
          then have D: "degree p = Suc n" 
            by (simp add: A1 nat_less_le)
          show ?thesis
          proof-
            have P0: "degree ((trunc p) of g) = 0" using IH 
              by (metis A0 D less_Suc_eq_le trunc_degree trunc_simps(3) zero_less_Suc)
            have P1: "degree ((lt p) of g) = 0" 
              by (metis A0 D P_def UP_domain.sub_monom UP_domain_axioms assms(1) assms(3) 
                coeff_simp1 deg_nzero_nzero  lcoeff_closed lcoeff_nonzero2 
                leading_term_def mult_is_0 nat_less_le zero_less_Suc)
            have P2: "p of g = (trunc p of g) \<oplus>\<^bsub>P\<^esub> ((lt p) of g)"
              by (metis A0 assms(1) lt_closed sub_add trunc_simps(1) trunc_simps(3))
            then show ?thesis 
              using P0 P1 P2 deg_add[of "trunc p of g" "lt p of g"] 
              by (simp add: A0 assms(1) lt_closed sub_closed trunc_simps(3))
          qed
        qed
      qed
    qed
  qed
  then show ?thesis 
    using assms(2) by blast
qed

lemma sub_deg0:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "g \<noteq> \<zero>\<^bsub>P\<^esub>"
  assumes "f \<noteq> \<zero>\<^bsub>P\<^esub>"
  shows "degree (f of g) = degree f * degree g"
proof-
  have "\<And>n. \<And> p. p \<in> carrier P \<Longrightarrow> (degree p) \<le> n \<Longrightarrow> degree (p of g) = degree p * degree g"
  proof-
    fix n::nat
    show "\<And> p. p \<in> carrier P \<Longrightarrow> (degree p) \<le> n \<Longrightarrow> degree (p of g) = degree p * degree g"
    proof(induction n)
      case 0
      then have B0: "degree p = 0" by auto 
      then show ?case using sub_const[of g p] 
        by (simp add: "0.prems"(1) assms(1))
    next
      case (Suc n)
      fix n
      assume IH: "(\<And>p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> degree (p of g) = degree p * degree g)"
      show " p \<in> carrier P \<Longrightarrow> degree p \<le> Suc n \<Longrightarrow> degree (p of g) = degree p * degree g"
      proof-
        assume A0: "p \<in> carrier P"
        assume A1: "degree p \<le> Suc n"
        show ?thesis 
        proof(cases "degree p < Suc n")
          case True
          then show ?thesis using IH 
            by (simp add: A0)
        next
          case False
          then have D: "degree p = Suc n" 
            using A1 by auto  
          have P0: "(p of g) = ((trunc p) of g) \<oplus>\<^bsub>P\<^esub> ((lt p) of g)"
            by (metis A0 assms(1) lt_closed sub_add trunc_simps(1) trunc_simps(3))
          have P1: "degree ((trunc p) of g) = (degree (trunc p))*(degree g)"
            using IH  by (metis A0 D less_Suc_eq_le trunc_degree trunc_simps(3) zero_less_Suc)
          have P2: "degree ((lt p) of g) = (degree p) * degree g"
            using A0 D P_def UP_domain.sub_monom UP_domain_axioms assms(1) coeff_simp1
              deg_zero  lcoeff_closed lcoeff_nonzero2 leading_term_def 
              by (metis False less_Suc_eq_0_disj)
          then show ?thesis
            proof(cases "degree g = 0")
              case True
              then show ?thesis 
                by (simp add: Suc(2) assms(1) sub_in_const)
            next
              case False
              then show ?thesis 
              proof-
                have P3: "degree ((trunc p) of g) < degree ((lt p) of g)"
                  using False D  P1 P2  
                  by (metis (no_types, lifting) A0 mult.commute mult_right_cancel 
                      nat_less_le nat_mult_le_cancel_disj trunc_degree zero_less_Suc)
                then show ?thesis 
                  by (simp add: A0 P0 P2 UP_a_comm assms(1) degree_of_sum_diff_degree 
                    lt_closed sub_closed trunc_simps(3))
              qed
            qed
          qed
        qed
      qed
    qed
    then show ?thesis 
      using assms(2) by blast
  qed

lemma sub_deg:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "g \<noteq> \<zero>\<^bsub>P\<^esub>"
  shows "degree (f of g) = degree f * degree g"
proof(cases "f = \<zero>\<^bsub>P\<^esub>")
  case True
  then show ?thesis 
    using assms(1)  sub_const by auto
next
  case False
  then show ?thesis 
    by (simp add: assms(1) assms(2) assms(3) sub_deg0)
qed

lemma lt_sub:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "g \<noteq> \<zero>\<^bsub>P\<^esub>"
  assumes "degree g \<noteq> 0"
  shows "lt (f of g) = lt ((lt f) of g)"
proof-
  have P0: "degree (f of g) = degree ((lt f) of g)"
    using sub_deg 
    by (simp add: assms(1) assms(2) assms(3)  lt_closed)
  have P1: "f of g = ((trunc f) of g) \<oplus>\<^bsub>P\<^esub>((lt f) of g)"
    by (metis assms(1) assms(2) lt_closed rev_sub_add sub_rev_sub trunc_simps(1) trunc_simps(3))
  then show ?thesis
  proof(cases "degree f = 0")
    case True
    then show ?thesis 
      by (simp add: assms(2))
  next
    case False
    then have P2: "degree ((trunc f) of g) < degree ((lt f) of g)"
      using sub_deg 
      by (metis P0 assms(1) assms(2) assms(3) assms(4) mult_less_cancel2 neq0_conv trunc_degree trunc_simps(3))
    then show ?thesis using P0 P1 P2 
      by (simp add: UP_a_comm assms(1) assms(2) lt_closed lt_of_sum_diff_degree sub_closed trunc_simps(3))
  qed
qed

(*lemma on the leading coefficient*)
lemma lc_eq:
  assumes "f \<in> carrier P"
  shows "lc f = lc (lt f)"
  unfolding leading_coefficient_def
  using lt_deg_0 apply(auto simp: assms)
  by (simp add: assms lt_coeffs)

lemma lc_eq_deg_eq_imp_lt_eq:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "degree p > 0"
  assumes "degree p = degree q"
  assumes "lc p = lc q"
  shows "lt p = lt q"
  using assms(4) assms(5) leading_coefficient_def 
  by (simp add: lc_lt)

lemma lt_eq_imp_lc_eq:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "lt p = lt q"
  shows "lc p = lc q"
  by (simp add: assms(1) assms(2) assms(3) lc_eq)

lemma lt_eq_imp_deg_drop:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "lt p = lt q"
  assumes "degree p >0"
  shows "degree (p \<ominus>\<^bsub>P\<^esub> q) < degree p"
proof-
  have P0: "degree p = degree q"
    by (metis assms(1) assms(2) assms(3) degree_lt)
  then have P1: "degree (p \<ominus>\<^bsub>P\<^esub> q) \<le> degree p"
    by (metis P.add.inv_solve_right P.minus_closed P.minus_eq assms(1)
        assms(2) degree_of_sum_diff_degree neqE order.strict_implies_order order_refl)
  have "degree (p \<ominus>\<^bsub>P\<^esub> q) \<noteq> degree p"
  proof
    assume A: "degree (p \<ominus>\<^bsub>P\<^esub> q) = degree p"
    have Q0: "p \<ominus>\<^bsub>P\<^esub> q = ((trunc p) \<oplus>\<^bsub>P\<^esub> (lt p)) \<ominus>\<^bsub>P\<^esub> ((trunc q) \<oplus>\<^bsub>P\<^esub> (lt p))"
      using assms(1) assms(2) assms(3) trunc_simps(1) by force
    have Q1: "p \<ominus>\<^bsub>P\<^esub> q = (trunc p)  \<ominus>\<^bsub>P\<^esub> (trunc q)" 
    proof-
      have "p \<ominus>\<^bsub>P\<^esub> q = ((trunc p) \<oplus>\<^bsub>P\<^esub> (lt p)) \<ominus>\<^bsub>P\<^esub> (trunc q) \<ominus> \<^bsub>P\<^esub> (lt p)"
        using Q0 
        by (simp add: P.minus_add P.minus_eq UP_a_assoc assms(1) assms(2) lt_closed trunc_simps(3))
      then show ?thesis 
        by (metis (no_types, lifting) P.add.inv_mult_group P.minus_eq P_def UP_a_assoc assms(1)
            assms(2) assms(3) carrier_is_submodule lt_closed truncate_def submoduleE(3) 
            trunc_simps(1) trunc_simps(3))
    qed
    have Q2: "degree (trunc p) < degree p" 
      by (simp add: assms(1) assms(4) trunc_degree)
    have Q3: "degree (trunc q) < degree q" 
      using P0 assms(2) assms(4) trunc_degree by auto
    then show False  using A Q1 Q2 Q3 by (simp add: P.add.inv_solve_right
          P.minus_eq P0 assms(1) assms(2) degree_of_sum_diff_degree trunc_simps(3))
  qed
  then show ?thesis 
    using P1 by auto
qed

lemma lc_scalar_mult:
  assumes "p \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "lc (a \<odot>\<^bsub>P\<^esub> p) = a \<otimes> (lc p)"
proof-
  have "lc (a \<odot>\<^bsub>P\<^esub> p) = lc (lt (a \<odot>\<^bsub>P\<^esub> p))"
    by (simp add: assms(1) assms(2) lc_eq)
  then have "lc (a \<odot>\<^bsub>P\<^esub> p) = lc (a \<odot>\<^bsub>P\<^esub> (lt p))"
    by (simp add: assms(1) assms(2) lt_smult)
  then show ?thesis 
    unfolding leading_term_def leading_coefficient_def
    by (metis P.m_comm P.r_null P_def UP_zero_closed assms(1) assms(2) 
        coeff_monom coeff_simp1 coeff_smult deg_smult  monom_mult_is_smult
        monom_zero smult_closed)
qed

lemma lc_mult:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "lc (p \<otimes>\<^bsub>P\<^esub> q) = (lc p) \<otimes> (lc q)"
proof-
  have P0: "lt (p \<otimes>\<^bsub>P\<^esub> q) = (lt p) \<otimes>\<^bsub>P\<^esub> (lt q)"
    using assms lt_mult by auto 
  obtain a where a_def: "a \<in> carrier R \<and> (lt p) = monom P a (degree p)"
    using cfs_closed assms(1)   by (metis P_def leading_term_def)
  obtain b where b_def: "b \<in> carrier R \<and> (lt q) = monom P b (degree q)"
    using cfs_closed assms(2) leading_term_def  P_def by blast
  have P1: "a = lc p" using a_def 
    by (metis P_def assms(1) coeff_monom coeff_simp1 leading_coefficient_def lt_coeffs monom_closed)
  have P2: "b = lc q" using b_def 
    by (metis P_def assms(2) coeff_monom coeff_simp1 leading_coefficient_def lt_coeffs monom_closed)
  have P3: "(lt p) \<otimes>\<^bsub>P\<^esub> (lt q) =  monom P (a \<otimes> b) ((degree p) + (degree q))"
    using a_def b_def  by simp
  then have P4: "lc ((lt p) \<otimes>\<^bsub>P\<^esub> (lt q)) = a \<otimes>b"
    using R.m_closed a_def b_def lc_monom monom_mult 
    by metis 
  show ?thesis using P0 P1 P2 P4 
    by (simp add: assms(1) assms(2) lc_eq)
qed

lemma lc_pow:
  assumes "p \<in> carrier P"
  shows "lc (p[^]\<^bsub>P\<^esub>(n::nat)) = (lc p)[^]n"
proof-
  show ?thesis 
  proof(induction n)
    case 0
    then show ?case 
      by (metis (no_types, lifting) P.nat_pow_0 P_def R.nat_pow_0 R.one_closed
          UP_domain.lc_monom UP_domain_axioms UP_pre_univ_prop.axioms(1) 
          ring_hom_cring.hom_pow to_poly_UP_pre_univ_prop to_polynomial_def)
  next
    case (Suc n)
    fix n
    assume IH: "lc (p[^]\<^bsub>P\<^esub>(n::nat)) = (lc p)[^]n"
    show "lc (p[^]\<^bsub>P\<^esub>(Suc n)) = (lc p)[^](Suc n)"
    proof-
      have "lc (p[^]\<^bsub>P\<^esub>(Suc n)) = lc ((p[^]\<^bsub>P\<^esub>n) \<otimes>\<^bsub>P\<^esub>p)"
        by simp
      then have "lc (p[^]\<^bsub>P\<^esub>(Suc n)) = (lc p)[^]n \<otimes> (lc p)"
        by (simp add: IH assms lc_mult)
      then show ?thesis by auto 
    qed
  qed
qed

lemma lc_of_sub_in_lt:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "degree f = n"
  assumes "g \<noteq> \<zero>\<^bsub>P\<^esub>"
  assumes "degree g \<noteq> 0"
  shows "lc ((lt f) of g) = (lc f) \<otimes> ((lc g)[^]n)"
proof(cases "degree f = 0")
  case True
  then show ?thesis 
    by (metis P_def UP_cring_axioms UP_cring_def assms(1) assms(2) assms(3) coeff_simp1 
        cring_def  leading_coefficient_def lcoeff_closed lt_deg_0 monoid.nat_pow_0
        monoid.r_one ring_def sub_const)
next
  case False
  then show ?thesis 
  proof-
    have P0: "(lt f) of g = (to_poly (lc f)) \<otimes>\<^bsub>P\<^esub> (g[^]\<^bsub>P\<^esub>n)"
      unfolding compose_def
      using assms UP_pre_univ_prop.eval_monom[of R P to_poly "(lc f)" g n] to_poly_UP_pre_univ_prop 
      unfolding P_def  
      using P_def coeff_simp1  leading_coefficient_def lc_lt lcoeff_closed 
      by (simp add: leading_coefficient_def )
    have P1: "(lt f) of g = (lc f) \<odot>\<^bsub>P\<^esub>(g[^]\<^bsub>P\<^esub>n)"
      using P0 P.nat_pow_closed 
      by (metis P_def assms(1) assms(2) coeff_simp1 leading_coefficient_def 
          lcoeff_closed monom_mult_is_smult to_polynomial_def)

    have P2: "lt ((lt f) of g) = (lt (to_poly (lc f))) \<otimes>\<^bsub>P\<^esub> (lt (g[^]\<^bsub>P\<^esub>n))"
      using P0 lt_mult P.nat_pow_closed P_def assms(1) assms(2) coeff_simp1 
         leading_coefficient_def lcoeff_closed to_poly_is_poly 
      by (simp add: leading_coefficient_def)
    have P3: "lt ((lt f) of g) =  (to_poly (lc f)) \<otimes>\<^bsub>P\<^esub> (lt (g[^]\<^bsub>P\<^esub>n))"
      using P2  by (simp add:  assms(2)  leading_coefficient_def to_poly_is_poly)
    have P4: "lt ((lt f) of g) = (lc f) \<odot>\<^bsub>P\<^esub> ((lt g)[^]\<^bsub>P\<^esub>n)"
      using P.nat_pow_closed P1 P_def assms(1) assms(2) coeff_simp1 
         leading_coefficient_def lcoeff_closed lt_pow0 lt_smult 
        by (simp add: leading_coefficient_def)
    have P5: "lc ((lt f) of g) = (lc f) \<otimes> (lc ((lt g)[^]\<^bsub>P\<^esub>n))"
      using lc_scalar_mult P4  by (metis P.nat_pow_closed P1 cfs_closed 
          UP_smult_closed assms(1) assms(2) assms(3) leading_coefficient_def lc_eq lt_closed sub_rev_sub)
    show ?thesis
      using P5 lt_pow lc_pow assms(1) lc_eq lt_closed by presburger
  qed
qed

lemma lt_of_sub_in_lt:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "degree f = n"
  assumes "g \<noteq> \<zero>\<^bsub>P\<^esub>"
  assumes "degree g \<noteq> 0"
  shows "lt ((lt f) of g) = (lc f) \<odot>\<^bsub>P\<^esub> ((lt g)[^]\<^bsub>P\<^esub>n)"
proof-
  have "lt f = (monom P (lc f) (degree f))"
    by (simp add: lc_lt)
  then have "lt f = (lc f) \<odot>\<^bsub>P\<^esub>  (monom P \<one> (degree f))"
    by (metis P.r_one P_def R.one_closed UP_domain.lc_mult UP_domain_axioms 
        UP_one_closed assms(2) coeff_simp1 lc_monom lcoeff_closed 
        leading_coefficient_def monom_mult_smult monom_one)
  then have 0:"lt f = (lc f) \<odot>\<^bsub>P\<^esub>  (monom P \<one> n)" 
    using assms(3) by simp
  then have 1: "lt f = to_poly (lc f) \<otimes>\<^bsub>P\<^esub>  (monom P \<one> n)" 
    by (metis P_def R.one_closed assms(2) coeff_simp1 lcoeff_closed 
        leading_coefficient_def monom_closed monom_mult_is_smult to_polynomial_def)
  have 2:"(monom P \<one> n)of g = (g[^]\<^bsub>P\<^esub>n) " 
    by (metis (no_types, lifting) P.m_lcomm P.nat_pow_closed P.r_one P_def 
        R.one_closed UP_one_closed UP_pre_univ_prop.eval_monom assms(1) 
        monom_one compose_def to_poly_UP_pre_univ_prop to_polynomial_def)
  have 3: " ((lt f) of g) =  (to_poly (lc f) \<otimes>\<^bsub>P\<^esub>  (g[^]\<^bsub>P\<^esub>n))" using 1 2  
    by (metis (no_types, lifting) P_def UP_pre_univ_prop.eval_monom
        \<open>lt f = monom P (lc f) (degree f)\<close> assms(1) assms(2) assms(3) coeff_simp1 lcoeff_closed
        leading_coefficient_def compose_def to_poly_UP_pre_univ_prop)
  have 4: " (to_poly (lc f) \<otimes>\<^bsub>P\<^esub>  (g[^]\<^bsub>P\<^esub>n)) =  ((lc f) \<odot>\<^bsub>P\<^esub>  (g[^]\<^bsub>P\<^esub>n))" 
    using  P_def R.one_closed assms(2) coeff_simp1 lcoeff_closed 
        leading_coefficient_def monom_closed monom_mult_is_smult 
        by (metis P.nat_pow_closed assms(1) to_polynomial_def)
  have 5: " ((lt f) of g) =  ((lc f) \<odot>\<^bsub>P\<^esub>  (g[^]\<^bsub>P\<^esub>n))" 
    using 3 4  by simp
  have "degree  ((lc f) \<odot>\<^bsub>P\<^esub>  (g[^]\<^bsub>P\<^esub>n)) = degree ((lc f) \<odot>\<^bsub>P\<^esub> ((lt g)[^]\<^bsub>P\<^esub>n))"
    by (simp add:  assms(1) assms(2) deg_pow leading_coefficient_def lt_closed)
  then have P0: "degree ((lt f) of g) = degree ((lc f) \<odot>\<^bsub>P\<^esub> ((lt g)[^]\<^bsub>P\<^esub>n))" 
    using 5 by simp
  have P1: "lc ((lt f) of g) = lc ((lc f) \<odot>\<^bsub>P\<^esub> ((lt g)[^]\<^bsub>P\<^esub>n))" 
  proof-
    have A0: "lc ((lt f) of g) = (lc f) \<otimes> ((lc g)[^]n)" 
      using assms(1) assms(2) assms(3) assms(4) assms(5) lc_of_sub_in_lt by blast
    have A1: "lc ((lc f) \<odot>\<^bsub>P\<^esub> ((lt g)[^]\<^bsub>P\<^esub>n)) = (lc f) \<otimes> (lc ((lt g)[^]\<^bsub>P\<^esub>n))"
      using cfs_closed assms(1) assms(2) leading_coefficient_def lc_scalar_mult lt_closed 
      by (simp add: leading_coefficient_def)
    then show ?thesis 
      using A0 A1 lc_pow assms  by (metis lc_eq lt_closed)
  qed
  have P2: "lt ((lt f) of g) = lt ((lc f) \<odot>\<^bsub>P\<^esub> ((lt g)[^]\<^bsub>P\<^esub>n))" 
    using P0 P1   by (simp add: lc_lt)
  then show ?thesis 
    using P.nat_pow_closed P_def assms(1) assms(2) coeff_simp1 
       leading_coefficient_def lcoeff_closed lt_closed lt_pow0 lt_smult 
        by (simp add: P2 leading_coefficient_def)
qed

(*formula for the leading term of f \<circ> g *)
lemma lt_of_sub:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "degree f = n"
  assumes "g \<noteq> \<zero>\<^bsub>P\<^esub>"
  assumes "degree g \<noteq> 0"
  shows "lt (f of g) = (lc f) \<odot>\<^bsub>P\<^esub> ((lt g)[^]\<^bsub>P\<^esub>n)"
  using assms lt_sub lt_of_sub_in_lt apply auto 
  done
(*subtitution is associative*)

lemma sub_assoc_monom:
  assumes "f \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "r \<in> carrier P"
  shows "(lt f) of (q of r) = ((lt f) of q) of r"
proof-
  obtain n where n_def: "n = degree f"
    by simp
  obtain a where a_def: "a \<in> carrier R \<and> (lt f) = monom P a n"
    using cfs_closed assms(1) leading_coefficient_def lc_lt n_def  by metis
  have LHS: "(lt f) of (q of r) = a \<odot>\<^bsub>P\<^esub> (q of r)[^]\<^bsub>P\<^esub> n"
    by (metis P.nat_pow_closed P_def UP_pre_univ_prop.eval_monom a_def assms(2)
        assms(3) compose_def monom_mult_is_smult sub_closed to_poly_UP_pre_univ_prop to_polynomial_def)
  have RHS0: "((lt f) of q) of r = (a \<odot>\<^bsub>P\<^esub> q[^]\<^bsub>P\<^esub> n)of r"
    by (metis P.nat_pow_closed P_def UP_pre_univ_prop.eval_monom a_def 
        assms(2) compose_def monom_mult_is_smult to_poly_UP_pre_univ_prop to_polynomial_def)
  have RHS1: "((lt f) of q) of r = ((to_poly a) \<otimes>\<^bsub>P\<^esub> q[^]\<^bsub>P\<^esub> n)of r"
    using RHS0  by (metis P.nat_pow_closed P_def a_def 
        assms(2) monom_mult_is_smult to_polynomial_def)
  have RHS2: "((lt f) of q) of r = ((to_poly a) of r) \<otimes>\<^bsub>P\<^esub> (q[^]\<^bsub>P\<^esub> n of r)"
    using RHS1 a_def assms(2) assms(3) sub_mult to_poly_is_poly by auto
  have RHS3: "((lt f) of q) of r = (to_poly a) \<otimes>\<^bsub>P\<^esub> (q[^]\<^bsub>P\<^esub> n of r)"
    using RHS2 a_def assms(3) sub_to_poly by auto
  have RHS4: "((lt f) of q) of r = a \<odot>\<^bsub>P\<^esub> ((q[^]\<^bsub>P\<^esub> n)of r)"
    using RHS3 
    by (metis P.nat_pow_closed P_def a_def assms(2) assms(3) 
        monom_mult_is_smult sub_closed to_polynomial_def)
  have "(q of r)[^]\<^bsub>P\<^esub> n = ((q[^]\<^bsub>P\<^esub> n)of r)" 
    apply(induction n) apply(auto) apply (simp add: assms(3))
    using assms sub_mult  by simp
  then show ?thesis using RHS4 LHS by simp
qed

lemma sub_assoc:
  assumes "f \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "r \<in> carrier P"
  shows "f of (q of r) = (f of q) of r"
proof-
  have "\<And> n. \<And> p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> p of (q of r) = (p of q) of r"
  proof-
    fix n
    show "\<And> p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> p of (q of r) = (p of q) of r"
    proof(induction n)
      case 0
      then have "degree p = 0"
        by blast
      then have B0: "p of (q of r) = p"
        using sub_const[of "q of r" p] assms  "0.prems"(1) sub_closed by blast
      have B1: "(p of q) of r = p"
      proof-
        have "p of q = p"
          by (simp add: "0.prems"(1) \<open>degree p = 0\<close> assms(2))
        then show ?thesis 
          by (simp add: "0.prems"(1) \<open>degree p = 0\<close> assms(3))
      qed
      then show "p of (q of r) = (p of q) of r" using B0 B1 by auto 
    next
      case (Suc n)
      fix n
      assume IH: "\<And> p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> p of (q of r) = (p of q) of r"
      then show "\<And> p. p \<in> carrier P \<Longrightarrow> degree p \<le> Suc n \<Longrightarrow> p of (q of r) = (p of q) of r"
      proof-
        fix p
        assume A0: " p \<in> carrier P "
        assume A1: "degree p \<le> Suc n"
        show "p of (q of r) = (p of q) of r"
        proof(cases "degree p < Suc n")
          case True
          then show ?thesis using A0 A1 IH by auto 
        next
          case False
          then have "degree p = Suc n"
            using A1 by auto 
          have I0: "p of (q of r) = ((trunc p) \<oplus>\<^bsub>P\<^esub> (lt p)) of (q of r)"
            using A0 trunc_simps(1) by auto
          have I1: "p of (q of r) = ((trunc p)  of (q of r)) \<oplus>\<^bsub>P\<^esub> ((lt p)  of (q of r))"
            using I0 sub_add 
            by (simp add: A0 assms(2) assms(3) lt_closed rev_sub_closed sub_rev_sub trunc_simps(3))
          have I2: "p of (q of r) = (((trunc p)  of q) of r) \<oplus>\<^bsub>P\<^esub> (((lt p)  of q) of r)"
            using IH[of "trunc p"] sub_assoc_monom[of p q r] 
            by (metis A0 I1 \<open>degree p = Suc n\<close> assms(2) assms(3) 
                less_Suc_eq_le trunc_degree trunc_simps(3) zero_less_Suc)
          have I3: "p of (q of r) = (((trunc p)  of q) \<oplus>\<^bsub>P\<^esub> ((lt p)  of q)) of r"
            using sub_add trunc_simps(1) assms   
            by (simp add: A0 I2 lt_closed sub_closed trunc_simps(3))
          have I4: "p of (q of r) = (((trunc p)\<oplus>\<^bsub>P\<^esub>(lt p))   of q)  of r"
            using sub_add trunc_simps(1) assms   
            by (simp add: trunc_simps(1) A0 I3 lt_closed trunc_simps(3))
          then show ?thesis 
            using A0 trunc_simps(1) by auto
        qed
      qed
    qed
  qed
  then show ?thesis 
    using assms(1) by blast
qed

lemma sub_smult:
  assumes "f \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "(a\<odot>\<^bsub>P\<^esub>f ) of q = a\<odot>\<^bsub>P\<^esub>(f of q)"
proof-
  have "(a\<odot>\<^bsub>P\<^esub>f ) of q = ((to_poly a) \<otimes>\<^bsub>P\<^esub>f) of q"
    using assms  by (metis P_def monom_mult_is_smult to_polynomial_def)
    then have "(a\<odot>\<^bsub>P\<^esub>f ) of q = ((to_poly a) of q) \<otimes>\<^bsub>P\<^esub>(f of q)"
      by (simp add: assms(1) assms(2) assms(3) sub_mult to_poly_is_poly)
      then have "(a\<odot>\<^bsub>P\<^esub>f ) of q = (to_poly a) \<otimes>\<^bsub>P\<^esub>(f of q)"
        by (simp add: assms(2) assms(3))
        then show ?thesis 
          by (metis P_def assms(1) assms(2) assms(3) 
              monom_mult_is_smult sub_closed to_polynomial_def)
qed

lemma fun_of_sub_monom:
  assumes "is_monom f"
  assumes "g \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "fun_of (f of g) a = fun_of f (fun_of g a)"
proof-
  obtain b n where b_def: "b \<in> carrier R \<and> f = monom P b n"
    by (meson UP_domain.lc_closed UP_domain_axioms assms(1) is_monom_id is_monom_poly_def)
  then have P0: "f of g = b \<odot>\<^bsub>P\<^esub> (g[^]\<^bsub>P\<^esub>n)"
    using b_def unfolding compose_def 
    by (metis P.nat_pow_closed P_def UP_pre_univ_prop.eval_monom assms(2) 
        monom_mult_is_smult to_poly_UP_pre_univ_prop to_polynomial_def)
  have P1: "UP_pre_univ_prop R R (\<lambda>x. x)" 
    by (simp add: UP_pre_univ_prop_fact)
  then have P2: "fun_of f (fun_of g a) = b \<otimes>((fun_of g a)[^]n)"
    unfolding function_of_def 
    using b_def assms eval_ring_hom[of a] UP_pre_univ_prop.eval_monom[of R R "(\<lambda>x. x)" b "(fun_of g a)" n]
    unfolding function_of_def
    by (simp add: \<open>a \<in> carrier R\<close> P_def ring_hom_closed)
  have P3: "fun_of (monom P b n of g) a =  b \<otimes>((fun_of g a)[^]n)"
  proof-
    have 0: "fun_of (monom P b n of g) a = eval R R (\<lambda>x. x) a  (to_poly b \<otimes>\<^bsub>UP R\<^esub> g [^]\<^bsub>UP R\<^esub> n )"
      unfolding function_of_def
                compose_def
      using UP_pre_univ_prop.eval_monom[of R "(UP R)" to_poly b g n]
            P_def assms(2) b_def to_poly_UP_pre_univ_prop 
      by auto
    have 1: "fun_of (monom P b n of g) a = (eval R R (\<lambda>x. x) a  (to_poly b)) \<otimes> ( eval R R (\<lambda>x. x) a ( g [^]\<^bsub>UP R\<^esub> n ))"
      using 0 eval_ring_hom 
      by (metis P.nat_pow_closed P_def UP_domain.fun_of_mult UP_domain_axioms 
          assms(2) assms(3) b_def function_of_def to_poly_is_poly)
    have 2: "fun_of (monom P b n of g) a = b \<otimes> ( eval R R (\<lambda>x. x) a ( g [^]\<^bsub>UP R\<^esub> n ))"
      using 1 by (metis UP_domain.fun_of_to_poly UP_domain_axioms assms(3) b_def function_of_def)
    then show ?thesis 
      unfolding function_of_def
      using eval_ring_hom P_def UP_pre_univ_prop.ring_homD UP_pre_univ_prop_fact 
            assms(2) assms(3) ring_hom_cring.hom_pow by fastforce
  qed
  then show ?thesis 
    using b_def P2 by auto
qed


lemma fun_of_sub[simp]:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "fun_of (f of  g) a = (fun_of f) (fun_of g a)"
proof(rule poly_induct2[of f])
  show "f \<in> carrier P" 
    using assms by auto 
  show "\<And>p. p \<in> carrier P \<Longrightarrow> degree p = 0 \<Longrightarrow> fun_of (p of g) a = fun_of p (fun_of g a)"
  proof-
    fix p
    assume A0: "p \<in> carrier P"
    assume A1: "degree p = 0"
    then have P0: "degree (p of g) = 0"
      by (simp add: A0 assms(1))
    then obtain b where b_def: "p of g = to_poly b \<and> b \<in> carrier R"
      using A0 A1 cfs_closed assms(1) to_poly_inverse 
      by (meson sub_closed)
    then have "fun_of (p of g) a = b" 
      by (simp add: assms(3))
    have "p of g = p"
      using A0 A1 P_def UP_domain.sub_const UP_domain_axioms assms(1) by blast
    then have P1: "p = to_poly b"
      using b_def by auto
    have "fun_of g a \<in> carrier R"
      using assms  by simp
    then show "fun_of (p of g) a =  fun_of p (fun_of g a)"
      using P1 \<open>fun_of (p of g) a = b\<close> b_def by auto
  qed
  show "\<And>p. 0 < degree p \<Longrightarrow> p \<in> carrier P \<Longrightarrow> 
            fun_of (trunc p of g) a = fun_of (trunc p) (fun_of g a) \<Longrightarrow> 
            fun_of (p of g) a = fun_of p (fun_of g a)"
  proof-
    fix p
    assume A0: "0 < degree p"
    assume A1: " p \<in> carrier P"
    assume A2: "fun_of (trunc p of g) a = fun_of (trunc p) (fun_of g a)"
    show "fun_of (p of g) a = fun_of p (fun_of g a)"
    proof-
      have "p of g = (trunc p) of g \<oplus>\<^bsub>P\<^esub> (lt p) of g"
        by (metis A1 assms(1) lt_closed sub_add trunc_simps(1) trunc_simps(3))
      then have "fun_of (p of g) a = fun_of ((trunc p) of g) a \<oplus> (fun_of ((lt p) of g) a)"
        by (simp add: A1 assms(1) assms(3) lt_closed sub_closed trunc_simps(3))
      then have 0: "fun_of (p of g) a = fun_of (trunc p) (fun_of g a) \<oplus> (fun_of ((lt p) of g) a)"
        by (simp add: A2)
      have "(fun_of ((lt p) of g) a) = fun_of (lt p) (fun_of g a)"
        using fun_of_sub_monom 
        by (simp add: A1 assms(1) assms(3) is_monom_prop1)
      then have "fun_of (p of g) a = fun_of (trunc p) (fun_of g a) \<oplus>  fun_of (lt p) (fun_of g a)"
        using 0 by auto 
      then show ?thesis 
        by (metis A1 assms(1) assms(3) fun_of_closed fun_of_plus lt_closed trunc_simps(1) trunc_simps(3))
    qed
  qed
qed


end
(**************************************************************************************************)
(**************************************************************************************************)
(***************************  Constructor for monic linear polynomials  ***************************)
(**************************************************************************************************)
(**************************************************************************************************)

(*The polynomial representing the variable X*)

definition X_poly where
"X_poly R= monom (UP R) \<one>\<^bsub>R\<^esub> 1"


context UP_domain
begin

abbreviation X where
"X \<equiv> X_poly R"

lemma X_closed[simp]:
"X \<in> carrier P"
  unfolding X_poly_def 
  using P_def monom_closed by blast

lemma degree_X[simp]:
"degree X = 1" 
  unfolding X_poly_def 
  using P_def deg_monom  by auto

lemma X_not_zero[simp]:
"X \<noteq> \<zero>\<^bsub>P\<^esub>"
  using degree_X  by fastforce


lemma X_sub0[simp]:
  assumes "p \<in> carrier P"
  shows "X of p = p"
  unfolding X_poly_def
  using P_def UP_pre_univ_prop.eval_monom1 assms compose_def to_poly_UP_pre_univ_prop 
  by metis

lemma X_sub[simp]:
  assumes "p \<in> carrier P"
  shows "p of X = p"
proof-
  have "\<And>n. \<And>f. f \<in> carrier P \<Longrightarrow> degree f \<le>n \<Longrightarrow> f of X = f"
  proof-
    fix n
    show " \<And>f. f \<in> carrier P \<Longrightarrow> degree f \<le>n \<Longrightarrow> f of X = f"
    proof(induction n)
      case 0
      then show ?case 
        by simp
    next
      case (Suc n)
      fix n
      assume IH: " \<And>f. f \<in> carrier P \<Longrightarrow> degree f \<le>n \<Longrightarrow> f of X = f"
      fix f
      show "f \<in> carrier P \<Longrightarrow> degree f \<le>(Suc n) \<Longrightarrow> f of X = f"
      proof-
        assume A0: "f \<in> carrier P"
        assume A1: "degree f \<le>(Suc n)"
        show " f of X = f"
        proof(cases "degree f < Suc n")
          case True
          then show ?thesis using IH A0 A1 
            using Suc_leI by blast
        next
          case False
          have D: "degree f = Suc n"
            using A1 False nat_less_le by blast
          have "f of X = (trunc f) of X \<oplus>\<^bsub>P\<^esub> (lt f) of X"
            by (metis A0 P_def UP_domain.trunc_simps(1) UP_domain_axioms X_closed lt_closed sub_add trunc_simps(3))
          then have P: "f of X = (trunc f) \<oplus>\<^bsub>P\<^esub> ((lt f) of X)"
            using D IH[of "trunc f"] 
            by (metis A0 P_def UP_domain.trunc_simps(3) UP_domain_axioms 
                less_Suc_eq_le trunc_degree zero_less_Suc)
          have "lt f =  ((lt f) of X)"
          proof-
            have 0: "lt f = (lc f) \<odot>\<^bsub>P\<^esub> (monom P \<one> (degree f))"
              by (metis A0 D cfs_closed R.l_one R.m_comm R.one_closed 
                  leading_coefficient_def lc_lt monom_mult_smult)
            then have 1: "((lt f) of X) = (lc f) \<odot>\<^bsub>P\<^esub> (monom P \<one> (degree f)) of X"
              by simp
            then have 2: "((lt f) of X) = (lc f) \<odot>\<^bsub>P\<^esub> (monom P \<one> (degree f) of X)"
              using A0 P_def X_closed coeff_simp1  leading_coefficient_def
                lcoeff_closed monom_closed sub_smult 
              by (simp add: leading_coefficient_def)
            have 3: "((lt f) of X) = (lc f) \<odot>\<^bsub>P\<^esub> (X[^]\<^bsub>P\<^esub>(degree f))" 
              using "2" P.nat_pow_closed P_def R.one_closed R_cring  UP_pre_univ_prop.eval_monom 
                  X_closed compose_def monom_one   to_poly_UP_pre_univ_prop  
              by (metis (no_types, lifting) UP_one_closed UP_ring.UP_ring 
                  UP_ring.intro cring_def deg_one leading_coefficient_def 
                  lc_monom monoid.l_one ring_def to_poly_inverse)
            then show ?thesis unfolding X_poly_def P_def using 0  
              using P_def monom_pow by auto
          qed
          then show ?thesis using P 
            using A0 P_def UP_domain.trunc_simps(1) UP_domain_axioms by fastforce
        qed
      qed
    qed
  qed
  then show ?thesis 
    using assms by blast
qed

(*representation of monomials as scalar multiples of powers of X*)
lemma monom_rep_X_pow:
  assumes "a \<in> carrier R"
  shows "monom P a n = a\<odot>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)"
proof-
  have "monom P a n = a\<odot>\<^bsub>P\<^esub>monom P \<one> n"
    by (metis R.one_closed R.r_one assms monom_mult_smult)
  then show ?thesis 
    unfolding X_poly_def 
    using monom_pow 
    by (simp add: P_def)
qed

lemma lt_rep_X_pow:
  assumes "p \<in> carrier P"
  shows "lt p = (lc p)\<odot>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(degree p))"
proof-
  have "lt p =  monom P (lc p) (degree p)"
    using assms unfolding leading_term_def leading_coefficient_def by (simp add: P_def)
  then show ?thesis 
    using monom_rep_X_pow P_def assms coeff_simp1  leading_coefficient_def lcoeff_closed 
    by (simp add: leading_coefficient_def)
qed

lemma fun_of_monom'[simp]:
  assumes "c \<in> carrier R"
  assumes "c \<noteq>\<zero>"
  assumes "x \<in> carrier R"
  shows "fun_of (c \<odot>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub>(n::nat)) x = c \<otimes> x [^] n"
  using P_def UP_domain.fun_of_monom UP_domain.monom_rep_X_pow UP_domain_axioms assms(1) assms(2) assms(3) by fastforce

lemma fun_of_X_pow[simp]:
  assumes "x \<in> carrier R"
  shows "fun_of (X[^]\<^bsub>P\<^esub>(n::nat)) x = x [^] n"
  by (simp add: P_def UP_cring.monom_pow UP_cring_axioms UP_domain.fun_of_monom UP_domain_axioms X_poly_def assms)

end
(*monic linear polynomials*)

definition X_poly_plus where
"X_poly_plus R a = (X_poly R) \<oplus>\<^bsub>(UP R)\<^esub> to_polynomial R a"

definition X_poly_minus where
"X_poly_minus R a = (X_poly R) \<ominus>\<^bsub>(UP R)\<^esub> to_polynomial R a"

context UP_domain
begin

abbreviation X_plus where
"X_plus \<equiv> X_poly_plus R"

abbreviation X_minus where
"X_minus \<equiv> X_poly_minus R"

lemma X_plus_closed[simp]:
  assumes "a \<in> carrier R"
  shows "(X_plus a) \<in> carrier P"
  unfolding X_poly_plus_def using X_closed to_poly_is_poly 
  using P_def UP_a_closed assms by auto

lemma X_minus_closed[simp]:
  assumes "a \<in> carrier R"
  shows "(X_minus a) \<in> carrier P"
  unfolding X_poly_minus_def using X_closed to_poly_is_poly 
  by (simp add: P_def UP_ring.UP_ring assms ring.ring_simprules(4))

lemma X_minus_plus:
  assumes "a \<in> carrier R"
  shows "(X_minus a) = X_plus (\<ominus>a)"
  using P_def UP_ring.UP_ring  UP_ring_axioms
  by (simp add: UP_ring.UP_ring X_poly_minus_def X_poly_plus_def assms ring.ring_simprules(14))

lemma degree_of_X_plus:
  assumes "a \<in> carrier R"
  shows "degree (X_plus a) = 1"
proof-
  have 0:"degree (X_plus a) \<le> 1"
    using deg_add  P_def X_poly_plus_def 
      UP_domain_axioms X_closed assms degree_X to_poly_is_poly 
      by (metis UP_domain.degree_to_poly max_0_1(2))
  have 1:"degree (X_plus a) > 0"
    by (metis One_nat_def P_def R.one_closed R.r_zero X_poly_def 
        X_closed X_poly_plus_def X_plus_closed  assms  coeff_add coeff_monom deg_aboveD  
        degree_X  gr0I lcoeff_nonzero_deg  lessI  n_not_Suc_n to_polynomial_def to_poly_is_poly)
  then show ?thesis 
    using "0" by linarith
qed

lemma degree_of_X_minus:
  assumes "a \<in> carrier R"
  shows "degree (X_minus a) = 1"
  using degree_of_X_plus[of "\<ominus>a"] X_minus_plus[simp] assms by auto  

lemma lt_of_X:
"lt X = X"
  unfolding leading_term_def
  by (metis P_def R.one_closed X_poly_def X_closed coeff_monom coeff_simp1 degree_X)

lemma lt_of_X_plus:
  assumes "a \<in> carrier R"
  shows "lt (X_plus a) = X"
  unfolding X_poly_plus_def
  using X_closed  assms  lt_of_sum_diff_degree[of X "to_poly a"]  
    degree_to_poly[of a]  to_poly_is_poly[of a] degree_X lt_of_X 
    by (simp add: P_def)  

lemma lt_of_X_minus:
  assumes "a \<in> carrier R"
  shows "lt (X_plus a) = X"
  using X_minus_plus[of a]  assms lt_of_X_plus by blast

lemma fun_of_X[simp]:
  assumes "a \<in> carrier R"
  shows "fun_of X a = a"
  using X_closed assms fun_of_sub_monom is_monom_prop1 lt_of_X to_poly_is_poly 
  by (metis X_sub0 fun_of_to_poly)

lemma fun_of_X_plus[simp]:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "fun_of (X_plus a) b = b \<oplus> a"
  unfolding X_poly_plus_def 
  using assms fun_of_X[of b] fun_of_plus[of "to_poly a" X  b] fun_of_to_poly[of a b] 
  using P_def X_closed to_poly_is_poly by auto


lemma fun_of_X_minus[simp]:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "fun_of (X_minus a) b = b \<ominus> a"
  using fun_of_X_plus[of "\<ominus> a" b] X_minus_plus[of a] assms 
  by (simp add: R.minus_eq)

(*Linear substituions*)
 

definition trans_left where
"trans_left f a = f of (X_minus a)"

lemma trans_left_is_poly:
  assumes "a \<in> carrier R"
  assumes "f \<in> carrier P"
  shows "trans_left f a \<in> carrier P"
  unfolding trans_left_def using assms X_minus_closed[of a]
  sub_closed by blast

lemma trans_left_deg:
  assumes "a \<in> carrier R"
  assumes "f \<in> carrier P"
  shows "degree (trans_left f a) = degree f" 
  unfolding trans_left_def 
  using assms sub_deg[of f "X_minus a"] 
        degree_of_X_minus[of a] 
        X_minus_closed[of a]
  apply auto
  using deg_nzero_nzero  sub_deg by auto

lemma X_plus_sub_deg:
  assumes "a \<in> carrier R"
  assumes "f \<in> carrier P"
  shows "degree (f of (X_plus a)) = degree f"
  by (metis  X_plus_closed assms(1) assms(2) 
      deg_zero   degree_of_X_plus 
        mult.right_neutral  sub_deg zero_neq_one)

lemma X_minus_sub_deg:
  assumes "a \<in> carrier R"
  assumes "f \<in> carrier P"
  shows "degree (f of (X_minus a)) = degree f"
  by (metis  X_minus_closed assms(1) assms(2) 
      deg_zero   degree_of_X_minus
        mult.right_neutral  sub_deg zero_neq_one)

end

(*Taylor expansions of polynomials*)

definition taylor_expansion where
"taylor_expansion R a p = compose R p (X_poly_plus R a)"


abbreviation(in UP_domain) Taylor ("T\<^bsub>_\<^esub>") where
"Taylor \<equiv> taylor_expansion R"

lemma(in UP_domain) Taylor_closed[simp]:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "T\<^bsub>a\<^esub> f \<in>  carrier P"
  by (simp add: X_plus_closed assms(1) assms(2) sub_closed taylor_expansion_def)

lemma Taylor_closed_UP_domain[simp]:
  assumes "UP_domain R"
  assumes "f \<in> carrier (UP R)"
  assumes "a \<in> carrier R"
  shows "taylor_expansion R a f \<in>  carrier (UP R)"
  using assms UP_domain.Taylor_closed 
  by (simp add: UP_domain.Taylor_closed)


context UP_domain
begin

lemma Taylor_deg:
  assumes "a \<in> carrier R"
  assumes "p \<in> carrier P"
  shows "degree (T\<^bsub>a\<^esub> p) = degree p"
  unfolding taylor_expansion_def using X_plus_sub_deg[of a p] assms 
  by (simp add: taylor_expansion_def)

lemma plus_minus_sub[simp]:
  assumes " a \<in> carrier R"
  shows "X_plus a of X_minus a = X"
  unfolding X_poly_plus_def
proof-
  have "(X \<oplus>\<^bsub>P\<^esub> to_poly a) of X_minus a = (X  of X_minus a) \<oplus>\<^bsub>P\<^esub> (to_poly a) of X_minus a"
    using sub_add 
    by (simp add: X_minus_closed assms to_poly_is_poly)
  then have "(X \<oplus>\<^bsub>P\<^esub> to_poly a) of X_minus a = (X_minus a) \<oplus>\<^bsub>P\<^esub> (to_poly a)"
    by (simp add: X_minus_closed assms)
  then show "(X \<oplus>\<^bsub>UP R\<^esub> to_poly a) of X_minus a = X" 
    unfolding to_polynomial_def X_poly_minus_def
    by (metis P.add.inv_solve_right P.minus_eq P_def 
        X_closed X_poly_minus_def X_minus_closed assms monom_closed to_polynomial_def)
qed

lemma minus_plus_sub[simp]:
  assumes " a \<in> carrier R"
  shows "X_minus a of X_plus a = X"
  using plus_minus_sub[of "\<ominus>a"]
  unfolding X_poly_minus_def
  unfolding X_poly_plus_def
  using assms  apply simp
  by (metis P_def R.add.inv_closed R.minus_minus a_minus_def to_poly_ominus)

lemma Taylor_id:
  assumes "a \<in> carrier R"
  assumes "p \<in> carrier P"
  shows "p = (T\<^bsub>a\<^esub> p) of (X_minus a)"
  unfolding taylor_expansion_def 
  using assms sub_assoc[of p "X_plus a" "X_minus a"] X_plus_closed[of a]  X_minus_closed[of a]
  by (metis P_def UP_domain.X_sub UP_domain.plus_minus_sub UP_domain_axioms taylor_expansion_def)

lemma Taylor_eval:
  assumes "a \<in> carrier R"
  assumes "f \<in> carrier P"
  assumes "b \<in> carrier R"
  shows "fun_of (T\<^bsub>a\<^esub> f) b = fun_of f (b \<oplus> a)"
  unfolding  taylor_expansion_def 
  using fun_of_sub[of "(X_plus a)" f b] fun_of_X_plus[of a b] 
        assms X_plus_closed[of a] by auto

end
(*derivative function*)

definition derivative where
"derivative R f a = (taylor_expansion R a f) 1"

abbreviation(in UP_domain) deriv where
"deriv \<equiv> derivative R"

lemma(in UP_domain) derivative_closed:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "(derivative R f a) \<in> carrier R"
  unfolding derivative_def  
  by (metis P_def UP_domain.cfs_closed UP_domain_axioms 
      X_plus_closed assms(1) assms(2) sub_closed taylor_expansion_def)

(*Constant term  and coefficient function*)

definition zero_coefficient where
"zero_coefficient f = (f 0)"

abbreviation(in UP_domain) coeff_0 where
"coeff_0 \<equiv> zero_coefficient"

definition constant_term where
"constant_term R f = to_polynomial R (f 0)"

abbreviation(in UP_domain) ct where
"ct \<equiv> constant_term R"

context UP_domain
begin

lemma ct_is_poly[simp]:
  assumes "p \<in> carrier P"
  shows "ct p \<in> carrier P"
  by (simp add:  assms constant_term_def to_poly_is_poly)

lemma ct_degree:
  assumes "p \<in> carrier P"
  shows "degree (ct p) = 0"
  unfolding constant_term_def 
  by (simp add:  assms)


lemma ct_coeff_0[simp]:
assumes "f \<in> carrier P"
assumes "coeff_0 f = \<zero>"
shows "ct f = \<zero>\<^bsub>P\<^esub>"
  using assms
  unfolding constant_term_def
            zero_coefficient_def
            to_polynomial_def 
  apply simp 
  using P_def monom_zero by blast 

lemma coeff_0_degree_zero:
  assumes "f \<in> carrier P"
  assumes "degree f = 0"
  shows "lc f = coeff_0 f"
  by (simp add: assms(2) zero_coefficient_def leading_coefficient_def)

lemma coeff_0_zero_degree_zero:
  assumes "f \<in> carrier P"
  assumes "degree f = 0"
  assumes "coeff_0 f = \<zero>"
  shows "f = \<zero>\<^bsub>P\<^esub>"
  using coeff_0_degree_zero assms
  by (metis P_def coeff_simp1 zero_coefficient_def  lcoeff_nonzero2)

lemma coeff_0_ct[simp]:
  assumes "p \<in> carrier P"
  shows "coeff_0 (ct p) = coeff_0 p"
  unfolding zero_coefficient_def constant_term_def to_polynomial_def 
  by (metis P_def cfs_closed assms coeff_simp1 deg_const deg_zero_impl_monom lc_monom monom_closed)


lemma ctrunc:
  assumes "p \<in> carrier P"
  assumes "degree p >0"
  shows "coeff_0 (trunc p) = coeff_0 p"
proof-
  have 0: "(lt p) 0 = \<zero>"
    using assms(1) assms(2) lt_coeffs by auto
  have "p = (trunc p) \<oplus>\<^bsub>P\<^esub> (lt p)"
    using assms(1) trunc_simps(1) by auto
  then have "p 0 = (trunc p) 0 \<oplus> (lt p) 0"
    by (metis assms(1) cf_add lt_closed trunc_simps(3))
  then show ?thesis using 0 
    by (simp add: 0  assms(1) zero_coefficient_def trunc_simps(3))
qed

lemma fun_of_ct[simp]:
  assumes "f \<in> carrier P"
  assumes  "b \<in> carrier R"  
  shows "fun_of (ct f) b = (f 0)"
  by (simp add:  assms(1) assms(2) constant_term_def)


(*fun_of simp rule for scalar multiples*)

lemma fun_of_smult[simp]:
  assumes "f \<in> carrier P"
  assumes "b \<in> carrier R"
  assumes "c \<in> carrier R"
  shows "fun_of (c \<odot>\<^bsub>P\<^esub> f) b = c \<otimes>(fun_of f b)"
proof-
  have "(c \<odot>\<^bsub>P\<^esub> f) = (to_poly c) \<otimes>\<^bsub>P\<^esub> f"
    by (metis P_def assms(1) assms(3) monom_mult_is_smult to_polynomial_def)
  then have "fun_of (c \<odot>\<^bsub>P\<^esub> f) b = fun_of (to_poly c) b \<otimes> fun_of f b"
    by (simp add: assms(1) assms(2) assms(3) to_poly_is_poly)
  then show  ?thesis 
    by (simp add: assms(2) assms(3))
qed

(*Constant coefficient function is a ring homomorphism*)
lemma coeff_0_to_poly[simp]:
  assumes "a \<in> carrier R"
  shows "coeff_0 (to_poly a) = a"
  by (metis P_def UP_domain.degree_to_poly UP_domain_axioms assms zero_coefficient_def
      coeff_simp1 deg_zero_impl_monom lc_monom lcoeff_closed to_poly_is_poly to_polynomial_def)

lemma coeff_0_add[simp]:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "coeff_0 (p \<oplus>\<^bsub>P\<^esub> q) = (coeff_0 p) \<oplus> (coeff_0 q)"
  by (simp add: assms(1) assms(2) zero_coefficient_def)

lemma coeff_lt[simp]:
  assumes "p \<in> carrier P"
  assumes "degree p > 0"
  shows "coeff_0 (lt p) = \<zero>"
  unfolding zero_coefficient_def leading_term_def 
  by (metis assms(1) assms(2) leading_term_def lt_coeffs nat_less_le)

lemma coeff_lt_mult[simp]:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "degree p > 0"
  shows "coeff_0 ((lt p) \<otimes>\<^bsub>P\<^esub> q) = \<zero>"
  apply(rule poly_induct[of q])
  using assms(2) apply(simp)
proof-
  show B: "\<And>pa. pa \<in> carrier P \<Longrightarrow> degree pa = 0 \<Longrightarrow> coeff_0 (lt p \<otimes>\<^bsub>P\<^esub> pa) = \<zero>"
  proof-
    fix f
    assume B0:"f \<in> carrier P"
    assume B1: "degree f = 0"
    then show "coeff_0 (lt p \<otimes>\<^bsub>P\<^esub> f) = \<zero>"
    proof(cases "f = \<zero>\<^bsub>P\<^esub>")
      case True
      then show ?thesis 
        by (metis B0 zero_coefficient_def assms(1) assms(3) 
            coeff_0_ct ct_coeff_0 domain.integral_iff local.domain_axioms
            lt_coeffs lt_closed neq0_conv)
    next
      case False
      then have "p \<otimes>\<^bsub>P\<^esub> f = (lc f) \<odot>\<^bsub>P\<^esub>p"
        by (simp add: B0 B1 UP_m_comm assms(1) lc_deg_0)
      then have "coeff_0 (p \<otimes>\<^bsub>P\<^esub> f) = coeff_0 ((lc f) \<odot>\<^bsub>P\<^esub>p)"
        by simp
      then show ?thesis 
        by (metis B0 B1 False P_def UP_domain.lt_mult UP_domain_axioms UP_mult_closed 
            \<open>p \<otimes>\<^bsub>P\<^esub> f = lc f \<odot>\<^bsub>P\<^esub> p\<close> assms(1) assms(3) coeff_0_degree_zero 
            coeff_0_zero_degree_zero coeff_lt coeff_simp1 deg_smult  
            leading_coefficient_def lcoeff_closed lt_deg_0)
    qed
  qed
  show "\<And>pa. (\<And>q. q \<in> carrier P \<Longrightarrow> degree q < degree pa \<Longrightarrow> coeff_0 (lt p \<otimes>\<^bsub>P\<^esub> q) = \<zero>)
                 \<Longrightarrow> pa \<in> carrier P \<Longrightarrow> 0 < degree pa \<Longrightarrow> coeff_0 (lt p \<otimes>\<^bsub>P\<^esub> pa) = \<zero>"
  proof-
    fix f
    assume IH: " (\<And>q. q \<in> carrier P \<Longrightarrow> degree q < degree f \<Longrightarrow> coeff_0 (lt p \<otimes>\<^bsub>P\<^esub> q) = \<zero>)"
    assume A: "f \<in> carrier P" " 0 < degree f " 
    show "coeff_0 (lt p \<otimes>\<^bsub>P\<^esub> f) = \<zero>"
    proof-
      have 0: "(lt p \<otimes>\<^bsub>P\<^esub> f) = (lt p \<otimes>\<^bsub>P\<^esub> trunc f) \<oplus>\<^bsub>P\<^esub> (lt p \<otimes>\<^bsub>P\<^esub> lt f)"
        by (metis A(1) P.r_distr assms(1) lt_closed trunc_simps(1) trunc_simps(3))
      then have 1:  "coeff_0 (lt p \<otimes>\<^bsub>P\<^esub> f) = coeff_0 (lt p \<otimes>\<^bsub>P\<^esub> trunc f) \<oplus> coeff_0  (lt p \<otimes>\<^bsub>P\<^esub> lt f)"
        by (simp add: A(1) assms(1) lt_closed trunc_simps(3))
      have 2: " coeff_0 (lt p \<otimes>\<^bsub>P\<^esub> trunc f) = \<zero>" 
        using A IH  by (simp add: trunc_degree trunc_simps(3))
      have 3: "coeff_0  (lt p \<otimes>\<^bsub>P\<^esub> lt f) = \<zero>"
      proof-
        have "degree (lt p \<otimes>\<^bsub>P\<^esub> lt f) > 0" using  deg_mult assms A 
          by (metis add_gr_0 deg_zero  degree_lt lt_closed nat_less_le)
        then have "coeff_0 (lt (lt p \<otimes>\<^bsub>P\<^esub> lt f)) = \<zero>"
        by (meson A(1) UP_mult_closed assms(1) coeff_lt lt_closed)
        then show ?thesis 
          by (simp add: A(1) assms(1))
      qed
      then show ?thesis using 3 2 1 by auto 
    qed
  qed
qed

lemma coeff_0_mult[simp]:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "coeff_0 (p \<otimes>\<^bsub>P\<^esub> q) = (coeff_0 p) \<otimes> (coeff_0 q)"
  apply(rule poly_induct[of p])
  apply(simp add: assms)
proof-
  show B:" \<And>p. p \<in> carrier P \<Longrightarrow> degree p = 0 \<Longrightarrow> coeff_0 (p \<otimes>\<^bsub>P\<^esub> q) = coeff_0 p \<otimes> coeff_0 q"
  proof-
    fix p
    assume A0: "p \<in> carrier P"
    assume A1: "degree p = 0"
    show "coeff_0 (p \<otimes>\<^bsub>P\<^esub> q) = coeff_0 p \<otimes> coeff_0 q"
    proof-
      have "p \<otimes>\<^bsub>P\<^esub> q = (lc p) \<odot>\<^bsub>P\<^esub> q"
        using A0 A1  by (simp add: assms(2) lc_deg_0)
      then have 0: "coeff_0 (p \<otimes>\<^bsub>P\<^esub> q) = (lc p) \<otimes> coeff_0 q"
        by (metis A0 P_def UP_mult_closed assms(2) zero_coefficient_def
            coeff_simp1 coeff_smult  leading_coefficient_def lcoeff_closed)
      have 1: "lc p = coeff_0 p"
        using A0   by (simp add: A1 coeff_0_degree_zero)
      then show ?thesis using 0 1 by auto 
    qed
  qed
  show  "\<And>p. (\<And>qa. qa \<in> carrier P \<Longrightarrow> degree qa < degree p \<Longrightarrow> coeff_0 (qa \<otimes>\<^bsub>P\<^esub> q) = coeff_0 qa \<otimes> coeff_0 q) \<Longrightarrow>
         p \<in> carrier P \<Longrightarrow> degree p > 0 \<Longrightarrow> coeff_0 (p \<otimes>\<^bsub>P\<^esub> q) = coeff_0 p \<otimes> coeff_0 q"
  proof-
    fix p
    assume IH: "(\<And>qa. qa \<in> carrier P \<Longrightarrow> degree qa < degree p 
                \<Longrightarrow> coeff_0 (qa \<otimes>\<^bsub>P\<^esub> q) = coeff_0 qa \<otimes> coeff_0 q)"
    show "p \<in> carrier P \<Longrightarrow> degree p > 0 \<Longrightarrow> coeff_0 (p \<otimes>\<^bsub>P\<^esub> q) = coeff_0 p \<otimes> coeff_0 q"
    proof-
      assume A0: "p \<in> carrier P"
      assume A1: "degree p > 0"
      show "coeff_0 (p \<otimes>\<^bsub>P\<^esub> q) = coeff_0 p \<otimes> coeff_0 q"
      proof- 
        have 0: "coeff_0 (p \<otimes>\<^bsub>P\<^esub> q) = coeff_0 ((trunc p) \<otimes>\<^bsub>P\<^esub> q) \<oplus> coeff_0 ((lt p) \<otimes>\<^bsub>P\<^esub> q)"
          by (metis (no_types, hide_lams) A0 P.l_distr P.m_closed assms(2)
              cf_add zero_coefficient_def lt_closed trunc_simps(1) trunc_simps(3))
        have 1: "coeff_0 ((lt p) \<otimes>\<^bsub>P\<^esub> q) = \<zero>"
          by (simp add: A0 A1 assms(2))
        have "degree (trunc p) < degree p" 
          using A0 A1  by (simp add: trunc_degree)
        then have 2: "coeff_0 ((trunc p) \<otimes>\<^bsub>P\<^esub> q) = coeff_0 (trunc p) \<otimes> coeff_0 q"
          using A0 IH  by (simp add: trunc_simps(3))
        then have 3: "coeff_0 (p \<otimes>\<^bsub>P\<^esub> q) = coeff_0 (trunc p) \<otimes> coeff_0 q"
          using 0 1 2 by (simp add: A0  assms(2) zero_coefficient_def trunc_simps(3))
        show ?thesis 
          by (simp add: "3" A0 A1 ctrunc)
      qed
    qed
  qed
qed

lemma coeff_0_zero[simp]:
"coeff_0 \<zero>\<^bsub>P\<^esub> = \<zero>"
  by (metis P_def UP_zero_closed coeff_simp1 coeff_zero zero_coefficient_def)

lemma coeff_0_one[simp]:
"coeff_0 \<one>\<^bsub>P\<^esub> = \<one>"
  using coeff_0_to_poly 
  by (metis P_def R.one_closed monom_one to_polynomial_def)

lemma coeff_0_is_ring_hom:
"coeff_0 \<in> ring_hom P R"
  apply(rule ring_hom_memI)
  apply(auto)
  apply((simp add:  zero_coefficient_def)) done

lemma ct_is_ring_hom[simp]:
"ct \<in> ring_hom P P"
proof-
  have 0: "to_poly \<in> ring_hom R P"
    by (simp add: to_poly_is_ring_hom)
  have 1: "coeff_0 \<in> ring_hom P R"
    by (simp add: coeff_0_is_ring_hom)
  have 2[simp]: "\<And> x. x \<in> carrier P \<Longrightarrow> ct x = to_poly (coeff_0 x)"
    by (simp add: constant_term_def zero_coefficient_def)
  then show ?thesis 
    using ring_hom_compose R.ring_axioms UP_ring coeff_0_is_ring_hom to_poly_is_ring_hom by blast
qed

lemma ct_smult[simp]:
  assumes "f \<in> carrier P"
  assumes "a \<in>  carrier R"
  shows "ct (a \<odot>\<^bsub>P\<^esub> f) = a \<odot>\<^bsub>P\<^esub>(ct f)"
  unfolding constant_term_def
            to_polynomial_def 
  using assms  
  by (metis P_def UP_domain.coeff_simp1 UP_domain_axioms 
      UP_ring.coeff_smult UP_ring_axioms UP_smult_closed cfs_closed monom_mult_smult)

(*if the constant term of f is 0, then f factors by X*)
lemma coeff_0_eq_zero:
  assumes "f \<in> carrier P"
  assumes "coeff_0 f = \<zero>"
  shows "\<exists> g. g \<in> carrier P \<and> (f = X \<otimes>\<^bsub>P\<^esub> g)"
proof-
  have "\<And>n. \<And>p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> coeff_0 p = \<zero> \<Longrightarrow> (\<exists> g. g \<in> carrier P \<and> (p = X \<otimes>\<^bsub>P\<^esub> g))"
  proof-
    fix n
    show "\<And>p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> coeff_0 p = \<zero> \<Longrightarrow> (\<exists> g. g \<in> carrier P \<and> (p = X \<otimes>\<^bsub>P\<^esub> g))"
      proof(induction n)
        case 0
        then have "degree p = 0" 
          using "0.prems"(2) by blast
        then have "p = \<zero>\<^bsub>P\<^esub>" 
          by (simp add: "0.prems"  coeff_0_zero_degree_zero)
        then have  "p = X \<otimes>\<^bsub>P\<^esub> \<zero>\<^bsub>P\<^esub>" 
          by simp
        then show " \<exists>g. g \<in> carrier P \<and> p = X \<otimes>\<^bsub>P\<^esub> g"
          by blast
      next
        case (Suc n)
        fix n
        assume IH: "\<And>p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> coeff_0 p = \<zero> \<Longrightarrow> (\<exists> g. g \<in> carrier P \<and> (p = X \<otimes>\<^bsub>P\<^esub> g))"
        show "p \<in> carrier P \<Longrightarrow> degree p \<le> Suc n \<Longrightarrow> coeff_0 p = \<zero> \<Longrightarrow> \<exists>g. g \<in> carrier P \<and> p = X \<otimes>\<^bsub>P\<^esub> g" 
        proof-
          assume A0: "p \<in> carrier P" and
                 A1: "degree p \<le> Suc n" and 
                 A2: "coeff_0 p = \<zero>"
          show "\<exists>g. g \<in> carrier P \<and> p = X \<otimes>\<^bsub>P\<^esub> g"
          proof(cases "degree p < Suc n")
          case True
          then show ?thesis 
            using A0 A1 A2 IH by auto 
        next
          case False
          then have D: "degree p = Suc n" 
            using A2  A1 by auto
          have C0:"coeff_0 (trunc p) = \<zero>"
            by (simp add: A0 A2 D ctrunc)
          have C1: "degree (trunc p) \<le>n"
            using D A0 P_def UP_domain.trunc_degree UP_domain_axioms by fastforce
          obtain g where g_def : " g \<in> carrier P \<and> (trunc p) = X \<otimes>\<^bsub>P\<^esub> g" 
            using A0 IH C0 C1  trunc_simps(3) by auto
          have LT0: "lt p = (lc p) \<odot>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> Suc n"
            by (simp add: A0 D lt_rep_X_pow)
          then have LT1: "lt p = X \<otimes>\<^bsub>P\<^esub> ((lc p) \<odot>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> n)"
            by (metis (no_types, lifting) A0 P.m_comm P.nat_pow_Suc P.nat_pow_closed 
                P_def X_closed algebra.smult_assoc2 algebra_axioms coeff_simp1 
                 leading_coefficient_def lcoeff_closed smult_closed)
          have "p = (trunc p) \<oplus>\<^bsub>P\<^esub> lt p"
            using trunc_simps A0 by auto 
          then have "p =  X \<otimes>\<^bsub>P\<^esub> g \<oplus>\<^bsub>P\<^esub> X \<otimes>\<^bsub>P\<^esub> ((lc p) \<odot>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> n)"
            using g_def LT1 by auto 
          then have "p = X \<otimes>\<^bsub>P\<^esub> (g \<oplus>\<^bsub>P\<^esub> ((lc p) \<odot>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> n))"
            using A0 P.nat_pow_closed P.r_distr P_def X_closed coeff_simp1 
               g_def leading_coefficient_def lcoeff_closed smult_closed by metis
          then show ?thesis 
            by (metis A0 P.nat_pow_closed P_def UP_a_closed X_closed 
                coeff_simp1  g_def leading_coefficient_def lcoeff_closed smult_closed)
        qed
      qed
    qed
  qed
  then show ?thesis 
    using assms(1) assms(2) by blast
qed

lemma ct_monom[simp]:
  assumes "a \<in> carrier R"
  shows "ct (monom P a (Suc k)) = \<zero>\<^bsub>P\<^esub>"
  unfolding constant_term_def
proof-
  have "(monom P a (Suc k) 0) = \<zero>"
    using assms  P_def coeff_monom coeff_simp1 monom_closed by auto
  then show " to_poly (monom P a (Suc k) 0) = \<zero>\<^bsub>P\<^esub>"
    by (metis UP_zero_closed coeff_0_zero deg_zero to_poly_inverse zero_coefficient_def)
qed

(*The factorization of f by X is unique*)
lemma coeff_0_eq_zero_unique:
  assumes "f \<in> carrier P"
  assumes "g \<in> carrier P \<and> (f = X \<otimes>\<^bsub>P\<^esub> g)"
  shows "\<And> h. h  \<in> carrier P \<and> (f = X \<otimes>\<^bsub>P\<^esub> h) \<Longrightarrow> h = g"
proof-
  fix h
  assume A: "h  \<in> carrier P \<and> (f = X \<otimes>\<^bsub>P\<^esub> h)"
  then have " X \<otimes>\<^bsub>P\<^esub> g =  X \<otimes>\<^bsub>P\<^esub> h"
    using assms(2) by auto
  then show "h = g" using assms 
    by (simp add: assms(2) A local.m_lcancel)
qed

lemma f_minus_ct:
  assumes "f \<in> carrier P"
  shows "coeff_0 (f \<ominus>\<^bsub>P\<^esub> ct f) = \<zero>"
proof-
  have "coeff_0 (f \<ominus>\<^bsub>P\<^esub> ct f) = coeff_0 f \<ominus> coeff_0  (ct f)"
    using assms coeff_0_is_ring_hom 
    by (metis P.minus_closed P_def zero_coefficient_def coeff_minus coeff_simp1 ct_is_poly)
  then show ?thesis 
    using assms apply simp 
    by (metis R.ring_axioms abelian_group.r_neg
        coeff_0_is_ring_hom ring.ring_simprules(14) ring_def ring_hom_closed)
qed


end

definition polynomial_shift where
"polynomial_shift R f = (THE g. g \<in> carrier (UP R) \<and> f \<ominus>\<^bsub>(UP R)\<^esub> (constant_term R) f = X_poly R \<otimes>\<^bsub>UP R\<^esub> g)"

context UP_domain
begin

abbreviation poly_shift where
"poly_shift \<equiv> polynomial_shift R"

lemma poly_shift_prop:
  assumes "f \<in> carrier P"
  assumes "g = poly_shift f"
  shows " g \<in> carrier P \<and> f \<ominus>\<^bsub>P\<^esub> ct f = X \<otimes>\<^bsub>P\<^esub> g"
proof-
  obtain h where h_def: "h \<in> carrier P \<and> f \<ominus>\<^bsub>P\<^esub> ct f = X \<otimes>\<^bsub>P\<^esub> h"
    using f_minus_ct coeff_0_eq_zero assms P.minus_closed ct_is_poly by presburger
  have 0:"(THE g. g \<in> carrier P \<and> f \<ominus>\<^bsub>P\<^esub> ct f = X \<otimes>\<^bsub>P\<^esub> g) = h" 
  proof(rule the_equality)
    show "h \<in> carrier P \<and> f \<ominus>\<^bsub>P\<^esub> ct f = X \<otimes>\<^bsub>P\<^esub> h" 
      using h_def apply auto done
    show "\<And>g. g \<in> carrier P \<and> f \<ominus>\<^bsub>P\<^esub> ct f = X \<otimes>\<^bsub>P\<^esub> g \<Longrightarrow> g = h"
    proof-
      fix k
      assume A: "k \<in> carrier P \<and> f \<ominus>\<^bsub>P\<^esub> ct f = X \<otimes>\<^bsub>P\<^esub> k"
      show "k = h" 
        using coeff_0_eq_zero_unique[of "f \<ominus>\<^bsub>P\<^esub> ct f"] h_def 
        by (metis A UP_mult_closed X_closed)
    qed
  qed
  have "g = (THE g. g \<in> carrier P \<and> f \<ominus>\<^bsub>P\<^esub> ct f = X \<otimes>\<^bsub>P\<^esub> g)"
    using assms(2) unfolding polynomial_shift_def P_def by auto   
  then have "h = g"
    using 0 assms by auto 
  then show ?thesis 
    using h_def by simp
qed

lemma poly_shift_closed[simp]:
  assumes "f \<in> carrier P"
  shows "poly_shift f \<in> carrier P"
  using assms poly_shift_prop by blast 
end

lemma poly_shift_closed_UP_domain[simp]:
  assumes "UP_domain R"
  assumes "f \<in> carrier (UP R)"
  shows "polynomial_shift R f \<in> carrier (UP R)"
    by (simp add: UP_domain.poly_shift_closed assms(1) assms(2))


context UP_domain
begin

lemma poly_shift_id:
  assumes "f \<in> carrier P"
  shows "f \<ominus>\<^bsub>P\<^esub> ct f = X \<otimes>\<^bsub>P\<^esub> poly_shift f"
  using assms poly_shift_prop by blast 

lemma poly_shift_id':
  assumes "f \<in> carrier P"
  shows "f  = ct f \<oplus>\<^bsub>P\<^esub> X \<otimes>\<^bsub>P\<^esub> poly_shift f"
proof-
  have  "f \<ominus>\<^bsub>P\<^esub> ct f = X \<otimes>\<^bsub>P\<^esub> poly_shift f" 
    using poly_shift_id assms by auto 
  then show ?thesis 
    by (metis P.add.inv_solve_right P.minus_closed P.minus_eq UP_a_comm assms(1) ct_is_poly)
qed

lemma poly_shift_degree_zero:
  assumes "p \<in> carrier P"
  assumes "degree p = 0"
  shows "poly_shift p = \<zero>\<^bsub>P\<^esub>"
proof-
  have "p \<ominus>\<^bsub>P\<^esub> ct p = \<zero>\<^bsub>P\<^esub>" 
    using assms  by (metis P.minus_eq P.r_neg constant_term_def to_poly_inverse)
  then have "X \<otimes>\<^bsub>P\<^esub> (poly_shift p) = \<zero>\<^bsub>P\<^esub>" 
    using assms poly_shift_id by auto 
  then show ?thesis 
    using X_closed X_not_zero assms(1) local.integral poly_shift_closed by blast
qed

lemma poly_shift_degree:
  assumes "p \<in> carrier P"
  assumes "degree p >0"
  shows "degree (poly_shift p) = degree p - 1 "
proof-
  have 0: "degree (p \<ominus>\<^bsub>P\<^esub> ct p) = degree p"
    using assms ct_degree  by (simp add: degree_of_difference_diff_degree)
  have 1: "p \<ominus>\<^bsub>P\<^esub> ct p = X \<otimes>\<^bsub>P\<^esub> poly_shift p"
    using assms poly_shift_id by auto
  have 2: "degree (X \<otimes>\<^bsub>P\<^esub> poly_shift p) = 1 + degree(poly_shift p)"
    by (metis "0" "1" P.r_null X_closed X_not_zero assms(1) assms(2)
        deg_mult deg_zero degree_X  nat_less_le poly_shift_closed)
  show ?thesis using 0 1 2  by simp
qed

lemma poly_shift_monom:
  assumes "a \<in> carrier R"
  shows "poly_shift (monom P a (Suc k)) = (monom P a k)"
proof-
  have "(monom P a (Suc k)) = ct (monom P a (Suc k)) \<oplus>\<^bsub>P\<^esub> X \<otimes>\<^bsub>P\<^esub>poly_shift (monom P a (Suc k))"
    using poly_shift_id'[of "monom P a (Suc k)"] assms monom_closed 
    by blast
  then have "(monom P a (Suc k)) = \<zero>\<^bsub>P\<^esub> \<oplus>\<^bsub>P\<^esub> X \<otimes>\<^bsub>P\<^esub>poly_shift (monom P a (Suc k))"
    using assms by simp
  then have "(monom P a (Suc k)) = X \<otimes>\<^bsub>P\<^esub>poly_shift (monom P a (Suc k))"
    using X_closed assms by auto
  then have "X \<otimes>\<^bsub>P\<^esub>(monom P a k) = X \<otimes>\<^bsub>P\<^esub>poly_shift (monom P a (Suc k))"
    by (metis P_def R.l_one R.one_closed X_poly_def assms monom_mult plus_1_eq_Suc)
  then show ?thesis 
    using X_closed X_not_zero assms domain.m_lcancel local.domain_axioms by fastforce
qed

lemma(in UP_domain) poly_shift_add[simp]:
  assumes "f \<in> carrier P"
  assumes "g \<in> carrier P"
  shows "poly_shift (f \<oplus>\<^bsub>P\<^esub> g) = (poly_shift f) \<oplus>\<^bsub>P\<^esub> (poly_shift g)"
proof-
  have  "f \<oplus>\<^bsub>P\<^esub> g = ct(f \<oplus>\<^bsub>P\<^esub> g) \<oplus>\<^bsub>P\<^esub> (X \<otimes>\<^bsub>P\<^esub>poly_shift (f \<oplus>\<^bsub>P\<^esub> g))"
    using assms poly_shift_id'[of "f \<oplus>\<^bsub>P\<^esub>g"] by auto 
  then have 0: "f \<oplus>\<^bsub>P\<^esub> g = (ct f \<oplus>\<^bsub>P\<^esub> ct g) \<oplus>\<^bsub>P\<^esub> (X \<otimes>\<^bsub>P\<^esub>poly_shift (f \<oplus>\<^bsub>P\<^esub> g))"
    using assms(1) assms(2) ct_is_ring_hom ring_hom_add 
    by (metis (mono_tags, lifting))
  have 1: "f = ct f \<oplus>\<^bsub>P\<^esub> (X \<otimes>\<^bsub>P\<^esub>poly_shift (f))"
    using assms poly_shift_id'[of f] by auto 
  have 2: "g = ct g \<oplus>\<^bsub>P\<^esub> (X \<otimes>\<^bsub>P\<^esub>poly_shift (g))"
    using assms poly_shift_id'[of g] by auto 
  have 3: "f \<oplus>\<^bsub>P\<^esub> g = ct f \<oplus>\<^bsub>P\<^esub> (X \<otimes>\<^bsub>P\<^esub>poly_shift (f)) \<oplus>\<^bsub>P\<^esub> ct g \<oplus>\<^bsub>P\<^esub> (X \<otimes>\<^bsub>P\<^esub>poly_shift (g))"
    using 1 2  P.add.m_assoc X_closed assms(1) assms(2) by auto
  have 4: "f \<oplus>\<^bsub>P\<^esub> g = ct f \<oplus>\<^bsub>P\<^esub>  ct g \<oplus>\<^bsub>P\<^esub>  (X \<otimes>\<^bsub>P\<^esub>poly_shift (f)) \<oplus>\<^bsub>P\<^esub> (X \<otimes>\<^bsub>P\<^esub>poly_shift (g))"
    using 3  UP_a_assoc UP_a_comm X_closed assms(1) assms(2) by auto
  have 5: "f \<oplus>\<^bsub>P\<^esub> g = ct f \<oplus>\<^bsub>P\<^esub>  ct g \<oplus>\<^bsub>P\<^esub>  (X \<otimes>\<^bsub>P\<^esub> ((poly_shift (f)) \<oplus>\<^bsub>P\<^esub> poly_shift (g)))"
    by (simp add: "4" P.r_distr UP_a_assoc assms(1) assms(2))
  have 6: "f \<oplus>\<^bsub>P\<^esub> g = (ct f \<oplus>\<^bsub>P\<^esub>  ct g) \<oplus>\<^bsub>P\<^esub>  (X \<otimes>\<^bsub>P\<^esub> ((poly_shift (f)) \<oplus>\<^bsub>P\<^esub> poly_shift (g)))"
    using "5" by blast
  have "(X \<otimes>\<^bsub>P\<^esub> ((poly_shift (f)) \<oplus>\<^bsub>P\<^esub> poly_shift (g))) =  (X \<otimes>\<^bsub>P\<^esub>poly_shift (f \<oplus>\<^bsub>P\<^esub> g))"
    using 0 6 X_closed assms(1) assms(2) by auto
  then show ?thesis 
    by (metis P.add.m_closed P.m_closed P_def UP_domain.coeff_0_eq_zero_unique 
        UP_domain_axioms X_closed assms(1) assms(2) poly_shift_prop)
qed

lemma(in UP_domain) poly_shift_s_mult[simp]:
  assumes "f \<in> carrier P"
  assumes "s \<in> carrier R"
  shows "poly_shift (s \<odot>\<^bsub>P\<^esub>f) = s \<odot>\<^bsub>P\<^esub> (poly_shift f)"
proof-
  have "(s \<odot>\<^bsub>P\<^esub>f) = (ct (s \<odot>\<^bsub>P\<^esub>f)) \<oplus>\<^bsub>P\<^esub>(X \<otimes>\<^bsub>P\<^esub> poly_shift (s \<odot>\<^bsub>P\<^esub>f))"
    using poly_shift_id'[of "(s \<odot>\<^bsub>P\<^esub>f)"] assms(1) assms(2) 
    by blast
  then have 0: "(s \<odot>\<^bsub>P\<^esub>f) = (s \<odot>\<^bsub>P\<^esub>(ct f)) \<oplus>\<^bsub>P\<^esub>(X \<otimes>\<^bsub>P\<^esub> poly_shift (s \<odot>\<^bsub>P\<^esub>f))"
    using assms(1) assms(2) 
    by auto
  have 1: "(s \<odot>\<^bsub>P\<^esub>f) = s \<odot>\<^bsub>P\<^esub> ((ct f) \<oplus>\<^bsub>P\<^esub>  (X \<otimes>\<^bsub>P\<^esub> (poly_shift f)))"
    using assms(1) poly_shift_id' by auto
  have 2:  "(s \<odot>\<^bsub>P\<^esub>f) = (s \<odot>\<^bsub>P\<^esub>(ct f)) \<oplus>\<^bsub>P\<^esub>  (s \<odot>\<^bsub>P\<^esub>(X \<otimes>\<^bsub>P\<^esub> (poly_shift f)))"
    by (simp add: "1" assms(1) assms(2) smult_r_distr)
  have 3:  "(s \<odot>\<^bsub>P\<^esub>f) = (s \<odot>\<^bsub>P\<^esub>(ct f)) \<oplus>\<^bsub>P\<^esub>  (X \<otimes>\<^bsub>P\<^esub> (s \<odot>\<^bsub>P\<^esub>(poly_shift f)))"
    using "2" UP_m_comm X_closed assms(1) assms(2) smult_assoc2 
    by auto
  have 4: "(X \<otimes>\<^bsub>P\<^esub> poly_shift (s \<odot>\<^bsub>P\<^esub>f)) =  (X \<otimes>\<^bsub>P\<^esub> (s \<odot>\<^bsub>P\<^esub>(poly_shift f)))"
    using 3 0  X_closed assms(1) assms(2)
    by auto
  then show ?thesis 
    using X_closed X_not_zero assms(1) assms(2) local.m_lcancel 
    by auto
qed

lemma coeff_0_poly_shift[simp]:
  assumes "f \<in>  carrier P"
  shows "coeff_0 (poly_shift f) = f 1"
proof(rule poly_induct2)
  show "f \<in> carrier P" 
    using assms by auto 
  show " \<And>p. p \<in> carrier P \<Longrightarrow> degree p = 0 \<Longrightarrow> coeff_0 (poly_shift p) = p 1"
    using cf_f coeff_0_degree_zero deg_aboveD poly_shift_degree_zero by force
  show "\<And>p. 0 < degree p \<Longrightarrow> p \<in> carrier P \<Longrightarrow> zero_coefficient (poly_shift (trunc p)) = trunc p 1 
            \<Longrightarrow> zero_coefficient (poly_shift p) = p 1"
  proof-
    fix p
    assume A0: "0 < degree p" and A1: "p \<in> carrier P" and A2: "coeff_0 (poly_shift (trunc p)) = trunc p 1"
    show "coeff_0 (poly_shift p) = p 1"
    proof-
      have "coeff_0 (poly_shift p) = coeff_0 (poly_shift ((trunc p) \<oplus>\<^bsub>P\<^esub> (lt p)))"
        using A1 trunc_simps(1) 
        by auto
      then have "coeff_0 (poly_shift p) = coeff_0 ((poly_shift (trunc p)) \<oplus>\<^bsub>P\<^esub> ((poly_shift (lt p))))"
        by (simp add: A1 lt_closed trunc_simps(3))
      then have 0: "coeff_0 (poly_shift p) = coeff_0 (poly_shift (trunc p)) \<oplus>\<^bsub>R\<^esub> coeff_0 ((poly_shift (lt p)))"
        by (simp add: A1 lt_closed trunc_simps(3))
      show ?thesis 
      proof(cases "degree p = 1")
        case True
        then have "poly_shift (trunc p) = \<zero>\<^bsub>P\<^esub>"
          by (metis A1 P_def UP_domain.trunc_degree UP_domain_axioms
              less_one poly_shift_degree_zero trunc_simps(3))
        then have T0: "coeff_0 (poly_shift p) = coeff_0 ((poly_shift (lt p)))"
          using 0 
          using A1 UP_l_zero \<open>zero_coefficient (poly_shift p) =
                 zero_coefficient (poly_shift (trunc p) \<oplus>\<^bsub>P\<^esub> poly_shift (lt p))\<close> 
              lt_closed poly_shift_closed 
          by presburger
        have T1: "poly_shift (lt p) = monom P (lc p) 0"
          using True
          by (simp add: A1 lc_closed lc_lt poly_shift_monom)
        show ?thesis using T1 T0 
          by (metis A1 True deg_const lc_closed lc_monom 
              leading_coefficient_def zero_coefficient_def)
      next
        case False
        then have F0: "degree p \<ge> 2"
          using A0 by linarith
        obtain k where k_def: "degree p = Suc (Suc k)"
          using F0 
          by (metis A0 False One_nat_def lessE)
        have "lt p = monom P (lc p) (degree p)"
          by (simp add: lc_lt)
        then have "poly_shift (lt p) =  monom P (lc p) (Suc k)"
          by (simp add: A1 k_def lc_closed poly_shift_monom)
        then have "coeff_0 ((poly_shift (lt p))) = \<zero>"
          by (metis A0 A1 \<open>lt p = monom P (lc p) (degree p)\<close> coeff_lt deg_monom 
              lc_closed lt_monom monom_closed monom_zero zero_less_Suc)
        then have F1: "coeff_0 (poly_shift p) = coeff_0 (poly_shift (trunc p))"
          using 0 
          by (metis (no_types, lifting) A1 P.l_zero P_def UP_a_comm UP_domain.coeff_0_add 
              UP_domain.poly_shift_closed UP_domain.trunc_simps(3)
              UP_domain_axioms UP_zero_closed coeff_0_zero)
        have F2: "coeff_0 (poly_shift p) = (trunc p) 1"
          using F1 A2 by auto 
        have "p 1 = trunc p 1"
          using F0 
          by (simp add: A1)
        then show ?thesis 
          by (simp add: F2)
      qed
    qed
  qed
qed


end 


fun poly_shift_iter where
Base:"poly_shift_iter R 0 f = f"|
Step:"poly_shift_iter R (Suc n) f = polynomial_shift R (poly_shift_iter R n f)"

context UP_domain 
begin 

abbreviation shift where
"shift \<equiv>poly_shift_iter R"

lemma shift_closed[simp]:
  assumes "f \<in> carrier P"
  shows "shift n f \<in> carrier P"
proof(induction n)
  case 0
  show "shift 0 f \<in> carrier P" 
    using assms by auto 
next
  case (Suc n)
  fix n
  assume "shift n f \<in> carrier P"
  then show " shift (Suc n) f \<in> carrier P"
    using poly_shift_closed by (metis cring_poly.Step)
qed

end 

lemma shift_closed_UP_domain[simp]:
  assumes "UP_domain R"
  assumes "f \<in> carrier (UP R)"
  shows "poly_shift_iter R n f \<in> carrier (UP R)"
  by (simp add: UP_domain.shift_closed assms(1) assms(2))

(*A Factor of the derivative operator*)

definition n_mult where 
"n_mult R f = (\<lambda>n. [n]\<cdot>\<^bsub>R\<^esub>(f n))"

lemma(in UP_domain) n_mult_closed[simp]:
  assumes "f \<in> carrier P"
  shows "n_mult R f \<in> carrier P"
proof-
  have 0:"bound \<zero> (degree f) (n_mult R f)"
  proof-
    have B: "bound \<zero> (degree f) f"
      using assms P_def coeff_simp1 deg_aboveD by auto
    show ?thesis
    proof
      fix m
      assume A: "degree f < m "
      then have "f m = \<zero>" 
        using B by blast
      then show "n_mult R f m = \<zero>"
        unfolding n_mult_def  by simp
    qed
  qed
  have "n_mult R f \<in> up R"
  proof(rule mem_upI)
    show "\<And>n. n_mult R f n \<in> carrier R"
      unfolding n_mult_def
      using assms   by simp
    show "\<exists>n. bound \<zero> n (n_mult R f)" 
      using 0 by auto
  qed
  then show ?thesis 
    by (simp add: P_def UP_def)
qed

(*The derivative operator*)

definition poly_deriv where
"poly_deriv R p = polynomial_shift R (n_mult R p)"

lemma(in UP_domain) poly_deriv_closed[simp]:
  assumes "p \<in> carrier P"
  shows "poly_deriv R p \<in> carrier P"
  unfolding  poly_deriv_def 
  using assms n_mult_closed[of p]  poly_shift_closed[of "n_mult R p"] 
  by blast

abbreviation(in UP_domain) pderiv where
"pderiv \<equiv> poly_deriv R"

(*Facts about the shift function*)

lemma(in UP_domain) shift_factor0:
  assumes "f \<in> carrier P"
  shows "degree f \<ge> (Suc k) \<Longrightarrow> degree (f \<ominus>\<^bsub>P\<^esub> ((shift (Suc k) f) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc k)))) < (Suc k)"
proof(induction k)
  case 0
  have 0: " f \<ominus>\<^bsub>P\<^esub> (ct f) =  (shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>X"
    by (simp add: UP_m_comm  assms poly_shift_id)
  then have  " f \<ominus>\<^bsub>P\<^esub>(shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>X =    (ct f) "
  proof-
    have " f \<ominus>\<^bsub>P\<^esub> (ct f) \<ominus>\<^bsub>P\<^esub> (shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>X=  (shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>X \<ominus>\<^bsub>P\<^esub> (shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>X"
      using 0   by simp
    then have " f \<ominus>\<^bsub>P\<^esub> (ct f) \<ominus>\<^bsub>P\<^esub> (shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>X = \<zero>\<^bsub>P\<^esub>"
      using UP_cring.UP_cring[of R] assms 
      by (metis "0" P.ring_simprules(4) P_def UP_ring.UP_ring UP_ring_axioms 
          a_minus_def abelian_group.r_neg ct_is_poly ring_def)
    then have " f \<ominus>\<^bsub>P\<^esub> ((ct f) \<oplus>\<^bsub>P\<^esub> (shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>X) = \<zero>\<^bsub>P\<^esub>"
      using assms P.ring_simprules  
      by (metis "0" poly_shift_id poly_shift_id')
    then have " f \<ominus>\<^bsub>P\<^esub> ((shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>X \<oplus>\<^bsub>P\<^esub> (ct f) ) = \<zero>\<^bsub>P\<^esub>"
      by (simp add: P.add.m_comm assms)
    then have "f \<ominus>\<^bsub>P\<^esub> ((shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>X) \<ominus>\<^bsub>P\<^esub> (ct f)= \<zero>\<^bsub>P\<^esub>"
      by (simp add: P.add.m_assoc P.ring_simprules(14) P.ring_simprules(19) assms)
    then show ?thesis 
      by (metis "0" P.add.m_comm P.m_closed P.ring_simprules(14) P.ring_simprules(18) 
          P.ring_simprules(3) X_closed assms ct_is_poly poly_shift_id poly_shift_id' 
          shift_closed)
  qed
  then have  " f \<ominus>\<^bsub>P\<^esub>(shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc 0)) =    (ct f) "
    by simp
  then have " degree (f \<ominus>\<^bsub>P\<^esub>(shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc 0))) < 1"
    using ct_degree[of f] assms   by simp
  then show ?case 
    by blast
next
  case (Suc n)
  fix k
  assume IH: "degree f \<ge> (Suc k) \<Longrightarrow> degree (f \<ominus>\<^bsub>P\<^esub> ((shift (Suc k) f) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc k)))) < (Suc k)"
  show  "degree f \<ge> (Suc (Suc k)) \<Longrightarrow> degree (f \<ominus>\<^bsub>P\<^esub> ((shift (Suc (Suc k)) f) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc (Suc k))))) < (Suc (Suc k))"
  proof-
    obtain n where n_def: "n = Suc k"
      by simp
    have IH': "degree f \<ge> n \<Longrightarrow> degree (f \<ominus>\<^bsub>P\<^esub> ((shift n f) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n))) < n"
      using n_def IH by auto 
    have P: "degree f \<ge> (Suc n) \<Longrightarrow> degree (f \<ominus>\<^bsub>P\<^esub> ((shift (Suc n) f) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc n)))) < (Suc n)"
    proof-
      obtain g where g_def: "g = (f \<ominus>\<^bsub>P\<^esub> ((shift n f) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)))"
        by simp
      obtain s where s_def: "s = shift n f"
        by simp
      obtain s' where s'_def: "s' = shift (Suc n) f"
        by simp
      have P: "g \<in> carrier P" "s \<in> carrier P" "s' \<in> carrier P" "(X[^]\<^bsub>P\<^esub>n) \<in> carrier P"
        using s_def s'_def g_def assms shift_closed[of f n]  
        apply simp 
        apply (simp add: assms s_def)
        apply (simp add: assms s'_def)
        by simp
      
      have g_def': "g = (f \<ominus>\<^bsub>P\<^esub> (s \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)))"
        using g_def s_def by auto 
      assume "degree f \<ge> (Suc n)"
      then have " degree (f \<ominus>\<^bsub>P\<^esub> (s \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n))) < n" 
        using IH' Suc_leD s_def by blast
      then have d_g: "degree g < n" using g_def' by auto 
      have P0: "f \<ominus>\<^bsub>P\<^esub> (s' \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc n))) = ((ct s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) \<oplus>\<^bsub>P\<^esub> g"
      proof-
        have "s = (ct s) \<oplus>\<^bsub>P\<^esub> (X \<otimes>\<^bsub>P\<^esub> s')"
          using s_def s'_def  P_def UP_domain.poly_shift_id' UP_domain_axioms assms shift_closed 
          by (simp add: UP_domain.poly_shift_id')
        then have 0: "g = f \<ominus>\<^bsub>P\<^esub> ((ct s) \<oplus>\<^bsub>P\<^esub> (X \<otimes>\<^bsub>P\<^esub> s')) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)"
          using g_def'  by auto
        then have "g = f \<ominus>\<^bsub>P\<^esub> ((ct s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) \<ominus>\<^bsub>P\<^esub> ((X \<otimes>\<^bsub>P\<^esub> s') \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n))"
          using P cring X_closed 
          by (simp add: P.l_distr P.ring_simprules(19) UP_a_assoc a_minus_def assms)
        then have "g \<oplus>\<^bsub>P\<^esub> ((X \<otimes>\<^bsub>P\<^esub> s') \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) =  f \<ominus>\<^bsub>P\<^esub> ((ct s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n))"
          using P cring X_closed  P.l_distr P.ring_simprules UP_a_assoc a_minus_def assms 
          by auto 
        then have " ((ct s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) =  f \<ominus>\<^bsub>P\<^esub> (g \<oplus>\<^bsub>P\<^esub> ((X \<otimes>\<^bsub>P\<^esub> s') \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)))"
          using P cring X_closed P.ring_simprules UP_a_assoc a_minus_def assms 
          by (simp add: \<open>\<And>y x. \<lbrakk>x \<in> carrier P; y \<in> carrier P\<rbrakk> \<Longrightarrow> x \<oplus>\<^bsub>P\<^esub> (\<ominus>\<^bsub>P\<^esub> x \<oplus>\<^bsub>P\<^esub> y) = y\<close>
            \<open>\<And>z y x. \<lbrakk>x \<in> carrier P; y \<in> carrier P; z \<in> carrier P\<rbrakk> \<Longrightarrow> x \<otimes>\<^bsub>P\<^esub> y \<otimes>\<^bsub>P\<^esub> z = x \<otimes>\<^bsub>P\<^esub> (y \<otimes>\<^bsub>P\<^esub> z)\<close>
            \<open>\<And>z y x. \<lbrakk>x \<in> carrier P; y \<in> carrier P; z \<in> carrier P\<rbrakk> \<Longrightarrow> z \<otimes>\<^bsub>P\<^esub> (x \<oplus>\<^bsub>P\<^esub> y) = z \<otimes>\<^bsub>P\<^esub> x \<oplus>\<^bsub>P\<^esub> z \<otimes>\<^bsub>P\<^esub> y\<close>
            \<open>cring P\<close>)
        then have " ((ct s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) =  f \<ominus>\<^bsub>P\<^esub> (((X \<otimes>\<^bsub>P\<^esub> s') \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) \<oplus>\<^bsub>P\<^esub> g)"
          by (simp add: P(1) P(3) P.add.m_comm)
        then have "((ct s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) =  f \<ominus>\<^bsub>P\<^esub> ((X \<otimes>\<^bsub>P\<^esub> s') \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) \<ominus>\<^bsub>P\<^esub> g"
          by (simp add: P(1) P(3) P.ring_simprules(19) UP_a_assoc a_minus_def assms)
        then have "((ct s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) \<oplus>\<^bsub>P\<^esub> g=  f \<ominus>\<^bsub>P\<^esub> ((X \<otimes>\<^bsub>P\<^esub> s') \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n))"
          by (metis P(1) P(3) P(4) P.add.inv_solve_right P.m_closed P.ring_simprules(14)
              P.ring_simprules(4) P_def UP_domain.X_closed UP_domain_axioms assms)
        then have "((ct s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) \<oplus>\<^bsub>P\<^esub> g=  f \<ominus>\<^bsub>P\<^esub> ((s' \<otimes>\<^bsub>P\<^esub> X) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n))"
          by (simp add: P(3) UP_m_comm)
        then have "((ct s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) \<oplus>\<^bsub>P\<^esub> g=  f \<ominus>\<^bsub>P\<^esub> (s' \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc n)))"
          using P(3) P.nat_pow_Suc2 UP_m_assoc X_closed by auto
        then show ?thesis
          by auto 
      qed
      have P1: "degree (((ct s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) \<oplus>\<^bsub>P\<^esub> g) \<le> n"
      proof-
        have Q0: "degree ((ct s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n))  \<le> n"
        proof(cases "ct s = \<zero>\<^bsub>P\<^esub>")
          case True
          then show ?thesis 
            by (simp add: P(4))
        next
          case False
          then have "degree ((ct s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n))  = degree (ct s) + degree (X[^]\<^bsub>P\<^esub>n) "
            by (simp add: P(2) local.nonzero_pow_nonzero)
          then show ?thesis 
            by (simp add: P(2) ct_degree deg_pow)
        qed
        then show ?thesis 
          using d_g by (simp add: P(1) P(2) P(4))
      qed
      then show ?thesis 
        using s'_def P0 by auto
    qed
    assume "degree f \<ge> (Suc (Suc k)) "
    then show "degree (f \<ominus>\<^bsub>P\<^esub> ((shift (Suc (Suc k)) f) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc (Suc k))))) < (Suc (Suc k))"
      using P by(simp add: n_def)
  qed
qed


lemma(in UP_domain) shift_degree0:
  assumes "f \<in> carrier P"
  shows "degree f >n \<Longrightarrow> Suc (degree (shift (Suc n) f)) = degree (shift n f)"
proof(induction n)
  case 0
  assume B: "0< degree f"
  have 0: "degree (shift 0 f) = degree f"
    by simp
  have 1: "degree f = degree (f \<ominus>\<^bsub>P\<^esub> (ct f))"
    using assms(1) B ct_degree degree_of_difference_diff_degree by auto
  have "(f \<ominus>\<^bsub>P\<^esub> (ct f)) = X \<otimes>\<^bsub>P\<^esub>(shift 1 f)"
    using P_def UP_domain.poly_shift_id UP_domain_axioms assms(1) by auto
  then have "degree (f \<ominus>\<^bsub>P\<^esub> (ct f)) = 1 + (degree (shift 1 f))"
    by (metis P.r_null X_closed X_not_zero \<open>degree f = degree (f \<ominus>\<^bsub>P\<^esub> ct f)\<close> 
        assms(1) B deg_mult deg_zero degree_X gr_implies_not_zero shift_closed)
  then have  "degree (shift 0 f) = 1 + (degree (shift 1 f))"
    using 0 1 by auto 
  then show ?case 
    by simp
next
  case (Suc n)
  fix n 
  assume IH: "(n < degree f \<Longrightarrow> Suc (degree (shift (Suc n) f)) = degree (shift n f))"
  show "Suc n < degree f \<Longrightarrow> Suc (degree (shift (Suc (Suc n)) f)) = degree (shift (Suc n) f)"
  proof-
    assume A: " Suc n < degree f"
    then have 0: "(shift (Suc n) f) = ct ((shift (Suc n) f)) \<oplus>\<^bsub>P\<^esub>  (shift (Suc (Suc n)) f)\<otimes>\<^bsub>P\<^esub>X"
      by (simp add: UP_m_comm assms poly_shift_id')
    have N: "(shift (Suc (Suc n)) f) \<noteq> \<zero>\<^bsub>P\<^esub>"
    proof
      assume C: "shift (Suc (Suc n)) f = \<zero>\<^bsub>P\<^esub>"
      obtain g where g_def: "g = f \<ominus>\<^bsub>P\<^esub>  (shift (Suc (Suc n)) f)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc (Suc n)))"
        by simp
      have C0: "degree g < degree f"
        using g_def assms A 
        by (meson Suc_leI Suc_less_SucD Suc_mono less_trans_Suc shift_factor0)
      have C1: "g = f" 
        using C 
        by (simp add:a_minus_def assms g_def) 
      then show False 
        using C0 by auto 
    qed
    have 1: "degree (shift (Suc n) f) = degree ((shift (Suc n) f) \<ominus>\<^bsub>P\<^esub> ct ((shift (Suc n) f)))"
    proof(cases "degree (shift (Suc n) f) = 0")
      case True
      then show ?thesis 
        by (metis P.ring_simprules(16) a_minus_def 
            assms constant_term_def deg_zero shift_closed to_poly_inverse)
    next
      case False
      then have "degree (shift (Suc n) f) > degree  (ct ((shift (Suc n) f)))"
        by (simp add: assms ct_degree)
      then show ?thesis 
        by (simp add: assms degree_of_difference_diff_degree)
    qed
    have 2: "(shift (Suc n) f) \<ominus>\<^bsub>P\<^esub> ct ((shift (Suc n) f)) =  (shift (Suc (Suc n)) f)\<otimes>\<^bsub>P\<^esub>X"
      using 0 
      by (simp add: UP_m_comm assms poly_shift_id)
    have 3: "degree ((shift (Suc n) f) \<ominus>\<^bsub>P\<^esub> ct ((shift (Suc n) f))) =  degree (shift (Suc (Suc n)) f) + 1"
      using 2 N 
      by (simp add: assms) 
    then show ?thesis using 1 
      by linarith
  qed
qed

lemma(in UP_domain) shift_degree:
  assumes "f \<in> carrier P"
  shows "degree f \<ge> n \<Longrightarrow>  degree (shift n f) + n = degree f"
proof(induction n)
  case 0
  then show ?case 
    by auto
next
  case (Suc n)
  fix n
  assume IH: "(n \<le> degree f \<Longrightarrow> degree (shift n f) + n = degree f)"
  show "Suc n \<le> degree f \<Longrightarrow> degree (shift (Suc n) f) + Suc n = degree f"
  proof-
    assume A: "Suc n \<le> degree f "
    have 0: "degree (shift n f) + n = degree f" 
      using IH A by auto  
    have 1: "degree (shift n f) = Suc (degree (shift (Suc n) f))"
      using A assms shift_degree0 by auto 
    show "degree (shift (Suc n) f) + Suc n = degree f" 
      using 0 1  by simp
  qed
qed

lemma(in UP_domain) shift_degree':
  assumes "f \<in> carrier P"
  shows "degree (shift (degree f) f) = 0"
  using shift_degree assms 
  by fastforce

lemma(in UP_domain) shift_above_degree[simp]:
  assumes "f \<in> carrier P"
  assumes "k > degree f"
  shows "(shift k f) = \<zero>\<^bsub>P\<^esub>"
proof-
  have "\<And>n. shift ((degree f)+ (Suc n)) f = \<zero>\<^bsub>P\<^esub>"
  proof-
    fix n
    show "shift ((degree f)+ (Suc n)) f = \<zero>\<^bsub>P\<^esub>"
    proof(induction n)
      case 0
      have B0:"shift (degree f) f  = ct(shift (degree f) f) \<oplus>\<^bsub>P\<^esub> (shift (degree f + Suc 0) f)\<otimes>\<^bsub>P\<^esub>X"
        by (simp add: UP_m_comm   assms(1) poly_shift_id')
      have B1:"shift (degree f) f = ct(shift (degree f) f)"
        by (simp add: assms(1) constant_term_def shift_degree' to_poly_inverse)
      have B2: "(shift (degree f + Suc 0) f)\<otimes>\<^bsub>P\<^esub>X = \<zero>\<^bsub>P\<^esub>"
        using B0 B1 X_closed assms(1) 
        by auto
      then show ?case 
        using UP_integral X_closed X_not_zero assms(1) shift_closed 
        by blast
    next
      case (Suc n)
      fix n
      assume "shift (degree f + Suc n) f = \<zero>\<^bsub>P\<^esub>"
      then show "shift (degree f + Suc (Suc n)) f = \<zero>\<^bsub>P\<^esub>"
        by (simp add: poly_shift_degree_zero)
    qed
  qed
  then show ?thesis 
    using assms(2) less_iff_Suc_add by auto
qed

lemma(in UP_domain) shift_ct0:
  assumes "f \<in> carrier P"
  shows "coeff_0 (shift 1 f) = f 1"
  using assms by auto

lemma(in UP_domain) X_mult_cf[simp]:
  assumes "p \<in> carrier P"
  shows "(p \<otimes>\<^bsub>P\<^esub> X) (k+1) = p k"
  unfolding X_poly_def
  using assms 
  by (metis P.m_closed P_def R.l_one R.one_closed UP_domain.cfs_closed 
      UP_domain.coeff_simp1 UP_domain_axioms UP_m_comm 
      UP_ring.monom_closed UP_ring_axioms coeff_monom_mult)
 
lemma(in UP_domain) X_pow_cf[simp]:
  assumes "p \<in> carrier P"
  shows "(p \<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub>(n::nat)) (n + k) = p k"
proof-
  have P: "\<And>f. f \<in> carrier P \<Longrightarrow> (f \<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub>(n::nat)) (n + k) = f k"
  proof(induction n)
    show "\<And>f. f \<in> carrier P \<Longrightarrow> (f \<otimes>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> (0::nat)) (0 + k) = f k"
    proof-
      fix f
      assume B0: "f \<in> carrier P"
      show "(f \<otimes>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> (0::nat)) (0 + k) = f k"
        by (simp add: B0)
    qed
    fix n
    fix f
    assume IH: "(\<And>f. f \<in> carrier P \<Longrightarrow> (f \<otimes>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> n) (n + k) = f k)"
    assume A0: " f \<in> carrier P"
    show "(f \<otimes>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc n) (Suc n + k) = f k"
    proof-
      have 0: "(f \<otimes>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> n)(n + k) = f k"
        using A0 IH by simp
      have 1: "((f \<otimes>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> n)\<otimes>\<^bsub>P\<^esub>X) (Suc n + k) = (f \<otimes>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> n)(n + k)"
        using X_mult_cf A0 P.m_closed P.nat_pow_closed 
              Suc_eq_plus1 X_closed add_Suc by presburger
      have 2: "(f \<otimes>\<^bsub>P\<^esub> (X [^]\<^bsub>P\<^esub> n \<otimes>\<^bsub>P\<^esub>X)) (Suc n + k) = (f \<otimes>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> n)(n + k)"
        using 1 
        by (simp add: A0 P.m_assoc  )
      then show ?thesis 
        by (simp add: "0")
    qed
  qed
  show ?thesis using assms P[of p] by auto 
qed

lemma(in UP_domain) shift_ct:
  assumes "p \<in> carrier P"
  shows "(shift k p) n = p (k + n)"
proof(cases "degree p < k")
  case True
  then show ?thesis 
    by (metis P_def UP_domain.shift_above_degree UP_domain_axioms UP_ring.deg_aboveD UP_ring_axioms
        UP_zero_closed assms coeff_0_zero coeff_simp1 deg_nzero_nzero gr_zeroI 
        trans_less_add1 zero_coefficient_def)
next
  case False
  then have B: "k \<le>degree p" 
    by auto 
  show ?thesis 
  proof(cases "k = 0")
    case True
    then show ?thesis 
      by simp
  next
    case False
    then obtain m where n_def: "k = Suc m"
      by (meson lessI less_Suc_eq_0_disj)
    obtain g where g_def: "g = p \<ominus>\<^bsub>P\<^esub>(shift k p)\<otimes>\<^bsub>P\<^esub>X[^]\<^bsub>P\<^esub>k"
      by simp
    have "degree g < k"
    using B g_def n_def False shift_factor0[of p m] 
           assms by blast
  then have "(p \<ominus>\<^bsub>P\<^esub>(shift k p)\<otimes>\<^bsub>P\<^esub>X[^]\<^bsub>P\<^esub>k) (k + n) = \<zero>"
    using g_def 
    by (metis P.m_closed P.minus_closed P.nat_pow_closed P_def 
        UP_ring.deg_aboveD UP_ring_axioms X_closed assms cf_f shift_closed trans_less_add1)
  then have 0: "(cf p (k+n)) \<ominus>\<^bsub>R\<^esub> ((cf (shift k p)\<otimes>\<^bsub>P\<^esub>X[^]\<^bsub>P\<^esub>k) (k +n)) = \<zero>"
    using X_closed assms coeff_minus cf_f by auto
  then have "cf p (k+n) = cf ((shift k p)\<otimes>\<^bsub>P\<^esub>X[^]\<^bsub>P\<^esub>k) (k +n) "
  proof-
    have  "(cf p (k+n)) \<ominus>\<^bsub>R\<^esub> ((cf (shift k p)\<otimes>\<^bsub>P\<^esub>X[^]\<^bsub>P\<^esub>k) (k +n)) \<oplus> ((cf (shift k p)\<otimes>\<^bsub>P\<^esub>X[^]\<^bsub>P\<^esub>k) (k +n))
           = \<zero> \<oplus> ((cf (shift k p)\<otimes>\<^bsub>P\<^esub>X[^]\<^bsub>P\<^esub>k) (k +n))"
      using 0 by auto 
    then have "(cf p (k+n)) \<oplus> \<ominus>\<^bsub>R\<^esub> ((cf (shift k p)\<otimes>\<^bsub>P\<^esub>X[^]\<^bsub>P\<^esub>k) (k +n)) \<oplus> ((cf (shift k p)\<otimes>\<^bsub>P\<^esub>X[^]\<^bsub>P\<^esub>k) (k +n))
           = ((cf (shift k p)\<otimes>\<^bsub>P\<^esub>X[^]\<^bsub>P\<^esub>k) (k +n))"
      by (metis "0" R.l_zero X_pow_cf a_minus_def assms coeff_closed cf_f shift_closed)
    then show ?thesis 
      by (metis "0" P.m_closed P.minus_closed P.nat_pow_closed P_def R.add.inv_solve_right R.minus_eq UP_domain.cfs_closed UP_domain_axioms X_closed \<open>(p \<ominus>\<^bsub>P\<^esub> shift k p \<otimes>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> k) (k + n) = \<zero>\<close> assms cf_f shift_closed)
  qed
  then have 1: "p (k+n) = ((shift k p)\<otimes>\<^bsub>P\<^esub>X[^]\<^bsub>P\<^esub>k) (k +n) "
    by (simp add:   assms cf_f)
  have 2: "((shift k p)\<otimes>\<^bsub>P\<^esub>X[^]\<^bsub>P\<^esub>k) (k +n)  = (shift k p) n"
    by (simp add: assms)
  then show ?thesis using 1 by auto 
qed
qed


(*Function which obtains the first n+1 terms of f, in ascending order of degree*)


definition degree_n_or_less_terms where
"degree_n_or_less_terms R n f 
  = (f \<ominus>\<^bsub>(UP R)\<^esub> ((poly_shift_iter R (Suc n) f) \<otimes>\<^bsub>UP R\<^esub>((X_poly R)[^]\<^bsub>UP R\<^esub>(Suc n))))"

abbreviation(in UP_domain) deg_leq where
"deg_leq n f \<equiv> degree_n_or_less_terms R n f"

lemma(in UP_domain) deg_leq_closed:
  assumes "f \<in> carrier P"
  shows "deg_leq n f \<in> carrier P"
  by (metis (no_types, hide_lams) P.m_closed P.minus_closed P.nat_pow_closed
      P_def X_closed assms degree_n_or_less_terms_def shift_closed)

lemma(in UP_domain) deg_leq_id:
  assumes "f \<in> carrier P"
  shows "f \<ominus>\<^bsub>P\<^esub> (deg_leq k f) = ((shift (Suc k) f) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc k)))"
proof-
  have "f \<ominus>\<^bsub>P\<^esub> (deg_leq k f) =f \<ominus>\<^bsub>P\<^esub> (f \<ominus>\<^bsub>P\<^esub> ((shift (Suc k) f) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc k))))"
    using assms deg_leq_closed degree_n_or_less_terms_def[of R k f]
    unfolding P_def by simp
  then have "f \<ominus>\<^bsub>P\<^esub> (deg_leq k f) =f \<ominus>\<^bsub>P\<^esub> f \<oplus>\<^bsub>P\<^esub> ((shift (Suc k) f) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc k)))"
    using assms cring a_minus_def 
    by (simp add: a_minus_def P.add.inv_mult_group P.add.m_assoc P.add.m_comm  )
  then show ?thesis 
    using assms a_minus_def by (simp add: a_minus_def P.ring_simprules(16)  )
qed

lemma(in UP_domain) deg_leq_id':
  assumes "f \<in> carrier P"
  shows "f = (deg_leq k f)  \<oplus>\<^bsub>P\<^esub>((shift (Suc k) f) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc k)))"
  using deg_leq_id assms 
  by (metis P.add.inv_solve_right P.m_closed P.nat_pow_closed P_def 
      X_closed a_minus_def deg_leq_closed degree_n_or_less_terms_def shift_closed)

lemma(in UP_domain) deg_leq_deg:
  assumes "f \<in> carrier P"
  assumes "degree f > k"
  shows "degree (deg_leq k f) \<le> k"
proof-
  have 0: "degree f \<ge> Suc k"
      using assms 
      by (simp add: Suc_le_eq)
  show "degree (deg_leq k f) \<le> k"
    by (metis "0" P_def assms(1) degree_n_or_less_terms_def less_Suc_eq_le shift_factor0) 
qed

lemma(in UP_domain) deg_leq_zero[simp]:
  assumes "f \<in> carrier P"
  assumes "degree f > 0"
  shows "deg_leq 0 f = ct f"
proof-
  have "f = ct f \<oplus>\<^bsub>P\<^esub> (X \<otimes>\<^bsub>P\<^esub> (shift (Suc 0) f))"
    using assms poly_shift_id' 
    by simp
  then have "f = ct f \<oplus>\<^bsub>P\<^esub> (X [^]\<^bsub>UP R\<^esub> Suc 0 \<otimes>\<^bsub>P\<^esub> (shift (Suc 0) f))"
    using P.nat_pow_eone P_def X_closed  by auto
  then show ?thesis 
  unfolding degree_n_or_less_terms_def 
  by (metis One_nat_def P.add.inv_solve_right P.m_closed P.nat_pow_eone P_def UP_m_comm
      X_closed a_minus_def assms(1) ct_is_poly shift_closed)
qed

lemma(in UP_domain) deg_leq_iter:
  assumes "f \<in> carrier P"
  assumes "k < degree f "
  shows "deg_leq (Suc k) f = (deg_leq k f) \<oplus>\<^bsub>P\<^esub> (f (Suc k))\<odot>\<^bsub>P\<^esub>X[^]\<^bsub>P\<^esub>(Suc k)"
proof-
  have "shift (Suc (Suc k)) f \<otimes>\<^bsub>P\<^esub> X  =
         shift (Suc k) f \<ominus>\<^bsub>P\<^esub> ct(shift (Suc k) f )"
    using poly_shift_id'[of "shift (Suc k) f"] assms  
    by (metis P_def UP_domain.poly_shift_id UP_domain_axioms 
        UP_m_comm X_closed cring_poly.Step shift_closed)
  then have "shift (Suc (Suc k)) f \<otimes>\<^bsub>P\<^esub> X \<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> (Suc k)  =
         (shift (Suc k) f \<ominus>\<^bsub>P\<^esub> ct(shift (Suc k) f ))\<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> (Suc k)"
    by auto
  then have "shift (Suc (Suc k)) f \<otimes>\<^bsub>P\<^esub> X \<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> (Suc k)  =
         (shift (Suc k) f \<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> (Suc k) )\<ominus>\<^bsub>P\<^esub> ct(shift (Suc k) f )\<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> (Suc k)"
    using P.add.m_comm P.m_closed P.nat_pow_closed a_minus_def P.ring_simprules(13)
          P_def UP_domain.ct_is_poly UP_domain.shift_closed UP_domain_axioms  
          UP_ring_axioms X_closed a_minus_def assms(1) poly_shift_id' 
    by (metis (no_types, lifting) P.ring_simprules(26) P.ring_simprules(3))
  then have 0: "\<ominus>\<^bsub>P\<^esub> shift (Suc (Suc k)) f \<otimes>\<^bsub>P\<^esub> (X \<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> (Suc k))  =
         \<ominus>\<^bsub>P\<^esub>((shift (Suc k) f \<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> (Suc k) )\<ominus>\<^bsub>P\<^esub> ct(shift (Suc k) f )\<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> (Suc k))"
    by (simp add: P.l_minus P.m_assoc   assms(1))
  then have "\<ominus>\<^bsub>P\<^esub> shift (Suc (Suc k)) f \<otimes>\<^bsub>P\<^esub> (X \<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> (Suc k))  =
         \<ominus>\<^bsub>P\<^esub>(shift (Suc k) f \<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> (Suc k) )\<oplus>\<^bsub>P\<^esub> ct(shift (Suc k) f )\<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> (Suc k)"
    using a_minus_def 
    by (simp add:0 a_minus_def P.minus_add UP_m_comm   assms(1))
  then have 1: "f \<ominus>\<^bsub>P\<^esub> shift (Suc (Suc k)) f \<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> (Suc (Suc k))  =
         f \<ominus>\<^bsub>P\<^esub>(shift (Suc k) f \<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> (Suc k) )\<oplus>\<^bsub>P\<^esub> ct(shift (Suc k) f )\<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> (Suc k)"
    using a_minus_def 
    by (metis (no_types, hide_lams) P.add.inv_closed P.l_minus P.nat_pow_Suc2
        P.nat_pow_closed UP_a_assoc UP_mult_closed X_closed assms(1) ct_is_poly shift_closed)
  have 2: "ct(shift (Suc k) f )\<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> (Suc k) =  coeff_0(shift (Suc k) f )\<odot>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> (Suc k)"
    unfolding zero_coefficient_def constant_term_def to_polynomial_def   
    by (metis P.nat_pow_closed P_def cfs_closed X_closed assms(1) monom_mult_is_smult shift_closed)
  then have "f \<ominus>\<^bsub>P\<^esub> shift (Suc (Suc k)) f \<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> (Suc (Suc k))  =
         f \<ominus>\<^bsub>P\<^esub>(shift (Suc k) f \<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> (Suc k) )\<oplus>\<^bsub>P\<^esub> coeff_0(shift (Suc k) f )\<odot>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> (Suc k)"
    using 1 2 by simp
  then show ?thesis 
    unfolding degree_n_or_less_terms_def P_def  zero_coefficient_def 
    using shift_ct[of f "Suc k" 0] 
    by (simp add:  assms(1))
qed

lemma(in UP_domain) deg_leq_0[simp]:
  assumes "f \<in> carrier P"
  shows "deg_leq 0 f = ct f"
  by (metis (no_types, lifting) One_nat_def P.l_null P.nat_pow_eone 
      P.r_zero P.ring_simprules(21) P_def UP_domain.shift_above_degree 
      UP_domain_axioms UP_ring X_closed assms constant_term_def 
      deg_leq_zero degree_n_or_less_terms_def lessI neq0_conv 
      ring.ring_simprules(14) to_poly_inverse)

lemma(in UP_domain) deg_leq_degree_f[simp]:
  assumes "f \<in>  carrier P"
  assumes "degree f > 0"
  shows "deg_leq (degree f) f = f"
  unfolding degree_n_or_less_terms_def 
  by (metis P.l_null P.nat_pow_closed P.r_zero P.ring_simprules(21) 
      P_def X_closed a_minus_def assms(1) lessI shift_above_degree)

definition linear_part where
"linear_part R f = degree_n_or_less_terms R 1 f"

abbreviation(in UP_domain) lin_part where
"lin_part \<equiv> linear_part R"

lemma(in UP_domain) lin_part_id:
  assumes "f \<in> carrier P"
  shows "lin_part f = (ct f) \<oplus>\<^bsub>P\<^esub> (f 1)\<odot>\<^bsub>P\<^esub>X"
  unfolding linear_part_def
proof-
  have "deg_leq 0 f = ct f"
    using assms by simp
  then show "deg_leq 1 f = ct f \<oplus>\<^bsub>P\<^esub> f 1 \<odot>\<^bsub>P\<^esub> X" 
    by (metis (no_types, lifting) One_nat_def P.nat_pow_Suc2 P.nat_pow_eone P.r_zero
        P.ring_simprules(11) P.ring_simprules(16) P_def UP_domain.X_closed 
        UP_domain.coeff_0_poly_shift UP_domain.deg_leq_iter UP_domain.shift_above_degree
        UP_domain_axioms UP_zero_closed a_minus_def assms coeff_0_degree_zero 
        coeff_0_eq_zero_unique constant_term_def deg_leq_closed deg_leq_id deg_leq_id' 
        deg_zero lc_deg_0 neq0_conv poly_shift_closed poly_shift_id poly_shift_iter.simps(2)
        to_poly_inverse zero_less_Suc)
qed

lemma(in UP_domain) lin_part_eq:
  assumes "f \<in> carrier P"
  shows "f = lin_part f \<oplus>\<^bsub>P\<^esub> (shift 2 f) \<otimes>\<^bsub>P\<^esub>X[^]\<^bsub>P\<^esub>(2::nat)"
  unfolding linear_part_def degree_n_or_less_terms_def
  using assms 
  by (metis Suc_1 deg_leq_id' degree_n_or_less_terms_def)

(*Constant term of a substitution*)

context UP_domain
begin

lemma coeff_0_eval:
  assumes "f \<in> carrier P"
  shows "coeff_0 f = fun_of f \<zero>"
proof-
  have "f = ct f \<oplus>\<^bsub>P\<^esub> (X \<otimes>\<^bsub>P\<^esub> shift 1 f)"
    by (simp add: assms poly_shift_id')
  then have "fun_of f \<zero> = fun_of (ct f) \<zero> \<oplus> fun_of (X \<otimes>\<^bsub>P\<^esub> shift 1 f) \<zero>"
    by (metis P.m_closed R.zero_closed X_closed assms ct_is_poly fun_of_plus shift_closed)
  then have "fun_of f \<zero> = fun_of (ct f) \<zero> \<oplus> (fun_of X \<zero>)\<otimes> fun_of ( shift 1 f) \<zero>"
    by (simp add:  assms)
  then have "fun_of f \<zero> = fun_of (ct f) \<zero> \<oplus> \<zero>\<otimes> fun_of ( shift 1 f) \<zero>"
    by simp
  then have "fun_of f \<zero> = fun_of (ct f) \<zero>"
    using assms fun_of_closed by auto
  then show ?thesis 
    unfolding constant_term_def zero_coefficient_def
    using fun_of_to_poly[of "f 0" \<zero>]
          P_def UP_domain.cfs_closed UP_domain_axioms assms 
    by force
qed

lemma ct_of_sub:
  assumes "f \<in> carrier P"
  assumes "g \<in> carrier P"
  shows "coeff_0 (f of g) = fun_of f (coeff_0 g)"
proof(rule poly_induct2[of f])
  show "f \<in> carrier P"
    using assms by auto 
  show " \<And>p. p \<in> carrier P \<Longrightarrow>
         degree p = 0 \<Longrightarrow> 
          zero_coefficient (p of g) = fun_of p (zero_coefficient g)"
  proof-
    fix p assume B: "p \<in> carrier P" "degree p = 0"
    show "zero_coefficient (p of g) = fun_of p (zero_coefficient g)"
      using B assms(2) 
      by (metis P_def R.zero_closed UP_domain.sub_const UP_domain_axioms coeff_0_eval
          coeff_simp1 fun_of_closed fun_of_to_poly lcoeff_closed to_poly_inverse) 
  qed
  show "\<And>p. 0 < degree p \<Longrightarrow>
         p \<in> carrier P \<Longrightarrow>
         zero_coefficient (trunc p of g) = fun_of (trunc p) (zero_coefficient g) \<Longrightarrow>
         zero_coefficient (p of g) = fun_of p (zero_coefficient g)"
  proof-
    fix p assume A0: "0 < degree p" "p \<in> carrier P"
           and   IH: "zero_coefficient (trunc p of g) = fun_of (trunc p) (zero_coefficient g)"
    show "zero_coefficient (p of g) = fun_of p (zero_coefficient g)"
    proof-
      have 0: "p of g = (trunc p) of g \<oplus>\<^bsub>P\<^esub> (lt p) of g" 
        by (metis A0(2) assms(2) lt_closed sub_add trunc_simps(1) trunc_simps(3))
      then have 1: "coeff_0 (p of g) = coeff_0 ((trunc p) of g) \<oplus> coeff_0 ((lt p) of g)"
        by (simp add: A0(2) assms(2) lt_closed sub_closed trunc_simps(3))
      have 2: "coeff_0 ((trunc p) of g) = fun_of (trunc p) (coeff_0 g)"
        using IH 
        by blast
      have 3: "coeff_0 ((lt p) of g) = fun_of (lt p) (coeff_0 g)"
      proof-
        have "coeff_0 ((lt p) of g) = fun_of ((lt p) of g) \<zero>"
          by (simp add: A0(2) assms(2) coeff_0_eval lt_closed sub_closed)
        then have "coeff_0 ((lt p) of g) = (lc p) \<otimes>((fun_of g) \<zero>)[^](degree p)"
          by (metis (no_types, lifting) A0(1) A0(2) P_def R.zero_closed 
              UP_cring.deg_nzero_nzero UP_cring_axioms UP_domain.fun_of_monom 
              UP_domain_axioms UP_ring.monom_zero UP_ring_axioms assms(2) 
              degree_lt fun_of_closed fun_of_sub lc_closed lc_lt lt_closed nat_less_le)
        then have "coeff_0 ((lt p) of g) = (lc p)\<otimes> (coeff_0 g)[^](degree p)" 
          using assms(2) coeff_0_eval by auto
        then show ?thesis 
        using A0(2) assms(2) coeff_0_eval lt_closed sub_closed by auto
      qed
      have 4: "coeff_0 (p of g) =  fun_of (trunc p) (coeff_0 g) \<oplus>fun_of (lt p) (coeff_0 g)"
        by (simp add: "1" "3" IH)
      then show ?thesis 
        by (metis (no_types, lifting) A0(2) assms(2) coeff_0_is_ring_hom fun_of_plus 
            lt_closed ring_hom_closed trunc_simps(1) trunc_simps(3))
    qed
  qed
qed

(*Evaluation of linear part*)

lemma fun_of_lin_part:
  assumes "f \<in> carrier P"
  assumes "b \<in> carrier R"
  shows "fun_of (lin_part f) b = (f 0) \<oplus> (f 1) \<otimes> b"
proof-
  have "fun_of (lin_part f) b = fun_of (ct f \<oplus>\<^bsub>P\<^esub> f 1 \<odot>\<^bsub>P\<^esub> X) b  "
  using lin_part_id[of f] 
  by (simp add: assms(1))
  then have "fun_of (lin_part f) b = fun_of (ct f) b \<oplus> fun_of( f 1 \<odot>\<^bsub>P\<^esub> X) b " 
    by (simp add:   assms(1) assms(2))
  then have "fun_of (lin_part f) b = f 0 \<oplus>  (f 1) \<otimes>fun_of( X) b " 
    using X_closed assms(1) assms(2) by fastforce
  then show ?thesis 
    by (simp add: assms(2))
qed
(*Constant term of taylor expansion*)

lemma Taylor_coeff_0:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "coeff_0 (T\<^bsub>a\<^esub> f) = fun_of f a"
  unfolding taylor_expansion_def
  using ct_of_sub assms 
  using P_def UP_domain.coeff_0_eval UP_domain_axioms X_plus_closed 
  by fastforce

lemma(in UP_domain) Taylor_eq_1:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "(T\<^bsub>a\<^esub> f) \<ominus>\<^bsub>P\<^esub> (deg_leq 1 (T\<^bsub>a\<^esub> f)) = (shift (2::nat) (T\<^bsub>a\<^esub> f))\<otimes>\<^bsub>P\<^esub> (X[^]\<^bsub>P\<^esub>(2::nat))"
  using deg_leq_id[of "(T\<^bsub>a\<^esub> f)" 1] Taylor_closed[of f a] assms Suc_1 
  by presburger

lemma(in UP_domain) Taylor_deg_1:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "f of (X_plus a) = (lin_part (T\<^bsub>a\<^esub> f)) \<oplus>\<^bsub>P\<^esub> (shift (2::nat) (T\<^bsub>a\<^esub> f))\<otimes>\<^bsub>P\<^esub> (X[^]\<^bsub>P\<^esub>(2::nat))"
  using Taylor_eq_1[of f a]
  unfolding taylor_expansion_def linear_part_def
  using One_nat_def X_plus_closed assms(1) 
        assms(2) deg_leq_id' numeral_2_eq_2 sub_closed 
  by presburger

lemma(in UP_domain) Taylor_deg_1_eval:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "c = fun_of (shift (2::nat) (T\<^bsub>a\<^esub> f)) b"
  assumes "fa = fun_of f a"
  assumes "f'a = deriv f a"
  shows "fun_of f (b \<oplus> a) = fa \<oplus> (f'a \<otimes> b) \<oplus> (c \<otimes> b[^](2::nat))"
proof-
  have 0: "fun_of f (b \<oplus> a) = fun_of (f of (X_plus a)) b"
    using fun_of_sub assms 
    by (metis Taylor_eval taylor_expansion_def)
  have 1: "fun_of (lin_part (T\<^bsub>a\<^esub> f)) b = fa \<oplus> (f'a \<otimes> b) "
    using assms fun_of_lin_part[of "(T\<^bsub>a\<^esub> f)" b]  
    by (metis Taylor_closed Taylor_coeff_0 derivative_def zero_coefficient_def)
  have 2: "(T\<^bsub>a\<^esub> f) = (lin_part (T\<^bsub>a\<^esub> f)) \<oplus>\<^bsub>P\<^esub> ((shift 2 (T\<^bsub>a\<^esub> f))\<otimes>\<^bsub>P\<^esub>X[^]\<^bsub>P\<^esub>(2::nat))"
    using lin_part_eq[of "(T\<^bsub>a\<^esub>f)"]
    using assms(1) assms(2) by fastforce
  then have "fun_of (T\<^bsub>a\<^esub>f) b = fa \<oplus> (f'a \<otimes> b) \<oplus> fun_of ((shift 2 (T\<^bsub>a\<^esub> f))\<otimes>\<^bsub>P\<^esub>X[^]\<^bsub>P\<^esub>(2::nat)) b"
    using 1 2 
    by (metis P.m_closed P.nat_pow_closed Taylor_closed X_closed
        assms(1) assms(2) assms(3) deg_leq_closed fun_of_plus linear_part_def shift_closed)
  then have  "fun_of (T\<^bsub>a\<^esub>f) b = fa \<oplus> (f'a \<otimes> b) \<oplus> c \<otimes> fun_of (X[^]\<^bsub>P\<^esub>(2::nat)) b"
    by (simp add: assms(1) assms(2) assms(3) assms(4))
  then have 3: "fun_of f (b \<oplus> a)= fa \<oplus> (f'a \<otimes> b) \<oplus> c \<otimes> fun_of (X[^]\<^bsub>P\<^esub>(2::nat)) b"
    using Taylor_eval assms(1) assms(2) assms(3) by auto
  have "fun_of (X[^]\<^bsub>P\<^esub>(2::nat)) b = b[^](2::nat)"
    by (metis P.nat_pow_Suc2 P.nat_pow_eone R.nat_pow_Suc2 
        R.nat_pow_eone Suc_1 UP_domain.fun_of_X UP_domain_axioms 
        X_closed assms(3) fun_of_mult)
  then show ?thesis 
    using 3 by auto 
qed

lemma(in UP_domain) Taylor_deg_1_eval':
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "c = fun_of (shift (2::nat) (T\<^bsub>a\<^esub> f)) b"
  assumes "fa = fun_of f a"
  assumes "f'a = deriv f a"
  shows "fun_of f (a \<oplus> b) = fa \<oplus> (f'a \<otimes> b) \<oplus> (c \<otimes> b[^](2::nat))"
  using R.add.m_comm Taylor_deg_1_eval assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) 
  by auto


lemma(in UP_domain) Taylor_deg_1_eval'':
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "c = fun_of (shift (2::nat) (T\<^bsub>a\<^esub> f)) (\<ominus>b)"
  shows "fun_of f (a \<ominus> b) = (fun_of f a) \<ominus> (deriv f a \<otimes> b) \<oplus> (c \<otimes> b[^](2::nat))"
proof-
  have "\<ominus>b \<in> carrier R"
    using assms 
    by blast
  then have 0: "fun_of f (a \<ominus> b) = (fun_of f a)\<oplus> (deriv f a \<otimes> (\<ominus>b)) \<oplus> (c \<otimes> (\<ominus>b)[^](2::nat))"
  unfolding a_minus_def
  using Taylor_deg_1_eval'[of f a "\<ominus>b" c "(fun_of f a)" "deriv f a"] assms
  by auto 
  have 1: "\<ominus> (deriv f a \<otimes> b) = (deriv f a \<otimes> (\<ominus>b))"
    using assms 
    by (simp add: R.r_minus derivative_closed)
  have 2: "(c \<otimes> b[^](2::nat)) = (c \<otimes> (\<ominus>b)[^](2::nat))"
    using assms 
    by (metis R.add.inv_closed R.add.inv_solve_right R.l_zero R.nat_pow_Suc2 
        R.nat_pow_eone R.zero_closed Suc_1 UP_ring_axioms UP_ring_def
        ring.ring_simprules(26) ring.ring_simprules(27))
  show ?thesis 
    using 0 1 2 
    unfolding a_minus_def
    by simp 
qed

lemma(in UP_domain) Taylor_deg_1_expansion:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "c = fun_of (shift (2::nat) (T\<^bsub>a\<^esub> f)) (b \<ominus> a)"
  assumes "fa = fun_of f a"
  assumes "f'a = deriv f a"
  shows "fun_of f (b) = fa \<oplus> f'a \<otimes> (b \<ominus> a) \<oplus> (c \<otimes> (b \<ominus> a)[^](2::nat))"
proof-
  obtain b' where b'_def: "b'= b \<ominus> a "
    by simp
  then have b'_def': "b = b' \<oplus> a"
    using assms 
    by (metis R.add.inv_solve_right R.minus_closed R.minus_eq)
  have "fun_of f (b' \<oplus> a) = fa \<oplus> (f'a \<otimes> b') \<oplus> (c \<otimes> b'[^](2::nat))" 
    using assms Taylor_deg_1_eval[of f a b' c fa f'a]  b'_def 
    by blast
  then have "fun_of f (b) = fa \<oplus> (f'a \<otimes> b') \<oplus> (c \<otimes> b'[^](2::nat))" 
    using b'_def' 
    by auto 
  then show "fun_of f (b) = fa \<oplus> f'a \<otimes> (b \<ominus> a) \<oplus> c \<otimes> (b \<ominus> a) [^] (2::nat)"
    using b'_def
    by auto   
qed

(*Basic Properties of deriv and pderiv*)

lemma n_mult_degree_bound:
  assumes "f \<in> carrier P"
  shows "degree (n_mult R f) \<le> degree f"
proof-
  have "bound \<zero>  (degree f)  (n_mult R f) "
  proof
    show " \<And>m. degree f < m \<Longrightarrow> n_mult R f m = \<zero>"
    proof-
      fix m
      assume A: "degree f < m"
      show "n_mult R f m = \<zero>"
      proof-
        have "f m = \<zero>"
          using assms A  P_def coeff_simp1 deg_aboveD by auto
        then show ?thesis 
          unfolding n_mult_def 
          using assms 
          by simp
      qed
    qed
  qed
  then show ?thesis using assms 
    by (metis (full_types) P_def bound_below coeff_simp1
        deg_belowI lcoeff_nonzero_deg n_mult_closed)
qed

lemma pderiv_deg_0[simp]:
  assumes "f \<in> carrier P"
  assumes "degree f = 0"
  shows "pderiv f = \<zero>\<^bsub>P\<^esub>"
proof-
  have "degree (n_mult R f) = 0"
    using P_def UP_domain.n_mult_degree_bound UP_domain_axioms assms(1) assms(2) by fastforce
  then show ?thesis 
    unfolding poly_deriv_def 
    by (simp add: assms(1) poly_shift_degree_zero)
qed

lemma deriv_deg_0[simp]:
  assumes "f \<in> carrier P"
  assumes "degree f = 0"
  assumes "a \<in> carrier R"
  shows "deriv f a = \<zero>"
  unfolding derivative_def
            taylor_expansion_def
  using assms P_def X_plus_closed coeff_simp1 deg_belowI
  by force

lemma shift_monom:
  assumes "a \<in> carrier R"
  shows "poly_shift (a \<odot>\<^bsub>P\<^esub> (X[^]\<^bsub>P\<^esub>(Suc n))) = a\<odot>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)"
  using assms monom_rep_X_pow poly_shift_monom by auto

lemma monom_coeff:
  assumes "a \<in> carrier R"
  shows "(a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> (n::nat)) k = (if (k = n) then a else \<zero>)"
  unfolding X_poly_def
proof-
  have "(a \<odot>\<^bsub>P\<^esub> monom (UP R) \<one> 1 [^]\<^bsub>P\<^esub> n) k = (a \<odot>\<^bsub>P\<^esub> monom (UP R) \<one> n ) k"
    using assms 
    by (metis P_def R.one_closed R.r_one UP_domain.monom_rep_X_pow 
        UP_domain_axioms X_poly_def monom_mult_smult)
  then show "(a \<odot>\<^bsub>P\<^esub> monom (UP R) \<one> 1 [^]\<^bsub>P\<^esub> n) k = (if k = n then a else \<zero>)"
    by (metis P.nat_pow_closed P_def UP_ring.coeff_monom UP_ring_axioms 
        UP_smult_closed X_closed X_poly_def assms coeff_simp1 monom_rep_X_pow)
qed

lemma pderiv_monom:
  assumes "a \<in> carrier R"
  shows "pderiv (a \<odot>\<^bsub>P\<^esub> (X[^]\<^bsub>P\<^esub>(Suc n))) = ([Suc n]\<cdot>a)\<odot>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)"
proof-
  have "n_mult R (a \<odot>\<^bsub>P\<^esub> (X[^]\<^bsub>P\<^esub>(Suc n))) = ([Suc n]\<cdot>a) \<odot>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc n))"
  proof
    fix x
    show "n_mult R (a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc n) x = ([Suc n] \<cdot> a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc n) x"
      unfolding n_mult_def
    proof(cases "x = Suc n")
      show "x = Suc n \<Longrightarrow> [x] \<cdot> (a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc n) x = ([Suc n] \<cdot> a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc n) x"
      proof-
        assume "x = Suc n"
        then have "[x] \<cdot> (a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc n) x = [Suc n] \<cdot> (a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc n) (Suc n)"
          by simp
        then have "[x] \<cdot> (a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc n) x = [Suc n] \<cdot> a"
          using assms monom_coeff  \<open>x = Suc n\<close> 
          by presburger
        then show ?thesis 
          using R.add.nat_pow_closed \<open>x = Suc n\<close> assms monom_coeff
          by presburger
      qed
      show "x \<noteq> Suc n \<Longrightarrow> [x] \<cdot> (a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc n) x = ([Suc n] \<cdot> a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc n) x"
      proof-
        assume A: "x \<noteq>Suc n"
        have "[x] \<cdot> ((a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc n) x) = \<zero>" 
          using A R.add.nat_pow_one assms monom_coeff 
          by presburger  
        then show ?thesis 
          by (metis A R.add.nat_pow_closed assms monom_coeff)
      qed
    qed
  qed
  then show ?thesis 
    unfolding poly_deriv_def  
    using assms shift_monom 
    by auto
qed

lemma deriv_monom:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "deriv (a \<odot>\<^bsub>P\<^esub> (X[^]\<^bsub>P\<^esub>(Suc n))) b =  ([Suc n]\<cdot>a)\<otimes>(b[^]n)"
proof(induction n)
  show "deriv (a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc 0) b = [Suc 0] \<cdot> a \<otimes> b [^] (0::nat)"
    unfolding derivative_def taylor_expansion_def
  proof-
    have LHS0: "(a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc 0 of X_plus b) = (a \<odot>\<^bsub>P\<^esub> X_plus b)"
    proof-
      have "X [^]\<^bsub>P\<^esub> Suc 0 = X"
        by simp
      then show ?thesis 
        by (simp add:assms(1) assms(2) sub_smult)
    qed
    have LHS: "(a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc 0 of X_plus b) 1 = a"
    proof-
      have 0: " (a \<odot>\<^bsub>P\<^esub> X_plus b) 1 = a \<otimes> (X_plus b) 1"
        using assms 
        by (metis (no_types, lifting) R.integral_iff UP_smult_closed X_plus_closed cfs_closed
          coeff_0_poly_shift coeff_0_zero deg_smult degree_of_X_plus lc_scalar_mult 
          leading_coefficient_def poly_shift_degree_zero)
      have " (a \<odot>\<^bsub>P\<^esub> X_plus b) 1 = a \<otimes> \<one>"
      proof-
        have 00: "(X \<oplus>\<^bsub>UP R\<^esub> to_poly b) 1 = (X 1) \<oplus> (to_poly b) 1"
          using P_def X_closed assms(2) cf_add to_poly_is_poly by auto
        have "(X \<oplus>\<^bsub>UP R\<^esub> to_poly b) 1 = \<one>"
        proof-
          have "X 1 = \<one>"
            unfolding  X_poly_def
            by (metis One_nat_def P_def R.one_closed X_closed 
                X_poly_def coeff_0_one coeff_0_poly_shift monom_one poly_shift_monom)
          have "to_poly b 1 = \<zero>"
            by (metis assms(2) coeff_0_poly_shift coeff_0_zero degree_to_poly
                poly_shift_degree_zero to_poly_is_poly)
          then show ?thesis 
            using "00" \<open>X 1 = \<one>\<close> by auto
        qed
        then show ?thesis 
          by (metis "0" X_poly_plus_def)
      qed
      then show ?thesis 
        using LHS0 assms(1) by auto
    qed
    have RHS: "[Suc 0] \<cdot> a \<otimes> b [^] (0::nat) = a"
      by (simp add: assms(1))
    show "(a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc 0 of X_plus b) 1 = [Suc 0] \<cdot> a \<otimes> b [^] (0::nat)"
      using LHS RHS 
      by auto 
  qed
  show "\<And>n. deriv (a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc n) b = [Suc n] \<cdot> a \<otimes> b [^] n
           \<Longrightarrow> deriv (a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc (Suc n)) b = [Suc (Suc n)] \<cdot> a \<otimes> b [^] Suc n"
  proof-
    fix n
    assume IH: "deriv (a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc n) b = [Suc n] \<cdot> a \<otimes> b [^] n"
    show "deriv (a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc (Suc n)) b = [Suc (Suc n)] \<cdot> a \<otimes> b [^] Suc n"
      unfolding derivative_def taylor_expansion_def
    proof-
      have A0: "(a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc (Suc n) of X_plus b) = a \<odot>\<^bsub>P\<^esub> (X_plus b)[^]\<^bsub>P\<^esub> Suc (Suc n)"
        by (metis P.nat_pow_closed P_def UP_domain.monom_rep_X_pow UP_domain_axioms 
            UP_pre_univ_prop.eval_monom X_plus_closed assms(1) assms(2) cring_poly.compose_def
            monom_mult_is_smult to_poly_UP_pre_univ_prop to_polynomial_def)
      have A1: "(a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc (Suc n) of X_plus b) = a \<odot>\<^bsub>P\<^esub> ((X_plus b)[^]\<^bsub>P\<^esub>(Suc n) \<otimes>\<^bsub>P\<^esub> X_plus b)"
        using A0  by simp
      have A2: "(a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc (Suc n) of X_plus b) 
                  = a \<odot>\<^bsub>P\<^esub> ((X_plus b)[^]\<^bsub>P\<^esub>(Suc n)\<otimes>\<^bsub>P\<^esub>X \<oplus>\<^bsub>P\<^esub> (X_plus b)[^]\<^bsub>P\<^esub>(Suc n)\<otimes>\<^bsub>P\<^esub> (to_poly b))"
        using A1 unfolding X_poly_plus_def 
        by (metis P.nat_pow_closed P.r_distr P_def X_closed X_plus_closed X_poly_plus_def assms(2) to_poly_is_poly)
      have A3: "(a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc (Suc n) of X_plus b) 
                  = a \<odot>\<^bsub>P\<^esub> ((X_plus b)[^]\<^bsub>P\<^esub>(Suc n)\<otimes>\<^bsub>P\<^esub>X) \<oplus>\<^bsub>P\<^esub> (a \<otimes>b) \<odot>\<^bsub>P\<^esub>(X_plus b)[^]\<^bsub>P\<^esub>(Suc n)"
        using A2 
        by (metis (no_types, lifting) P.m_closed P.nat_pow_closed P_def UP_domain_axioms 
            X_closed X_plus_closed assms(1) assms(2) smult_assoc1 smult_r_distr 
            to_poly_is_poly to_poly_mult_simp(2))
      have A4: "(a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc (Suc n) of X_plus b) 1 
                  = (a \<odot>\<^bsub>P\<^esub> ((X_plus b)[^]\<^bsub>P\<^esub>(Suc n)\<otimes>\<^bsub>P\<^esub>X)) 1 \<oplus> ((a \<otimes>b) \<odot>\<^bsub>P\<^esub>(X_plus b)[^]\<^bsub>P\<^esub>(Suc n)) 1"
        using A3 
        by (simp add: assms(1) assms(2))
      have A5: "(a \<odot>\<^bsub>P\<^esub> ((X_plus b)[^]\<^bsub>P\<^esub>(Suc n)\<otimes>\<^bsub>P\<^esub>X)) 1 =  a \<otimes> b [^] Suc n"
      proof-
        have A50: "(a \<odot>\<^bsub>P\<^esub> ((X_plus b)[^]\<^bsub>P\<^esub>(Suc n)\<otimes>\<^bsub>P\<^esub>X)) 1 = a \<otimes> ((((X_plus b)[^]\<^bsub>P\<^esub>(Suc n)\<otimes>\<^bsub>P\<^esub>X)) 1)"
          using UP_ring.coeff_smult cf_f P.m_closed P.nat_pow_closed P_def 
            UP_ring_axioms UP_smult_closed  X_closed X_plus_closed assms(1) assms(2) 
          by (metis coeff_simp1)
        have A51: "((((X_plus b)[^]\<^bsub>P\<^esub>(Suc n)\<otimes>\<^bsub>P\<^esub>X)) 1) = ((X_plus b)[^]\<^bsub>P\<^esub>(Suc n)) 0"
          by (metis One_nat_def P.nat_pow_closed Suc_eq_plus1 X_mult_cf X_plus_closed assms(2))
        have A52: " ((X_plus b)[^]\<^bsub>P\<^esub>(Suc n)) 0 =  b [^] Suc n"
        proof-
          have " (X[^]\<^bsub>P\<^esub>(Suc n)) of (X_plus b) = ((X_plus b)[^]\<^bsub>P\<^esub>(Suc n)) "
            unfolding compose_def X_poly_def
            using P.nat_pow_closed P_def  UP_domain_axioms 
            UP_pre_univ_prop.eval_monom X_plus_closed assms(1) assms(2) 
            monom_mult_is_smult to_poly_UP_pre_univ_prop to_polynomial_def 
            by (metis R.one_closed UP_domain.monom_rep_X_pow UP_smult_one X_closed X_poly_def)
          then have "((X[^]\<^bsub>P\<^esub>(Suc n)) of (X_plus b)) 0 = ((X_plus b)[^]\<^bsub>P\<^esub>(Suc n)) 0"
            by auto 
          then have "(fun_of ((X[^]\<^bsub>P\<^esub>(Suc n)))) ((X_plus b) 0) = ((X_plus b)[^]\<^bsub>P\<^esub>(Suc n)) 0"
            using ct_of_sub
            unfolding zero_coefficient_def
            by (simp add:  assms(2))
          then have A520:"(fun_of ((X[^]\<^bsub>P\<^esub>(Suc n)))) b = ((X_plus b)[^]\<^bsub>P\<^esub>(Suc n)) 0"
            by (metis P.nat_pow_closed Taylor_coeff_0 X_closed 
                \<open>X [^]\<^bsub>P\<^esub> Suc n of X_plus b = X_plus b [^]\<^bsub>P\<^esub> Suc n\<close> 
                assms(2) taylor_expansion_def zero_coefficient_def)
          have "(fun_of ((X[^]\<^bsub>P\<^esub>(Suc n)))) b = b[^](Suc n)"
            using fun_of_monom[of \<one> b "Suc n"]
            by (simp add: assms(2) monom_rep_X_pow)
          then have "b[^](Suc n)= ((X_plus b)[^]\<^bsub>P\<^esub>(Suc n)) 0"
            using A520 by auto 
          then show ?thesis by auto 
        qed
        show ?thesis 
          using A52 A51 A50 
          by simp
      qed
      have A6: "((a \<otimes>b) \<odot>\<^bsub>P\<^esub>(X_plus b)[^]\<^bsub>P\<^esub>(Suc n)) 1 = [(Suc n)] \<cdot> a \<otimes> b [^] Suc n"
      proof-
        have "((a \<otimes>b) \<odot>\<^bsub>P\<^esub>(X_plus b)[^]\<^bsub>P\<^esub>(Suc n)) 1 = b \<otimes> ((a\<odot>\<^bsub>P\<^esub>(X_plus b)[^]\<^bsub>P\<^esub>(Suc n)) 1)"
        proof-
          have "((a \<otimes>b) \<odot>\<^bsub>P\<^esub>(X_plus b)[^]\<^bsub>P\<^esub>(Suc n)) 1 = (a \<otimes>b) \<otimes>((X_plus b)[^]\<^bsub>P\<^esub>(Suc n)) 1"
            using coeff_smult cf_f 
            by (simp add:  assms(1) assms(2))
          then have "((a \<otimes>b) \<odot>\<^bsub>P\<^esub>(X_plus b)[^]\<^bsub>P\<^esub>(Suc n)) 1 = b \<otimes> (a \<otimes>((X_plus b)[^]\<^bsub>P\<^esub>(Suc n)) 1)"
            by (simp add: R.m_assoc R.m_lcomm assms(1) assms(2))
          then show ?thesis
            using coeff_smult cf_f 
            by (simp add: assms(1) assms(2))
        qed
        then have "((a \<otimes>b) \<odot>\<^bsub>P\<^esub>(X_plus b)[^]\<^bsub>P\<^esub>(Suc n)) 1 = b \<otimes> ([(Suc n)] \<cdot> a \<otimes> b [^] n)"
          using IH
          unfolding derivative_def taylor_expansion_def compose_def
          by (metis P.nat_pow_closed P_def UP_domain.monom_rep_X_pow UP_domain_axioms 
              UP_pre_univ_prop.eval_monom X_plus_closed assms(1) assms(2) 
              to_poly_UP_pre_univ_prop to_poly_mult_simp(1))
        then have "((a \<otimes>b) \<odot>\<^bsub>P\<^esub>(X_plus b)[^]\<^bsub>P\<^esub>(Suc n)) 1 = ([(Suc n)] \<cdot> a \<otimes> b [^] n) \<otimes>b"
          by (simp add: R.m_comm assms(1) assms(2))
        then have "((a \<otimes>b) \<odot>\<^bsub>P\<^esub>(X_plus b)[^]\<^bsub>P\<^esub>(Suc n)) 1 =  ([(Suc n)] \<cdot> a \<otimes> b [^] n \<otimes>b)"
          by blast
        then show ?thesis 
          by (simp add: R.m_assoc assms(1) assms(2))
      qed
      then show "(a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc (Suc n) of X_plus b) 1 = [Suc (Suc n)] \<cdot> a \<otimes> b [^] Suc n"
        using A5 A6 A4 
        by (metis R.add.nat_pow_Suc2 R.add.nat_pow_closed
            R.l_distr R.nat_pow_closed assms(1) assms(2)) 
    qed
  qed
qed

lemma pderiv_eval_deriv_monom:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "fun_of (pderiv (a \<odot>\<^bsub>P\<^esub> (X[^]\<^bsub>P\<^esub>(Suc n)))) b = deriv (a \<odot>\<^bsub>P\<^esub> (X[^]\<^bsub>P\<^esub>(Suc n))) b"
  using deriv_monom[of a b n] pderiv_monom[of a n] assms
  by (metis P.nat_pow_closed P.r_null P_def R.add.nat_pow_closed R.integral_iff
      R.nat_pow_closed UP_domain.monom_rep_X_pow UP_domain_axioms UP_zero_closed
      X_closed coeff_0_eval coeff_0_zero deg_nzero_nzero degree_0_imp_constant0  
      fun_of_monom to_poly_inverse to_poly_mult_simp(2) zero_coefficient_def)

lemma pderiv_eval_deriv_lt:
  assumes "f \<in> carrier P"
  assumes "b \<in> carrier R"
  assumes "degree f > 0"
  shows "fun_of (pderiv (lt f)) b = deriv (lt f) b"
proof-
  obtain n where n_def: "Suc n = degree f"
    using assms gr0_conv_Suc by auto
  then have "lt f = (lc f) \<odot>\<^bsub>P\<^esub> (X[^]\<^bsub>P\<^esub> (Suc n))"
    by (simp add: assms(1) lt_rep_X_pow)
  then show ?thesis using pderiv_eval_deriv_monom
    by (simp add: assms(1) assms(2) lc_closed)
qed

lemma n_mult_add:
  assumes "f \<in> carrier P"
  assumes "g \<in> carrier P"
  shows " n_mult R (f \<oplus>\<^bsub>P\<^esub> g) = (n_mult R f) \<oplus>\<^bsub>P\<^esub> (n_mult R g)"
proof
  fix x
  show "n_mult R (f \<oplus>\<^bsub>P\<^esub> g) x = (n_mult R f \<oplus>\<^bsub>P\<^esub> n_mult R g) x"
  proof-
    have "n_mult R (f \<oplus>\<^bsub>P\<^esub> g) x = [x] \<cdot> (f \<oplus>\<^bsub>P\<^esub> g) x"
      unfolding n_mult_def by auto 
    then have "n_mult R (f \<oplus>\<^bsub>P\<^esub> g) x = [x] \<cdot> (f x \<oplus> g x)"
      by (simp add: assms(1) assms(2))
    then show ?thesis 
      by (metis (mono_tags, lifting) R.add.nat_pow_distr 
          assms(1) assms(2) cf_add cfs_closed n_mult_closed n_mult_def)
  qed
qed

lemma pderiv_add:
  assumes "f \<in> carrier P"
  assumes "g \<in> carrier P"
  shows " pderiv (f \<oplus>\<^bsub>P\<^esub> g) = (pderiv f) \<oplus>\<^bsub>P\<^esub> (pderiv g)"
  unfolding poly_deriv_def 
  using n_mult_add poly_shift_add assms 
  by simp

lemma deriv_add:
  assumes "f \<in> carrier P"
  assumes "g \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "deriv (f \<oplus>\<^bsub>P\<^esub> g) a = (deriv f a) \<oplus> (deriv g a)"
  unfolding derivative_def
  unfolding taylor_expansion_def
  using sub_add[of "X_plus a" f g]
  by (metis X_plus_closed assms(1) assms(2) assms(3) cf_add sub_closed)

lemma pderiv_eval_deriv:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "deriv f a = fun_of (pderiv f) a"
proof(rule poly_induct2[of f])
  show "f \<in> carrier P" using assms by auto 
  show "\<And>p. p \<in> carrier P \<Longrightarrow> degree p = 0 \<Longrightarrow> deriv p a = fun_of (pderiv p) a" 
    by (metis R.zero_closed UP_domain.fun_of_to_poly UP_domain_axioms UP_zero_closed 
        assms(2) coeff_0_zero deg_zero deriv_deg_0 pderiv_deg_0 to_poly_inverse 
        zero_coefficient_def)
  show "\<And>p. 0 < degree p \<Longrightarrow> p \<in> carrier P \<Longrightarrow> deriv (trunc p) a = fun_of (pderiv (trunc p)) a 
            \<Longrightarrow> deriv p a = fun_of (pderiv p) a"
  proof-
    fix p
    assume A: "0 < degree p" " p \<in> carrier P" 
    assume IH : "deriv (trunc p) a = fun_of (pderiv (trunc p)) a"
    show "deriv p a = fun_of (pderiv p) a"
    proof-
      have 0: "pderiv p = pderiv (trunc p) \<oplus>\<^bsub>P\<^esub> pderiv (lt p)"
        by (metis A(2) lt_closed pderiv_add trunc_simps(1) trunc_simps(3))
      have 1: "deriv p a = (deriv (trunc p) a) \<oplus> (deriv (lt p) a)"
        by (metis A(2) assms(2) deriv_add lt_closed trunc_simps(1) trunc_simps(3))
      then show ?thesis using IH  pderiv_eval_deriv_lt
        by (metis "0" A(1) A(2) P_def UP_domain.fun_of_plus 
            UP_domain_axioms assms(2) lt_closed poly_deriv_closed trunc_simps(3))
    qed
  qed
qed


lemma nmult_smult[simp]:
  assumes "a \<in> carrier R"
  assumes "f \<in> carrier P"
  shows "n_mult R (a \<odot>\<^bsub>P\<^esub> f) = a \<odot>\<^bsub>P\<^esub> (n_mult R f)"
  unfolding n_mult_def
proof
  fix n
  show "[n] \<cdot> (a \<odot>\<^bsub>P\<^esub> f) n = (a \<odot>\<^bsub>P\<^esub> (\<lambda>n. [n] \<cdot> f n)) n"
  proof-
    have LHS: "[n] \<cdot> (a \<odot>\<^bsub>P\<^esub> f) n = a \<otimes> [n] \<cdot> f n "
      using cf_f R.add_pow_rdistr assms(1) assms(2) coeff_smult 
      by auto
    have RHS: "(a \<odot>\<^bsub>P\<^esub> (\<lambda>n. [n] \<cdot> f n)) n =  a \<otimes> [n] \<cdot> f n "
    proof-
      have "(\<lambda>n. [n] \<cdot> f n) \<in> carrier P"
        using n_mult_closed[of f] n_mult_def[of R f] assms(2) 
        by auto 
      then show ?thesis 
        using assms  coeff_smult cf_f 
        by simp
    qed
    show ?thesis 
      using LHS RHS 
      by auto 
  qed
qed

lemma pderiv_smult[simp]:
  assumes "a \<in> carrier R"
  assumes "f \<in> carrier P"
  shows "pderiv (a \<odot>\<^bsub>P\<^esub> f) = a \<odot>\<^bsub>P\<^esub> (pderiv f)"
  unfolding poly_deriv_def
  using assms by simp

end

definition poly_root_divide where
"poly_root_divide R f a =  compose R (polynomial_shift R (taylor_expansion R a f)) (X_poly_minus R a)"

definition poly_root_remainder where
"poly_root_remainder R f a = constant_term R  (taylor_expansion R a f)"

context UP_domain
begin

abbreviation div_by where 
"div_by \<equiv> poly_root_divide R"

lemma div_by_closed[simp]:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "div_by f a \<in> carrier P"
  using assms 
  unfolding poly_root_divide_def 
  by simp


abbreviation rem where 
"rem \<equiv> poly_root_remainder R"

lemma rem_closed[simp]:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "rem f a \<in> carrier P"
  using assms 
  unfolding poly_root_remainder_def 
  by simp

lemma rem_deg[simp]:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "degree (rem f a) = 0"
  by (simp add: assms(1) assms(2) ct_degree poly_root_remainder_def)

lemma remainder_theorem:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "g = div_by f a"
  assumes "r = rem f a"
  shows "f = r \<oplus>\<^bsub>P\<^esub> (X_minus a) \<otimes>\<^bsub>P\<^esub> g "
proof-
  have 0: "T\<^bsub>a\<^esub>f = (ct (T\<^bsub>a\<^esub>f)) \<oplus>\<^bsub>P\<^esub> X \<otimes>\<^bsub>P\<^esub> (poly_shift (T\<^bsub>a\<^esub>f))"
    using poly_shift_id'[of "T\<^bsub>a\<^esub>f"] assms 
    by simp
  have 1: "T\<^bsub>a\<^esub>f of (X_minus a) = (ct (T\<^bsub>a\<^esub>f)) \<oplus>\<^bsub>P\<^esub> (X_minus a) \<otimes>\<^bsub>P\<^esub> (poly_shift (T\<^bsub>a\<^esub>f) of (X_minus a))"
    using 0 
    by (smt P_def UP_domain.Taylor_closed UP_domain.ct_is_poly UP_domain_axioms
        UP_mult_closed X_closed X_minus_closed X_sub0 assms(1) assms(2) ct_degree 
        poly_shift_prop sub_add sub_const sub_mult)
  have 2: "f = (ct (T\<^bsub>a\<^esub>f)) \<oplus>\<^bsub>P\<^esub> (X_minus a) \<otimes>\<^bsub>P\<^esub> (poly_shift (T\<^bsub>a\<^esub>f) of (X_minus a))"
    using 1 Taylor_id[of a f] assms 
    by simp 
  then show ?thesis
    using assms
    unfolding poly_root_divide_def poly_root_remainder_def
    by auto 
qed

lemma factor_theorem:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "g = div_by f a"
  assumes "fun_of f a = \<zero>"
  shows "f = (X_minus a) \<otimes>\<^bsub>P\<^esub> g "
proof-
  have "rem f a = to_poly (fun_of f a)"
    using assms 
    by (metis Taylor_coeff_0 constant_term_def poly_root_remainder_def zero_coefficient_def)
  then have "rem f a = \<zero>\<^bsub>P\<^esub>"
    using assms 
    by (metis UP_zero_closed coeff_0_zero deg_zero to_poly_inverse zero_coefficient_def)
  then have "f = \<zero>\<^bsub>P\<^esub> \<oplus>\<^bsub>P\<^esub>(X_minus a) \<otimes>\<^bsub>P\<^esub> g "
    using remainder_theorem assms 
    by fastforce
  then show ?thesis 
    by (metis P.l_zero P.m_closed X_minus_closed assms(1) assms(2) assms(3) div_by_closed)
qed

lemma geom_quot:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
assumes "p = X[^]\<^bsub>P\<^esub> (Suc n) \<oplus>\<^bsub>P\<^esub> (to_poly (\<ominus> (b[^](Suc n))))"
assumes "g = div_by p b"
shows "a[^](Suc n) \<ominus>b[^] (Suc n) = (a \<ominus> b) \<otimes> (fun_of g a)"
proof-
  have "p = (X_minus b) \<otimes>\<^bsub>P\<^esub> g"
  proof-
    have 0: "fun_of (X[^]\<^bsub>P\<^esub> (Suc n)) b = b[^](Suc n) "
      using assms by simp 
    have "fun_of p b = \<zero>"
      using 0 assms  P.nat_pow_closed R.add.inv_closed R.nat_pow_closed 
            R.r_neg X_closed assms(2) fun_of_plus fun_of_to_poly to_poly_is_poly 
      by presburger
    then show ?thesis 
      using assms 
      by (simp add: factor_theorem to_poly_is_poly)
  qed
  have LHS: "fun_of p a = a[^](Suc n) \<ominus> b[^](Suc n)"
    using assms 
    by (metis (no_types, lifting) P.nat_pow_closed R.nat_pow_closed
        UP_cring_axioms UP_cring_def X_closed a_minus_def cring.cring_simprules(3)
        fun_of_X_pow fun_of_plus fun_of_to_poly to_poly_is_poly)
  have RHS: "fun_of ((X_minus b) \<otimes>\<^bsub>P\<^esub> g) a= (a \<ominus> b) \<otimes> (fun_of g a)"
    by (simp add: assms to_poly_is_poly)
  show ?thesis using RHS LHS 
    by (simp add: \<open>p = X_minus b \<otimes>\<^bsub>P\<^esub> g\<close>)
qed

end

definition geometric_quotient where
"geometric_quotient R n a b = function_of R (poly_root_divide R ((X_poly R)[^]\<^bsub>UP R\<^esub> (Suc n) \<oplus>\<^bsub>UP R\<^esub> (to_polynomial R (\<ominus>\<^bsub>R\<^esub> (b[^]\<^bsub>R\<^esub>(Suc n))))) b) a"

context UP_domain 

begin 
lemma geom_quot_id:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "a[^](Suc n) \<ominus>b[^] (Suc n) = (a \<ominus> b) \<otimes> (geometric_quotient R n a b)"
  using assms geometric_quotient_def geom_quot 
  by (simp add: geometric_quotient_def P_def)

lemma geom_quot_closed[simp]:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "(geometric_quotient R n a b) \<in> carrier R"
  by (metis P.nat_pow_closed P.semiring_axioms P_def R.nat_pow_closed 
      UP_domain.div_by_closed UP_domain.fun_of_closed UP_domain_axioms  
      X_closed algebra.R_cring algebra_axioms assms(1) assms(2)
      cring.cring_simprules(3) geometric_quotient_def semiring.semiring_simprules(1)
      to_poly_is_poly)

lemma fun_of_lt_diff: 
    assumes "a \<in> carrier R"
    assumes "b \<in> carrier R"
    assumes "f \<in> carrier P"
    shows "\<exists>c. c \<in> carrier R\<and> (fun_of (lt f) a) \<ominus>  (fun_of (lt f) b) = (a \<ominus> b) \<otimes>c"
proof(cases "degree f = 0")
  case True
  then have "(fun_of (lt f) a) \<ominus>  (fun_of (lt f) b) = \<zero>"
    using assms 
    by (metis P_def R.add.inv_solve_right R.l_zero R.ring_simprules(14) 
        R.zero_closed constant_term_def degree_0_imp_constant0 fun_of_ct  
        lt_deg_0 to_poly_inverse)
  then have "\<zero>\<in> carrier R \<and>(fun_of (lt f) a) \<ominus>  (fun_of (lt f) b) = (a \<ominus> b) \<otimes>\<zero>"
    using assms 
    by simp
  then show ?thesis by blast 
next
  case False
  then obtain k where k_def: "Suc k = degree f"
    using less_iff_Suc_add by auto
  then have "lt f = (lc f)\<odot>\<^bsub>P\<^esub>X[^]\<^bsub>P\<^esub>(Suc k)"
    by (simp add: assms(3) lt_rep_X_pow)
  then have 0: "(fun_of (lt f) a) = (lc f)\<otimes>a[^](Suc k)"
    by (simp add: assms(1) assms(3) lc_closed)
  then have 1: "(fun_of (lt f) b) = (lc f)\<otimes>b[^](Suc k)"
    using P.nat_pow_closed \<open>lt f = lc f \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc k\<close> assms(2) assms(3) lc_closed 
    by fastforce
  then have "(fun_of (lt f) a)  \<ominus> (fun_of (lt f) b) = (lc f)\<otimes>a[^](Suc k) \<ominus> (lc f)\<otimes>b[^](Suc k)"
    by (simp add: "0")
  then have "(fun_of (lt f) a)  \<ominus> (fun_of (lt f) b) =(lc f)\<otimes> (a[^](Suc k) \<ominus> b[^](Suc k))"
    by (simp add: R.ring_simprules(23) R.ring_simprules(27) 
        a_minus_def assms(1) assms(2) assms(3) lc_closed)
  then have "(fun_of (lt f) a)  \<ominus> (fun_of (lt f) b) = (a[^](Suc k) \<ominus> b[^](Suc k)) \<otimes> (lc f)"
    by (simp add: R.m_comm assms(1) assms(2) assms(3) lc_closed)
  then have "(fun_of (lt f) a)  \<ominus> (fun_of (lt f) b) = (a \<ominus> b) \<otimes> (geometric_quotient R k a b)\<otimes>(lc f)"
    using assms(1) assms(2) geom_quot_id by auto
  then have "(fun_of (lt f) a)  \<ominus> (fun_of (lt f) b) = (a \<ominus> b) \<otimes> ((geometric_quotient R k a b)\<otimes>(lc f))"
    using assms 
    by (simp add: R.m_assoc lc_closed)
  then have "((geometric_quotient R k a b)\<otimes>(lc f))\<in> carrier R \<and>
              (fun_of (lt f) a)  \<ominus> (fun_of (lt f) b) = (a \<ominus> b) \<otimes> ((geometric_quotient R k a b)\<otimes>(lc f))"
    by (simp add: assms(1) assms(2) assms(3) lc_closed)
    then show ?thesis by blast 
qed

lemma fun_of_diff:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "f \<in> carrier P"
  shows "\<exists>c. c \<in> carrier R \<and>(fun_of f a) \<ominus> (fun_of f b) = (a \<ominus> b)\<otimes>c"
proof(rule poly_induct2[of f])
  show "f \<in> carrier P" 
    using assms 
    by auto 
  show "\<And>p. p \<in> carrier P \<Longrightarrow> degree p = 0 \<Longrightarrow> \<exists>c. c \<in> carrier R \<and> fun_of p a \<ominus> fun_of p b = (a \<ominus> b) \<otimes> c"
  proof-
    fix p
    assume A: "p \<in> carrier P" and "degree p = 0"
    show "\<exists>c. c \<in> carrier R \<and> fun_of p a \<ominus> fun_of p b = (a \<ominus> b) \<otimes> c"
    proof-
      have "fun_of p a \<ominus> fun_of p b = \<zero>"
        using A 
        by (metis P_def R.r_neg UP_domain.fun_of_to_poly UP_domain_axioms
            \<open>degree p = 0\<close> a_minus_def assms(1) assms(2) coeff_simp1 lcoeff_closed to_poly_inverse)
      then have "\<zero>\<in> carrier R \<and> fun_of p a \<ominus> fun_of p b = (a \<ominus> b) \<otimes> \<zero>"
        by (simp add: assms(1) assms(2))
      then show ?thesis 
        by blast 
    qed
  qed
  show "\<And>p. 0 < degree p \<Longrightarrow>
         p \<in> carrier P \<Longrightarrow>
         \<exists>c. c \<in> carrier R \<and> fun_of (trunc p) a \<ominus> fun_of (trunc p) b = (a \<ominus> b) \<otimes> c \<Longrightarrow>
         \<exists>c. c \<in> carrier R \<and> fun_of p a \<ominus> fun_of p b = (a \<ominus> b) \<otimes> c"
  proof-
    fix p
    assume A[simp]:"0 < degree p" "p \<in> carrier P"
    assume IH: "\<exists>c. c \<in> carrier R \<and> fun_of (trunc p) a \<ominus> fun_of (trunc p) b = (a \<ominus> b) \<otimes> c"
    show "\<exists>c. c \<in> carrier R \<and> fun_of p a \<ominus> fun_of p b = (a \<ominus> b) \<otimes> c"
    proof-
      obtain c0 where c0_def: "c0 \<in> carrier R \<and> fun_of (trunc p) a \<ominus> fun_of (trunc p) b = (a \<ominus> b) \<otimes> c0"
        using IH by blast
      have "fun_of p a \<ominus> fun_of p b = fun_of (trunc p) a \<ominus> fun_of (trunc p) b 
                                    \<oplus> (fun_of (lt p) a) \<ominus> (fun_of (lt p) b)"
      proof-
        have 0:"fun_of p a = fun_of (trunc p) a\<oplus> (fun_of (lt p) a)"
          by (metis A(2) assms(1) fun_of_plus lt_closed trunc_simps(1) trunc_simps(3))
        have 1:"fun_of p b = fun_of (trunc p) b\<oplus> (fun_of (lt p) b)"
          by (metis A(2) assms(2) fun_of_plus lt_closed trunc_simps(1) trunc_simps(3))
        have 2: "fun_of p a \<ominus> fun_of p b = fun_of (trunc p) a\<oplus> (fun_of (lt p) a) \<ominus> 
                                            (fun_of (trunc p) b\<oplus> (fun_of (lt p) b))"
          using 0 1 by auto 
        have 3: "fun_of p a \<ominus> fun_of p b = fun_of (trunc p) a\<oplus> (fun_of (lt p) a) \<oplus>
                                           \<ominus> (fun_of (trunc p) b) \<oplus> \<ominus>(fun_of (lt p) b)"
          using 2 
          by (metis (no_types, lifting) "0" A(2) P_def R.ring_simprules(14) R.ring_simprules(19) 
              R.ring_simprules(7) UP_domain.fun_of_closed UP_domain.lt_closed UP_domain_axioms
              UP_ring_axioms UP_ring_def assms(1) assms(2) ring.ring_simprules(3) trunc_simps(3))
        have 4: "fun_of p a \<ominus> fun_of p b = fun_of (trunc p) a\<oplus> \<ominus> (fun_of (trunc p) b)
                                         \<oplus> (fun_of (lt p) a)  \<oplus> \<ominus>(fun_of (lt p) b)"
            by (smt "0" "1" A(2) P_def R.ring_simprules(14) R.ring_simprules(19) 
                R.ring_simprules(22) R.ring_simprules(7) UP_domain.fun_of_closed 
                UP_domain.lt_closed UP_domain_axioms UP_ring_axioms UP_ring_def 
                assms(1) assms(2) ring.ring_simprules(3) trunc_simps(3))
        then show ?thesis 
            by (simp add: a_minus_def)
        qed
      then have 0: "fun_of p a \<ominus> fun_of p b = (a \<ominus> b) \<otimes> c0 
                                    \<oplus> (fun_of (lt p) a) \<ominus> (fun_of (lt p) b)"
        using c0_def by auto
      then have 1: "fun_of p a \<ominus> fun_of p b = (a \<ominus> b) \<otimes> c0 
                                    \<oplus> ((fun_of (lt p) a) \<ominus> (fun_of (lt p) b))"
        using 0 
        by (metis (no_types, lifting) A(2) P_def R.minus_closed R.ring_simprules(5)
            UP_domain.fun_of_closed UP_domain_axioms UP_ring_axioms UP_ring_def 
            a_minus_def assms(1) assms(2) c0_def lt_closed ring.ring_simprules(3)
            ring.ring_simprules(7))
      obtain c1 where c1_def: " c1 \<in> carrier R\<and> (fun_of (lt p) a) \<ominus>  (fun_of (lt p) b) = (a \<ominus> b) \<otimes>c1"
        using A fun_of_lt_diff assms by blast 
      have 2: "fun_of p a \<ominus> fun_of p b = (a \<ominus> b) \<otimes> c0
                                    \<oplus> ((a \<ominus> b) \<otimes>c1)"
        using c1_def 1 
        by simp
      have 3: "fun_of p a \<ominus> fun_of p b = (a \<ominus> b) \<otimes> (c0 \<oplus> c1)"
        using  2 
        by (simp add: R.r_distr assms(1) assms(2) c0_def c1_def)
      then show ?thesis
        using R.add.m_closed c0_def c1_def by blast                              
    qed
  qed
qed

(*
fun list_to_poly :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" where
"list_to_poly [] = (\<lambda>n. \<zero>)"|
"list_to_poly (a#as) = (\<lambda>n. (if n=0 then a else (list_to_poly as (n-1))))"

fun trunc :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "trunc f = (\<lambda>i. (if i < (degree f) then  f i else \<zero>\<^bsub>R\<^esub>))"

fun list_iter where
"list_iter 0 f = [f 0]" |
"list_iter (Suc n) f = (list_iter n (trunc f))@ [(f n)]"

definition poly_to_list where 
"poly_to_list f =(if (f = (\<lambda>n. \<zero>)) then [] else (list_iter (degree f) f))"

lemma poly_0:
  shows "\<lbrakk>\<And>m. p m = \<zero>\<rbrakk> \<Longrightarrow> p = (\<lambda>a. \<zero>)" 
  by auto

lemma deg_0_poly_simp:
  shows "degree (\<lambda>a. \<zero>) = 0"
  unfolding degree_def
proof-
  have "\<And>m. (\<lambda>a. \<zero>) m = \<zero>" by simp
  hence "bound \<zero> 0 (\<lambda>a. \<zero>)" by auto
  thus "deg R (\<lambda>a. \<zero>) = 0" using deg_def
    by (smt R.zero_closed UP_cring_axioms UP_cring_def UP_def UP_ring.intro UP_ring.lcoeff_nonzero_deg cring_def mem_upI partial_object.select_convs(1) restrict_apply up_ring.simps(2))
qed

lemma poly_to_list_simp_0:
  shows "poly_to_list (\<lambda>a. \<zero>) = []"
  sledgehammer
  by (simp add: poly_to_list_def)
(*
proof-
  have 0: "degree (\<lambda>a. \<zero>) = 0" using deg_0_poly_simp by simp
  have "poly_to_list (\<lambda>a. \<zero>) = list_iter (degree (\<lambda>a. \<zero>)) (\<lambda>a. \<zero>)"
    by (simp add: poly_to_list_def)
  hence "poly_to_list (\<lambda>a. \<zero>) = list_iter 0 (\<lambda>a. \<zero>)" using 0 by simp
  have "list_iter 0 (\<lambda>a. \<zero>) = [\<zero>]"
    by simp
  thus ?thesis 
    by (simp add: \<open>poly_to_list (\<lambda>a. \<zero>) = list_iter 0 (\<lambda>a. \<zero>)\<close>)
qed

*)

lemma degree_length:
  shows "degree (list_to_poly as) = length as"
proof-
  obtain n where "degree(list_to_poly as) = n"

lemma list_poly_inverse_0:
  assumes "as \<noteq> bs @ [\<zero>]"
  shows "poly_to_list(list_to_poly as) = as"
proof(induction as)
  case Nil
  then show ?case 
    by (simp add: poly_to_list_def)
next
  case (Cons a as)
  fix a as
  assume IH: "poly_to_list (list_to_poly as) = as"
  show "poly_to_list (list_to_poly (a # as)) = a # as"  
  
  qed




  show "poly_to_list (list_to_poly []) = []"
    unfolding poly_to_list_def apply simp done
  show "\<And>a as. (\<And>x. x \<noteq> 0 \<Longrightarrow> poly_to_list (list_to_poly as) = as) \<Longrightarrow> poly_to_list (list_to_poly (a # as)) = a # as "  
  proof-
    fix a as
    assume 
qed
  
lemma list_poly_inverse_1:
  shows "list_to_poly(poly_to_list p) = p" 
  using deg_0_poly_simp poly_to_list_def poly_to_list_simp_0 by auto

lemma list_to_poly_is_poly:
  shows "\<lbrakk>(set as) \<subset> carrier R\<rbrakk> \<Longrightarrow> list_to_poly as \<in> carrier (UP R)"
proof(induction as)
  case Nil
  fix n
  have "list_to_poly Nil n = \<zero>"
    by simp
  have "\<zero> \<in> carrier R" by simp
  then show ?case 
    by (smt P_def UP_cring.list_to_poly.simps(1) UP_cring_axioms UP_def UP_zero_closed ring.simps(1))
next
  case (Cons a as)
  fix as
  assume IH: "\<lbrakk>(set as) \<subset> carrier R\<rbrakk> \<Longrightarrow> list_to_poly as \<in> carrier (UP R)"
  show "\<lbrakk>(set (a#as)) \<subset> carrier R\<rbrakk> \<Longrightarrow> list_to_poly (a#as) \<in> carrier (UP R)"
  proof-
    assume "set (a # as) \<subset> carrier R"
    have "(set as) \<subset> carrier R"
      using \<open>set (a # as) \<subset> carrier R\<close> set_subset_Cons subset_antisym by auto
    then have "list_to_poly as \<in> carrier (UP R)" 
      using IH by blast
    obtain n where "bound \<zero> n (list_to_poly as)" 
      by (metis (no_types, lifting) R.bound_upD UP_def \<open>list_to_poly as \<in> carrier (UP R)\<close> partial_object.select_convs(1))
    have "\<And>m. list_to_poly as m = list_to_poly (a#as) (m+1)"
      by simp
    then have "\<And>m. \<lbrakk>m > (n+1)\<rbrakk> \<Longrightarrow> list_to_poly (a#as) m = \<zero>" 
      by (metis (mono_tags, lifting) \<open>bound \<zero> n (list_to_poly as)\<close> add_less_same_cancel2 bound.bound less_diff_conv list_to_poly.simps(2) not_add_less2)
      then have b0: "bound \<zero> (n+1) (list_to_poly (a#as))" 
        by blast
      have "\<And>m. list_to_poly(a#as) m \<in> carrier R" 
        by (metis (no_types, lifting) UP_def \<open>list_to_poly as \<in> carrier (UP R)\<close> \<open>set (a # as) \<subset> carrier R\<close> list.set_intros(1) list_to_poly.simps(2) mem_upD partial_object.select_convs(1) psubsetD)
      thus "list_to_poly (a # as) \<in> carrier (UP R)" using b0
        by (metis (no_types, lifting) UP_def mem_upI partial_object.select_convs(1))
    qed
  qed

*)

(*
context UP_domain
begin
definition pr_term where
" pr_term f g = f \<otimes>\<^bsub>P\<^esub> (pderiv g) \<oplus>\<^bsub>P\<^esub> (pderiv f)\<otimes>\<^bsub>P\<^esub> g"

lemma product_rule_degree_zero:
  assumes "f \<in> carrier P"
  assumes "g \<in> carrier P"
  assumes "degree f = 0"
  shows "pderiv (f \<otimes>\<^bsub>P\<^esub> g) = pr_term f g"
proof-
  have "f \<otimes>\<^bsub>P\<^esub>g = (f 0)\<odot>\<^bsub>P\<^esub>g"
    using assms 
    by (simp add: lc_deg_0 leading_coefficient_def)
  then show ?thesis 
    unfolding pr_term_def 
    using assms pderiv_deg_0[of f]
    by (metis P.m_closed P.r_zero P_def UP_domain.pderiv_smult UP_domain_axioms 
        UP_ring.deg_zero_impl_monom UP_ring.monom_mult_is_smult UP_ring_axioms 
        cfs_closed coeff_simp1 local.integral_iff poly_deriv_closed)
qed

lemma product_rule_X:
  assumes "g \<in> carrier P"
  shows "pderiv (X \<otimes>\<^bsub>P\<^esub> g) = pr_term (X) g"
proof-
  have "(g) = (poly_shift (X \<otimes>\<^bsub>P\<^esub> g))"
  proof-
    have 0:"(X \<otimes>\<^bsub>P\<^esub> g) \<ominus>\<^bsub>P\<^esub> (ct (X \<otimes>\<^bsub>P\<^esub> g))=  X \<otimes>\<^bsub>P\<^esub> (poly_shift (X \<otimes>\<^bsub>P\<^esub> g))"
      using assms poly_shift_id by auto 
    have 1: "(X \<otimes>\<^bsub>P\<^esub> g) 0 = \<zero>"
      by (smt One_nat_def P.m_closed P.nat_pow_eone P_def UP_domain.coeff_0_mult 
          UP_domain.coeff_0_poly_shift UP_domain_axioms UP_m_comm X_closed X_pow_cf 
          assms f_minus_ct plus_1_eq_Suc poly_shift_prop zero_coefficient_def)
    have 2: "ct (X \<otimes>\<^bsub>P\<^esub> g) = \<zero>\<^bsub>P\<^esub>"
      using assms 1 
      by (metis UP_zero_closed coeff_0_zero constant_term_def 
          deg_nzero_nzero to_poly_inverse zero_coefficient_def)
    have 3: "(X \<otimes>\<^bsub>P\<^esub> g) =  X \<otimes>\<^bsub>P\<^esub> (poly_shift (X \<otimes>\<^bsub>P\<^esub> g))"
      using 0 2 
      by (simp add: a_minus_def assms)
    show ?thesis using 0 3 assms 
      using local.m_lcancel by auto
  qed




lemma product_rule_monom:
  assumes "g \<in> carrier P"
  shows "pderiv (X[^]\<^bsub>P\<^esub>(n::nat) \<otimes>\<^bsub>P\<^esub> g) = pr_term (X[^]\<^bsub>P\<^esub>(n::nat)) g"
proof(induction n)
case 0
  then show ?case 
    using  product_rule_degree_zero assms 
    by (metis P.nat_pow_closed X_closed deg_pow mult_eq_0_iff)
next
  case (Suc n)
  fix n::nat
  assume IH: "pderiv (X [^]\<^bsub>P\<^esub> n \<otimes>\<^bsub>P\<^esub> g) = pr_term (X [^]\<^bsub>P\<^esub> n) g"
  show "pderiv (X [^]\<^bsub>P\<^esub> Suc n \<otimes>\<^bsub>P\<^esub> g) = pr_term (X [^]\<^bsub>P\<^esub> Suc n) g"
  proof-
    have 0: " (X [^]\<^bsub>P\<^esub> Suc n \<otimes>\<^bsub>P\<^esub> g) = X \<otimes>\<^bsub>P\<^esub>  (X [^]\<^bsub>P\<^esub>n \<otimes>\<^bsub>P\<^esub> g)"
      have 1: "pderiv (X [^]\<^bsub>P\<^esub> Suc n \<otimes>\<^bsub>P\<^esub> g) =  pr_term (X) (X [^]\<^bsub>P\<^esub>n \<otimes>\<^bsub>P\<^esub> g)"
        using 0 assms 
        have 2: "pderiv (X [^]\<^bsub>P\<^esub> Suc n \<otimes>\<^bsub>P\<^esub> g) = 
qed

lemma product_rule:
  assumes "f \<in> carrier P"
  assumes "g \<in> carrier P"
  shows "pderiv (f \<otimes>\<^bsub>P\<^esub> g) = pr_term f g"
  sorry

*)
end
end

