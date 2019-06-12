theory poly_sub
imports "~~/src/HOL/Algebra/UnivPoly" cring_poly
begin

(**************************************************************************************************)
(**************************************************************************************************)
(**********************************    Polynomial Substitution   **********************************)
(**************************************************************************************************)

(*Inclusion of R into P*)

definition to_polynomial where
"to_polynomial R  =  (\<lambda>a. monom (UP R) a 0)"

abbreviation(in UP_ring) to_poly where
"to_poly  \<equiv> to_polynomial R "

(**************************************************************************************************)
context UP_domain
begin 


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

lemma(in UP_ring) to_poly_is_ring_hom:
"to_poly \<in> ring_hom R P"
  unfolding to_polynomial_def
  unfolding P_def
  using UP_ring.const_ring_hom[of R]
  UP_ring_axioms by simp 

lemma(in UP_ring) to_poly_add[simp]:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "to_poly (a \<oplus> b) = to_poly a \<oplus>\<^bsub>P\<^esub> to_poly b"
  by (simp add: assms(1) assms(2) ring_hom_add to_poly_is_ring_hom)

lemma(in UP_ring) to_poly_mult[simp]:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "to_poly (a \<otimes> b) = to_poly a \<otimes>\<^bsub>P\<^esub> to_poly b"
  by (simp add: assms(1) assms(2) ring_hom_mult to_poly_is_ring_hom)

lemma(in UP_ring) to_poly_minus[simp]:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "to_poly (a \<ominus> b) = to_poly a \<ominus>\<^bsub>P\<^esub> to_poly b"
  by (metis P.minus_eq P_def R.add.inv_closed R.ring_axioms UP_ring.monom_add 
      UP_ring_axioms assms(1) assms(2) monom_a_inv ring.ring_simprules(14) to_polynomial_def)

lemma(in UP_ring) to_poly_ominus[simp]:
  assumes "a \<in> carrier R"
  shows "to_poly (\<ominus> a) =  \<ominus>\<^bsub>P\<^esub> to_poly a"
  by (metis P_def assms monom_a_inv to_polynomial_def)

end
(*Substitution of one polynomial into another*)



definition compose where
"compose R f g = eval R (UP R) (to_polynomial R) g f"

abbreviation(in UP_ring) sub  (infixl "of" 70) where
"sub f g \<equiv> compose R f g"


definition rev_compose  where
"rev_compose R = eval R (UP R) (to_polynomial R)"

abbreviation(in UP_ring) rev_sub  where
"rev_sub \<equiv> rev_compose R"


context UP_domain
begin

lemma(in UP_ring) sub_rev_sub:
"sub f g = rev_sub g f"
  unfolding compose_def rev_compose_def by simp

lemma(in UP_cring) to_poly_UP_pre_univ_prop:
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

lemma sub_closed:
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
  apply (metis P.add.inv_solve_right P.minus_closed P_def a_minus_def assms lt_in_car)
  apply (metis (no_types, hide_lams) P.add.inv_solve_right 
        P.minus_closed P_def UP_a_comm a_minus_def assms lt_in_car)
  using P.minus_closed P_def assms lt_in_car by blast



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
  by (metis P.add.inv_solve_right P_def a_minus_def lt_decomp lt_in_car)

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
        coeff_simp1 deg_nzero_nzero deg_zero_impl_monom leading_term_def lt_in_car)
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
        by (simp add: P1 assms(1) assms(2) lt_in_car smult_r_distr trunc_simps(3))
      have P3: "degree (lt (a \<odot>\<^bsub>P\<^esub>p)) = degree (a \<odot>\<^bsub>P\<^esub>(lt p))" 
        using assms(1) assms(2)  degree_lt lt_in_car by auto
      have P4: "degree (a \<odot>\<^bsub>P\<^esub>(lt p)) = degree p"
        by (metis False P3 assms(1) assms(2) deg_smult  degree_lt smult_closed)
      have P5: "degree (a \<odot>\<^bsub>P\<^esub>(trunc p)) = degree (trunc p)"
        using False by (simp add: assms(1) assms(2)  trunc_simps(3))
      have P6: "degree (a \<odot>\<^bsub>P\<^esub>(trunc p)) < degree (a \<odot>\<^bsub>P\<^esub>(lt p))"
        using F P4 P5 P_def UP_domain.trunc_degree UP_domain_axioms assms(1) by auto
      have  P7: "(a \<odot>\<^bsub>P\<^esub>(lt p)) = monom P (a \<otimes> (p (degree p))) (degree p)" 
        unfolding leading_term_def 
        using P_def P_fact0 assms(1) assms(2) monom_mult_smult by auto
      have P8: "(a \<otimes> (p (degree p))) \<noteq>\<zero>" 
        using F P4 P_def P_fact0 R.integral assms(1) assms(2) coeff_simp1 deg_smult
          deg_zero  lcoeff_nonzero2 lt_in_car by fastforce
      show ?thesis 
        using P6 P2 P7 P8 lt_id  P4 P_fact0 assms(1) assms(2) trunc_simps(3) by auto
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
      by (metis P_def P_fact0 assms(1) assms(2) coeff_simp1
          deg_zero_impl_monom monom_mult_is_smult)
    have RHS: "(lt p) \<otimes>\<^bsub>P\<^esub> (lt q) = (p 0) \<odot>\<^bsub>P\<^esub> (lt q)"
      using L True P_fact0 assms(1) assms(2) leading_term_def lt_in_car monom_mult_is_smult 
      by (metis P_def)
    then show ?thesis using LHS RHS lt_smult  P_fact0 assms(1) assms(2) by auto
  next
    case False
    then have "degree q = 0" 
      using True by linarith
    then show ?thesis 
      by (metis P.m_comm P_def P_fact0 UP_domain.lt_smult UP_domain_axioms assms(1)
          assms(2) leading_term_def lt_deg_0 lt_in_car monom_mult_is_smult)
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
      by (simp add: P.r_distr assms(1) assms(2) lt_in_car p0_def q0_def trunc_simps(3))
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
            degree_lt lt_in_car p0_def trunc_simps(1))
      then show ?thesis using RHS LHS 
        using Pq by linarith
    qed
    then have P2: "lt (p \<otimes>\<^bsub>P\<^esub> q) = lt ((p0 \<oplus>\<^bsub>P\<^esub> lt(p))\<otimes>\<^bsub>P \<^esub>lt(q))"
      using P0 P1  
      by (simp add: UP_a_comm assms(1) assms(2) lt_in_car 
          lt_of_sum_diff_degree p0_def q0_def trunc_simps(3))
    have P3: " lt ((p0 \<oplus>\<^bsub>P\<^esub> lt(p))\<otimes>\<^bsub>P \<^esub>lt(q)) = lt p \<otimes>\<^bsub>P\<^esub> lt q"
    proof-
      have Q0: "((p0 \<oplus>\<^bsub>P\<^esub> lt(p))\<otimes>\<^bsub>P \<^esub>lt(q)) = (p0 \<otimes>\<^bsub>P \<^esub>lt(q)) \<oplus>\<^bsub>P\<^esub>  (lt(p))\<otimes>\<^bsub>P \<^esub>lt(q)"
        by (simp add: P.l_distr assms(1) assms(2) lt_in_car p0_def trunc_simps(3))
      have Q1: "degree ((p0 \<otimes>\<^bsub>P \<^esub>lt(q)) ) < degree ((lt(p))\<otimes>\<^bsub>P \<^esub>lt(q))"
      proof(cases "p0 = \<zero>\<^bsub>P\<^esub>")
        case True
        then show ?thesis 
          using P1 assms(1) assms(2)  lt_in_car by auto
      next
        case F: False
        then show ?thesis
          proof-
            have LHS: "degree ((p0 \<otimes>\<^bsub>P \<^esub>lt(q))) < degree p + degree q"
              using False F deg_mult Pp assms(1) assms(2) deg_nzero_nzero 
                 degree_lt lt_in_car p0_def trunc_simps(3) by auto
            have RHS: "degree ((lt(p))\<otimes>\<^bsub>P \<^esub>lt(q)) = degree p + degree q" 
               by (metis False  assms(1) assms(2) deg_mult deg_zero 
                     degree_lt lt_in_car)
            then show ?thesis using LHS RHS by auto 
        qed
      qed
      have Q2: "lt ((p0 \<oplus>\<^bsub>P\<^esub> lt(p))\<otimes>\<^bsub>P \<^esub>lt(q)) = lt ((lt(p))\<otimes>\<^bsub>P \<^esub>lt(q))" 
        using Q0 Q1 by (simp add: UP_a_comm assms(1) assms(2) 
            lt_in_car lt_of_sum_diff_degree p0_def trunc_simps(3))
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
     by (metis P_fact0 coeff_simp0)

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
            degree_lt k_bound0 k_def lt_in_car q_is_poly by auto
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
              by (metis A0 assms(1) lt_in_car sub_add trunc_simps(1) trunc_simps(3))
            then show ?thesis 
              using P0 P1 P2 deg_add[of "trunc p of g" "lt p of g"] 
              by (simp add: A0 assms(1) lt_in_car sub_closed trunc_simps(3))
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
            by (metis A0 assms(1) lt_in_car sub_add trunc_simps(1) trunc_simps(3))
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
                    lt_in_car sub_closed trunc_simps(3))
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
    by (simp add: assms(1) assms(2) assms(3)  lt_in_car)
  have P1: "f of g = ((trunc f) of g) \<oplus>\<^bsub>P\<^esub>((lt f) of g)"
    by (metis assms(1) assms(2) lt_in_car rev_sub_add sub_rev_sub trunc_simps(1) trunc_simps(3))
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
      by (simp add: UP_a_comm assms(1) assms(2) lt_in_car lt_of_sum_diff_degree sub_closed trunc_simps(3))
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
        by (simp add: P.minus_add P.minus_eq UP_a_assoc assms(1) assms(2) lt_in_car trunc_simps(3))
      then show ?thesis 
        by (metis (no_types, lifting) P.add.inv_mult_group P.minus_eq P_def UP_a_assoc assms(1)
            assms(2) assms(3) carrier_is_submodule lt_in_car poly_sub.truncate_def submoduleE(3) 
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

lemma lc_monom:
  assumes "a \<in> carrier R"
  assumes "f = monom P a n"
  shows "lc f = a"
  by (metis P_def assms(1) assms(2) coeff_monom coeff_simp1 deg_monom  leading_coefficient_def monom_closed)

lemma lc_monom_simp[simp]:
  assumes "a \<in> carrier R"
  shows "lc (monom P a n) = a"
  by (simp add: assms lc_monom)

lemma lc_mult:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "lc (p \<otimes>\<^bsub>P\<^esub> q) = (lc p) \<otimes> (lc q)"
proof-
  have P0: "lt (p \<otimes>\<^bsub>P\<^esub> q) = (lt p) \<otimes>\<^bsub>P\<^esub> (lt q)"
    using assms lt_mult by auto 
  obtain a where a_def: "a \<in> carrier R \<and> (lt p) = monom P a (degree p)"
    using P_fact0 assms(1)   by (metis P_def leading_term_def)
  obtain b where b_def: "b \<in> carrier R \<and> (lt q) = monom P b (degree q)"
    using P_fact0 assms(2) leading_term_def  P_def by blast
  have P1: "a = lc p" using a_def 
    by (metis P_def assms(1) coeff_monom coeff_simp1 leading_coefficient_def lt_coeffs monom_closed)
  have P2: "b = lc q" using b_def 
    by (metis P_def assms(2) coeff_monom coeff_simp1 leading_coefficient_def lt_coeffs monom_closed)
  have P3: "(lt p) \<otimes>\<^bsub>P\<^esub> (lt q) =  monom P (a \<otimes> b) ((degree p) + (degree q))"
    using a_def b_def  by simp
  then have P4: "lc ((lt p) \<otimes>\<^bsub>P\<^esub> (lt q)) = a \<otimes>b"
    using R.m_closed a_def b_def lc_monom by blast
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
      by (simp add: leading_coefficient_def P_fact0)
    have P1: "(lt f) of g = (lc f) \<odot>\<^bsub>P\<^esub>(g[^]\<^bsub>P\<^esub>n)"
      using P0 P.nat_pow_closed 
      by (metis P_def assms(1) assms(2) coeff_simp1 leading_coefficient_def 
          lcoeff_closed monom_mult_is_smult to_polynomial_def)

    have P2: "lt ((lt f) of g) = (lt (to_poly (lc f))) \<otimes>\<^bsub>P\<^esub> (lt (g[^]\<^bsub>P\<^esub>n))"
      using P0 lt_mult P.nat_pow_closed P_def assms(1) assms(2) coeff_simp1 
         leading_coefficient_def lcoeff_closed to_poly_is_poly 
      by (simp add: leading_coefficient_def)
    have P3: "lt ((lt f) of g) =  (to_poly (lc f)) \<otimes>\<^bsub>P\<^esub> (lt (g[^]\<^bsub>P\<^esub>n))"
      using P2  by (simp add: P_fact0 assms(2)  leading_coefficient_def to_poly_is_poly)
    have P4: "lt ((lt f) of g) = (lc f) \<odot>\<^bsub>P\<^esub> ((lt g)[^]\<^bsub>P\<^esub>n)"
      using P.nat_pow_closed P1 P_def assms(1) assms(2) coeff_simp1 
         leading_coefficient_def lcoeff_closed lt_pow0 lt_smult 
        by (simp add: leading_coefficient_def)
    have P5: "lc ((lt f) of g) = (lc f) \<otimes> (lc ((lt g)[^]\<^bsub>P\<^esub>n))"
      using lc_scalar_mult P4  by (metis P.nat_pow_closed P1 P_fact0 
          UP_smult_closed assms(1) assms(2) assms(3) leading_coefficient_def lc_eq lt_in_car sub_rev_sub)
    show ?thesis
      using P5 lt_pow lc_pow assms(1) lc_eq lt_in_car by presburger
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
        monom_one poly_sub.compose_def to_poly_UP_pre_univ_prop to_polynomial_def)
  have 3: " ((lt f) of g) =  (to_poly (lc f) \<otimes>\<^bsub>P\<^esub>  (g[^]\<^bsub>P\<^esub>n))" using 1 2  
    by (metis (no_types, lifting) P_def UP_pre_univ_prop.eval_monom
        \<open>lt f = monom P (lc f) (degree f)\<close> assms(1) assms(2) assms(3) coeff_simp1 lcoeff_closed
        leading_coefficient_def poly_sub.compose_def to_poly_UP_pre_univ_prop)
  have 4: " (to_poly (lc f) \<otimes>\<^bsub>P\<^esub>  (g[^]\<^bsub>P\<^esub>n)) =  ((lc f) \<odot>\<^bsub>P\<^esub>  (g[^]\<^bsub>P\<^esub>n))" 
    using  P_def R.one_closed assms(2) coeff_simp1 lcoeff_closed 
        leading_coefficient_def monom_closed monom_mult_is_smult 
        by (metis P.nat_pow_closed assms(1) to_polynomial_def)
  have 5: " ((lt f) of g) =  ((lc f) \<odot>\<^bsub>P\<^esub>  (g[^]\<^bsub>P\<^esub>n))" 
    using 3 4  by simp
  have "degree  ((lc f) \<odot>\<^bsub>P\<^esub>  (g[^]\<^bsub>P\<^esub>n)) = degree ((lc f) \<odot>\<^bsub>P\<^esub> ((lt g)[^]\<^bsub>P\<^esub>n))"
    by (simp add: P_fact0 assms(1) assms(2) deg_pow leading_coefficient_def lt_in_car)
  then have P0: "degree ((lt f) of g) = degree ((lc f) \<odot>\<^bsub>P\<^esub> ((lt g)[^]\<^bsub>P\<^esub>n))" 
    using 5 by simp
  have P1: "lc ((lt f) of g) = lc ((lc f) \<odot>\<^bsub>P\<^esub> ((lt g)[^]\<^bsub>P\<^esub>n))" 
  proof-
    have A0: "lc ((lt f) of g) = (lc f) \<otimes> ((lc g)[^]n)" 
      using assms(1) assms(2) assms(3) assms(4) assms(5) lc_of_sub_in_lt by blast
    have A1: "lc ((lc f) \<odot>\<^bsub>P\<^esub> ((lt g)[^]\<^bsub>P\<^esub>n)) = (lc f) \<otimes> (lc ((lt g)[^]\<^bsub>P\<^esub>n))"
      using P_fact0 assms(1) assms(2) leading_coefficient_def lc_scalar_mult lt_in_car 
      by (simp add: leading_coefficient_def)
    then show ?thesis 
      using A0 A1 lc_pow assms  by (metis lc_eq lt_in_car)
  qed
  have P2: "lt ((lt f) of g) = lt ((lc f) \<odot>\<^bsub>P\<^esub> ((lt g)[^]\<^bsub>P\<^esub>n))" 
    using P0 P1   by (simp add: lc_lt)
  then show ?thesis 
    using P.nat_pow_closed P_def assms(1) assms(2) coeff_simp1 
       leading_coefficient_def lcoeff_closed lt_in_car lt_pow0 lt_smult 
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
    using P_fact0 assms(1) leading_coefficient_def lc_lt n_def  by metis
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
            by (simp add: A0 assms(2) assms(3) lt_in_car rev_sub_closed sub_rev_sub trunc_simps(3))
          have I2: "p of (q of r) = (((trunc p)  of q) of r) \<oplus>\<^bsub>P\<^esub> (((lt p)  of q) of r)"
            using IH[of "trunc p"] sub_assoc_monom[of p q r] 
            by (metis A0 I1 \<open>degree p = Suc n\<close> assms(2) assms(3) 
                less_Suc_eq_le trunc_degree trunc_simps(3) zero_less_Suc)
          have I3: "p of (q of r) = (((trunc p)  of q) \<oplus>\<^bsub>P\<^esub> ((lt p)  of q)) of r"
            using sub_add trunc_simps(1) assms   
            by (simp add: A0 I2 lt_in_car sub_closed trunc_simps(3))
          have I4: "p of (q of r) = (((trunc p)\<oplus>\<^bsub>P\<^esub>(lt p))   of q)  of r"
            using sub_add trunc_simps(1) assms   
            by (simp add: trunc_simps(1) A0 I3 lt_in_car trunc_simps(3))
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

lemma X_is_poly:
"X \<in> carrier P"
  unfolding X_poly_def 
  using P_def monom_closed by blast

lemma degree_X:
"degree X = 1" 
  unfolding X_poly_def 
  using P_def deg_monom  by auto

lemma X_not_zero:
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
        by (simp add: X_is_poly)
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
            by (metis A0 P_def UP_domain.trunc_simps(1) UP_domain_axioms X_is_poly lt_in_car sub_add trunc_simps(3))
          then have P: "f of X = (trunc f) \<oplus>\<^bsub>P\<^esub> ((lt f) of X)"
            using D IH[of "trunc f"] 
            by (metis A0 P_def UP_domain.trunc_simps(3) UP_domain_axioms 
                less_Suc_eq_le trunc_degree zero_less_Suc)
          have "lt f =  ((lt f) of X)"
          proof-
            have 0: "lt f = (lc f) \<odot>\<^bsub>P\<^esub> (monom P \<one> (degree f))"
              by (metis A0 D P_fact0 R.l_one R.m_comm R.one_closed 
                  leading_coefficient_def lc_lt monom_mult_smult)
            then have 1: "((lt f) of X) = (lc f) \<odot>\<^bsub>P\<^esub> (monom P \<one> (degree f)) of X"
              by simp
            then have 2: "((lt f) of X) = (lc f) \<odot>\<^bsub>P\<^esub> (monom P \<one> (degree f) of X)"
              using A0 P_def X_is_poly coeff_simp1  leading_coefficient_def
                lcoeff_closed monom_closed sub_smult 
              by (simp add: leading_coefficient_def)
            have 3: "((lt f) of X) = (lc f) \<odot>\<^bsub>P\<^esub> (X[^]\<^bsub>P\<^esub>(degree f))" 
              using "2" P.nat_pow_closed P_def R.one_closed R_cring  UP_pre_univ_prop.eval_monom 
                  X_is_poly compose_def monom_one   to_poly_UP_pre_univ_prop  
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

lemma X_plus_is_poly:
  assumes "a \<in> carrier R"
  shows "(X_plus a) \<in> carrier P"
  unfolding X_poly_plus_def using X_is_poly to_poly_is_poly 
  using P_def UP_a_closed assms by auto

lemma X_minus_is_poly:
  assumes "a \<in> carrier R"
  shows "(X_minus a) \<in> carrier P"
  unfolding X_poly_minus_def using X_is_poly to_poly_is_poly 
  by (simp add: P_def UP_ring.UP_ring UP_ring_axioms assms ring.ring_simprules(4))

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
      UP_domain_axioms X_is_poly assms degree_X to_poly_is_poly 
      by (metis UP_domain.degree_to_poly max_0_1(2))
  have 1:"degree (X_plus a) > 0"
    by (metis One_nat_def P_def R.one_closed R.r_zero X_poly_def 
        X_is_poly X_poly_plus_def X_plus_is_poly  assms  coeff_add coeff_monom deg_aboveD  
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
  by (metis P_def R.one_closed X_poly_def X_is_poly coeff_monom coeff_simp1 degree_X)

lemma lt_of_X_plus:
  assumes "a \<in> carrier R"
  shows "lt (X_plus a) = X"
  unfolding X_poly_plus_def
  using X_is_poly  assms  lt_of_sum_diff_degree[of X "to_poly a"]  
    degree_to_poly[of a]  to_poly_is_poly[of a] degree_X lt_of_X 
    by (simp add: P_def)  

lemma lt_of_X_minus:
  assumes "a \<in> carrier R"
  shows "lt (X_plus a) = X"
  using X_minus_plus[of a]  assms lt_of_X_plus by blast

(*Linear substituions*)
 

definition trans_left where
"trans_left f a = f of (X_minus a)"

lemma trans_left_is_poly:
  assumes "a \<in> carrier R"
  assumes "f \<in> carrier P"
  shows "trans_left f a \<in> carrier P"
  unfolding trans_left_def using assms X_minus_is_poly[of a]
  sub_closed by blast

lemma trans_left_deg:
  assumes "a \<in> carrier R"
  assumes "f \<in> carrier P"
  shows "degree (trans_left f a) = degree f" 
  unfolding trans_left_def 
  using assms sub_deg[of f "X_minus a"] 
        degree_of_X_minus[of a] 
        X_minus_is_poly[of a]
  apply auto
  using deg_nzero_nzero  sub_deg by auto

lemma X_plus_sub_deg:
  assumes "a \<in> carrier R"
  assumes "f \<in> carrier P"
  shows "degree (f of (X_plus a)) = degree f"
  by (metis  X_plus_is_poly assms(1) assms(2) 
      deg_zero   degree_of_X_plus 
        mult.right_neutral  sub_deg zero_neq_one)

lemma X_minus_sub_deg:
  assumes "a \<in> carrier R"
  assumes "f \<in> carrier P"
  shows "degree (f of (X_minus a)) = degree f"
  by (metis  X_minus_is_poly assms(1) assms(2) 
      deg_zero   degree_of_X_minus
        mult.right_neutral  sub_deg zero_neq_one)

end

(*Taylor expansions of polynomials*)

definition taylor_expansion where
"taylor_expansion R a p = compose R p (X_poly_plus R a)"

context UP_domain
begin

definition Taylor ("T\<^bsub>_\<^esub>") where
"Taylor = taylor_expansion R"

lemma Taylor_deg:
  assumes "a \<in> carrier R"
  assumes "p \<in> carrier P"
  shows "degree (T\<^bsub>a\<^esub> p) = degree p"
  unfolding taylor_expansion_def using X_plus_sub_deg[of a p] assms 
  by (simp add: Taylor_def taylor_expansion_def)

lemma plus_minus_sub[simp]:
  assumes " a \<in> carrier R"
  shows "X_plus a of X_minus a = X"
  unfolding X_poly_plus_def
proof-
  have "(X \<oplus>\<^bsub>P\<^esub> to_poly a) of X_minus a = (X  of X_minus a) \<oplus>\<^bsub>P\<^esub> (to_poly a) of X_minus a"
    using sub_add 
    by (simp add: X_is_poly X_minus_is_poly assms to_poly_is_poly)
  then have "(X \<oplus>\<^bsub>P\<^esub> to_poly a) of X_minus a = (X_minus a) \<oplus>\<^bsub>P\<^esub> (to_poly a)"
    by (simp add: X_minus_is_poly assms)
  then show "(X \<oplus>\<^bsub>UP R\<^esub> to_poly a) of X_minus a = X" 
    unfolding to_polynomial_def X_poly_minus_def
    by (metis P.add.inv_solve_right P.minus_eq P_def 
        X_is_poly X_poly_minus_def X_minus_is_poly assms monom_closed to_polynomial_def)
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
  using assms sub_assoc[of p "X_plus a" "X_minus a"] X_plus_is_poly[of a]  X_minus_is_poly[of a]
  by (metis P_def Taylor_def UP_domain.X_sub UP_domain.plus_minus_sub UP_domain_axioms taylor_expansion_def)

end

(*derivative function*)

definition derivative where
"derivative R f a = (taylor_expansion R a f) 1"

abbreviation(in UP_domain) deriv where
"deriv \<equiv> derivative R"

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
  by (simp add: P_fact0 assms constant_term_def to_poly_is_poly)

lemma ct_degree:
  assumes "p \<in> carrier P"
  shows "degree (ct p) = 0"
  unfolding constant_term_def 
  by (simp add: P_fact0 assms)


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
  by (metis P_def P_fact0 assms coeff_simp1 deg_const deg_zero_impl_monom lc_monom monom_closed)


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
    by (metis assms(1) cf_add lt_in_car trunc_simps(3))
  then show ?thesis using 0 
    by (simp add: 0 P_fact0 assms(1) zero_coefficient_def trunc_simps(3))
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
            lt_coeffs lt_in_car neq0_conv)
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
        by (metis A(1) P.r_distr assms(1) lt_in_car trunc_simps(1) trunc_simps(3))
      then have 1:  "coeff_0 (lt p \<otimes>\<^bsub>P\<^esub> f) = coeff_0 (lt p \<otimes>\<^bsub>P\<^esub> trunc f) \<oplus> coeff_0  (lt p \<otimes>\<^bsub>P\<^esub> lt f)"
        by (simp add: A(1) assms(1) lt_in_car trunc_simps(3))
      have 2: " coeff_0 (lt p \<otimes>\<^bsub>P\<^esub> trunc f) = \<zero>" 
        using A IH  by (simp add: trunc_degree trunc_simps(3))
      have 3: "coeff_0  (lt p \<otimes>\<^bsub>P\<^esub> lt f) = \<zero>"
      proof-
        have "degree (lt p \<otimes>\<^bsub>P\<^esub> lt f) > 0" using  deg_mult assms A 
          by (metis add_gr_0 deg_zero  degree_lt lt_in_car nat_less_le)
        then have "coeff_0 (lt (lt p \<otimes>\<^bsub>P\<^esub> lt f)) = \<zero>"
        by (meson A(1) UP_mult_closed assms(1) coeff_lt lt_in_car)
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
              cf_add zero_coefficient_def lt_in_car trunc_simps(1) trunc_simps(3))
        have 1: "coeff_0 ((lt p) \<otimes>\<^bsub>P\<^esub> q) = \<zero>"
          by (simp add: A0 A1 assms(2))
        have "degree (trunc p) < degree p" 
          using A0 A1  by (simp add: trunc_degree)
        then have 2: "coeff_0 ((trunc p) \<otimes>\<^bsub>P\<^esub> q) = coeff_0 (trunc p) \<otimes> coeff_0 q"
          using A0 IH  by (simp add: trunc_simps(3))
        then have 3: "coeff_0 (p \<otimes>\<^bsub>P\<^esub> q) = coeff_0 (trunc p) \<otimes> coeff_0 q"
          using 0 1 2 by (simp add: A0 P_fact0 assms(2) zero_coefficient_def trunc_simps(3))
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
  apply((simp add: P_fact0 zero_coefficient_def)) done

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
          by (simp add: X_is_poly)
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
                P_def X_is_poly algebra.smult_assoc2 algebra_axioms coeff_simp1 
                 leading_coefficient_def lcoeff_closed smult_closed)
          have "p = (trunc p) \<oplus>\<^bsub>P\<^esub> lt p"
            using trunc_simps A0 by auto 
          then have "p =  X \<otimes>\<^bsub>P\<^esub> g \<oplus>\<^bsub>P\<^esub> X \<otimes>\<^bsub>P\<^esub> ((lc p) \<odot>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> n)"
            using g_def LT1 by auto 
          then have "p = X \<otimes>\<^bsub>P\<^esub> (g \<oplus>\<^bsub>P\<^esub> ((lc p) \<odot>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub> n))"
            using A0 P.nat_pow_closed P.r_distr P_def X_is_poly coeff_simp1 
               g_def leading_coefficient_def lcoeff_closed smult_closed by metis
          then show ?thesis 
            by (metis A0 P.nat_pow_closed P_def UP_a_closed X_is_poly 
                coeff_simp1  g_def leading_coefficient_def lcoeff_closed smult_closed)
        qed
      qed
    qed
  qed
  then show ?thesis 
    using assms(1) assms(2) by blast
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
    by (simp add: assms(2) A X_is_poly X_not_zero local.m_lcancel)
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
        by (metis A UP_mult_closed X_is_poly)
    qed
  qed
  have "g = (THE g. g \<in> carrier P \<and> f \<ominus>\<^bsub>P\<^esub> ct f = X \<otimes>\<^bsub>P\<^esub> g)"
    using assms(2) unfolding polynomial_shift_def P_def by auto   
  then have "h = g"
    using 0 assms by auto 
  then show ?thesis 
    using h_def by simp
qed

lemma poly_shift_is_poly[simp]:
  assumes "f \<in> carrier P"
  assumes "g = poly_shift f"
  shows " g \<in> carrier P"
  using assms poly_shift_prop by blast 

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
    using X_is_poly X_not_zero assms(1) local.integral poly_shift_is_poly by blast
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
    by (metis "0" "1" P.r_null X_is_poly X_not_zero assms(1) assms(2)
        deg_mult deg_zero degree_X  nat_less_le poly_shift_is_poly)
  show ?thesis using 0 1 2  by simp
qed

end 
end