theory Zp_poly_test
imports "~~/src/HOL/Algebra/UnivPoly" padic_sequences cring_poly
begin

context padic_integers
begin

lemma(in cring) plus_pairs:
  assumes "a1 \<in> carrier R"
  assumes "a2 \<in> carrier R"
  assumes "a3 \<in> carrier R"
  assumes "b1 \<in> carrier R"
  assumes "b2 \<in> carrier R"
  assumes "b3 \<in> carrier R"
  shows "(a1 \<oplus> a2 \<oplus> a3) \<oplus> (b1 \<oplus> b2 \<oplus> b3) = (a1 \<oplus> b1) \<oplus> (a2 \<oplus> b2) \<oplus> (a3 \<oplus> b3)"
  by (simp add: add.m_assoc add.m_lcomm assms(1) assms(2) assms(3) assms(4) assms(5) assms(6))

lemma(in cring) minus_pairs:
  assumes "a1 \<in> carrier R"
  assumes "a2 \<in> carrier R"
  assumes "a3 \<in> carrier R"
  assumes "b1 \<in> carrier R"
  assumes "b2 \<in> carrier R"
  assumes "b3 \<in> carrier R"
  shows "(a1 \<oplus> a2 \<oplus> a3) \<ominus> (b1 \<oplus> b2 \<oplus> b3) = (a1 \<ominus> b1) \<oplus> (a2 \<ominus> b2) \<oplus> (a3 \<ominus> b3)"
proof-
  have " \<ominus> (b1 \<oplus> b2 \<oplus> b3) = \<ominus>b1 \<oplus>(\<ominus>b2) \<oplus>(\<ominus>b3)"
    using assms inv_add minus_eq 
    by auto
  then show ?thesis 
  unfolding a_minus_def
  using plus_pairs[of a1 a2 a3 "\<ominus>b1" "\<ominus>b2" "\<ominus>b3"]
        a_inv_closed[of "b1"]
        a_inv_closed[of "b2"]
        a_inv_closed[of "b3"]
        assms 
  by auto 
qed

lemma(in cring) minus_pairs_cancel_1:
  assumes "a1 \<in> carrier R"
  assumes "a2 \<in> carrier R"
  assumes "a3 \<in> carrier R"
  assumes "b2 \<in> carrier R"
  assumes "b3 \<in> carrier R"
  shows "(a1 \<oplus> a2 \<oplus> a3) \<ominus> (a1 \<oplus> b2 \<oplus> b3) = (a2 \<ominus> b2) \<oplus> (a3 \<ominus> b3)"
  using assms  minus_pairs[of a1 a2 a3 a1 b2 b3]
  by simp

lemma(in cring) minus_pair_factor:
  assumes "a1 \<in> carrier R"
  assumes "b1 \<in> carrier R"
  assumes "c \<in> carrier R"
  assumes "d \<in> carrier R"
  shows "(c \<otimes> a1 \<ominus> c \<otimes> b1) = c \<otimes>(a1 \<ominus> b1)"
proof-
  have "(c \<otimes> a1 \<oplus> c \<otimes> (\<ominus>b1)) = c \<otimes>(a1 \<ominus> b1)"
    using assms 
    by (simp add: minus_eq r_distr)
  then show ?thesis 
    by (simp add: assms cring.cring_simprules(29) is_cring minus_eq)
qed

lemma(in cring) minus_pairs_factor:
  assumes "a1 \<in> carrier R"
  assumes "a2 \<in> carrier R"
  assumes "b1 \<in> carrier R"
  assumes "b2 \<in> carrier R"
  assumes "c \<in> carrier R"
  assumes "d \<in> carrier R"
  shows "(c \<otimes> a1 \<ominus> c \<otimes> b1) \<oplus> (d \<otimes> a2 \<ominus> c \<otimes> b2) = c \<otimes>(a1 \<ominus> b1)\<oplus> (d \<otimes> a2 \<ominus> c \<otimes> b2)"
  using minus_pair_factor assms(1) assms(3) assms(5)
  by auto

lemma(in cring) minus_pairs_cancel_2:
  assumes "a1 \<in> carrier R"
  assumes "a2 \<in> carrier R"
  assumes "a \<in> carrier R"
  shows "(a1 \<ominus> a \<ominus> (a2 \<ominus> a)) =a1 \<ominus>a2"
  by (smt a_minus_def abelian_group.a_inv_closed abelian_group.minus_closed 
      abelian_group.right_inv_add assms(1) assms(2) assms(3) cring.cring_simprules(17) 
      is_abelian_group is_cring local.ring_axioms ring.ring_simprules(15) ring.ring_simprules(22))


type_synonym padic_int_poly = "nat \<Rightarrow> padic_int"


lemma monom_term_car:
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "x \<in> carrier Z\<^sub>p"
  shows "c \<otimes> x[^](n::nat) \<in> carrier Z\<^sub>p"
  using assms Zp_is_cring monoid.nat_pow_closed 
  by (simp add: monoid.nat_pow_closed cring.cring_simprules(5) cring_def ring_def)

(*Univariate polynomial ring over Z\<^sub>p*)

abbreviation P_Zp where
"P_Zp \<equiv> UP Z\<^sub>p"

lemma P_Zp_is_UP_ring[simp]:
"UP_ring Z\<^sub>p"
  by (metis UP_ring.intro Zp_is_cring cring_def)

lemma P_Zp_is_UP_cring[simp]:
"UP_cring Z\<^sub>p"
  by (simp add: UP_cring_def)

lemma P_Zp_is_UP_domain[simp]:
"UP_domain Z\<^sub>p"
  by (simp add: UP_domain_def Zp_is_domain)

lemma P_Zp_ring[simp]:
"ring P_Zp "
  by (simp add: UP_ring.UP_ring)

lemma P_Zp_cring[simp]:
"cring P_Zp "
  by (simp add: UP_cring.UP_cring)

lemma P_Zp_domain[simp]:
"domain P_Zp "
  by (simp add: UP_domain.UP_domain)

(*Basic simp rules to streaminline computation*)

lemma pow_closedP[simp]:
  assumes "f \<in> carrier P_Zp"
  shows "f[^]\<^bsub>P_Zp\<^esub>(n::nat) \<in> carrier P_Zp " 
  by (meson P_Zp_ring assms monoid.nat_pow_closed ring_def)

lemma pow_closed[simp]:
  assumes "f \<in> carrier Z\<^sub>p"
  shows "f[^](n::nat) \<in> carrier Z\<^sub>p"
  by (meson Zp_is_domain domain_def cring_def assms monoid.nat_pow_closed ring_def)

lemma(in ring) pow_zero[simp]:
  assumes "(n::nat)>0"
  shows "\<zero>[^] n = \<zero>"
  by (simp add: assms nat_pow_zero)

lemma pow_zero[simp]:
  assumes "(n::nat)>0"
  shows "\<zero>[^] n = \<zero>"
  using Zp_is_cring
  unfolding cring_def
  using ring.pow_zero 
        assms 
  by blast

lemma pow_zeroP[simp]:
  assumes "n >0"
  shows "\<zero>\<^bsub>P_Zp\<^esub>[^]\<^bsub>P_Zp\<^esub>(n::nat) = \<zero>\<^bsub>P_Zp\<^esub>"
  using assms ring.pow_zero[of P_Zp] by simp

lemma sum_closedP[simp]:
  assumes "f \<in> carrier P_Zp"
  assumes "g \<in> carrier P_Zp"
  shows "f \<oplus>\<^bsub>P_Zp\<^esub>g \<in>  carrier P_Zp"
  by (simp add: assms(1) assms(2) cring.cring_simprules(1))

lemma sum_closed[simp]:
  assumes "f \<in> carrier Z\<^sub>p"
  assumes "g \<in> carrier Z\<^sub>p"
  shows "f \<oplus> g \<in>  carrier Z\<^sub>p"
  by (simp add: assms(1) assms(2) cring.cring_simprules(1))

lemma mult_zero[simp]:
  assumes "f \<in> carrier Z\<^sub>p"
  shows "f \<otimes> \<zero> = \<zero>"
        "\<zero> \<otimes> f = \<zero>"
   apply (simp add: assms cring.cring_simprules(27))
   apply (simp add: assms cring.cring_simprules(26))
  done

lemma mult_zeroP[simp]:
  assumes "f \<in> carrier P_Zp" 
  shows "f \<otimes>\<^bsub>P_Zp\<^esub> \<zero>\<^bsub>P_Zp\<^esub> = \<zero>\<^bsub>P_Zp\<^esub>"
        "\<zero>\<^bsub>P_Zp\<^esub> \<otimes>\<^bsub>P_Zp\<^esub> f = \<zero>\<^bsub>P_Zp\<^esub>"
  apply (simp add: assms cring.cring_simprules(27))
  apply (simp add: assms cring.cring_simprules(26))
  done

lemma add_zero[simp]:
  assumes "f \<in> carrier Z\<^sub>p"
  shows "f \<oplus> \<zero> = f"
        "\<zero> \<oplus> f = f"
   apply (simp add: Zp_is_cring assms cring.cring_simprules)
   apply (simp add: Zp_is_cring assms cring.cring_simprules)
   done

lemma add_zeroP[simp]:
  assumes "f \<in> carrier P_Zp "
  shows "f \<oplus>\<^bsub>P_Zp\<^esub> \<zero>\<^bsub>P_Zp\<^esub> = f"
        "\<zero>\<^bsub>P_Zp\<^esub> \<oplus>\<^bsub>P_Zp\<^esub> f = f"
   apply (simp add: assms cring.cring_simprules)
   apply (simp add: assms cring.cring_simprules)
   done

(*Degree function*)
abbreviation degree:: "padic_int_poly \<Rightarrow> nat" where
"degree f \<equiv>  deg Z\<^sub>p f"

(*Coefficient function*)
abbreviation cf :: "padic_int_poly \<Rightarrow> nat \<Rightarrow> padic_int" where
"cf  \<equiv> coeff (UP Z\<^sub>p)"

(*Leading term function*)
abbreviation lt  where
"lt \<equiv> leading_term Z\<^sub>p"

(*Leading coefficient function*)
abbreviation lc where
"lc \<equiv> leading_coefficient Z\<^sub>p"

(*Truncation function*)
abbreviation trunc where 
"trunc \<equiv> truncate Z\<^sub>p"

(*Turning a padic polynomial into a function on Z\<^sub>p*)
abbreviation fun_of :: "_ \<Rightarrow> padic_int_fun" (infixl "\<star>" 70) where
"fun_of f a \<equiv> function_of Z\<^sub>p f a"

(*predicate for monomial polynomials*)
abbreviation is_monom where
"is_monom \<equiv> is_monom_poly Z\<^sub>p"

(*technical lemmas for reasoning about fun_of*)
lemma id_is_hom:
"ring_hom_cring Z\<^sub>p Z\<^sub>p (\<lambda>x. x)"
proof(rule ring_hom_cringI)
  show "cring Z\<^sub>p" 
    using Zp_is_cring by auto  
  show "cring Z\<^sub>p" 
    using Zp_is_cring by auto  
  show "(\<lambda>x. x) \<in> ring_hom Z\<^sub>p Z\<^sub>p"
    unfolding ring_hom_def
    apply(auto)
    done
qed

lemma UP_pre_univ_prop_fact:
"UP_pre_univ_prop Z\<^sub>p Z\<^sub>p (\<lambda>x. x)"
  unfolding UP_pre_univ_prop_def
  by (simp add: UP_cring_def  id_is_hom)

(*P_Zp addition commutes with evaluation addition*)
lemma fun_of_fun_sum:
  assumes "f \<in> carrier P_Zp"
  assumes "g \<in> carrier P_Zp"
  assumes "h = f \<oplus>\<^bsub>P_Zp\<^esub> g"
  shows "fun_sum (fun_of f) (fun_of g) \<doteq> fun_of h" 
  unfolding eq_on_Zp_def
  apply(auto)
proof-
  fix x
  assume A: "x \<in> carrier Z\<^sub>p"
  show "fun_sum (fun_of f) (fun_of g) x = fun_of h x "
    unfolding fun_sum_def
    unfolding function_of_def
  proof-
    have "(eval Z\<^sub>p Z\<^sub>p (\<lambda>x. x)) x \<in> (ring_hom P_Zp Z\<^sub>p)"
      using UP_pre_univ_prop_fact A UP_pre_univ_prop.eval_ring_hom[of Z\<^sub>p Z\<^sub>p "(\<lambda>x. x)" x]    by auto   
    then show "eval Z\<^sub>p Z\<^sub>p (\<lambda>x. x) x f \<oplus> eval Z\<^sub>p Z\<^sub>p (\<lambda>x. x) x g = eval Z\<^sub>p Z\<^sub>p (\<lambda>x. x) x h "
      using assms ring_hom_add   by (simp add: \<open>f \<in> carrier P_Zp\<close> ring_hom_def)
  qed
qed

(*monomial functions are monomials*)
lemma fun_of_monom_is_monom0:
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "c \<noteq>\<zero>"
  assumes "f = monom P_Zp c n"
  assumes "x \<in> carrier Z\<^sub>p"
  shows "fun_of f x = mon c n x"
proof-
  have 1: "fun_of f x = c \<otimes> x [^] n"
    using UP_domain.fun_of_monom assms P_Zp_is_UP_domain 
    by (simp add: UP_domain.fun_of_monom)
  show ?thesis
    unfolding mon_def scalar_mult_def X_pow_Zp_def
    apply auto 
     apply (metis "1" Zp_is_cring cring.axioms(1) monoid.nat_pow_0 ring_def)
    using 1  by simp
qed

lemma fun_of_monom_is_monom:
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "f = monom P_Zp c n"
  shows "fun_of f \<doteq> mon c n"
proof(cases "c = \<zero>")
  case True
  have H: "f = (\<lambda> i. \<zero>)"
    apply(auto simp: assms(2))
    apply(auto simp:True)
  proof-
    have A: "\<zero> \<in> carrier Z\<^sub>p" 
      using True assms(1) by auto
    then have "monom  (UP Z\<^sub>p) = (\<lambda>a\<in>carrier Z\<^sub>p. (\<lambda>n i. if i = n then a else \<zero>)) " 
      by(simp add: UP_def)
    then have "monom (UP Z\<^sub>p) \<zero>  = (\<lambda>n i. if i = n then \<zero> else \<zero>)" 
      using A by simp 
    then have "monom (UP Z\<^sub>p) \<zero> n  =  (\<lambda>i. if i = n then \<zero> else \<zero>)"
      by simp
    then show "monom (UP Z\<^sub>p) \<zero> n = (\<lambda>i. \<zero>)" 
      by simp
  qed
  have H1: "cf f= f"
    by (simp add:P_Zp_is_UP_ring UP_domain.coeff_simp1 UP_ring.monom_closed assms(1) assms(2))
  show ?thesis
    unfolding eq_on_Zp_def
    apply(auto )
    unfolding mon_def scalar_mult_def X_pow_Zp_def
  proof-
    fix x
    assume A: "x \<in> carrier Z\<^sub>p"
    have P0: "fun_of f x = \<zero>"
    proof-
      have C0: "abelian_monoid Z\<^sub>p"
        using Zp_is_cring abelian_group_def cring_def ring_def by blast
      have C1: "\<And> i::nat. \<zero> \<otimes> x [^]i = \<zero>"
      proof-
        fix i::nat
        show "\<zero> \<otimes> x [^] i = \<zero>" 
          using Zp_is_cring A monoid.nat_pow_closed 
          by (simp add: monoid.nat_pow_closed cring.cring_simprules(26) cring_def ring_def)
      qed
      have C2: "f \<in> carrier P_Zp"
        apply(auto simp: assms(2))
        using assms(1) P_Zp_is_UP_ring UP_ring.monom_closed[of Z\<^sub>p c n] apply simp
        done
      have C3: "fun_of f x = (\<Oplus>i \<in> {..degree f}. (cf f i) \<otimes> x [^] i)" 
        using  A  C2 P_Zp_is_UP_domain UP_domain.fun_of_formula[of Z\<^sub>p f x]  
        by blast
      show ?thesis 
        apply(auto simp: C3 H1 )
        apply(auto simp: H)
        apply(auto simp: C1)
        apply(auto simp: C0 abelian_monoid.finsum_zero)
        done
    qed
    show "fun_of f x = c \<otimes> (if n = 0 then \<one> else x [^] n) "
      apply(auto simp: P0)
       apply (simp add: True Zp_one_car cring.cring_simprules(26))
      using A assms(1) monom_term_car[of c x] 
      by (metis True Zp_is_cring cring.cring_simprules(26) cring_def monoid.nat_pow_closed ring_def)
  qed
next
  case False
  then show ?thesis 
    unfolding eq_on_Zp_def
    apply(auto)
    by (simp add: assms(1) assms(2) fun_of_monom_is_monom0)
qed

lemma fun_of_monom_is_monom':
  assumes "is_monom f"
  shows "fun_of f \<doteq> mon (lc f) (degree f)"
  using P_Zp_is_UP_domain assms 
    UP_domain.is_monom_id[of Z\<^sub>p f] 
    fun_of_monom_is_monom[of "lc f" f "degree f"] 
    UP_domain.lc_closed[of Z\<^sub>p f] 
  unfolding   is_monom_poly_def
  by auto 

(*monomials are continuous*)

lemma monom_poly_is_continuous:
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "f = monom P_Zp c n"
  shows "is_continuous (fun_of f)"
proof-
  have 0: "is_continuous (mon c n)"
    unfolding mon_def using assms(1) 
    by (simp add: X_pow_Zp_is_continuous scalar_mult_is_continuous)
  have 1: "fun_of f \<doteq> mon c n" 
    by (simp add: assms(1) assms(2) fun_of_monom_is_monom)
  show ?thesis using 0 1 is_continuous_eq eq_on_Zp_def by auto
qed

lemma monom_poly_is_continuous':
  assumes "is_monom f"
  shows "is_continuous (fun_of f)"
  using P_Zp_is_UP_domain UP_domain.is_monom_id[of Z\<^sub>p f]
        monom_poly_is_continuous[of "lc f" f "degree f"]
        assms UP_domain.lc_closed[of Z\<^sub>p f] 
  unfolding is_monom_poly_def 
  by (simp add:  )

lemma degree_0_imp_constant1:
  assumes "f \<in> carrier P_Zp"
  assumes "degree f = 0"
  obtains g where "is_constant_fun g" and "g \<doteq> fun_of f"
proof- 
  obtain c where c0: "c \<in> carrier Z\<^sub>p" and  c1: "\<And>x.  x \<in> carrier Z\<^sub>p \<Longrightarrow> (fun_of f) x = c"
    using P_Zp_is_UP_domain UP_domain.degree_0_imp_constant0  assms(1) assms(2) by blast
  obtain g where g_def: "g = to_const_fun c"
    by simp
  have 0: "is_constant_fun g" 
    by (simp add: \<open>g = to_const_fun c\<close> c0 to_const_fun_is_const)
  have 1: "g \<doteq> fun_of f"
    unfolding eq_on_Zp_def
    apply(auto)
  proof-
    fix x
    assume A: "x \<in> carrier Z\<^sub>p"
    show "g x = fun_of f x "
    proof-
      have LHS: "g x = c" 
        using g_def using to_const_fun_def by simp  
      have RHS: "fun_of f x = c"
        apply(auto simp: A c1)
        done
      then show ?thesis
        using RHS LHS by auto 
    qed
  qed
  show ?thesis
    using 0 1  that by auto
qed

(*degree 0 polynomials induce continuous functions*)
lemma degree_0_imp_continuous:
  assumes "f \<in> carrier P_Zp"
  assumes "degree f = 0"
  shows "is_continuous (fun_of f)"
proof-
  obtain g where 0: "is_constant_fun g" and 1: "g \<doteq> fun_of f"
    using assms degree_0_imp_constant1 by auto 
  have "is_continuous g" 
    using 0 by (simp add: constant_is_continuous)
  then show ?thesis 
    using 1 is_continuous_eq by blast
qed

(*all polynomials induce continuous functions*)
lemma polynomial_is_continuous0:
  fixes n::nat
  shows "\<And>f. f \<in> carrier P_Zp \<Longrightarrow> degree f \<le> n \<Longrightarrow> is_continuous (fun_of f)"
proof(induction n)
case 0
  then show ?case 
    using degree_0_imp_continuous by blast
next
  case (Suc n)
  fix n
  assume IH: "\<And>f. f \<in> carrier P_Zp \<Longrightarrow> (degree f \<le> n \<Longrightarrow> is_continuous (fun_of f))"
  show "\<And>f. f \<in> carrier P_Zp \<Longrightarrow> degree f \<le> Suc n \<Longrightarrow> is_continuous (fun_of f) "
  proof-
    fix f
    assume A0:"f \<in> carrier P_Zp"
    assume D: "degree f \<le> Suc n"
    show "is_continuous (fun_of f)"
    proof(cases "degree f < Suc n")
      case True
      then show ?thesis
        using IH A0 by simp
    next
      case False
      then have E: "degree f = Suc n" 
        using D by auto 
      then have E0: "degree f > (0::nat)" 
        by auto 
      obtain g where g_def: "g \<in> carrier P_Zp \<and> (f = g \<oplus>\<^bsub>P_Zp\<^esub> (lt f)) \<and> degree g < degree f"
        using E0 A0 P_Zp_is_UP_domain UP_domain.lt_decomp[of Z\<^sub>p f] by auto  
      have g0: "g \<in> carrier P_Zp"
        using g_def by auto 
      have g1: "f = g \<oplus>\<^bsub>P_Zp\<^esub> (lt f)" 
        using g_def by auto 
      have g2: "degree g < degree f" 
        using g_def by auto 
      have LS: "is_continuous (fun_of g)" 
        using E g0 g1 g2 IH by auto 
      have RS: "is_continuous (fun_of (lt f))"
        using monom_poly_is_continuous leading_term_def A0  UP_ring.lcoeff_closed
            P_Zp_is_UP_ring UP_domain.coeff_simp1 P_Zp_is_UP_domain   by metis
      have "fun_of f \<doteq>  fun_sum (fun_of g) (fun_of (lt f))"
        using  fun_of_fun_sum g0 A0 g1  eq_on_Zp_def UP_domain.lt_closed 
        by (metis (mono_tags, lifting) P_Zp_is_UP_domain)
      then show ?thesis
        using LS RS sum_of_cont_is_cont 
        by (metis eq_on_Zp_def is_continuous_eq)
    qed
  qed
qed

lemma polynomial_is_continuous:
  assumes "f \<in> carrier P_Zp"
  shows "is_continuous (fun_of f)"
proof-
  obtain n where n_def: "n = degree f" 
    by simp
  then show ?thesis 
    using assms polynomial_is_continuous0 by auto 
qed

(**************************************************************************************************)
(**************************************************************************************************)
(**********************************    Polynomial Substitution   **********************************)
(**************************************************************************************************)
(**************************************************************************************************)

(*The inclusion of Z\<^sub>p into P_Zp*)
abbreviation to_poly :: "padic_int \<Rightarrow> padic_int_poly" where
"to_poly \<equiv> to_polynomial Z\<^sub>p"

lemma to_poly_is_ring_hom:
"to_poly \<in> ring_hom Z\<^sub>p P_Zp"
  by (simp add: UP_domain.to_poly_is_ring_hom)

abbreviation sub :: "padic_int_poly \<Rightarrow> padic_int_poly \<Rightarrow> padic_int_poly" (infixl "of" 70)where
"sub \<equiv> compose Z\<^sub>p"

abbreviation rev_sub :: "padic_int_poly \<Rightarrow> padic_int_poly \<Rightarrow> padic_int_poly" where
"rev_sub \<equiv> rev_compose Z\<^sub>p"

lemma sub_rev_sub:
"sub f g = rev_sub g f"
  by (simp add:  UP_domain.sub_rev_sub)

(*The polynomial X*)

abbreviation X where 
"X \<equiv> X_poly Z\<^sub>p"

(*Translates of X*)

abbreviation X_plus where
"X_plus \<equiv> X_poly_plus  Z\<^sub>p"

abbreviation X_minus where
"X_minus \<equiv> X_poly_minus  Z\<^sub>p"

(*The Taylor expansion*)

abbreviation Taylor ("T\<^bsub>_\<^esub>") where
"Taylor \<equiv> taylor_expansion Z\<^sub>p"

(*Derivative function*)

abbreviation deriv   where
"deriv \<equiv> derivative Z\<^sub>p"


(*Zero coefficient function*)

abbreviation cf0 where
"cf0 \<equiv> zero_coefficient"

(*The shift function*)

abbreviation poly_shift where
"poly_shift \<equiv> polynomial_shift Z\<^sub>p"

(*The iterated shift function*)

abbreviation shift where
"shift \<equiv> poly_shift_iter Z\<^sub>p"

(*The "first n+1 terms" function*)

abbreviation deg_leq where
"deg_leq \<equiv> degree_n_or_less_terms Z\<^sub>p"

(*The linear part function*)
abbreviation lin_part where 
"lin_part \<equiv> linear_part Z\<^sub>p"

(*the derivative operator*)

abbreviation pderiv where
"pderiv \<equiv> poly_deriv Z\<^sub>p"

(*Evaluating polynomials in the residue rings*)

lemma fun_of_res_X_pow:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "a k = b k"
  shows "(fun_of (X[^]\<^bsub>P_Zp\<^esub>(n::nat)) a) k = (fun_of (X[^]\<^bsub>P_Zp\<^esub>n) b) k"
proof(induction n)
  case 0
  then show ?case 
    by (smt P_Zp_is_UP_domain P_Zp_is_UP_ring P_Zp_ring UP_domain.X_is_poly UP_ring.deg_monom 
        UP_ring.monom_one Zp_one_car Zp_one_notzero assms(1) assms(2) degree_0_imp_constant1 
        eq_on_Zp_def is_constant_fun_def monoid.nat_pow_0 pow_closedP ring_def)
next
  case (Suc n)
  fix n::nat
  assume IH: "(X [^]\<^bsub>P_Zp\<^esub> n \<star> a) k = (X [^]\<^bsub>P_Zp\<^esub> n \<star> b) k"
  show "(X [^]\<^bsub>P_Zp\<^esub> Suc n \<star> a) k = (X [^]\<^bsub>P_Zp\<^esub> Suc n \<star> b) k"
  proof-
    have LHS0: "(X [^]\<^bsub>P_Zp\<^esub> Suc n \<star> a) k = ((X [^]\<^bsub>P_Zp\<^esub> n \<star> a) \<otimes> (X \<star> a)) k"
      by (metis (no_types, lifting) P_Zp_is_UP_domain P_Zp_ring UP_domain.X_is_poly
          UP_domain.fun_of_mult assms(1) monoid.nat_pow_Suc pow_closedP ring_def)
    have LHS1: "(X [^]\<^bsub>P_Zp\<^esub> Suc n \<star> a) k = (X [^]\<^bsub>P_Zp\<^esub> n \<star> a) k \<otimes>\<^bsub>R k\<^esub> (X \<star> a) k"
      using LHS0 
      by (simp add: Res_def Z\<^sub>p_def padic_mult_simp)
    then show ?thesis using assms IH 
      by (smt P_Zp_is_UP_domain P_Zp_ring UP_domain.X_is_poly 
          UP_domain.fun_of_X UP_domain.fun_of_mult Z\<^sub>p_def monoid.nat_pow_Suc 
          monoid.simps(1) padic_simps(3) pow_closedP ring_def)
  qed
qed

lemma fun_of_res_lt: 
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "f \<in> carrier P_Zp"
  assumes "a k = b k"
  shows "(fun_of (lt f) a) k = (fun_of (lt f) b) k"
proof-
  have "lt f = (lc f)\<odot>\<^bsub>P_Zp\<^esub>(X[^]\<^bsub>P_Zp\<^esub>(degree f))"
    by (simp add: UP_domain.lt_rep_X_pow assms(3))
  have LHS0: "(fun_of (lt f) a) = (lc f) \<otimes> (fun_of (X[^]\<^bsub>P_Zp\<^esub>(degree f)) a)"
    by (simp add: UP_domain.X_is_poly UP_domain.fun_of_smult UP_domain.lc_closed \<open>lt f = lc f \<odot>\<^bsub>P_Zp\<^esub> X [^]\<^bsub>P_Zp\<^esub> degree f\<close> assms(1) assms(3))
  have RHS0: "(fun_of (lt f) b) = (lc f) \<otimes> (fun_of (X[^]\<^bsub>P_Zp\<^esub>(degree f)) b)"
    by (simp add: UP_domain.X_is_poly UP_domain.fun_of_smult UP_domain.lc_closed \<open>lt f = lc f \<odot>\<^bsub>P_Zp\<^esub> X [^]\<^bsub>P_Zp\<^esub> degree f\<close> assms(2) assms(3))
  have LHS1: "(fun_of (lt f) a) k = ((lc f) k) \<otimes>\<^bsub>R k\<^esub> (fun_of (X[^]\<^bsub>P_Zp\<^esub>(degree f)) a) k"
    using LHS0 assms 
    by (simp add: Res_def Z\<^sub>p_def padic_simps(3))
  have RHS1: "(fun_of (lt f) b) k = ((lc f) k) \<otimes>\<^bsub>R k\<^esub> (fun_of (X[^]\<^bsub>P_Zp\<^esub>(degree f)) b) k"
    using RHS0 assms 
    by (simp add: Res_def Z\<^sub>p_def padic_simps(3))
  then show ?thesis 
    using LHS1 RHS1 assms 
    by (metis fun_of_res_X_pow)
qed

lemma fun_of_res:
  assumes "f \<in> carrier P_Zp"
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "a k = b k"
  shows "(fun_of f a) k = (fun_of f b) k"
proof(rule UP_domain.poly_induct2[of Z\<^sub>p f])
  show "UP_domain Z\<^sub>p" by simp
  show "f \<in> carrier P_Zp" using assms by simp
  show "\<And>p. p \<in> carrier P_Zp \<Longrightarrow> degree p = 0 \<Longrightarrow> (p \<star> a) k = (p \<star> b) k"
    by (metis P_Zp_is_UP_domain UP_domain.degree_0_imp_constant0 assms(2) assms(3))
  show "\<And>p. 0 < degree p \<Longrightarrow> p \<in> carrier P_Zp \<Longrightarrow> (trunc p \<star> a) k = (trunc p \<star> b) k 
                \<Longrightarrow> (p \<star> a) k = (p \<star> b) k"
  proof-
    fix p
    assume A: "0 < degree p" "p \<in> carrier P_Zp"
    assume IH: " (trunc p \<star> a) k = (trunc p \<star> b) k "
    show "(p \<star> a) k = (p \<star> b) k"
    proof-
      have "(p \<star> a) k = (((trunc p)\<star> a) \<oplus> ((lt p) \<star> a)) k "
        by (metis A(2) P_Zp_is_UP_domain UP_domain.fun_of_plus 
            UP_domain.lt_closed UP_domain.trunc_simps(1) UP_domain.trunc_simps(3) assms(2))
      then have 0: "(p \<star> a) k = (((trunc p)\<star> b) k) \<oplus>\<^bsub>R k\<^esub> ((lt p) \<star> a) k "
        using IH 
        by (simp add: Res_def Z\<^sub>p_def padic_add_def)
      have "((lt p) \<star> a) k = ((lt p) \<star> b) k"
        by (simp add: A(2) assms(2) assms(3) assms(4) fun_of_res_lt)
      then have 1: "(p \<star> a) k = (((trunc p)\<star> b) k) \<oplus>\<^bsub>R k\<^esub> ((lt p) \<star> b) k "
        using 0 by auto 
      then have 2: "(p \<star> a) k = (((trunc p)\<star> b) \<oplus> ((lt p) \<star> b)) k "
        using IH Z\<^sub>p_def \<open>(lt p \<star> a) k = (lt p \<star> b) k\<close> \<open>(p \<star> a) k = (trunc p \<star> a \<oplus> lt p \<star> a) k\<close> 
          padic_add_def by auto
      then have 2: "(p \<star> a) k = (((trunc p) \<oplus>\<^bsub>P_Zp\<^esub>(lt p)) \<star> b) k"
        by (simp add: A(2) UP_domain.fun_of_plus UP_domain.lt_closed 
            UP_domain.trunc_simps(3) assms(3))
      then show ?thesis 
        by (metis A(2) P_Zp_is_UP_domain UP_domain.trunc_simps(1))
    qed
  qed
qed

(*If a and b has equal kth residues, then do f'(a) and f'(b)*)
lemma deriv_res:
  assumes "f \<in> carrier P_Zp"
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "a k = b k"
  shows "(deriv f a) k = (deriv f b) k"
proof-
  have 0: "deriv f a = fun_of (pderiv f) a"
    by (simp add: UP_domain.pderiv_eval_deriv assms(1) assms(2))
  have 1: "deriv f b = fun_of (pderiv f) b"
    by (simp add: UP_domain.pderiv_eval_deriv assms(1) assms(3))
  have 2: "pderiv f \<in> carrier P_Zp"
    by (simp add: UP_domain.poly_deriv_closed assms(1))
  show ?thesis
    using assms fun_of_res[of "pderiv f" a b k] 0 1 2 
    by auto 
qed
    
(*Predicate for a polynomial that satisfies the hypothesis of Hensel's lemma at a point a*)
abbreviation hensel where
"hensel f a \<equiv> (f \<in> carrier P_Zp \<and> a \<in> carrier Z\<^sub>p \<and> ((f \<star> a) 1) = 0 \<and> (deriv f a 1) \<noteq> 0)"

(*Proving the existence of the sequence for hensel's lemma*)
lemma pre_hensel:
  assumes "hensel f a"
  assumes "b \<in> carrier Z\<^sub>p \<and> (f \<star> b) (Suc n) = 0 \<and> b 1 = a 1"
  shows "\<exists> b' \<in> carrier Z\<^sub>p. (f \<star> b') (Suc (Suc n)) = 0 \<and> b' 1 = a 1 \<and> b' (Suc n) = b (Suc n)"
proof-
    have b_def: "b \<in> carrier Z\<^sub>p \<and> (f \<star> b) (Suc n) = 0 \<and> b 1 = a 1"
      using assms by blast 
    have  "val_Zp (\<p>[^](Suc n)) \<preceq>\<^bsub>G\<^esub> val_Zp (f \<star> b)"
    proof(cases "f \<star> b = \<zero>")
      case True
      then show ?thesis 
        by (simp add: G_ord(1) val_Zp_def)
    next
      case False
      then have "f \<star> b \<in>nonzero Z\<^sub>p"
        by (meson assms b_def continuous_is_closed is_closed_fun_simp 
            not_nonzero_Zp order_refl polynomial_is_continuous0)
      then have "ord_Zp (f \<star> b) \<ge> Suc n" 
        using b_def  False Zp_nonzero_def(1) ord_Zp_geq by force
      then have "ord_Zp (\<p>[^](Suc n)) \<le> ord_Zp (f \<star> b)" 
        using b_def  by (simp add: ord_Zp_p_pow)
      then show ?thesis 
        using False G_ord(3) \<open>int (Suc n) \<le> ord_Zp (f \<star> b)\<close> ord_Zp_def val_Zp_def val_Zp_p_pow by auto
    qed
    then have 1:"divide (f \<star> b) (\<p>[^](Suc n)) \<otimes> (\<p>[^](Suc n)) = f \<star> b"
      using assms b_def continuous_is_closed divide_id'(2)  is_closed_fun_simp
        p_pow_nonzero polynomial_is_continuous by auto
    have 2: "(deriv f a) \<in> carrier Z\<^sub>p"
      by (simp add: UP_domain.derivative_closed assms)
    have 3: "(deriv f a) 1 \<noteq> 0" using assms by blast
    have "ord_Zp (deriv f a) = 0" using 2 3  
      by (simp )
    then have 4: "(deriv f a) \<in> Units Z\<^sub>p" 
      using 2 ord_Zp_0_imp_unit[of "(deriv f a)"] 
      by blast
    
    obtain k where  k_def: "k =inv\<^bsub>(R 1)\<^esub> ((deriv f a) 1)" by simp
    
    have "k \<otimes>\<^bsub>R 1\<^esub>((deriv f a) 1) = \<one>\<^bsub>R 1\<^esub> \<and> k \<in> carrier (R 1)"
    proof-
      have P0:"field (R 1)"
        using Res_1_field by auto
      have P1: "(deriv f a) 1 \<in> carrier (R 1)"
        using 2 Res_def Z\<^sub>p_def by (metis padic_set_simp0 partial_object.select_convs(1))
      have "\<zero>\<^bsub>R 1\<^esub> = 0" 
        by (simp add: Res_def residue_ring_def)
      then have P: "(deriv f a) 1 \<noteq> \<zero>\<^bsub>R 1\<^esub>" 
        using "3" by linarith
      then have P2: "k \<otimes>\<^bsub>R 1\<^esub>((deriv f a) 1) = \<one>\<^bsub>R 1\<^esub>"
        using residue_ring_def Res_def P0 P1 m_inv_def field.field_inv[of "R 1" "(deriv f a) 1"] k_def
        by auto 
      have "(deriv f a) 1 \<in> Units (R 1)"
        using "3" P1 Res_1_field \<open>\<zero>\<^bsub>R 1\<^esub> = 0\<close> field_axioms_def field_def by fastforce
      have P3: "k \<in> carrier (R 1)" using k_def P0 P1 P field.field_inv[of "R 1" "(deriv f a) 1"] by auto 
      then show ?thesis 
        using P3 P2 by auto 
    qed
    
    obtain m::int where m_def: "m =(\<ominus>\<^bsub>R 1\<^esub> (((divide (f \<star> b) (\<p>[^](Suc n))) 1) \<otimes>\<^bsub>R 1\<^esub> k))"
      by simp
    obtain t where t_def: "t = [m]\<cdot>\<one>"
      by simp
   
    have 5: "(f \<star> (b \<oplus> ((\<p>[^](Suc n)) \<otimes> t))) (Suc (Suc n)) = 0"
    proof-
      obtain fb where fb_def[simp]: "fb = f \<star> b"
        by simp
      obtain f'b where f'b_def[simp]: "f'b = (deriv f b)"
        by simp
      obtain c where c_def: "c = (shift 2 (T\<^bsub>b\<^esub>f)) \<star> ((\<p>[^](Suc n)) \<otimes> t)"
        by simp
      have pnt_car: "((\<p>[^](Suc n)) \<otimes> t) \<in> carrier Z\<^sub>p"
        by (simp add: Zp_int_mult_closed Zp_one_car
            cring.cring_simprules(5) t_def)
      have c_car:"c \<in> carrier Z\<^sub>p"
        using P_Zp_is_UP_domain Taylor_closed_UP_domain 
              poly_shift_closed_UP_domain pnt_car c_def
        by (simp add: assms b_def)
      have A0: " f \<star> (\<p> [^] (Suc n) \<otimes> t \<oplus> b) = fb \<oplus> f'b \<otimes> (\<p> [^] (Suc n) \<otimes> t) \<oplus> c \<otimes> (\<p> [^](Suc n) \<otimes> t) [^] (2::nat)"
      proof-
        have P0: "\<p> [^] (Suc n) \<otimes> t \<in> carrier Z\<^sub>p"
          by (simp add: Zp_int_mult_closed Zp_one_car cring.cring_simprules(5)  t_def)
        have P1: "f \<in> carrier P_Zp"
          using assms by auto 
        have P2: "b \<in> carrier Z\<^sub>p"
          using b_def by auto 
        show ?thesis
          using P0 P1 P2   fb_def f'b_def c_def  
                P_Zp_is_UP_domain UP_domain.Taylor_deg_1_eval[of Z\<^sub>p f b "(\<p>[^](Suc n)) \<otimes> t" c fb f'b]
        by auto 
      qed
      have A1: "(c \<otimes> (\<p> [^] (Suc n) \<otimes> t) [^] (2::nat)) (Suc (Suc n)) = 0"
      proof-
        have Q0: "(\<p> [^] (Suc n) \<otimes> t) [^] (2::nat) = ((\<p> [^] (Suc n)) [^] (2::nat)) \<otimes> (t [^] (2::nat))"
          using Zp_int_mult_closed Zp_is_cring Zp_one_car 
            comm_monoid.nat_pow_distr cring_def p_pow_car_nat t_def 
          by (simp add: comm_monoid.nat_pow_distr cring_def)
        then have Q1:"t = \<zero> \<or> ord_Zp ((\<p> [^] (Suc n) \<otimes> t) [^] (2::nat)) \<ge> 2*(Suc n)"
        proof(cases "t = \<zero>")
          case True
          then show ?thesis by auto 
        next
          case False
          then have Q1: "ord_Zp ((\<p> [^] (Suc n) \<otimes> t) [^] (2::nat)) = ord_Zp ((\<p> [^] (Suc n)) [^] (2::nat)) 
                                                         + ord_Zp (t [^] (2::nat))"
            using Q0 ord_Zp_mult 
            by (metis Zp_int_mult_closed Zp_nat_pow_nonzero Zp_one_car not_nonzero_Zp p_pow_nonzero t_def)
          have Q2: "ord_Zp ((\<p> [^] (Suc n)) [^] (2::nat))  = 2*(Suc n)"
            by (simp add: ord_Zp_p_pow)
          have Q3: "ord_Zp (t [^] (2::nat)) \<ge> 0"
            by (metis False Zp_int_mult_closed Zp_one_car mult_sign_intros(1) 
                not_nonzero_Zp of_nat_0_le_iff ord_Zp_pow ord_pos t_def)
          show ?thesis using Q1 Q2 Q3  
            by linarith
        qed
        show ?thesis 
        proof(cases "t = \<zero>")
          case True
          then have "(c \<otimes> (\<p> [^] (Suc n) \<otimes> t) [^] (2::nat)) = \<zero>"
          proof-
            have "(\<p> [^] (Suc n) \<otimes> t) = \<zero>"
              using True 
              by (metis Zp_int_mult_closed Zp_is_cring Zp_one_car 
                  cring.cring_simprules(14) cring.cring_simprules(26) p_pow_car_nat t_def)
            then have "(\<p> [^] (Suc n) \<otimes> t) [^] (2::nat) = \<zero>" 
              by simp
            then have "(c \<otimes> (\<p> [^] (Suc n) \<otimes> t) [^] (2::nat)) = \<zero>"
              using c_car by simp  
            then show ?thesis 
              by blast
          qed
          then show ?thesis 
            by (simp add: zero_vals)
        next
          case False
          then have Q2:"ord_Zp ((\<p> [^] (Suc n) \<otimes> t) [^] (2::nat)) \<ge> 2*(Suc n)"
            using Q1 by auto 
          have Q3: "2*(Suc n) \<ge> Suc (Suc n)"
            by auto 
          then have Q4:"ord_Zp ((\<p> [^] (Suc n) \<otimes> t) [^] (2::nat)) \<ge> (Suc (Suc n))"
            using Q2 by linarith
          have "((\<p> [^] (Suc n)   \<otimes> t) [^] (2::nat)) \<in> carrier Z\<^sub>p"
            by (simp add: Zp_int_mult_closed Zp_one_car cring.cring_simprules(5) t_def)
          then have "((\<p> [^] (Suc n)  \<otimes> t) [^] (2::nat)) (Suc (Suc n)) = 0"
            using  Q4  int.lless_eq zero_below_ord 
            by blast
          then show ?thesis 
            using  c_car  \<open>(\<p> [^] Suc n \<otimes> t) [^] 2 \<in> carrier Z\<^sub>p\<close> res_mult_zero(2)
            by blast
        qed
      qed
      have A2:"fb \<oplus> f'b \<otimes> (\<p> [^] (Suc n) \<otimes> t) \<in> carrier Z\<^sub>p"
      proof-
        have A20: "f'b \<in> carrier Z\<^sub>p"
          using f'b_def  assms b_def UP_domain.derivative_closed[of Z\<^sub>p f b] P_Zp_is_UP_domain  
          by blast
        have A21: "fb \<in> carrier Z\<^sub>p"
          using fb_def b_def assms  
          by simp
        then show ?thesis 
          using t_def  
          using A20 cring.cring_simprules(5) pnt_car by force
      qed
      have A3: "c \<otimes> (\<p> [^](Suc n) \<otimes> t) [^] (2::nat) \<in> carrier Z\<^sub>p"
        using c_car monom_term_car pnt_car by auto
      have A4: " (f \<star> (\<p> [^] (Suc n) \<otimes> t \<oplus> b)) (Suc (Suc n)) = (fb \<oplus> f'b \<otimes> (\<p> [^] (Suc n) \<otimes> t)) (Suc (Suc n))"
        using A0 A1 A2 A3
              res_add_zero(2)[of "(Suc (Suc n))" "c \<otimes> (\<p> [^](Suc n) \<otimes> t) [^] (2::nat)" 
                                          "fb \<oplus> f'b \<otimes> (\<p> [^] (Suc n) \<otimes> t)"]                            
        by auto 
      have A6: "(f'b \<otimes> (\<p> [^] (Suc n) \<otimes> t)) \<in> carrier Z\<^sub>p"
      proof-
        have A20: "f'b \<in> carrier Z\<^sub>p"
          using f'b_def  assms b_def UP_domain.derivative_closed[of Z\<^sub>p f b] P_Zp_is_UP_domain  
          by blast
        then show ?thesis using t_def 
          using Zp_is_cring cring.cring_simprules(5) pnt_car by fastforce
      qed
      have A7: "fb  \<in> carrier Z\<^sub>p"
        using fb_def b_def assms  
          by simp
      have A8: "(fb \<oplus> f'b \<otimes> (\<p> [^] (Suc n) \<otimes> t)) (Suc (Suc n)) = 0"
      proof-
        obtain fa where fa_def[simp]: "fa = fun_of f a" 
          by simp
        obtain f'a where f'a_def[simp]: "f'a = deriv f a"
          by simp
        have A80: "(f'a \<otimes> t) 1= \<ominus>\<^bsub>R 1\<^esub>(divide (fb) (\<p>[^](Suc n))) 1"
        proof-
          have C0: "t 1 = m mod p"
          proof-
            have 0: "t 1 = ([m]\<cdot>\<one>) 1"
              using t_def by auto 
            have 1: "([m]\<cdot>\<one>) 1 = m mod p"
              using  int_inc_rep r_def by auto
            then show ?thesis using 0 1 by auto 
          qed
          show C1: "(f'a \<otimes> t) 1 = \<ominus>\<^bsub>R 1\<^esub>(divide (fb) (\<p>[^](Suc n))) 1"
          proof-
            have C10:"(f'a \<otimes> t) 1  = (f'a 1) \<otimes>\<^bsub>R 1\<^esub> (t 1)"
              by (simp add: Res_def Z\<^sub>p_def padic_mult_simp)
            have C11:"(f'a \<otimes> t) 1  = (f'a 1) \<otimes>\<^bsub>R 1\<^esub>(\<ominus>\<^bsub>R 1\<^esub> (((divide (f \<star> b) (\<p>[^](Suc n))) 1) \<otimes>\<^bsub>R 1\<^esub> k))"
              using C10 m_def C0 
              by (smt R_residues Res_def mod_mult_right_eq of_nat_0_less_iff 
                  of_nat_le_0_iff power_one_right residues.res_mult_eq zero_neq_one)
            have C12: "(f'a \<otimes> t) 1  = ((f'a 1) )\<otimes>\<^bsub>R 1\<^esub>(\<ominus>\<^bsub>R 1\<^esub> (k \<otimes>\<^bsub>R 1\<^esub>(((divide (f \<star> b) (\<p>[^](Suc n))) 1))))"
            proof-
              have C120:"((divide (f \<star> b) (\<p>[^](Suc n))) 1) \<in> carrier (R 1)"
                by (metis A7 Res_def Z\<^sub>p_def \<open>val_Zp (f \<star> b) \<succeq>\<^bsub>G\<^esub> val_Zp (\<p> [^] Suc n)\<close> 
                    divide_id'(1) fb_def p_pow_nonzero padic_set_simp0 
                    partial_object.select_convs(1))
              have C121: "k \<in> carrier R 1" 
                using \<open>k \<otimes>\<^bsub>R 1\<^esub> deriv f a 1 = \<one>\<^bsub>R 1\<^esub> \<and> k \<in> carrier R 1\<close> by auto
              have C122: "(\<ominus>\<^bsub>R 1\<^esub> (((divide (f \<star> b) (\<p>[^](Suc n))) 1) \<otimes>\<^bsub>R 1\<^esub> k))
                              =(\<ominus>\<^bsub>R 1\<^esub> (k \<otimes>\<^bsub>R 1\<^esub> ((divide (f \<star> b) (\<p>[^](Suc n))) 1)))"
                using C120 C121   Res_1_field  
                by (metis R_residues Res_def mult.commute nat_less_le 
                    residues.res_mult_eq zero_le_one zero_neq_one)
              have C123: "f'a 1 \<in> carrier (R 1)"
                by (metis "2" Res_def Z\<^sub>p_def f'a_def padic_set_simp0 partial_object.select_convs(1))
              show ?thesis
                unfolding a_minus_def
                using  C11 C120 C121 C122 C123   Res_1_field  
                by simp
            qed
            have C13: "k \<in> carrier R 1" 
              using \<open>k \<otimes>\<^bsub>R 1\<^esub> deriv f a 1 = \<one>\<^bsub>R 1\<^esub> \<and> k \<in> carrier R 1\<close> by auto
            have C14: "f'a 1 \<in> carrier (R 1)"
              by (metis "2" Res_def Z\<^sub>p_def f'a_def padic_set_simp0 partial_object.select_convs(1))
            have C15: "(k \<otimes>\<^bsub>R 1\<^esub>(((divide (f \<star> b) (\<p>[^](Suc n))) 1))) \<in> carrier (R 1)"
            proof-
              have "(divide (f \<star> b) (\<p>[^](Suc n))) \<in> carrier Z\<^sub>p"
                using A7 \<open>val_Zp (f \<star> b) \<succeq>\<^bsub>G\<^esub> val_Zp (\<p> [^] Suc n)\<close> divide_id'(1) fb_def p_pow_nonzero 
                by blast
              then have "(divide (f \<star> b) (\<p>[^](Suc n))) 1 \<in> carrier (R 1)"
                by (metis Res_def Z\<^sub>p_def padic_set_simp0 partial_object.select_convs(1))
              then show ?thesis using Res_1_field C13 
                by simp
            qed
            then have "(f'a \<otimes> t) 1  = (\<ominus>\<^bsub>R 1\<^esub> ((f'a 1) )\<otimes>\<^bsub>R 1\<^esub>(k \<otimes>\<^bsub>R 1\<^esub>(((divide (f \<star> b) (\<p>[^](Suc n))) 1))))"
              using C12 C13 C14 C15 Res_1_field R_cring[of 1] R_residues[of 1]
              unfolding Res_def 
              by (simp add: cring.cring_simprules(28) cring.cring_simprules(29))
            then have "(f'a \<otimes> t) 1  = (\<ominus>\<^bsub>R 1\<^esub> ((f'a 1) \<otimes>\<^bsub>R 1\<^esub> k ) \<otimes>\<^bsub>R 1\<^esub>(((divide (f \<star> b) (\<p>[^](Suc n))) 1)))"
              using C12 C13 C14 C15 Res_1_field R_cring[of 1] R_residues[of 1]
              unfolding Res_def 
              by (metis (no_types, lifting) A7 Z\<^sub>p_def \<open>val_Zp (f \<star> b) \<succeq>\<^bsub>G\<^esub> val_Zp (\<p> [^] Suc n)\<close> cring.cring_simprules(11) cring.cring_simprules(28) cring.cring_simprules(3) divide_id'(1) fb_def p_pow_nonzero padic_set_simp0 partial_object.select_convs(1) zero_less_one)
            then have  "(f'a \<otimes> t) 1  = (\<ominus>\<^bsub>R 1\<^esub> (((divide (f \<star> b) (\<p>[^](Suc n))) 1)))"
              using k_def 4 Res_1_field  C12 C13 C14 C15 Res_1_field R_cring[of 1] R_residues[of 1]
              unfolding Res_def 
              by (smt A7 Res_def Z\<^sub>p_def \<open>k \<otimes>\<^bsub>R 1\<^esub> deriv f a 1 = \<one>\<^bsub>R 1\<^esub> \<and> k \<in> carrier R 1\<close> \<open>val_Zp (f \<star> b) \<succeq>\<^bsub>G\<^esub> val_Zp (\<p> [^] Suc n)\<close> cring.cring_simprules(12) cring.cring_simprules(14) cring.cring_simprules(29) cring.cring_simprules(3) cring.cring_simprules(5) divide_id'(1) f'a_def fb_def p_pow_nonzero padic_set_simp0 partial_object.select_convs(1) zero_less_one)
            then show ?thesis
              using fb_def by auto 
          qed
        qed
        then have A81: "(f'a \<otimes> t) 1= (\<ominus> (divide (fb) (\<p>[^](Suc n)))) 1"
          using res_uminus  
          using A7 Res_def Z\<^sub>p_def \<open>val_Zp (f \<star> b) \<succeq>\<^bsub>G\<^esub> val_Zp (\<p> [^] Suc n)\<close> 
            divide_id'(1) p_pow_nonzero padic_inv prime by auto
        have A82: "(fb \<oplus> f'a \<otimes>(\<p>[^](Suc n) \<otimes> t)) (Suc (Suc n)) = 0"
        proof-
          obtain h where h_def: "h \<in> carrier Z\<^sub>p \<and> (f'a \<otimes> t) = (\<ominus>(divide (fb) (\<p>[^](Suc n)))) \<oplus> h \<otimes> \<p>[^](1::nat)"
            using eq_res_mod[of "(f'a \<otimes> t)" "\<ominus>(divide (fb) (\<p>[^](Suc n)))" 1]
            by (metis (no_types, lifting) "2" A7 A81 Zp_int_inc_closed Zp_is_cring 
                \<open>val_Zp (f \<star> b) \<succeq>\<^bsub>G\<^esub> val_Zp (\<p> [^] Suc n)\<close> cring.cring_simprules(14)
                cring.cring_simprules(3) cring.cring_simprules(5) divide_id'(1) f'a_def
                fb_def p_pow_car_nat p_pow_nonzero t_def)
          have A820: "(f'a \<otimes> t) \<in> carrier Z\<^sub>p"
            by (metis A7 Zp_is_cring \<open>val_Zp (f \<star> b) \<succeq>\<^bsub>G\<^esub> val_Zp (\<p> [^] Suc n)\<close>
                cring.cring_simprules(3) cring.cring_simprules(5) divide_id'(1) 
                fb_def h_def p_pow_car_nat p_pow_nonzero sum_closed)
          have A821: "(\<ominus>(divide (fb) (\<p>[^](Suc n)))) \<in> carrier Z\<^sub>p"
            by (metis A7 Zp_is_cring \<open>val_Zp (f \<star> b) \<succeq>\<^bsub>G\<^esub> val_Zp (\<p> [^] Suc n)\<close> 
                cring.cring_simprules(3) divide_id'(1) fb_def p_pow_nonzero)
          have A822: "(h \<otimes> \<p>[^](1::nat)) \<in> carrier Z\<^sub>p"
            by (simp add: Zp_nat_inc_closed h_def monom_term_car)
          have A823:"(f'a \<otimes> t) \<oplus> (divide (fb) (\<p>[^](Suc n))) =  h \<otimes> \<p>[^](1::nat)"
            using h_def A820 A821 A822 Zp_is_cring 
            by (metis A7 \<open>val_Zp (f \<star> b) \<succeq>\<^bsub>G\<^esub> val_Zp (\<p> [^] Suc n)\<close>
                cring.cring_simprules(10) cring.cring_simprules(19) 
                cring.cring_simprules(21) divide_id'(1) fb_def p_pow_nonzero)
          then have A824: "(f'a \<otimes> t)\<otimes>  (\<p>[^](Suc n)) \<oplus> (fb)  = h \<otimes> (\<p>[^](Suc (Suc n)))"
          proof-
            have "((f'a \<otimes> t) \<oplus> (divide (fb) (\<p>[^](Suc n)))) \<otimes>  (\<p>[^](Suc n)) =  h \<otimes> \<p>[^](1::nat) \<otimes>  (\<p>[^](Suc n))"
              using A823 by auto 
            then have A8240: "((f'a \<otimes> t) \<otimes>  (\<p>[^](Suc n))) \<oplus> (divide (fb) (\<p>[^](Suc n))) \<otimes>  (\<p>[^](Suc n)) =  h \<otimes> (\<p>[^](1::nat) \<otimes>  (\<p>[^](Suc n)))"
              using A820 A821 A822 Zp_is_cring 
              by (metis A7 \<open>val_Zp (f \<star> b) \<succeq>\<^bsub>G\<^esub> val_Zp (\<p> [^] Suc n)\<close> cring.cring_simprules(11)
                  cring.cring_simprules(13) divide_id'(1) fb_def h_def p_pow_car_nat p_pow_nonzero)
            have "(divide (fb) (\<p>[^](Suc n))) \<otimes>  (\<p>[^](Suc n))  = fb"
              by (simp add: "1")
            then have A8241: "((f'a \<otimes> t) \<otimes>  (\<p>[^](Suc n))) \<oplus>  (fb) =  h \<otimes> (\<p>[^](1::nat) \<otimes>  (\<p>[^](Suc n)))"
              using A8240 by simp 
            then show ?thesis 
              by (simp add: p_natpow_prod)
          qed
          then show ?thesis 
            using p_pow_factor[of h "(Suc (Suc n))" "Suc (Suc n)"] 
            by (metis (mono_tags, lifting) "2" A7 A820 Zp_int_mult_closed Zp_is_cring 
                Zp_nat_mult_closed Zp_one_car cring.cring_simprules(10) 
                cring.cring_simprules(11) cring.cring_simprules(14) 
                f'a_def h_def monom_term_car order_refl p_pow_car_nat t_def)
        qed
        have A83: "(f'a \<otimes>(\<p>[^](Suc n) \<otimes> t)) (Suc (Suc n))=  (f'b \<otimes> (\<p> [^] (Suc n) \<otimes> t))(Suc (Suc n))"
        proof- 
          have A830: "f'a 1 = f'b 1"
            using f'a_def f'b_def b_def assms deriv_res
            by metis
          have A831: "f'a \<in> carrier Z\<^sub>p"
            using f'a_def   "2" by blast
          have A832: "f'b \<in> carrier Z\<^sub>p"
            using f'b_def b_def assms UP_domain.derivative_closed[of Z\<^sub>p f b] P_Zp_is_UP_domain 
            by auto 
          then obtain j where j_def0: "j \<in> carrier Z\<^sub>p \<and> f'a = f'b \<oplus> (\<p>[^](1::nat) \<otimes>j)"
            using f'a_def f'b_def   eq_res_mod[of f'a f'b 1] A830 A831 A832 
            by auto  
          then have j_def: "j \<in> carrier Z\<^sub>p \<and> f'a = f'b \<oplus> (j \<otimes> \<p>)"
            by (simp add: Zp_nat_inc_closed cring.cring_simprules(14) p_pow_rep0)
          then have "(f'a \<otimes>(\<p>[^](Suc n) \<otimes> t)) =  (f'b \<oplus> (j \<otimes> \<p>))\<otimes>(\<p>[^](Suc n) \<otimes> t)"
            by blast
          then have "(f'a \<otimes>(\<p>[^](Suc n) \<otimes> t)) =  (f'b\<otimes>(\<p>[^](Suc n) \<otimes> t)) \<oplus> (j \<otimes> \<p>)\<otimes>(\<p>[^](Suc n) \<otimes> t)"
            by (metis A832 Zp_is_cring Zp_nat_inc_closed cring.cring_simprules(13) 
                cring.cring_simprules(5) j_def0 pnt_car)
          then have "(f'a \<otimes>(\<p>[^](Suc n) \<otimes> t)) =  (f'b\<otimes>(\<p>[^](Suc n) \<otimes> t)) \<oplus> (j \<otimes> \<p>[^](Suc (Suc n)) \<otimes> t)"
            by (metis Zp_int_inc_closed Zp_is_cring Zp_nat_inc_closed cring.cring_simprules(11)
                j_def p_natpow_prod_Suc(1) p_pow_car_nat pnt_car t_def)
          then have A833: "(f'a \<otimes>(\<p>[^](Suc n) \<otimes> t)) =  (f'b\<otimes>(\<p>[^](Suc n) \<otimes> t)) \<oplus> ( \<p>[^](Suc (Suc n)) \<otimes> (j \<otimes>t))"
            by (metis (no_types, lifting) Z\<^sub>p_def Zp_is_cring Zp_one_car cring.cring_simprules(14)
                j_def p_pow_car_nat padic_integers.Zp_int_mult_closed padic_integers_axioms 
                padic_mult_assoc prime t_def)
          have A834:"( \<p>[^](Suc (Suc n)) \<otimes> (j \<otimes>t)) (Suc (Suc n)) = 0"
            by (smt Z\<^sub>p_def Zp_is_cring Zp_one_car cring.cring_simprules(5) j_def ord_Zp_p_pow 
                p_pow_car_nat padic_integers.Zp_int_mult_closed padic_integers.res_mult_zero(1) 
                padic_integers_axioms t_def zero_below_ord zero_less_Suc)
          have "(f'a \<otimes>(\<p>[^](Suc n) \<otimes> t)) (Suc (Suc n)) =  
                          (f'b\<otimes>(\<p>[^](Suc n) \<otimes> t)) (Suc (Suc n))
                        \<oplus>\<^bsub>R (Suc (Suc n))\<^esub> ( \<p>[^](Suc (Suc n)) \<otimes> (j \<otimes>t))(Suc (Suc n))"
            using A833
            by (simp add: Res_def Z\<^sub>p_def padic_add_def)
          then show ?thesis 
            using A834 
            unfolding Res_def 
            by (smt A6 Z\<^sub>p_def Zp_is_cring Zp_one_car 
                \<open>f'a \<otimes> (\<p> [^] Suc n \<otimes> t) = f'b \<otimes> (\<p> [^] Suc n \<otimes> t) \<oplus> j \<otimes> \<p> [^] Suc (Suc n) \<otimes> t\<close> 
                cring.cring_simprules(10) cring.cring_simprules(11) cring.cring_simprules(14)
                cring.cring_simprules(5) j_def p_pow_car_nat padic_integers.Zp_int_mult_closed
                padic_integers_axioms res_add_zero(1) t_def zero_less_Suc)
        qed
        then show "(fb \<oplus> f'b \<otimes>(\<p>[^](Suc n) \<otimes> t)) (Suc (Suc n)) = 0"
          using A83 A82 
          by (simp add: Z\<^sub>p_def padic_add_def)
      qed
      show ?thesis 
        using A8 A4 
        by (simp add: b_def cring.cring_simprules(10) pnt_car)
    qed
   
    obtain b1 where b1_def: "b1 = (b \<oplus> ((\<p>[^](Suc n)) \<otimes> t))"
      by simp
 
    have b10: "b1 \<in> carrier Z\<^sub>p"
      by (simp add: Zp_int_mult_closed Zp_one_car b1_def b_def cring.cring_simprules(5) t_def)
    have b11: "(f \<star> b1) (Suc (Suc n)) = 0"
      using b1_def 5 
      by auto
    have b12: "b1 1 = a 1"
    proof-
      have "b1 1 = b 1"
      proof-
        have "b1 1 = (b \<oplus> ((\<p>[^](Suc n)) \<otimes> t)) 1" 
          using b1_def by auto 
        then have b120: "b1 1 = (b 1) \<oplus>\<^bsub>R 1\<^esub> ((\<p>[^](Suc n)) \<otimes> t) 1" 
          by (simp add: Res_def Z\<^sub>p_def padic_add_def)
        have b121: "((\<p>[^](Suc n)) \<otimes> t) 1 = 0"
          by (metis Z\<^sub>p_def Zero_not_Suc Zp_int_mult_closed Zp_one_car nat_int of_nat_0 
              ord_Zp_0_criterion ord_Zp_p_pow p_pow_car_nat padic_integers.res_mult_zero(1) 
              padic_integers_axioms t_def zero_less_one)
        show ?thesis 
          using b120 b121 
          unfolding Res_def
          by (smt Z\<^sub>p_def Zp_int_inc_zero Zp_int_mult_closed Zp_one_car add_zero(1) 
              b_def ord_Zp_0_criterion ord_of_nonzero(1) padic_add_def ring.simps(2))
      qed
      then show ?thesis using b_def by auto 
    qed
    have b13: "b1 (Suc n) = b (Suc n)"
      using b1_def 
      by (simp add: Zp_int_mult_closed Zp_one_car b_def
          cring.cring_simprules(14) cring.cring_simprules(5) t_def)
    show ?thesis using b10 b11 b12 b13 by blast
qed

(*The sequence which will converge to the root obtained by hensel's lemma*)
fun hensel_seq where
"hensel_seq f a 0 = a"|
"hensel_seq f a (Suc n) = (SOME b. b \<in> carrier Z\<^sub>p \<and> (f \<star> b) (Suc (Suc n)) = 0 \<and> b 1 = a 1 \<and> b (Suc n) = (hensel_seq f a n) (Suc n))"

(*Inductive lemma for proving the properties of the hensel sequence*)
lemma hensel_seq_id_induct:
  assumes "hensel f a"
  shows 
 "\<And>b0 b1. b0  = hensel_seq f a n \<Longrightarrow>
  b1  = hensel_seq f a (Suc n) \<Longrightarrow>
  b1 \<in> carrier Z\<^sub>p \<and> (f \<star> b1) (Suc (Suc n)) = 0 \<and> b1 1 = a 1 \<and> b1 (Suc n) = b0 (Suc n)"
proof(induction n)
  show "\<And>b0 b1. b0 = hensel_seq f a 0 \<Longrightarrow> 
        b1 = hensel_seq f a (Suc 0) \<Longrightarrow> 
        b1 \<in> carrier Z\<^sub>p \<and> (f \<star> b1) (Suc (Suc 0)) = 0 \<and> b1 1 = a 1 \<and> b1 (Suc 0) = b0 (Suc 0)"
  proof-
    fix b0 b1
    assume B:  "b0 = hensel_seq f a 0" 
               "b1 = hensel_seq f a (Suc 0)"
    have B0: "b0 = a" 
      using B 
      by simp
    have B1: "b0 \<in> carrier Z\<^sub>p \<and> (f \<star> b0) (Suc 0) = 0 \<and> b0 1 = a 1"
      using assms B0 
      by auto 
    have B2: "\<exists> b' \<in> carrier Z\<^sub>p. (f \<star> b') (Suc (Suc 0)) = 0 \<and> b' 1 = a 1 \<and> b' (Suc 0) = b0 (Suc 0)"
      using pre_hensel assms B1 
      by blast
    have B3: "b1= (SOME b. b \<in> carrier Z\<^sub>p \<and> (f \<star> b) (Suc (Suc 0)) = 0 \<and> b 1 = a 1 \<and> b (Suc 0) = b0 (Suc 0))"
      using B
      by simp
    show  "b1 \<in> carrier Z\<^sub>p \<and> (f \<star> b1) (Suc (Suc 0)) = 0 \<and> b1 1 = a 1 \<and> b1 (Suc 0) = b0 (Suc 0)"
      using B3 B2 
      by (metis (mono_tags, lifting) B0 One_nat_def someI_ex)
  qed
  show "\<And>n b0 b1. (\<And>b0 b1. b0 = hensel_seq f a n \<Longrightarrow> b1 = hensel_seq f a (Suc n) \<Longrightarrow>
             b1 \<in> carrier Z\<^sub>p \<and> (f \<star> b1) (Suc (Suc n)) = 0 \<and> b1 1 = a 1 \<and> b1 (Suc n) = b0 (Suc n)) \<Longrightarrow>
             b0 = hensel_seq f a (Suc n) \<Longrightarrow>
             b1 = hensel_seq f a (Suc (Suc n)) \<Longrightarrow> 
             b1 \<in> carrier Z\<^sub>p \<and> (f \<star> b1) (Suc (Suc (Suc n))) = 0 \<and> b1 1 = a 1 \<and> b1 (Suc (Suc n)) = b0 (Suc (Suc n))"
  proof-
    fix n b0 b1
    assume IH: "(\<And> b0 b1. b0 = hensel_seq f a n \<Longrightarrow> b1 = hensel_seq f a (Suc n) \<Longrightarrow>
             b1 \<in> carrier Z\<^sub>p \<and> (f \<star> b1) (Suc (Suc n)) = 0 \<and> b1 1 = a 1 \<and> b1 (Suc n) = b0 (Suc n))" 
    assume A: "b0 = hensel_seq f a (Suc n)"
              "b1 = hensel_seq f a (Suc (Suc n))"
    show "b1 \<in> carrier Z\<^sub>p \<and> (f \<star> b1) (Suc (Suc (Suc n))) = 0 \<and> b1 1 = a 1 \<and> b1 (Suc (Suc n)) = b0 (Suc (Suc n))"
    proof-
      have A0: " b0 \<in> carrier Z\<^sub>p \<and> (f \<star> b0) (Suc (Suc n)) = 0 \<and> b0 1 = a 1 \<and> b0 (Suc n) = (hensel_seq f a n) (Suc n)"
        using A IH 
        by blast
      have A1: "\<exists> b' \<in> carrier Z\<^sub>p. (f \<star> b') (Suc (Suc (Suc n))) = 0 \<and> b' 1 = a 1 \<and> b' (Suc (Suc n)) = b0 (Suc (Suc n))"
        using pre_hensel A0 assms 
        by auto 
      have A2: "b1 = (SOME b. b \<in> carrier Z\<^sub>p \<and> (f \<star> b) (Suc (Suc (Suc n))) = 0 \<and> b 1 = a 1 \<and> b (Suc (Suc n)) = b0 (Suc (Suc n)))"
        using A 
        by simp
      let ?P = "(\<lambda> b. b \<in> carrier Z\<^sub>p \<and> (f \<star> b) (Suc (Suc (Suc n))) = 0 \<and> b 1 = a 1 \<and> b (Suc (Suc n)) = b0 (Suc (Suc n)))"
      show ?thesis 
        using A1 A2 someI_ex[of ?P]
        by blast 
    qed
  qed
qed

(*Properties of the hensel sequence*)
lemma hensel_seq_id_0:
  assumes "hensel f a"
  assumes "b = hensel_seq f a n"
  shows "b \<in> carrier Z\<^sub>p \<and> (f \<star> b) (Suc n) = 0 \<and> b 1 = a 1" 
proof(cases "n = 0")
  case True
  then have "a = b" 
    using assms by simp
  then show ?thesis 
    using True[simp] assms(1) 
    by auto 
next
  case False
  obtain k where k_def: "n = Suc k"
    using False 
    by (meson lessI less_Suc_eq_0_disj)
  show ?thesis 
    using assms k_def[simp] hensel_seq_id_induct[of f a "hensel_seq f a k" k b]
    by blast
qed

lemma hensel_seq_id_1:
  assumes "hensel f a"
  shows "(hensel_seq f a n) (Suc n) = (hensel_seq f a (Suc n)) (Suc n)"
  using assms hensel_seq_id_induct[of f a "(hensel_seq f a n)" n "(hensel_seq f a (Suc n))" ]
  by auto

(*Hensel sequence is closed over Z\<^sub>p*)
lemma hensel_seq_closed:
  assumes "hensel f a"
  shows "is_closed_seq (hensel_seq f a)"
  using assms hensel_seq_id_0[of f a] 
  unfolding is_closed_seq_def 
  by blast 

(*Hensel sequence is cauchy*)
lemma hensel_seq_is_cauchy:
  assumes "hensel f a"
  shows "is_cauchy (hensel_seq f a)"
proof(rule is_cauchyI)
  show "is_closed_seq (hensel_seq f a)"
    using hensel_seq_closed assms 
    by auto 
  show "\<And>n. \<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> hensel_seq f a n0 n = hensel_seq f a n1 n"
  proof-
    fix n
    have A0:  "\<And>m. hensel_seq f a (m+n) n = hensel_seq f a n n"
    proof-
      fix m
      show "hensel_seq f a (m+n) n = hensel_seq f a n n"
        apply(induction m)
         apply simp
      proof-
        fix m
        assume IH: "hensel_seq f a (m + n) n = hensel_seq f a n n "
        show "hensel_seq f a (Suc m + n) n = hensel_seq f a n n"
        proof-
          have I0: "hensel_seq f a (Suc m + n) (Suc m + n) = hensel_seq f a (m+n) (Suc m + n)"
            using assms hensel_seq_id_1[of f a "m+n"]
            using add_Suc by presburger
          have I1: "hensel_seq f a (Suc m + n) \<in> carrier Z\<^sub>p"  "hensel_seq f a (m+n) \<in> carrier Z\<^sub>p"
            using hensel_seq_closed[of f a] assms 
            unfolding is_closed_seq_def 
            apply blast
            using hensel_seq_closed[of f a] assms 
            unfolding is_closed_seq_def 
            apply blast done
          have I2: "hensel_seq f a (Suc m + n) n = hensel_seq f a (m+n) n"
          proof-
            have I20: "hensel_seq f a (Suc m + n) n = (hensel_seq f a (Suc m + n) (Suc m + n)) mod (p^n)"
              using I1 r_Zp r_def 
              by auto
            have I21: "hensel_seq f a (m + n) n = (hensel_seq f a (Suc m + n) (Suc m + n)) mod (p^n)"
              using I1 r_Zp r_def I0
              by auto 
            show ?thesis 
              using I20 I21 
              by auto 
          qed
          show ?thesis 
            using I2 IH 
            by auto 
        qed
      qed
    qed
    have A1: "\<forall>n0 n1. n < n0 \<and> n < n1 \<longrightarrow> hensel_seq f a n0 n = hensel_seq f a n1 n"
      apply auto
    proof-
      fix n0 n1
      assume A00: "n < n0" "n < n1"
      show " hensel_seq f a n0 n = hensel_seq f a n1 n" 
        using A0 A00 
        by (metis add.commute less_imp_add_positive)
    qed
    show "\<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> hensel_seq f a n0 n = hensel_seq f a n1 n"
      using A1 by blast 
  qed
qed

(*Basic version of hensel's lemma*)
lemma hensels_lemma:
assumes "hensel f a"
shows "\<exists> \<alpha> \<in> carrier Z\<^sub>p. f\<star>\<alpha> = \<zero> \<and> \<alpha> 1 = a 1"
proof-
  obtain s where s_def: "s = hensel_seq f a"
    by simp
  have C: "is_cauchy s" 
    using assms s_def hensel_seq_is_cauchy 
    by auto 
  obtain \<alpha> where alpha_def: "\<alpha>= res_lim s"
    by simp
  have Con: "converges_to s \<alpha>"
    using C alpha_def 
    by (simp add: C is_cauchy_imp_has_limit)
  have Cont: "is_continuous (fun_of f)"
    using assms  polynomial_is_continuous 
    by blast
  have A0: "(f\<star>\<alpha>) = res_lim ((fun_of f)\<^sub>*s)"
    using C Cont alpha_def padic_integers.alt_seq_limit
          padic_integers.res_lim_pushforward padic_integers.res_lim_pushforward'
          padic_integers_axioms 
    by auto
  have A1: "res_lim ((fun_of f)\<^sub>*s) = \<zero>"
  proof-
    have "converges_to ((fun_of f)\<^sub>*s) \<zero>"
    proof(rule converges_toI)
      show "is_closed_seq((fun_of f)\<^sub>*s)"
        using Con Cont continuous_is_closed converges_to_def push_forward_of_closed_is_closed by blast
      show "\<zero> \<in> carrier Z\<^sub>p"  
        by (simp add: cring.cring_simprules(2))
      show "\<And>n. \<exists>N. \<forall>k>N. ((fun_of f)\<^sub>*s) k n = \<zero> n"
      proof-
        fix n 
        show "\<exists>N. \<forall>k>N. ((fun_of f)\<^sub>*s) k n = \<zero> n"
        proof-
          have "\<forall>k>n. ((fun_of f)\<^sub>*s) k n = \<zero> n"
          proof
            fix k
            show "n < k \<longrightarrow> ((fun_of f)\<^sub>*s) k n = \<zero> n"
            proof
              assume "n < k"
              show "((fun_of f)\<^sub>*s) k n = \<zero> n"
              proof-
                have 0: "((fun_of f)\<^sub>*s) k n = (fun_of f) (s k) n"
                  by (simp add: push_forward_def)
                then have 1:  "((fun_of f)\<^sub>*s) k n  = (fun_of f) (hensel_seq f a k) n"
                  using s_def by blast
                have 2: "(fun_of f) (hensel_seq f a k) n = 0"
                  by (smt Cont \<open>n < k\<close> assms continuous_is_closed 
                      hensel_seq_id_0 is_closed_fun_simp less_imp_of_nat_less
                      ord_Zp_geq semiring_1_class.of_nat_simps(2) zero_below_ord zero_vals)
                show ?thesis using 1 2 
                  by (simp add: zero_vals)
              qed
            qed
          qed
          then show ?thesis 
            by blast
        qed
      qed
    qed
    then show ?thesis 
      by (metis converges_to_def unique_limit')
  qed
  have A2: "(f\<star>\<alpha>) = \<zero>"
    using A0 A1 by auto 
  have "\<alpha> 1 = a 1"
  proof-
    obtain N where N_def: "s N 1 = \<alpha> 1"
      using C alpha_def res_lim_cauchy by blast
    then have "s N 1 = a 1"
      using assms hensel_seq_id_0 s_def by blast
    then show ?thesis 
      using N_def by auto
  qed
  then show ?thesis using A2 
    using Con converges_to_def by blast
qed
end
end