theory padic_int_polynomials
imports padic_int_topology domain_poly
begin 

context padic_int_poly
begin

type_synonym padic_int_poly = "nat \<Rightarrow> padic_int"

lemma monom_term_car:
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "x \<in> carrier Z\<^sub>p"
  shows "c \<otimes> x[^](n::nat) \<in> carrier Z\<^sub>p"
  using assms Zp_is_cring monoid.nat_pow_closed 
  by (simp add: monoid.nat_pow_closed cring.cring_simprules(5) cring_def ring_def)

(*Univariate polynomial ring over Z\<^sub>p*)

abbreviation Z\<^sub>p_x where
"Z\<^sub>p_x \<equiv> UP Z\<^sub>p"

lemma Z\<^sub>p_x_is_UP_ring[simp]:
"UP_ring Z\<^sub>p"
  by (metis UP_ring.intro Zp_is_cring cring_def)

lemma Z\<^sub>p_x_is_UP_cring[simp]:
"UP_cring Z\<^sub>p"
  by (simp add: UP_cring_def)

lemma Z\<^sub>p_x_is_UP_domain[simp]:
"UP_domain Z\<^sub>p"
  by (simp add: UP_domain_def)

lemma Z\<^sub>p_x_ring[simp]:
"ring Z\<^sub>p_x "
  by (simp add: UP_ring.UP_ring)

lemma Z\<^sub>p_x_cring[simp]:
"cring Z\<^sub>p_x "
  by (simp add: UP_cring.UP_cring)

lemma Z\<^sub>p_x_domain[simp]:
"domain Z\<^sub>p_x "
  by (simp add: UP_domain.UP_domain)

(*Basic simp rules to streaminline computation*)
lemma pow_closedP[simp]:
  assumes "f \<in> carrier Z\<^sub>p_x"
  shows "f[^]\<^bsub>Z\<^sub>p_x\<^esub>(n::nat) \<in> carrier Z\<^sub>p_x " 
  by (meson Z\<^sub>p_x_ring assms monoid.nat_pow_closed ring_def)

lemma pow_closed[simp]:
  assumes "a \<in> carrier Z\<^sub>p"
  shows "a[^](n::nat) \<in> carrier Z\<^sub>p"
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
  shows "\<zero>\<^bsub>Z\<^sub>p_x\<^esub>[^]\<^bsub>Z\<^sub>p_x\<^esub>(n::nat) = \<zero>\<^bsub>Z\<^sub>p_x\<^esub>"
  using assms ring.pow_zero[of Z\<^sub>p_x] by simp

lemma sum_closedP[simp]:
  assumes "f \<in> carrier Z\<^sub>p_x"
  assumes "g \<in> carrier Z\<^sub>p_x"
  shows "f \<oplus>\<^bsub>Z\<^sub>p_x\<^esub>g \<in>  carrier Z\<^sub>p_x"
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
  assumes "f \<in> carrier Z\<^sub>p_x" 
  shows "f \<otimes>\<^bsub>Z\<^sub>p_x\<^esub> \<zero>\<^bsub>Z\<^sub>p_x\<^esub> = \<zero>\<^bsub>Z\<^sub>p_x\<^esub>"
        "\<zero>\<^bsub>Z\<^sub>p_x\<^esub> \<otimes>\<^bsub>Z\<^sub>p_x\<^esub> f = \<zero>\<^bsub>Z\<^sub>p_x\<^esub>"
  apply (simp add: assms cring.cring_simprules(27))
  apply (simp add: assms cring.cring_simprules(26))
  done

lemma add_zero[simp]:
  assumes "f \<in> carrier Z\<^sub>p"
  shows "f \<oplus> \<zero> = f"
        "\<zero> \<oplus> f = f"
   apply (simp add: assms cring.cring_simprules)
   apply (simp add: assms cring.cring_simprules)
   done

lemma add_zeroP[simp]:
  assumes "f \<in> carrier Z\<^sub>p_x "
  shows "f \<oplus>\<^bsub>Z\<^sub>p_x\<^esub> \<zero>\<^bsub>Z\<^sub>p_x\<^esub> = f"
        "\<zero>\<^bsub>Z\<^sub>p_x\<^esub> \<oplus>\<^bsub>Z\<^sub>p_x\<^esub> f = f"
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

(*Truncation function, which sends a polynomial f \<Longrightarrow> (f - leading_term (f)), which has strictly
smaller degree in the case where degree f > 0*)
abbreviation trunc where 
"trunc \<equiv> truncate Z\<^sub>p"

(*Turning a padic polynomial into a function on Z\<^sub>p*)
abbreviation fun_of :: "_ \<Rightarrow> padic_int_fun" (infixl "\<^emph>" 70) where
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

(*Z\<^sub>p_x addition commutes with evaluation addition*)
lemma fun_of_fun_sum:
  assumes "f \<in> carrier Z\<^sub>p_x"
  assumes "g \<in> carrier Z\<^sub>p_x"
  assumes "h = f \<oplus>\<^bsub>Z\<^sub>p_x\<^esub> g"
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
    have "(eval Z\<^sub>p Z\<^sub>p (\<lambda>x. x)) x \<in> (ring_hom Z\<^sub>p_x Z\<^sub>p)"
      using UP_pre_univ_prop_fact A UP_pre_univ_prop.eval_ring_hom[of Z\<^sub>p Z\<^sub>p "(\<lambda>x. x)" x]    by auto   
    then show "eval Z\<^sub>p Z\<^sub>p (\<lambda>x. x) x f \<oplus> eval Z\<^sub>p Z\<^sub>p (\<lambda>x. x) x g = eval Z\<^sub>p Z\<^sub>p (\<lambda>x. x) x h "
      using assms ring_hom_add   by (simp add: \<open>f \<in> carrier Z\<^sub>p_x\<close> ring_hom_def)
  qed
qed

(*monomial functions are monomials*)
lemma fun_of_monom_is_monom0:
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "c \<noteq>\<zero>"
  assumes "f = monom Z\<^sub>p_x c n"
  assumes "x \<in> carrier Z\<^sub>p"
  shows "f\<^emph>x = mon c n x"
proof-
  have 1: "f\<^emph>x = c \<otimes> x [^] n"
    using UP_domain.fun_of_monom assms Z\<^sub>p_x_is_UP_domain 
    by (simp add: UP_domain.fun_of_monom)
  show ?thesis
    unfolding mon_def scalar_mult_def X_pow_Zp_def
    apply auto 
     apply (metis "1" Zp_is_cring cring.axioms(1) monoid.nat_pow_0 ring_def)
    using 1  by simp
qed

lemma fun_of_monom_is_monom:
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "f = monom Z\<^sub>p_x c n"
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
    by (simp add:UP_domain.coeff_simp1 UP_ring.monom_closed assms(1) assms(2))
  show ?thesis
    unfolding eq_on_Zp_def
    apply(auto )
    unfolding mon_def scalar_mult_def X_pow_Zp_def
  proof-
    fix x
    assume A: "x \<in> carrier Z\<^sub>p"
    have P0: "f\<^emph>x = \<zero>"
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
      have C2: "f \<in> carrier Z\<^sub>p_x"
        apply(auto simp: assms(2))
        using assms(1) Z\<^sub>p_x_is_UP_ring UP_ring.monom_closed[of Z\<^sub>p c n] apply simp
        done
      have C3: "f\<^emph>x = (\<Oplus>i \<in> {..degree f}. (cf f i) \<otimes> x [^] i)" 
        using  A  C2 Z\<^sub>p_x_is_UP_domain UP_domain.fun_of_formula[of Z\<^sub>p f x]  
        by blast
      show ?thesis 
        apply(auto simp: C3 H1 )
        apply(auto simp: H)
        apply(auto simp: C1)
        apply(auto simp: C0 abelian_monoid.finsum_zero)
        done
    qed
    show "f\<^emph>x = c \<otimes> (if n = 0 then \<one> else x [^] n) "
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
  using Z\<^sub>p_x_is_UP_domain assms 
    UP_domain.is_monom_id[of Z\<^sub>p f] 
    fun_of_monom_is_monom[of "lc f" f "degree f"] 
    UP_domain.lc_closed[of Z\<^sub>p f] 
  unfolding   is_monom_poly_def
  by auto 

(*monomials are continuous*)

lemma monom_poly_is_continuous:
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "f = monom Z\<^sub>p_x c n"
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
  using Z\<^sub>p_x_is_UP_domain UP_domain.is_monom_id[of Z\<^sub>p f]
        monom_poly_is_continuous[of "lc f" f "degree f"]
        assms UP_domain.lc_closed[of Z\<^sub>p f] 
  unfolding is_monom_poly_def 
  by (simp add:  )

lemma degree_0_is_constant:
  assumes "f \<in> carrier Z\<^sub>p_x"
  assumes "degree f = 0"
  obtains g where "is_constant_fun g" and "g \<doteq> fun_of f"
proof- 
  obtain c where c0: "c \<in> carrier Z\<^sub>p" and  c1: "\<And>x.  x \<in> carrier Z\<^sub>p \<Longrightarrow> (fun_of f) x = c"
    using Z\<^sub>p_x_is_UP_domain UP_domain.degree_0_imp_constant0  assms(1) assms(2) by blast
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
    show "g x = f\<^emph>x "
    proof-
      have LHS: "g x = c" 
        using g_def using to_const_fun_def by simp  
      have RHS: "f\<^emph>x = c"
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
lemma degree_0_is_continuous:
  assumes "f \<in> carrier Z\<^sub>p_x"
  assumes "degree f = 0"
  shows "is_continuous (fun_of f)"
proof-
  obtain g where 0: "is_constant_fun g" and 1: "g \<doteq> fun_of f"
    using assms degree_0_is_constant by auto 
  have "is_continuous g" 
    using 0 by (simp add: constant_is_continuous)
  then show ?thesis 
    using 1 is_continuous_eq by blast
qed

(*all polynomials induce continuous functions*)
lemma polynomial_is_continuous_induct:
  fixes n::nat
  shows "\<And>f. f \<in> carrier Z\<^sub>p_x \<Longrightarrow> degree f \<le> n \<Longrightarrow> is_continuous (fun_of f)"
proof(induction n)
case 0
  then show ?case 
    using degree_0_is_continuous by blast
next
  case (Suc n)
  fix n
  assume IH: "\<And>f. f \<in> carrier Z\<^sub>p_x \<Longrightarrow> (degree f \<le> n \<Longrightarrow> is_continuous (fun_of f))"
  show "\<And>f. f \<in> carrier Z\<^sub>p_x \<Longrightarrow> degree f \<le> Suc n \<Longrightarrow> is_continuous (fun_of f) "
  proof-
    fix f
    assume A0:"f \<in> carrier Z\<^sub>p_x"
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
      obtain g where g_def: "g \<in> carrier Z\<^sub>p_x \<and> (f = g \<oplus>\<^bsub>Z\<^sub>p_x\<^esub> (lt f)) \<and> degree g < degree f"
        using E0 A0 Z\<^sub>p_x_is_UP_domain UP_domain.lt_decomp[of Z\<^sub>p f] by auto  
      have g0: "g \<in> carrier Z\<^sub>p_x"
        using g_def by auto 
      have g1: "f = g \<oplus>\<^bsub>Z\<^sub>p_x\<^esub> (lt f)" 
        using g_def by auto 
      have g2: "degree g < degree f" 
        using g_def by auto 
      have LS: "is_continuous (fun_of g)" 
        using E g0 g1 g2 IH by auto 
      have RS: "is_continuous (fun_of (lt f))"
        using monom_poly_is_continuous leading_term_def A0  UP_ring.lcoeff_closed
            Z\<^sub>p_x_is_UP_ring UP_domain.coeff_simp1 Z\<^sub>p_x_is_UP_domain   by metis
      have "fun_of f \<doteq>  fun_sum (fun_of g) (fun_of (lt f))"
        using  fun_of_fun_sum g0 A0 g1  eq_on_Zp_def UP_domain.lt_closed 
        by (metis (mono_tags, lifting) Z\<^sub>p_x_is_UP_domain)
      then show ?thesis
        using LS RS sum_of_cont_is_cont 
        by (metis eq_on_Zp_def is_continuous_eq)
    qed
  qed
qed

lemma polynomial_is_continuous:
  assumes "f \<in> carrier Z\<^sub>p_x"
  shows "is_continuous (fun_of f)"
proof-
  obtain n where n_def: "n = degree f" 
    by simp
  then show ?thesis 
    using assms polynomial_is_continuous_induct by auto 
qed

(**************************************************************************************************)
(**************************************************************************************************)
(**********************************    Polynomial Substitution   **********************************)
(**************************************************************************************************)
(**************************************************************************************************)

(*The inclusion of Z\<^sub>p into Z\<^sub>p_x*)

abbreviation to_poly :: "padic_int \<Rightarrow> padic_int_poly" where
"to_poly \<equiv> to_polynomial Z\<^sub>p"

lemma to_poly_is_ring_hom:
"to_poly \<in> ring_hom Z\<^sub>p Z\<^sub>p_x"
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

(*Powers of X*)
abbreviation X_pow where
"X_pow n \<equiv> X[^]\<^bsub>Z\<^sub>p_x\<^esub>n"

(*The Taylor expansion*)

abbreviation Taylor ("T\<^bsub>_\<^esub>") where
"Taylor \<equiv> taylor_expansion Z\<^sub>p"

(*Derivative function*)

abbreviation deriv   where
"deriv \<equiv> derivative Z\<^sub>p"

(*Zero coefficient function*)
abbreviation cf0 where
"cf0 \<equiv> zero_coefficient"

(*The horner shift function. Satisfies the equation:       f = a0 + X(poly_shift f)      *)
abbreviation poly_shift where
"poly_shift \<equiv> polynomial_shift Z\<^sub>p"

(*The iterated shift function. Satisfies   f = a0 + a1*X + ...+ (an-1)*X^(n-1) + X^n(shift n f) *)
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
  shows "(X_pow(n::nat)\<^emph> a) k = (X_pow n\<^emph>b) k"
proof(induction n)
  case 0
  then show ?case 
    by (smt Z\<^sub>p_x_is_UP_domain Z\<^sub>p_x_is_UP_ring Z\<^sub>p_x_ring UP_domain.X_closed UP_ring.deg_monom 
        UP_ring.monom_one Zp_one_car Zp_one_notzero assms(1) assms(2) degree_0_is_constant 
        eq_on_Zp_def is_constant_fun_def monoid.nat_pow_0 pow_closedP ring_def)
next
  case (Suc n)
  fix n::nat
  assume IH: "(X [^]\<^bsub>Z\<^sub>p_x\<^esub> n \<^emph> a) k = (X [^]\<^bsub>Z\<^sub>p_x\<^esub> n \<^emph> b) k"
  show "(X [^]\<^bsub>Z\<^sub>p_x\<^esub> Suc n \<^emph> a) k = (X [^]\<^bsub>Z\<^sub>p_x\<^esub> Suc n \<^emph> b) k"
  proof-
    have LHS0: "(X [^]\<^bsub>Z\<^sub>p_x\<^esub> Suc n \<^emph> a) k = ((X [^]\<^bsub>Z\<^sub>p_x\<^esub> n \<^emph> a) \<otimes> (X \<^emph> a)) k"
      by (metis (no_types, lifting) Z\<^sub>p_x_is_UP_domain Z\<^sub>p_x_ring UP_domain.X_closed
          UP_domain.fun_of_mult assms(1) monoid.nat_pow_Suc pow_closedP ring_def)
    have LHS1: "(X [^]\<^bsub>Z\<^sub>p_x\<^esub> Suc n \<^emph> a) k = (X [^]\<^bsub>Z\<^sub>p_x\<^esub> n \<^emph> a) k \<otimes>\<^bsub>R k\<^esub> (X \<^emph> a) k"
      using LHS0 
      by (simp add:  Z\<^sub>p_def padic_mult_simp)
    then show ?thesis using assms IH 
      by (smt Z\<^sub>p_x_is_UP_domain Z\<^sub>p_x_ring UP_domain.X_closed 
          UP_domain.fun_of_X UP_domain.fun_of_mult Z\<^sub>p_def monoid.nat_pow_Suc 
          monoid.simps(1) padic_simps(3) pow_closedP ring_def)
  qed
qed

lemma fun_of_res_lt: 
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "f \<in> carrier Z\<^sub>p_x"
  assumes "a k = b k"
  shows "((lt f)\<^emph>a) k = ((lt f)\<^emph>b) k"
proof-
  have "lt f = (lc f)\<odot>\<^bsub>Z\<^sub>p_x\<^esub>(X_pow (degree f))"
    by (simp add: UP_domain.lt_rep_X_pow assms(3))
  have LHS0: "(fun_of (lt f) a) = (lc f) \<otimes> (fun_of (X_pow (degree f)) a)"
    by (simp add: UP_domain.X_closed UP_domain.fun_of_smult UP_domain.lc_closed \<open>lt f = lc f \<odot>\<^bsub>Z\<^sub>p_x\<^esub> X [^]\<^bsub>Z\<^sub>p_x\<^esub> degree f\<close> assms(1) assms(3))
  have RHS0: "(fun_of (lt f) b) = (lc f) \<otimes> (fun_of (X_pow (degree f)) b)"
    by (simp add: UP_domain.X_closed UP_domain.fun_of_smult UP_domain.lc_closed \<open>lt f = lc f \<odot>\<^bsub>Z\<^sub>p_x\<^esub> X [^]\<^bsub>Z\<^sub>p_x\<^esub> degree f\<close> assms(2) assms(3))
  have LHS1: "(fun_of (lt f) a) k = ((lc f) k) \<otimes>\<^bsub>R k\<^esub> (fun_of (X_pow (degree f)) a) k"
    using LHS0 assms 
    by (simp add:  Z\<^sub>p_def padic_simps(3))
  have RHS1: "(fun_of (lt f) b) k = ((lc f) k) \<otimes>\<^bsub>R k\<^esub> (fun_of (X_pow (degree f)) b) k"
    using RHS0 assms 
    by (simp add:  Z\<^sub>p_def padic_simps(3))
  then show ?thesis 
    using LHS1 RHS1 assms 
    by (metis fun_of_res_X_pow)
qed

(*Polynomial application commutes with taking residues*)
lemma fun_of_res:
  assumes "f \<in> carrier Z\<^sub>p_x"
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "a k = b k"
  shows "(f\<^emph>a) k = (f\<^emph>b) k"
proof(rule UP_domain.poly_induct2[of Z\<^sub>p f])
  show "UP_domain Z\<^sub>p" 
    by simp
  show "f \<in> carrier Z\<^sub>p_x" 
    using assms by simp
  show "\<And>p. p \<in> carrier Z\<^sub>p_x \<Longrightarrow> degree p = 0 \<Longrightarrow> (p \<^emph> a) k = (p \<^emph> b) k"
    by (metis Z\<^sub>p_x_is_UP_domain UP_domain.degree_0_imp_constant0 assms(2) assms(3))
  show "\<And>p. 0 < degree p \<Longrightarrow> p \<in> carrier Z\<^sub>p_x \<Longrightarrow> (trunc p \<^emph> a) k = (trunc p \<^emph> b) k 
                \<Longrightarrow> (p \<^emph> a) k = (p \<^emph> b) k"
  proof-
    fix p
    assume A: "0 < degree p" "p \<in> carrier Z\<^sub>p_x"
    assume IH: " (trunc p \<^emph> a) k = (trunc p \<^emph> b) k "
    show "(p \<^emph> a) k = (p \<^emph> b) k"
    proof-
      have "(p \<^emph> a) k = (((trunc p)\<^emph> a) \<oplus> ((lt p) \<^emph> a)) k "
        by (metis A(2) Z\<^sub>p_x_is_UP_domain UP_domain.fun_of_plus 
            UP_domain.lt_closed UP_domain.trunc_simps(1) UP_domain.trunc_simps(3) assms(2))
      then have 0: "(p \<^emph> a) k = (((trunc p)\<^emph> b) k) \<oplus>\<^bsub>R k\<^esub> ((lt p) \<^emph> a) k "
        using IH 
        by (simp add:  Z\<^sub>p_def padic_add_def)
      have "((lt p) \<^emph> a) k = ((lt p) \<^emph> b) k"
        by (simp add: A(2) assms(2) assms(3) assms(4) fun_of_res_lt)
      then have 1: "(p \<^emph> a) k = (((trunc p)\<^emph> b) k) \<oplus>\<^bsub>R k\<^esub> ((lt p) \<^emph> b) k "
        using 0 by auto 
      then have 2: "(p \<^emph> a) k = (((trunc p)\<^emph> b) \<oplus> ((lt p) \<^emph> b)) k "
        using IH Z\<^sub>p_def \<open>(lt p \<^emph> a) k = (lt p \<^emph> b) k\<close> \<open>(p \<^emph> a) k = (trunc p \<^emph> a \<oplus> lt p \<^emph> a) k\<close> 
          padic_add_def by auto
      then have 2: "(p \<^emph> a) k = (((trunc p) \<oplus>\<^bsub>Z\<^sub>p_x\<^esub>(lt p)) \<^emph> b) k"
        by (simp add: A(2) UP_domain.fun_of_plus UP_domain.lt_closed 
            UP_domain.trunc_simps(3) assms(3))
      then show ?thesis 
        by (metis A(2) Z\<^sub>p_x_is_UP_domain UP_domain.trunc_simps(1))
    qed
  qed
qed

(*If a and b has equal kth residues, then do f'(a) and f'(b)*)
lemma deriv_res:
  assumes "f \<in> carrier Z\<^sub>p_x"
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "a k = b k"
  shows "(deriv f a) k = (deriv f b) k"
proof-
  have 0: "deriv f a = fun_of (pderiv f) a"
    by (simp add: UP_domain.pderiv_eval_deriv assms(1) assms(2))
  have 1: "deriv f b = fun_of (pderiv f) b"
    by (simp add: UP_domain.pderiv_eval_deriv assms(1) assms(3))
  have 2: "pderiv f \<in> carrier Z\<^sub>p_x"
    by (simp add: UP_domain.poly_deriv_closed assms(1))
  show ?thesis
    using assms fun_of_res[of "pderiv f" a b k] 0 1 2 
    by auto 
qed

end
end