theory padic_field_polynomials
  imports domain_poly padic_field_sequences

begin 

context padic_num_poly
begin

type_synonym padic_field_poly = "nat \<Rightarrow> padic_number"


(*type for function on Qp*)

type_synonym padic_field_fun = "padic_number \<Rightarrow> padic_number"



(**************************************************************************************************)
lemma monom_term_car:
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "x \<in> carrier Q\<^sub>p"
  shows "c \<otimes>\<^bsub>Q\<^sub>p\<^esub>  x[^]\<^bsub>Q\<^sub>p\<^esub>(n::nat) \<in> carrier Q\<^sub>p"
  using assms  monoid.nat_pow_closed 
  by (metis Group.comm_monoid_def Group.monoid_def Qp_is_comm_monoid)
(*Univariate polynomial ring over Q\<^sub>p*)

abbreviation Q\<^sub>p_x where
"Q\<^sub>p_x \<equiv> UP Q\<^sub>p"

lemma Q\<^sub>p_x_is_UP_ring[simp]:
"UP_ring Q\<^sub>p_x"
  by (meson Qp_is_domain UP_ring.UP_ring UP_ring.intro cring_def domain_def)

lemma Q\<^sub>p_x_is_UP_cring[simp]:
"UP_cring Q\<^sub>p"
  by (simp add: UP_cring_def domain.axioms(1))

lemma Q\<^sub>p_x_is_UP_domain[simp]:
"UP_domain Q\<^sub>p"
  by (simp add: UP_domain_def)

lemma Q\<^sub>p_x_ring[simp]:
"ring Q\<^sub>p_x "
  by (simp add: UP_ring.axioms)

lemma Q\<^sub>p_x_cring[simp]:
"cring Q\<^sub>p_x "
  by (simp add: UP_cring.UP_cring)

lemma Q\<^sub>p_x_domain[simp]:
"domain Q\<^sub>p_x "
  by (simp add: UP_domain.UP_domain)

(*Basic simp rules to streaminline computation*)
lemma Q\<^sub>p_pow_closedP[simp]:
  assumes "f \<in> carrier Q\<^sub>p_x"
  shows "f[^]\<^bsub>Q\<^sub>p_x\<^esub>(n::nat) \<in> carrier Q\<^sub>p_x " 
  by (meson Q\<^sub>p_x_ring assms monoid.nat_pow_closed ring_def)

lemma Qp_pow_closed[simp]:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "a[^]\<^bsub>Q\<^sub>p\<^esub>(n::nat) \<in> carrier Q\<^sub>p"
  by (meson Qp_is_domain assms cring_def domain_def monoid.nat_pow_closed ring_def)

lemma Qp_pow_zero[simp]:
  assumes "(n::nat)>0"
  shows "\<zero>\<^bsub>Q\<^sub>p\<^esub> [^]\<^bsub>Q\<^sub>p\<^esub> n = \<zero>\<^bsub>Q\<^sub>p\<^esub>"
  using assms ring.pow_zero[of Q\<^sub>p n] 
  by (simp add: cring.axioms(1) domain.axioms(1))

lemma Qp_pow_zeroP[simp]:
  assumes "n >0"
  shows "\<zero>\<^bsub>Q\<^sub>p_x\<^esub> [^]\<^bsub>Q\<^sub>p_x\<^esub>(n::nat) = \<zero>\<^bsub>Q\<^sub>p_x\<^esub>"
  using assms ring.pow_zero[of Q\<^sub>p_x] by simp

lemma Qp_sum_closedP[simp]:
  assumes "f \<in> carrier Q\<^sub>p_x"
  assumes "g \<in> carrier Q\<^sub>p_x"
  shows "f \<oplus>\<^bsub>Q\<^sub>p_x\<^esub>g \<in>  carrier Q\<^sub>p_x"
  by (simp add: assms(1) assms(2) cring.cring_simprules(1))

lemma Qp_sum_closed[simp]:
  assumes "f \<in> carrier Q\<^sub>p"
  assumes "g \<in> carrier Q\<^sub>p"
  shows "f \<oplus>\<^bsub>Q\<^sub>p\<^esub> g \<in>  carrier Q\<^sub>p"
  by (meson Qp_is_domain assms(1) assms(2) cring.cring_simprules(1) domain.axioms(1))

lemma Qp_mult_zero[simp]:
  assumes "f \<in> carrier Q\<^sub>p"
  shows "f \<otimes>\<^bsub>Q\<^sub>p\<^esub> \<zero>\<^bsub>Q\<^sub>p\<^esub> = \<zero>\<^bsub>Q\<^sub>p\<^esub>"
        "\<zero>\<^bsub>Q\<^sub>p\<^esub> \<otimes>\<^bsub>Q\<^sub>p\<^esub> f = \<zero>\<^bsub>Q\<^sub>p\<^esub>"
  apply (simp add: assms cring.cring_simprules(27) domain.axioms(1))
  by (simp add: assms cring.cring_simprules(26) domain.axioms(1))


lemma Qp_mult_zeroP[simp]:
  assumes "f \<in> carrier Q\<^sub>p_x" 
  shows "f \<otimes>\<^bsub>Q\<^sub>p_x\<^esub> \<zero>\<^bsub>Q\<^sub>p_x\<^esub> = \<zero>\<^bsub>Q\<^sub>p_x\<^esub>"
        "\<zero>\<^bsub>Q\<^sub>p_x\<^esub> \<otimes>\<^bsub>Q\<^sub>p_x\<^esub> f = \<zero>\<^bsub>Q\<^sub>p_x\<^esub>"
  apply (simp add: assms cring.cring_simprules(27))
  apply (simp add: assms cring.cring_simprules(26))
  done

lemma Qp_add_zero[simp]:
  assumes "f \<in> carrier Q\<^sub>p"
  shows "f \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<zero>\<^bsub>Q\<^sub>p\<^esub> = f"
        "\<zero>\<^bsub>Q\<^sub>p\<^esub> \<oplus>\<^bsub>Q\<^sub>p\<^esub> f = f"
  apply (meson Qp_is_domain assms cring.cring_simprules(16) domain_def)
  by (meson Qp_is_domain assms cring.cring_simprules(8) domain_def)

lemma Qp_add_zeroP[simp]:
  assumes "f \<in> carrier Q\<^sub>p_x "
  shows "f \<oplus>\<^bsub>Q\<^sub>p_x\<^esub> \<zero>\<^bsub>Q\<^sub>p_x\<^esub> = f"
        "\<zero>\<^bsub>Q\<^sub>p_x\<^esub> \<oplus>\<^bsub>Q\<^sub>p_x\<^esub> f = f"
   apply (simp add: assms cring.cring_simprules)
   apply (simp add: assms cring.cring_simprules)
   done

(*Degree function*)
abbreviation degree:: "padic_field_poly \<Rightarrow> nat" where
"degree f \<equiv>  deg Q\<^sub>p f"

(*Coefficient function*)
abbreviation cf :: "padic_field_poly \<Rightarrow> nat \<Rightarrow> padic_number" where
"cf  \<equiv> coeff (UP Q\<^sub>p)"

(*Leading term function*)
abbreviation lt  where
"lt \<equiv> leading_term Q\<^sub>p"

(*Leading coefficient function*)
abbreviation lc where
"lc \<equiv> leading_coefficient Q\<^sub>p"

(*Truncation function, which sends a polynomial f \<Longrightarrow> (f - leading_term (f)), which has strictly
smaller degree in the case where degree f > 0*)
abbreviation trunc where 
"trunc \<equiv> truncate Q\<^sub>p"

(*Turning a padic polynomial into a function on Q\<^sub>p*)
abbreviation fun_of :: "padic_field_poly \<Rightarrow> padic_number \<Rightarrow> padic_number" (infixl "\<^emph>" 70) where
"fun_of f a \<equiv> function_of Q\<^sub>p f a"


(*predicate for monomial polynomials*)
abbreviation is_monom where
"is_monom \<equiv> is_monom_poly Q\<^sub>p"

(*technical lemmas for reasoning about fun_of*)
lemma id_is_hom:
"ring_hom_cring Q\<^sub>p Q\<^sub>p (\<lambda>x. x)"
proof(rule ring_hom_cringI)
  show "cring Q\<^sub>p" 
    by (simp add: domain.axioms(1)) 
  show "cring Q\<^sub>p" 
     using \<open>cring Q\<^sub>p\<close> by auto   
  show "(\<lambda>x. x) \<in> ring_hom Q\<^sub>p Q\<^sub>p"
    unfolding ring_hom_def
    apply(auto)
    done
qed

lemma UP_pre_univ_prop_fact:
"UP_pre_univ_prop Q\<^sub>p Q\<^sub>p (\<lambda>x. x)"
  unfolding UP_pre_univ_prop_def
  by (simp add: id_is_hom)

(*Q\<^sub>p_x addition commutes with evaluation addition*)
lemma fun_of_fun_sum:
  assumes "f \<in> carrier Q\<^sub>p_x"
  assumes "g \<in> carrier Q\<^sub>p_x"
  assumes "h = f \<oplus>\<^bsub>Q\<^sub>p_x\<^esub> g"
  shows "(fun_sum (fun_of f) (fun_of g)) \<doteq> (fun_of h)"   
  unfolding eq_on_Qp_def
proof
  fix x
  show " x \<in> carrier Q\<^sub>p \<longrightarrow> fun_sum ((\<^emph>) f) ((\<^emph>) g) x = h \<^emph> x"
  proof
    assume A: "x \<in> carrier Q\<^sub>p"
    show "fun_sum (fun_of f) (fun_of g) x = fun_of h x "
      unfolding fun_sum_def
      unfolding function_of_def
    proof-
      have "(eval Q\<^sub>p Q\<^sub>p (\<lambda>x. x)) x \<in> (ring_hom Q\<^sub>p_x Q\<^sub>p)"
        using UP_pre_univ_prop_fact A UP_pre_univ_prop.eval_ring_hom[of Q\<^sub>p Q\<^sub>p "(\<lambda>x. x)" x]    
        by auto   
      then show "eval Q\<^sub>p Q\<^sub>p (\<lambda>x. x) x f \<oplus>\<^bsub>Q\<^sub>p\<^esub> eval Q\<^sub>p Q\<^sub>p (\<lambda>x. x) x g = eval Q\<^sub>p Q\<^sub>p (\<lambda>x. x) x h "
        using assms ring_hom_add   by (simp add: \<open>f \<in> carrier Q\<^sub>p_x\<close> ring_hom_def)
    qed
  qed
qed

(*monomial functions are monomials*)
lemma fun_of_monom_is_monom0:
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "c \<noteq>\<zero>\<^bsub>Q\<^sub>p\<^esub>"
  assumes "f = monom Q\<^sub>p_x c n"
  assumes "x \<in> carrier Q\<^sub>p"
  shows "f\<^emph>x = mon c n x"
proof-
  have 1: "f\<^emph>x = c \<otimes>\<^bsub>Q\<^sub>p\<^esub> x [^]\<^bsub>Q\<^sub>p\<^esub> n"
    using UP_domain.fun_of_monom assms Q\<^sub>p_x_is_UP_domain 
    by (simp add: UP_domain.fun_of_monom)
  show ?thesis
    unfolding mon_def scalar_mult_def X_Qp_pow_def function_of_def
    by (smt Qp_is_domain Qp_one_car UP_pre_univ_prop.eval_const UP_pre_univ_prop.eval_monom
        UP_pre_univ_prop_fact assms(1) assms(3) assms(4) cring.cring_simprules(12) 
        cring.cring_simprules(14) domain.axioms(1) fun_scalar_mult_def)
qed

lemma fun_of_monom_is_monom:
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "f = monom Q\<^sub>p_x c n"
  shows "fun_of f \<doteq> mon c n"
proof(cases "c = \<zero>\<^bsub>Q\<^sub>p\<^esub>") 
  case True
    have "monom Q\<^sub>p_x \<zero>\<^bsub>Q\<^sub>p\<^esub> n = \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
      by (simp add: UP_cring.is_UP_ring UP_ring.monom_zero)
    then have "f = \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
      by (simp add: True assms(2))
    then have T0: "\<And>x. x \<in> carrier Q\<^sub>p \<Longrightarrow> fun_of f x = \<zero>\<^bsub>Q\<^sub>p\<^esub>"
      unfolding function_of_def
      by (metis Q\<^sub>p_x_is_UP_cring True UP_cring.is_UP_ring UP_pre_univ_prop.eval_const
          UP_pre_univ_prop_fact UP_ring.monom_zero assms(1))
    have "\<And>x. x \<in> carrier Q\<^sub>p \<Longrightarrow> mon c n x = \<zero>\<^bsub>Q\<^sub>p\<^esub>"
      using True Qp_mult_zero(2) X_pow_Qp_is_closed fun_scalar_mult_def is_closed_fun_simp mon_def 
      by presburger
    then show ?thesis 
      using T0     
      unfolding eq_on_Qp_def 
      by blast
next
  case False
  then show ?thesis 
    unfolding eq_on_Qp_def
    using assms(1) assms(2) fun_of_monom_is_monom0
    by blast
qed

lemma fun_of_monom_is_monom':
  assumes "is_monom f"
  shows "fun_of f \<doteq> mon (lc f) (degree f)"
  using Q\<^sub>p_x_is_UP_domain assms 
    UP_domain.is_monom_id[of Q\<^sub>p f] 
    fun_of_monom_is_monom[of "lc f" f "degree f"] 
    UP_domain.lc_closed[of Q\<^sub>p f] 
  unfolding   is_monom_poly_def
  by blast

(*monomials are continuous*)

lemma monom_poly_is_continuous:
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "f = monom Q\<^sub>p_x c n"
  shows "is_continuous (fun_of f)"
proof-
  have 0: "is_continuous (mon c n)"
    unfolding mon_def using assms(1) 
    by (simp add: X_Qp_pow_Qp_is_continuous fun_scalar_mult_is_continuous)
  have 1: "fun_of f \<doteq> mon c n" 
    by (simp add: assms(1) assms(2) fun_of_monom_is_monom)
  show ?thesis using 0 1 is_continuous_eq eq_on_Qp_def 
    by auto
qed

lemma monom_poly_is_continuous':
  assumes "is_monom f"
  shows "is_continuous (fun_of f)"
  using Q\<^sub>p_x_is_UP_domain UP_domain.is_monom_id[of Q\<^sub>p f]
        monom_poly_is_continuous[of "lc f" f "degree f"]
        assms UP_domain.lc_closed[of Q\<^sub>p f] 
  unfolding is_monom_poly_def 
  by blast

lemma degree_0_is_constant:
  assumes "f \<in> carrier Q\<^sub>p_x"
  assumes "degree f = 0"
  obtains g where "is_constant_fun g" and "g \<doteq> fun_of f"
proof- 
  obtain c where c0: "c \<in> carrier Q\<^sub>p" and  c1: "\<And>x.  x \<in> carrier Q\<^sub>p \<Longrightarrow> (fun_of f) x = c"
    using Q\<^sub>p_x_is_UP_domain UP_domain.degree_0_imp_constant0  assms(1) assms(2) by blast
  obtain g where g_def: "g = to_const_fun c"
    by simp
  have 0: "is_constant_fun g" 
    by (simp add: \<open>g = to_const_fun c\<close> c0 to_const_fun_is_const)
  have 1: "g \<doteq> fun_of f"
    unfolding eq_on_Qp_def
  proof
    fix x
    show "x \<in> carrier Q\<^sub>p \<longrightarrow> g x = f \<^emph> x"
    proof
      assume A: "x \<in> carrier Q\<^sub>p"
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
  qed
  show ?thesis
    using 0 1  that by auto
qed

(*degree 0 polynomials induce continuous functions*)
lemma degree_0_is_continuous:
  assumes "f \<in> carrier Q\<^sub>p_x"
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
  shows "\<And>f. f \<in> carrier Q\<^sub>p_x \<Longrightarrow> degree f \<le> n \<Longrightarrow> is_continuous (fun_of f)"
proof(induction n)
case 0
  then show ?case 
    using degree_0_is_continuous by blast
next
  case (Suc n)
  fix n
  assume IH: "\<And>f. f \<in> carrier Q\<^sub>p_x \<Longrightarrow> (degree f \<le> n \<Longrightarrow> is_continuous (fun_of f))"
  show "\<And>f. f \<in> carrier Q\<^sub>p_x \<Longrightarrow> degree f \<le> Suc n \<Longrightarrow> is_continuous (fun_of f) "
  proof-
    fix f
    assume A0:"f \<in> carrier Q\<^sub>p_x"
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
      obtain g where g_def: "g \<in> carrier Q\<^sub>p_x \<and> (f = g \<oplus>\<^bsub>Q\<^sub>p_x\<^esub> (lt f)) \<and> degree g < degree f"
        using E0 A0 Q\<^sub>p_x_is_UP_domain UP_domain.lt_decomp[of Q\<^sub>p f] by auto  
      have g0: "g \<in> carrier Q\<^sub>p_x"
        using g_def by auto 
      have g1: "f = g \<oplus>\<^bsub>Q\<^sub>p_x\<^esub> (lt f)" 
        using g_def by auto 
      have g2: "degree g < degree f" 
        using g_def by auto 
      have LS: "is_continuous (fun_of g)" 
        using E g0 g1 g2 IH by auto 
      have RS: "is_continuous (fun_of (lt f))"
        using monom_poly_is_continuous leading_term_def A0  
            Q\<^sub>p_x_is_UP_ring Q\<^sub>p_x_is_UP_domain 
        by (metis UP_domain.cfs_closed)
      have "fun_of f \<doteq>  fun_sum (fun_of g) (fun_of (lt f))"
        using  fun_of_fun_sum g0 A0 g1  eq_on_Qp_def UP_domain.lt_closed 
        by (metis (mono_tags, lifting) Q\<^sub>p_x_is_UP_domain)
      then show ?thesis
        using LS RS sum_of_cont_is_cont 
        by (metis (no_types, lifting) Qp_complete' converges_to_def eq_on_Qp_def 
            is_closed_fun_def is_continuous_def push_forward_eq)
    qed
  qed
qed

lemma polynomial_is_continuous:
  assumes "f \<in> carrier Q\<^sub>p_x"
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

(*The inclusion of Q\<^sub>p into Q\<^sub>p_x*)

abbreviation to_poly :: "padic_number \<Rightarrow> padic_field_poly" where
"to_poly \<equiv> to_polynomial Q\<^sub>p"

lemma to_poly_is_ring_hom:
"to_poly \<in> ring_hom Q\<^sub>p Q\<^sub>p_x"
  by (simp add: UP_domain.to_poly_is_ring_hom)

abbreviation sub :: "padic_field_poly \<Rightarrow> padic_field_poly \<Rightarrow> padic_field_poly" (infixl "of" 70)where
"sub \<equiv> compose Q\<^sub>p"

abbreviation rev_sub :: "padic_field_poly \<Rightarrow> padic_field_poly \<Rightarrow> padic_field_poly" where
"rev_sub \<equiv> rev_compose Q\<^sub>p"

lemma sub_rev_sub:
"sub f g = rev_sub g f"
  by (simp add:  UP_domain.sub_rev_sub)

(*The polynomial X*)
abbreviation X where 
"X \<equiv> X_poly Q\<^sub>p"

(*Translates of X*)
abbreviation X_plus where
"X_plus \<equiv> X_poly_plus  Q\<^sub>p"

abbreviation X_minus where
"X_minus \<equiv> X_poly_minus  Q\<^sub>p"

(*Powers of X*)
abbreviation X_pow where
"X_pow n \<equiv> X[^]\<^bsub>Q\<^sub>p_x\<^esub>n"

(*The Taylor expansion*)

abbreviation Taylor ("T\<^bsub>_\<^esub>") where
"Taylor \<equiv> taylor_expansion Q\<^sub>p"

(*Derivative function*)

abbreviation deriv   where
"deriv \<equiv> derivative Q\<^sub>p"

(*Zero coefficient function*)
abbreviation cf0 where
"cf0 \<equiv> zero_coefficient"

(*The horner shift function. Satisfies the equation:       f = a0 + X(poly_shift f)      *)
abbreviation poly_shift where
"poly_shift \<equiv> polynomial_shift Q\<^sub>p"

(*The iterated shift function. Satisfies   f = a0 + a1*X + ...+ (an-1)*X^(n-1) + X^n(shift n f) *)
abbreviation shift where
"shift \<equiv> poly_shift_iter Q\<^sub>p"

(*The "first n+1 terms" function*)
abbreviation deg_leq where
"deg_leq \<equiv> degree_n_or_less_terms Q\<^sub>p"

(*The linear part function*)
abbreviation lin_part where 
"lin_part \<equiv> linear_part Q\<^sub>p"

(*the derivative operator*)

abbreviation pderiv where
"pderiv \<equiv> poly_deriv Q\<^sub>p"

end
end