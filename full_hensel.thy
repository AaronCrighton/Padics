theory full_hensel
  imports padic_int_polynomials padic_fields
begin

context padic_int_polynomial
begin

lemma poly_diff_ord:
  assumes "f \<in> carrier Z\<^sub>p_x"
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  shows "(f\<^emph>a = f\<^emph>b) \<or> (ord_Zp (f\<^emph>a \<ominus> f\<^emph>b) \<ge> ord_Zp (a \<ominus> b))"
proof(cases "(f\<^emph>a = f\<^emph>b)")
  case True
  then show ?thesis by metis 
next
  case False
  obtain c where c_def: "c \<in> carrier Z\<^sub>p \<and> (f\<^emph>a \<ominus> f\<^emph>b) = (a \<ominus> b) \<otimes> c"
    using assms Z\<^sub>p_x_is_UP_domain UP_domain.fun_of_diff[of Z\<^sub>p a b f]
    by blast 
  have 0: "c \<noteq>\<zero>" using False 
    by (metis Z\<^sub>p_x_is_UP_domain Zp_is_cring Zp_nonzero_def(2)
        Zp_not_eq_diff_nonzero assms(1) assms(2) assms(3) c_def 
        cring.cring_simprules(4) fun_of_closed_UP_domain mult_zero(1))
  have 1: "ord_Zp c \<ge>0"
    using 0 c_def ord_pos
    by blast
  have 2: "ord_Zp (f\<^emph>a \<ominus> f\<^emph>b) = ord_Zp (a \<ominus> b) + (ord_Zp c)"
    using c_def ord_Zp_mult 
    by (metis "0" False Zp_not_eq_diff_nonzero assms(2) assms(3) not_nonzero_Zp)
  then show ?thesis 
    using "1" by linarith
qed

lemma poly_diff_val:
  assumes "f \<in> carrier Z\<^sub>p_x"
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  shows " val_Zp (f\<^emph>a \<ominus> f\<^emph>b) \<succeq>\<^bsub>G\<^esub> val_Zp (a \<ominus> b)"
proof(cases "(f\<^emph>a = f\<^emph>b)")
  case True
  then show ?thesis 
    by (metis G_ord(1) Z\<^sub>p_x_is_UP_domain Zp_is_cring assms(1) assms(2) 
        cring_def fun_of_closed_UP_domain ring.r_right_minus_eq val_Zp_def)
next
  case False
  then show ?thesis using poly_diff_ord 
    by (metis (no_types, lifting) G_ord  Zp_is_cring assms(1)
        assms(2) assms(3) cring_def ord_Zp_def ring.r_right_minus_eq val_Zp_def)
qed

lemma equal_ord:
  assumes "a \<in> nonzero Z\<^sub>p"
  assumes "b \<in>  nonzero Z\<^sub>p"
  assumes "c \<in> nonzero Z\<^sub>p"
  assumes "ord_Zp a = ord_Zp b"
  assumes "ord_Zp (c \<ominus> a) > ord_Zp b"
  shows "ord_Zp c = ord_Zp b"
proof-
  have "c = c \<ominus> a \<oplus> a"
    using assms 
    by (smt Zp_is_cring a_minus_def cring.cring_simprules(10)
        cring.cring_simprules(19) cring.cring_simprules(21) 
        cring.cring_simprules(3) cring.cring_simprules(4) mem_Collect_eq nonzero_def)
  then have 0: "ord_Zp c = ord_Zp (c \<ominus> a \<oplus> a)"
    using assms 
    by metis 
  have "ord_Zp c \<ge> min (ord_Zp (c \<ominus> a)) (ord_Zp a)"
    using 0 Zp_nonzero_def(1) Zp_not_eq_diff_nonzero \<open>c = c \<ominus> a \<oplus> a\<close> 
      assms(1) assms(3) ord_Zp_ultrametric[of "c \<ominus> a" a]
    by smt
  then have 1: "ord_Zp c \<ge> (ord_Zp a)"
    using assms(4) assms(5) 
    by linarith
  have  "ord_Zp c = (ord_Zp a)"
  proof(rule ccontr)
    assume A: "ord_Zp c \<noteq> ord_Zp a"
    then have "ord_Zp c > ord_Zp a"
      using 1 A 
      by linarith  
    then have "ord_Zp (c \<oplus> (a \<ominus> c)) \<ge> min (ord_Zp c) (ord_Zp (a \<ominus> c))"
      using Zp_is_cring Zp_minus_ominus Zp_nonzero_def(1) Zp_not_eq_diff_nonzero \<open>c = c \<ominus> a \<oplus> a\<close> 
      assms(1) assms(3) cring.cring_simprules(10) cring.cring_simprules(19) ord_Zp_ultrametric
      by (metis (no_types, hide_lams) A  cring.cring_simprules(1) 
           cring.cring_simprules(21) cring.cring_simprules(4)
          cring.sum_zero_eq_neg not_nonzero_Zp)
    then have "ord_Zp a \<ge> min (ord_Zp c) (ord_Zp (a \<ominus> c))"
      by (metis Zp_is_cring Zp_minus_ominus Zp_nonzero_def(1) \<open>c = c \<ominus> a \<oplus> a\<close> 
          assms(1) assms(3) cring.cring_simprules(10) cring.cring_simprules(19)
          cring.cring_simprules(4))
    then have "ord_Zp a > ord_Zp a"
      by (smt Zp_nonzero_def(1) \<open>ord_Zp a < ord_Zp c\<close> assms(1)
          assms(3) assms(4) assms(5) ord_Zp_dist_sym)
    then show False 
      by blast
  qed
  then show ?thesis 
    using assms(4) 
    by linarith
qed

lemma equal_ord':
  assumes "a \<in> nonzero Z\<^sub>p"
  assumes "b \<in>  nonzero Z\<^sub>p"
  assumes "c \<in> nonzero Z\<^sub>p"
  assumes "ord_Zp a = ord_Zp b"
  assumes "ord_Zp c > ord_Zp b"
  shows "ord_Zp (a \<oplus> c) = ord_Zp b"
  using equal_ord[of a b "a \<oplus>c"] 
  by (smt Zp_is_cring Zp_nonzero_def(1) a_minus_def add_zero(1) assms(1) assms(2) assms(3) 
      assms(4) assms(5) cring.cring_simprules(10) cring.cring_simprules(19) cring.cring_simprules(3)
      not_nonzero_Zp ord_Zp_of_ominus sum_closed)
end

lemma(in UP_domain) Taylor_deg_1_eval''':
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "c = fun_of (shift (2::nat) (T\<^bsub>a\<^esub> f)) (\<ominus>b)"
  assumes "b \<otimes> (deriv f a) = (fun_of f a)"
  shows "fun_of f (a \<ominus> b) =  (c \<otimes> b[^](2::nat))"
proof-
  have 0: "fun_of f (a \<ominus> b) = (fun_of f a) \<ominus> (deriv f a \<otimes> b) \<oplus> (c \<otimes> b[^](2::nat))"
    using assms Taylor_deg_1_eval'' 
    by blast
  have 1: "(fun_of f a) \<ominus> (deriv f a \<otimes> b) = \<zero>"
    using assms 
    by (simp add: R.m_comm derivative_closed)
  have 2: "fun_of f (a \<ominus> b) = \<zero> \<oplus> (c \<otimes> b[^](2::nat))"
    using 0 1 
    by simp
  then show ?thesis using assms 
    by (simp add: monom_term_car)
qed

lemma(in padic_int_polynomial) is_cauchyI': 
assumes "is_closed_seq s"
assumes "\<forall>n::nat. \<exists> k::int.\<forall>m.  m \<ge>  k \<longrightarrow> ord_Zp (s (Suc m) \<ominus> s m) \<ge> n"
shows "is_cauchy s"
proof(rule is_cauchyI)
  show A0: "is_closed_seq s" 
    by (simp add: assms(1))
  show "\<And>n. \<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> s n0 n = s n1 n"
  proof-
    fix n
    show "\<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> s n0 n = s n1 n"
    proof(induction n)
      case 0
      then show ?case 
      proof-
        have "\<forall>n0 n1. 0 < n0 \<and> 0 < n1 \<longrightarrow> s n0 0 = s n1 0"
          apply auto 
        proof-
          fix n0 n1::nat
          assume A: "n0 > 0" "n1 > 0"
          show " s n0 0 = s n1 0"
            using A0
            unfolding is_closed_seq_def 
            by (smt One_nat_def of_nat_0 of_nat_Suc ord_Zp_0_criterion
                ord_Zp_geq zero_below_ord zero_vals)
        qed
        then show ?thesis 
          by blast 
      qed
    next
      case (Suc n)
      fix n
      assume IH: "\<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> s n0 n = s n1 n"
      show " \<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> s n0 (Suc n) = s n1 (Suc n)"
      proof-
        obtain N where N_def: "\<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> s n0 n = s n1 n"
          using IH 
          by blast  
        obtain k where k_def: "\<forall>m.  (Suc m) \<ge> k \<longrightarrow> ord_Zp (s (Suc (Suc m)) \<ominus> s (Suc m)) \<ge> Suc (Suc n)"
          using assms  Suc_n_not_le_n 
          by (meson nat_le_iff)
        have "\<forall>n0 n1.  Suc (max N (max n k)) < n0 \<and>  Suc (max N (max n k))< n1 \<longrightarrow> s n0 (Suc n) = s n1 (Suc n)"
          apply auto
        proof-
          fix n0 n1
          assume A: "Suc (max N (max n k)) < n0" " Suc (max N (max n k)) < n1"
          show "s n0 (Suc n) = s n1 (Suc n) "
          proof-
            obtain K where K_def: "K = Suc (max N (max n k))"
              by simp
            have P0: "\<And>m. s ((Suc m)+ K) (Suc n) = s (Suc K) (Suc n)"
              apply auto  
            proof-
              fix m
              show "s (Suc (m + K)) (Suc n) = s (Suc K) (Suc n)"
              apply(induction m)
                 apply auto 
              proof-
                fix m
                assume A0: " s (Suc (m + K)) (Suc n) = s (Suc K) (Suc n)"
                show " s (Suc (Suc (m + K))) (Suc n) = s (Suc K) (Suc n)"
                proof-
                  have I: "k < m + K"
                    using K_def 
                    by linarith
                  have D:"ord_Zp (s (Suc (Suc (m + K))) \<ominus> s (Suc (m + K))) \<ge>  Suc (Suc n)"
                  proof-
                    have "(Suc (m + K)) > k"
                      by (simp add: I less_Suc_eq)
                    then show ?thesis 
                      using k_def less_imp_le_nat 
                      by blast
                  qed
                  then have "s (Suc (Suc (m + K))) (Suc n) =  s (Suc (m + K)) (Suc n)"
                  proof-
                    have "(s (Suc (Suc (m + K))) \<ominus> s (Suc (m + K)))  (Suc n) = 0"
                      using D A0 
                      by (smt Zp_is_cring assms(1) cring.cring_simprules(4) 
                          is_closed_simp semiring_1_class.of_nat_simps(2) zero_below_ord)
                    then have "(s (Suc (Suc (m + K)))  (Suc n) \<ominus>\<^bsub>R  (Suc n)\<^esub> (s (Suc (m + K)))  (Suc n)) = 0"
                      unfolding a_minus_def
                      using R_residues[of "Suc n"]   A0 Z\<^sub>p_def padic_add_def
                        padic_uminus_def a_minus_def assms(1) is_closed_seq_def padic_inv prime 
                      by auto
                    then show ?thesis 
                      unfolding a_minus_def
                      using R_residues[of "Suc n"]   A0 Z\<^sub>p_def padic_add_def
                        padic_uminus_def a_minus_def assms(1) is_closed_seq_def padic_inv prime 
                      by (smt cring.cring_simprules(21) cring.cring_simprules(3)
                          cring.sum_zero_eq_neg padic_integers.R_cring padic_integers_axioms
                          padic_set_simp0 partial_object.select_convs(1) residues.res_zero_eq
                          zero_less_Suc)
                  qed
                  then show ?thesis using A0 
                    by simp
                qed
              qed
            qed
            have "\<exists>m0. n0 = (Suc m0) + K"
            proof-
              have "n0 > K"
                by (simp add: A(1) K_def)
              then have "n0 = (Suc (n0 - K - 1)) + K"
                by auto
              then show ?thesis by blast 
            qed
            then obtain m0 where m0_def: "n0 = (Suc m0) + K"
              by blast 
            have "\<exists>m0. n1 = (Suc m0) + K"
            proof-
              have "n1 > K"
                by (simp add: A(2) K_def)
              then have "n1 = (Suc (n1 - K - 1)) + K"
                by auto
              then show ?thesis by blast 
            qed
            then obtain m1 where m1_def: "n1 = (Suc m1) + K"
              by blast
            have 0: "s n0 (Suc n) = s (Suc K) (Suc n)" 
              using m0_def P0[of "m0"] by auto  
            have 1: "s n1 (Suc n) = s (Suc K) (Suc n)" 
              using m1_def P0[of "m1"] by auto  
            show ?thesis using 0 1 
              by auto
          qed
        qed
        then show ?thesis 
          by blast
      qed
    qed
  qed
qed

locale hensel = padic_int_polynomial+ 
  fixes f::padic_int_poly
  fixes a::padic_int
  assumes f_closed[simp]: "f \<in> carrier Z\<^sub>p_x"
  assumes a_closed[simp]: "a \<in> carrier Z\<^sub>p"
  assumes f'a_nonzero[simp]: "(pderiv f)\<^emph>a \<noteq> \<zero>"
  assumes fa_nonzero[simp]: "f\<^emph>a \<noteq>\<zero>"
  assumes hensel_hypothesis[simp]: "(ord_Zp (f\<^emph>a) > 2* ord_Zp ((pderiv f)\<^emph>a))"

context hensel
begin

abbreviation f' where
"f' \<equiv> pderiv f"

lemma f'_closed[simp]:
"f' \<in> carrier Z\<^sub>p_x"
  by (simp add: UP_domain.poly_deriv_closed)

lemma f'_vals_closed[simp]:
  assumes "a \<in> carrier Z\<^sub>p"
  shows "f'\<^emph>a \<in> carrier Z\<^sub>p"
  by simp

abbreviation f'a where
"f'a \<equiv> f' \<^emph> a"

abbreviation fa where
"fa \<equiv> f\<^emph>a"

lemma fa_closed[simp]:
"fa \<in> carrier Z\<^sub>p"
  by simp

lemma f'a_closed[simp]:
"f'a \<in> carrier Z\<^sub>p"
proof-
  have "f' \<in> carrier Z\<^sub>p_x"
    by (simp add: UP_domain.poly_deriv_closed)
  then show ?thesis 
    by simp
qed

lemma fa_nonzero'[simp]:
"fa \<in> nonzero Z\<^sub>p"
  by (simp add: nonzero_def)

lemma f'a_nonzero'[simp]:
"f'a \<in> nonzero Z\<^sub>p"
  by (simp add: nonzero_def)

lemma hensel_hypothesis_weakened[simp]:
"ord_Zp fa > ord_Zp f'a"
  by (smt fa_closed fa_nonzero hensel_hypothesis ord_pos)

definition newton_step :: "padic_int \<Rightarrow> padic_int" where
"newton_step x = x \<ominus> (divide (f\<^emph>x) (f'\<^emph>x))"

fun newton_seq :: "padic_int_seq" ("ns") where
"newton_seq 0 = a"|
"newton_seq (Suc n) = newton_step (newton_seq n)"

lemma hensel_factor_id:
"(divide fa f'a) \<otimes> (f'a) = fa"
  using hensel_hypothesis hensel_axioms
         divide_id(2)[of fa f'a] f'a_nonzero' 
        fa_nonzero' hensel_hypothesis_weakened 
  unfolding nonzero_def 
  by linarith

definition hensel_factor ("t") where
"hensel_factor= ord_Zp fa - 2*(ord_Zp f'a)"

lemma t_pos:
"t > 0"
  using hensel_factor_def hensel_hypothesis by linarith

lemma newton_seq_props_induct:
shows "\<And>k. k \<le>n \<Longrightarrow> (ns k) \<in> carrier Z\<^sub>p
              \<and> val_Zp (f'\<^emph>(ns k)) = val_Zp (f'a)
              \<and> val_Zp (f\<^emph>(ns k)) \<succeq>\<^bsub>G\<^esub> * (2*(ord_Zp f'a)) + (2^k)*t *"
proof(induction n)
  case 0
  then have kz: "k = 0"
    by simp
  have B0: "( ns k) \<in> carrier Z\<^sub>p"
    using kz 
    by simp
  have B1: "(val_Zp (f' \<^emph> ns k) = (val_Zp f'a))"
    using kz newton_seq.simps(1) 
    by presburger 
  have B2: "((val_Zp (f \<^emph> (ns k))) \<succeq>\<^bsub>G\<^esub> (Some ((2 * (ord_Zp f'a)) + 2 ^ k * t)))"
  proof-
    have "(Some ((2 * (ord_Zp f'a)) + 2 ^ k * t)) = Some ((2 * (ord_Zp f'a)) +  t)"
    proof-
      have "(2 * (ord_Zp f'a)) + 2 ^ k * t = (2 * (ord_Zp f'a)) +  t"
        using kz 
        by (smt mult.assoc mult.commute mult_cancel_right power.simps(1) power_mult_distrib)
      then show ?thesis 
        by blast
    qed
    then have "(Some ((2 * (ord_Zp f'a)) + 2 ^ k * t)) = Some ((2 * (ord_Zp f'a)) + ord_Zp fa - 2*(ord_Zp f'a))"
      unfolding hensel_factor_def 
      by (metis (no_types, hide_lams) add_diff_eq diff_diff_eq2 kz) 
    then have "(Some ((2 * (ord_Zp f'a)) + 2 ^ k * t)) = Some (ord_Zp fa)"
      by (metis \<open>Some ((2 * ord_Zp f'a) + 2 ^ k * t) = Some (2 * ord_Zp f'a + t)\<close> add_diff_cancel_left') 
    then have "((val_Zp (f \<^emph> (ns k))) = (Some ((2 * (ord_Zp f'a)) + 2 ^ k * t)))"
      using kz val_ord_Zp fa_closed fa_nonzero newton_seq.simps(1) 
      by smt 
    then show ?thesis 
      using G_eq 
      by blast
  qed
  then show "(( ns k) \<in> carrier Z\<^sub>p) \<and> (val_Zp (f' \<^emph> ns k) = (val_Zp f'a)) \<and> ((val_Zp (f \<^emph> (ns k))) \<succeq>\<^bsub>G\<^esub> (Some ((2 * (ord_Zp f'a)) + 2 ^ k * t)))"
    using B0 B1 B2 
    by blast 
next
  case (Suc n)
  fix n
  assume IH: "\<And>k. k \<le>n \<Longrightarrow> (ns k) \<in> carrier Z\<^sub>p
              \<and> val_Zp (f'\<^emph>(ns k)) = val_Zp (f'a)
              \<and> val_Zp (f\<^emph>(ns k)) \<succeq>\<^bsub>G\<^esub> * (2*(ord_Zp f'a)) + (2^k)*t *"

  show  "\<And>k. k \<le>Suc n \<Longrightarrow> (ns k) \<in> carrier Z\<^sub>p
              \<and> val_Zp (f'\<^emph>(ns k)) = val_Zp (f'a)
              \<and> val_Zp (f\<^emph>(ns k)) \<succeq>\<^bsub>G\<^esub> * (2*(ord_Zp f'a)) + (2^k)*t *"
  proof-
    fix k
    assume A: "k \<le> Suc n"
    show " (ns k) \<in> carrier Z\<^sub>p
              \<and> val_Zp (f'\<^emph>(ns k)) = val_Zp (f'a)
              \<and> val_Zp (f\<^emph>(ns k)) \<succeq>\<^bsub>G\<^esub> * (2*(ord_Zp f'a)) + (2^k)*t *"
    proof(cases "k \<le> n")
      case True
      then show ?thesis using IH 
        by blast
    next
      case False
      have F1: "(ns n) \<in> carrier Z\<^sub>p"
        using IH  by blast
      
      have F2: "val_Zp (f'\<^emph>(ns n)) = val_Zp (f'a)"
        using IH by blast 
      
      have F3: "val_Zp (f\<^emph>(ns n)) \<succeq>\<^bsub>G\<^esub> * (2*(ord_Zp f'a)) + (2^n)*t *"
        using IH by blast 

      have kval[simp]: "k = Suc n"
        using False A by auto 

      have F6: "val_Zp (f\<^emph>(ns n)) \<succeq>\<^bsub>G\<^esub> val_Zp (f'\<^emph>(ns n))"
      proof-
        have "(2*(ord_Zp f'a)) + (2^n)*t  \<ge> ord_Zp f'a"
          by (smt f'a_closed f'a_nonzero mult_nonneg_nonneg ord_pos t_pos zero_le_power)
        then have  "*(2*(ord_Zp f'a)) + (2^n)*t * \<succeq>\<^bsub>G\<^esub> *ord_Zp f'a*"
          using G_ord(2) by blast 
        then show ?thesis 
          by (metis F2 F3 G_ord_trans f'a_closed f'a_nonzero val_ord_Zp)
      qed

      have F5: " divide (f\<^emph>(ns n))(f'\<^emph>(ns n)) \<in> carrier Z\<^sub>p"
        using F6 
        by (smt F1 F2 continuous_is_closed divide_id'(1) divide_id(1) f'_closed f'a_closed 
            f'a_nonzero f_closed fa_closed fa_nonzero' hensel_factor_id hensel_hypothesis_weakened
            is_closed_fun_simp mult_zero(1) not_nonzero_Zp option.simps(1)
            polynomial_is_continuous val_Zp_mult val_ord_Zp) 

      have F4:  "(ns k) \<ominus> (ns n) = (\<ominus> divide (f\<^emph>(ns n))(f'\<^emph>(ns n)))"
      by (simp add: F1 F5 a_minus_def cring.axioms(1) cring.cring_simprules(10)
          cring.cring_simprules(3) newton_step_def ring.ring_simprules(18)) 


      have F7: "val_Zp (divide (f\<^emph>(ns n))(f'\<^emph>(ns n))) = val_Zp (f\<^emph>(ns n)) \<ominus>\<^bsub>G\<^esub> val_Zp (f'\<^emph>(ns n))"
        by (smt F1 F2 F6 continuous_is_closed divide_id'(3) divide_id(1) f'_closed f'a_closed 
            f'a_nonzero' f_closed fa_closed fa_nonzero' hensel_factor_id hensel_hypothesis_weakened
            is_closed_fun_simp mult_zero(1) not_nonzero_Zp option.simps(1) polynomial_is_continuous 
            val_Zp_mult val_ord_Zp) 
      show ?thesis
      proof
        show P0:"ns k \<in> carrier Z\<^sub>p"
        proof- 
          have A0: "ns k = ns n \<ominus> (divide (f\<^emph> (ns n)) (f'\<^emph>(ns n)))"
            by (simp add: newton_step_def)
          have A1: "val_Zp (f'\<^emph>(ns n)) = val_Zp f'a"
            using IH  
            by blast
          have A2: "val_Zp (f\<^emph>(ns n)) \<succeq>\<^bsub>G\<^esub>val_Zp f'a"
          proof-
            have A20: " Some ((2 * ord_Zp f'a) + 2 ^ n * (ord_Zp fa - 2 * ord_Zp f'a)) \<succeq>\<^bsub>G\<^esub>val_Zp f'a"
            proof-
              have "(ord_Zp fa - 2 * ord_Zp f'a) \<ge> 0"
                using hensel_hypothesis by linarith
              then have "  (2 ^ n) * (ord_Zp fa - 2 * ord_Zp f'a)
                        \<ge> (ord_Zp fa - 2 * ord_Zp f'a)"
                by (metis hensel_factor_def mult.commute mult_le_cancel_left1
                    mult_less_0_iff not_square_less_zero one_le_numeral one_le_power t_pos)
              then have  "  ((2 * ord_Zp f'a) + 2 ^ n * (ord_Zp fa - 2 * ord_Zp f'a))
                        \<ge> (2 * ord_Zp f'a) + (ord_Zp fa - 2 * ord_Zp f'a)"
                by (simp add: ord_Zp_def)
              then have  "  ((2 * ord_Zp f'a) + 2 ^ n * (ord_Zp fa - 2 * ord_Zp f'a))
                        \<ge> (ord_Zp fa )"
                by presburger
              then have  "  ((2 * ord_Zp f'a) + 2 ^ n * (ord_Zp fa - 2 * ord_Zp f'a))
                        \<ge> (ord_Zp f'a )"
                using hensel_hypothesis_weakened by linarith
              then show ?thesis 
                by (metis G_ord(2) f'a_closed f'a_nonzero val_ord_Zp)
            qed
            have A21:"val_Zp (f\<^emph>(ns n)) \<succeq>\<^bsub>G\<^esub> Some ((2 * ord_Zp f'a) + 2 ^ n * (ord_Zp fa - 2 * ord_Zp f'a))"
              using IH[of n] unfolding hensel_factor_def 
              by linarith
            show ?thesis using A21 A20 
              using G_ord_trans by blast
          qed
          have A3: "ns n \<in> carrier Z\<^sub>p"
            using IH by blast 
          have A4: "val_Zp (f\<^emph>(ns n)) \<succeq>\<^bsub>G\<^esub>val_Zp (f'\<^emph>(ns n))"
            using A1 A2 
            by presburger
          have A5: "f\<^emph>(ns n) \<in> carrier Z\<^sub>p"
            by (simp add: A3)
          have A6: "(f'\<^emph>(ns n)) \<in> nonzero Z\<^sub>p"
          proof-
            have "(f'\<^emph>(ns n)) \<in> carrier  Z\<^sub>p"
              by (simp add: A3)
            have "val_Zp (f'\<^emph>(ns n)) \<noteq> \<infinity>\<^bsub>G\<^esub>"
              using A1 
              by (smt G_mult(2) divide_id(1) f'a_closed f'a_nonzero f'a_nonzero' fa_closed 
                  fa_nonzero fa_nonzero' hensel_factor_id hensel_hypothesis_weakened 
                  option.simps(1) val_Zp_mult val_ord_Zp)
            then show ?thesis 
              using \<open>f' \<^emph> ns n \<in> carrier Z\<^sub>p\<close> not_nonzero_Zp val_Zp_def 
              by meson
          qed
          have A7: " (divide (f\<^emph> (ns n)) (f'\<^emph>(ns n))) \<in> carrier Z\<^sub>p"
            using A5 A6 A4 A3 divide_id'(1)[of "(f\<^emph> (ns n))"] 
            by blast 
          then show ?thesis 
            using A0 A3 cring.cring_simprules(4) 
            by (simp add: F1 F5 cring.cring_simprules(4))
        qed

        have P1: "val_Zp (f' \<^emph> ns k) = val_Zp f'a "
        proof(cases "(f' \<^emph> ns k) = (f' \<^emph> ns n)")
          case True
          then show ?thesis using IH[of n]
            by (metis order_refl)
        next
          case False
          have "val_Zp ((f' \<^emph> ns k) \<ominus> (f' \<^emph> ns n)) \<succeq>\<^bsub>G\<^esub> val_Zp ((ns k) \<ominus> (ns n))"
            using False P0 f'_closed  poly_diff_val IH 
            by blast
          then have "val_Zp ((f' \<^emph> ns k) \<ominus> (f' \<^emph> ns n)) \<succeq>\<^bsub>G\<^esub> val_Zp (\<ominus> divide (f\<^emph>(ns n))(f'\<^emph>(ns n)))"
            using  F4 by metis  
          then have "val_Zp ((f' \<^emph> ns k) \<ominus> (f' \<^emph> ns n)) \<succeq>\<^bsub>G\<^esub> val_Zp (divide (f\<^emph>(ns n))(f'\<^emph>(ns n)))"
            by (metis F1 F4 F5 P0 Zp_is_cring Zp_minus_ominus cring.cring_simprules(21) 
                cring.cring_simprules(3) cring_def ord_Zp_dist_sym ring.r_right_minus_eq val_ord_Zp)
          then have P10: "val_Zp ((f' \<^emph> ns k) \<ominus> (f' \<^emph> ns n)) \<succeq>\<^bsub>G\<^esub> val_Zp (f\<^emph>(ns n)) \<ominus>\<^bsub>G\<^esub> val_Zp (f'\<^emph>(ns n))"
            using F7 by metis 
          have P11: "val_Zp (f'\<^emph>(ns n)) \<noteq> \<infinity>\<^bsub>G\<^esub>"
            by (metis F2 G_EOAG extended_ordered_abelian_group.infinity_distinct f'a_nonzero' val_Zp_closed)
          then have "val_Zp ((f' \<^emph> ns k) \<ominus> (f' \<^emph> ns n)) \<succeq>\<^bsub>G\<^esub> *(2 * ord_Zp f'a) + 2 ^ n * t* \<ominus>\<^bsub>G\<^esub>  val_Zp (f'\<^emph>(ns n))"
            using F3 P10  G_ord_trans gord_minus 
            by blast  
          then have "val_Zp ((f' \<^emph> ns k) \<ominus> (f' \<^emph> ns n)) \<succeq>\<^bsub>G\<^esub> *(2 * ord_Zp f'a) + 2 ^ n * t - ord_Zp(f'\<^emph>(ns n))*"
            by (metis F1 P11 continuous_is_closed f'_closed gminus_minus is_closed_fun_simp
                polynomial_is_continuous val_Zp_def val_ord_Zp)  
          then have P12: "val_Zp ((f' \<^emph> ns k) \<ominus> (f' \<^emph> ns n)) \<succeq>\<^bsub>G\<^esub> *(2 *(ord_Zp f'a)) + 2 ^ n * t - (ord_Zp f'a) *"
            by (metis F2 P11 option.simps(1) ord_Zp_def val_Zp_def)  
          then have P13:"val_Zp ((f' \<^emph> ns k) \<ominus> (f' \<^emph> ns n)) \<succeq>\<^bsub>G\<^esub> * (ord_Zp f'a) + 2 ^ n * t *"
          proof-
            have "(2 *(ord_Zp f'a)) + (2 ^ n * t) - (ord_Zp f'a) = (ord_Zp f'a) + 2 ^ n * t"
              by linarith
            then show ?thesis using P12 by metis 
          qed
          then have P14: "val_Zp ((f' \<^emph> ns k) \<ominus> (f' \<^emph> ns n)) \<succeq>\<^bsub>G\<^esub> * (ord_Zp f'a) + 1*"
          proof-
            have "(ord_Zp f'a) + 2 ^ n * t  \<ge> (ord_Zp f'a) + 1"
              by (smt mult_less_cancel_right2 t_pos zero_less_power)
            then show ?thesis 
              using P13  G_ord(2) G_ord_trans by blast
          qed
          show ?thesis 
          proof(cases "(f' \<^emph> ns k) \<ominus> (f' \<^emph> ns n) = \<zero>")
            case True
            then have "(f' \<^emph> ns k) = (f' \<^emph> ns n)"
              using F1 P0 Zp_nonzero_def(2) Zp_not_eq_diff_nonzero continuous_is_closed
                f'_closed is_closed_fun_simp polynomial_is_continuous by blast
            then show ?thesis 
              using False by blast
          next
            case False
            then have 0: "ord_Zp ((f' \<^emph> ns k) \<ominus> (f' \<^emph> ns n)) \<ge> (ord_Zp f'a) + 1"
              using P14 
              by (metis G_ord(2) ord_Zp_def val_Zp_def)
            have 1: "ord_Zp (f' \<^emph> ns n) = ord_Zp (f'a)"
              by (metis F2 P11  option.simps(1) ord_Zp_def val_Zp_def)
            have 2: "ord_Zp (f' \<^emph> ns n) = ord_Zp(f' \<^emph> ns k)"
              using 0 1 equal_ord  
              by (smt F1 P0 P11 Zp_is_cring a_minus_def abelian_group.r_neg continuous_is_closed 
                  cring.cring_simprules(10) cring.cring_simprules(3) cring_def f'_closed 
                  is_closed_fun_simp ord_Zp_of_ominus ord_of_nonzero(2) ord_pos
                  polynomial_is_continuous ring.ring_simprules(18) ring_def val_Zp_def)
            then show ?thesis 
              by (metis "1" Zp_int_inc_zero' Zp_int_mult_closed f'a_closed 
                  f'a_nonzero ord_Zp_def ord_of_nonzero(1) ord_pos val_Zp_def)
          qed
        qed

        have P2: " val_Zp (f\<^emph>(ns k)) \<succeq>\<^bsub>G\<^esub> * (2*(ord_Zp f'a)) + (2^k)*t *"
        proof(cases "f\<^emph>(ns k) = \<zero>")
          case True
          then show ?thesis 
            using G_ord(1) val_Zp_def 
            by (simp add: G_ord(1) ord_Zp_def)
        next
          case False
          then have P20: "f\<^emph>(ns k) \<in> nonzero Z\<^sub>p"
            using P0 continuous_is_closed f_closed is_closed_fun_simp not_nonzero_Zp 
              polynomial_is_continuous 
            by blast
          have P21: "f\<^emph>(ns n) \<in> nonzero Z\<^sub>p"
          proof-
            have "f\<^emph>(ns n) \<noteq>\<zero>"
            proof
              assume "f \<^emph> ns n = \<zero>"
              then have "divide (f \<^emph> ns n) (f' \<^emph> ns n ) = \<zero>"
                by (simp add: divide_def)
              then have "f \<^emph> ns k = \<zero>"
                using kval newton_step_def
                by (metis F1 F4 F5 P0 Zp_is_cring Zp_minus_ominus Zp_nonzero_def(2)
                    Zp_not_eq_diff_nonzero \<open>f \<^emph> ns n = \<zero>\<close> cring.cring_simprules(21))
              then show False 
                using False by blast
            qed
            then show ?thesis 
              by (simp add: \<open>f \<^emph> ns n \<noteq> \<zero>\<close> F1 nonzero_def)
          qed
          have P23: "2 * (ord_Zp f'a) + ((2 ^ k) * t) \<le> ord_Zp (f \<^emph> ns k)"
          proof-
              obtain c where c_def: "c \<in> carrier Z\<^sub>p \<and>f\<^emph>((ns n) \<ominus> (divide (f\<^emph>(ns n)) (f'\<^emph>(ns n)))) =  
                                              (c \<otimes> (divide (f\<^emph>(ns n)) (f'\<^emph>(ns n)))[^](2::nat))"
              using   UP_domain.Taylor_deg_1_eval'''[of Z\<^sub>p f "ns n" "(divide (f\<^emph>(ns n)) (f'\<^emph>(ns n)))"]
              by (smt F1 F2 F5 F6 G_mult(2) UP_domain.Taylor_closed UP_domain.pderiv_eval_deriv
                  Z\<^sub>p_x_is_UP_domain Zp_is_cring Zp_nonzero_def(1) cring.cring_simprules(3)
                  divide_id'(2) divide_id(1) f'_closed f'a_nonzero' f_closed fa_nonzero' 
                  fun_of_closed_UP_domain hensel_factor_id hensel_hypothesis_weakened
                  not_nonzero_Zp option.simps(1) shift_closed_UP_domain val_Zp_def val_Zp_mult 
                  val_ord_Zp)
              have P230: "f\<^emph>(ns k) =  (c \<otimes> (divide (f\<^emph>(ns n)) (f'\<^emph>(ns n)))[^](2::nat))"
                using c_def 
                by (simp add: newton_step_def)
              have c_nonzero: "c \<in> nonzero Z\<^sub>p"
              proof-
                have "c \<noteq> \<zero>"
                proof-
                  have "f\<^emph>(ns k) \<in> nonzero Z\<^sub>p"
                    using P20 by metis 
                  then show ?thesis 
                    using F5 False P230 
                    by (metis mult_zero(2) pow_closed)
                qed
                then show ?thesis using c_def 
                  by (simp add: \<open>c \<noteq> \<zero>\<close> nonzero_def)
              qed
              have P231: "ord_Zp (f\<^emph>(ns k)) = ord_Zp c + 2*(ord_Zp (f\<^emph>(ns n)) - ord_Zp(f'\<^emph>(ns n)))"
              proof-
                have P2310: "ord_Zp (f\<^emph>(ns k)) =  ord_Zp c + ord_Zp ((divide (f\<^emph>(ns n)) (f'\<^emph>(ns n)))[^](2::nat))"
                  by (metis F5 P20 P230 Zp_nonzero_def(2) c_def c_nonzero 
                      mult_zero(1) not_nonzero_Zp ord_Zp_mult pow_closed)
                have P2311: "ord_Zp ((divide (f\<^emph>(ns n)) (f'\<^emph>(ns n)))[^](2::nat)) 
                                                    =  2*(ord_Zp (f\<^emph>(ns n)) - ord_Zp(f'\<^emph>(ns n)))"
                proof-
                  have P23110: "ord_Zp ((divide (f\<^emph>(ns n)) (f'\<^emph>(ns n)))[^](2::nat)) = 
                       2*(ord_Zp (divide (f\<^emph>(ns n)) (f'\<^emph>(ns n))))"
                    by (metis F5 P20 P230 Zp_nonzero_def(2) c_def mult_zero(1) 
                        not_nonzero_Zp of_nat_numeral ord_Zp_pow pow_zero zero_less_numeral)
                  have "(ord_Zp (divide (f\<^emph>(ns n)) (f'\<^emph>(ns n)))) = (ord_Zp (f\<^emph>(ns n)) - ord_Zp(f'\<^emph>(ns n))) "
                  proof-
                    have "ord_Zp (f\<^emph>(ns n)) \<ge> ord_Zp(f'\<^emph>(ns n))"
                    proof -
                      show ?thesis
                        by (smt F1 F6 G_ord(2) P21 Zp_nonzero_def(1) Zp_nonzero_def(2) 
                            continuous_is_closed f'_closed is_closed_fun_simp ord_of_nonzero(1) 
                            ord_pos polynomial_is_continuous val_ord_Zp) 
                      qed
                    then show ?thesis 
                      by (metis F1 F2 G_EOAG P21 continuous_is_closed divide_id(3) 
                          extended_ordered_abelian_group.infinity_distinct f'_closed f'a_nonzero' 
                          is_closed_fun_simp ord_of_nonzero(2) ord_pos polynomial_is_continuous
                          val_Zp_closed val_Zp_def)
                  qed
                  then show ?thesis using P23110 
                    by presburger
                qed
                show ?thesis 
                  using P2310 P2311 by linarith
              qed

              have P232: "ord_Zp (f\<^emph>(ns k)) \<ge> 2*(ord_Zp (f\<^emph>(ns n)) - ord_Zp(f'\<^emph>(ns n)))"
              proof-
                have "ord_Zp c \<ge> 0"
                proof -
                  have "\<zero> \<noteq> c"
                    using c_nonzero 
                    by (metis Zp_nonzero_def(2))
                  then show ?thesis
                    by (metis (no_types) c_def of_nat_0_le_iff ord_nat)
                qed
                then show ?thesis 
                  using P231 by linarith
              qed
              have P233: "(2 * ord_Zp f'a) + 2 ^ n * t \<le> ord_Zp (f \<^emph> ns n)"
                using IH[of n]  False  F3  P21 Zp_nonzero_def(1)
                      Zp_nonzero_def(2) val_ord_Zp 
                by (metis G_ord(2)) 
              have P234: " ord_Zp (f' \<^emph> ns n) = ord_Zp f'a"
                by (metis F2 G_EOAG extended_ordered_abelian_group.infinity_distinct 
                    f'a_nonzero' option.simps(1) ord_Zp_def val_Zp_closed val_Zp_def)
              have P236:  "ord_Zp (f\<^emph>(ns k)) \<ge> (2*((2 *ord_Zp f'a) + 2 ^ n * t) ) - 2* ord_Zp(f'\<^emph>(ns n))"
                using P232 P233 by presburger
              have P237:  "ord_Zp (f\<^emph>(ns k)) \<ge>(4*ord_Zp f'a) + (2*((2 ^ n)* t)) - 2* ord_Zp(f'\<^emph>(ns n))"
              proof-
                have "(2*((2 *ord_Zp f'a) + 2 ^ n * t) ) - 2* ord_Zp(f'\<^emph>(ns n)) \<ge>(4*ord_Zp f'a) + (2*((2 ^ n)* t)) - 2* ord_Zp(f'\<^emph>(ns n))"
                  by presburger
                then show ?thesis 
                  using P236
                  by linarith
              qed
              have P237:  "ord_Zp (f\<^emph>(ns k)) \<ge>(4*ord_Zp f'a) + (2*((2 ^ n)* t)) - 2* ord_Zp(f'a)"
                using P234 P237 by linarith
              have P238: "ord_Zp (f\<^emph>(ns k)) \<ge>(2*ord_Zp f'a) + (2*((2 ^ n)* t))"
                using P237 by linarith
              have P239:  "ord_Zp (f\<^emph>(ns k)) \<ge>(2*ord_Zp f'a) + (2*(2 ^ n))* t"
                using P238  by linarith
              have P23A:  "ord_Zp (f\<^emph>(ns k)) \<ge>(2*ord_Zp f'a) + (2*(2 ^ n))* t"
              proof-
                have "(2*(ord_Zp f'a)) + ((2*(2 ^ n))* t) = (2*ord_Zp f'a) + (2*(2 ^ n))* t"
                  by presburger 
                then show ?thesis using P239 by metis  
              qed
               show ?thesis 
              proof-
                have "(2*ord_Zp f'a) + ((2*(2 ^ n))* t) = (2*ord_Zp f'a) + ((2 ^ (Suc n)))* t"
                  by (metis kval power_Suc) 
                then show ?thesis 
                  using P23A 
                  by (metis kval)
              qed
          qed
          show ?thesis using P23 False 
            by (metis G_ord(2) ord_Zp_def val_Zp_def) 
        qed
        show "val_Zp (f' \<^emph> ns k) = val_Zp f'a 
                    \<and> (val_Zp (f \<^emph> ns k)) \<succeq>\<^bsub>G\<^esub> Some ((2 * ord_Zp f'a) + 2 ^ k * t)" 
          using P1 P2 by blast
      qed
    qed
  qed
qed

lemma newton_seq_simp0[simp]:
shows "ns m \<in> carrier Z\<^sub>p"
  using newton_seq_props_induct 
  by blast

lemma newton_seq_simp1[simp]:
"val_Zp (f'\<^emph>(ns k)) = val_Zp (f'a)"
using newton_seq_props_induct by blast

lemma newton_seq_simp2[simp]:
" val_Zp (f\<^emph>(ns k)) \<succeq>\<^bsub>G\<^esub> * (2*(ord_Zp f'a)) + (2^k)*t *"
  by (meson le_iff_add newton_seq_props_induct)

lemma newton_seq_simp3[simp]:
"val_Zp (f\<^emph>(ns l)) \<succeq>\<^bsub>G\<^esub> val_Zp (f'\<^emph>(ns l))"
  by (smt G_ord(1)  G_ord(2) f'a_closed f'a_nonzero mult_less_cancel_right2 
      newton_seq_simp1 newton_seq_simp2 ord_Zp_def ord_pos t_pos val_Zp_def zero_less_power)

lemma newton_seq_simp4[simp]:
  assumes "f\<^emph>(ns l) \<noteq>\<zero>"
  shows "ord_Zp (f\<^emph>(ns l)) \<ge> ord_Zp (f'\<^emph>(ns l))"
  by (metis G_ord G_ord_trans assms newton_seq_simp3 ord_Zp_def val_Zp_def)

lemma newton_seq_is_cauchy_0:
  assumes "\<And>k. f\<^emph>(ns k) \<noteq>\<zero>"
shows "is_cauchy ns"
proof(rule is_cauchyI')
  show P0: "is_closed_seq ns"
  proof(rule is_closedI)
    show "\<And>k. ns k \<in> carrier Z\<^sub>p "
      by simp 
  qed

  show " \<forall>n. \<exists>k. \<forall>m. k \<le> int m \<longrightarrow> int n \<le> ord_Zp_dist (ns (Suc m)) (ns m)"
  proof
    fix n
    show "\<exists>k. \<forall>m. k \<le> int m \<longrightarrow> int n \<le> ord_Zp_dist (ns (Suc m)) (ns m)"
    proof(induction "n")
      case 0
      have B0: "\<forall>n0 n1. 0 < n0 \<and> 0 < n1 \<longrightarrow> ns n0 0 = ns n1 0"
        apply auto 
      proof-
        fix n0 n1::nat 
        assume A: "0 < n0" "0 < n1"
        show "ns n0 0 = ns n1 0"
        proof-
          have 0: "ns n0 \<in> carrier Z\<^sub>p"
            using P0 
            by simp
          have 1: "ns n1 \<in> carrier Z\<^sub>p"
            using P0 
            by simp
          show ?thesis
            using 0 1 
            by (metis of_nat_0 ord_pos zero_below_ord zero_vals)
        qed
      qed
      have "\<forall>m. 1 \<le> int m \<longrightarrow> int 0 \<le> ord_Zp_dist (newton_step (ns m)) (ns m)"
      proof
        fix m
        show "1 \<le> int m \<longrightarrow> int 0 \<le> ord_Zp_dist (newton_step (ns m)) (ns m)"
        proof
        assume "1 \<le> int m "
        then have C0:"ns (Suc m) 0 = ns m 0"
          using B0 
          by (metis int_one_le_iff_zero_less int_ops(1) less_Suc_eq_0_disj of_nat_less_iff)
        then show "int 0 \<le> ord_Zp_dist (newton_step (ns m)) (ns m)"
        proof-
          have "(newton_step (ns m)) \<noteq>(ns m)"
          proof-
            have "divide (f\<^emph>(ns m)) (f'\<^emph>(ns m)) \<noteq>\<zero>"
            proof-
              have 0: "(f\<^emph>(ns m)) \<noteq> \<zero>"
                using assms by auto 
              have 1: " (f'\<^emph>(ns m)) \<in> carrier Z\<^sub>p"
                by simp 
              have 2:  "(f'\<^emph>(ns m)) \<noteq> \<zero>" 
                by (smt \<open>f' \<^emph> ns m \<in> carrier Z\<^sub>p\<close> divide_id'(1) f'a_closed f'a_nonzero' fa_closed
                    fa_nonzero hensel_factor_id hensel_hypothesis_weakened mult_zero(1)
                    newton_seq.simps(1) newton_seq_simp1 newton_seq_simp3 option.simps(1) 
                    val_Zp_mult val_ord_Zp) 
              show ?thesis using 0 1 2 
                by (metis continuous_is_closed divide_id'(2) f_closed is_closed_fun_simp 
                    mult_zero(2) newton_seq_simp0 newton_seq_simp3 not_nonzero_Zp
                    polynomial_is_continuous) 
            qed
            then show ?thesis using newton_step_def 
              by (smt  Zp_is_cring \<open>1 \<le> int m\<close> a_closed a_minus_def abelian_group.r_neg
                  assms continuous_is_closed cring.cring_simprules(21) cring.cring_simprules(3) 
                  cring_def divide_id(1) f'_closed f'a_nonzero' G_ord f_closed fa_nonzero 
                  hensel_factor_id hensel_hypothesis_weakened is_closed_fun_simp 
                  mult_less_cancel_right2 mult_zero(1) newton_seq_simp0 newton_seq_simp1 
                  newton_seq_simp2 not_nonzero_Zp of_nat_less_two_power option.simps(1) 
                  ord_pos polynomial_is_continuous ring.ring_simprules(18) ring_def
                  t_pos val_Zp_mult val_ord_Zp)
          qed
          then show ?thesis using C0 
            by (metis newton_seq.simps(2) newton_seq_simp0 ord_Zp_dist_res_eq2)
        qed
      qed
      qed
      then show ?case 
        using ord_Zp_def by auto
    next
      case (Suc n)
      show "\<And>n. \<exists>k. \<forall>m. k \<le> int m \<longrightarrow> int n \<le> ord_Zp_dist (ns (Suc m)) (ns m) \<Longrightarrow> \<exists>k. \<forall>m. k \<le> int m \<longrightarrow> int (Suc n) \<le> ord_Zp_dist (ns (Suc m)) (ns m)"
      proof-
        fix n 
        show " \<exists>k. \<forall>m. k \<le> int m \<longrightarrow> int n \<le> ord_Zp_dist (ns (Suc m)) (ns m) \<Longrightarrow> \<exists>k. \<forall>m. k \<le> int m \<longrightarrow> int (Suc n) \<le> ord_Zp_dist (ns (Suc m)) (ns m)"
      proof-
        assume IH: "\<exists>k. \<forall>m. k \<le> int m \<longrightarrow> int n \<le> ord_Zp_dist (ns (Suc m)) (ns m)"
        show " \<exists>k. \<forall>m. k \<le> int m \<longrightarrow> int (Suc n) \<le> ord_Zp_dist (ns (Suc m)) (ns m)"
      proof-
        obtain k0 where k0_def: "k0 \<ge>0 \<and> (\<forall>m. k0 \<le> int m \<longrightarrow>int  n \<le> ord_Zp_dist (newton_step (ns m)) (ns m))"
          using IH 
          by (metis  dual_order.strict_implies_order int_nat_eq le0
               linorder_not_less nat_le_iff newton_seq.simps(2) of_nat_0_eq_iff ord_Zp_def)
        have I0: "\<And>l. ord_Zp (ns (Suc l) \<ominus> ns l) = ord_Zp (f\<^emph> (ns l)) - ord_Zp (f'\<^emph>(ns l))"
        proof-
          fix l
          have I00:"(ns (Suc l) \<ominus> ns l) = (\<ominus> divide (f\<^emph>(ns l)) (f'\<^emph>(ns l)))"
            using newton_step_def[of "ns l"]  Zp_is_cring a_minus_def assms 
              continuous_is_closed cring.cring_simprules(10) cring.cring_simprules(3)
              cring_def divide_id(1) f'_closed f'a_closed f'a_nonzero f_closed fa_closed 
              fa_nonzero hensel_factor_id hensel_hypothesis_weakened is_closed_fun_simp
              mult_less_cancel_right2 mult_zero(1) newton_seq.simps(2) newton_seq_simp0
              newton_seq_simp1 newton_seq_simp2 not_nonzero_Zp option.simps(1) ord_pos
              polynomial_is_continuous ring.ring_simprules(18) t_pos val_Zp_mult
              val_ord_Zp zero_less_power G_ord
            by smt
          have I01: "ord_Zp (ns (Suc l) \<ominus> ns l) = ord_Zp (divide (f\<^emph>(ns l)) (f'\<^emph>(ns l)))"   
          proof-
            have I010: "(divide (f\<^emph>(ns l)) (f'\<^emph>(ns l))) \<in>carrier Z\<^sub>p"
             by (smt continuous_is_closed divide_id'(1) f'_closed f'a_nonzero f_closed fa_nonzero 
                 hensel_factor_id hensel_hypothesis_weakened is_closed_fun_simp mult_zero(1)
                 newton_seq.simps(1) newton_seq_simp0 newton_seq_simp1 newton_seq_simp3
                 not_nonzero_Zp option.simps(1) polynomial_is_continuous val_Zp_mult val_ord_Zp) 
           have I011: "(divide (f\<^emph>(ns l)) (f'\<^emph>(ns l))) \<noteq> \<zero>"
           proof-
             have A: "(f\<^emph>(ns l)) \<noteq>\<zero>"
               by (simp add: assms) 
             have B: " (f'\<^emph>(ns l))  \<in>carrier Z\<^sub>p"
               by simp 
             then have C: " (f'\<^emph>(ns l))  \<in>nonzero  Z\<^sub>p"
               by (smt divide_id'(1) f'a_closed f'a_nonzero fa_closed fa_nonzero
                   hensel_factor_id hensel_hypothesis_weakened mult_zero(1) newton_seq.simps(1)
                   newton_seq_simp1 newton_seq_simp3 not_nonzero_Zp option.simps(1)
                   val_Zp_mult val_ord_Zp) 
             then show ?thesis using I010 A 
               by (metis B continuous_is_closed divide_id'(2) f_closed is_closed_fun_simp 
                   mult_zero(2) newton_seq_simp0 newton_seq_simp3 polynomial_is_continuous)
           qed
           then have "ord_Zp (divide (f\<^emph>(ns l)) (f'\<^emph>(ns l)))
                    = ord_Zp (\<ominus> divide (f\<^emph>(ns l)) (f'\<^emph>(ns l)))"
             using I010 not_nonzero_Zp ord_Zp_of_ominus by blast
           then show ?thesis using I00 by metis  
          qed
          have I02: "ord_Zp (f\<^emph>(ns l)) \<ge> ord_Zp (f'\<^emph>(ns l))"
            using assms  newton_seq_simp4
            by blast  
          have I03: "(f\<^emph>(ns l)) \<in> nonzero Z\<^sub>p"
            by (simp add: assms nonzero_def)
          have I04: "f'\<^emph>(ns l) \<in> nonzero Z\<^sub>p"
            by (smt continuous_is_closed divide_id'(1) f'_closed f'a_nonzero fa_closed 
                fa_nonzero hensel_factor_id hensel_hypothesis_weakened is_closed_fun_simp
                mult_zero(1) newton_seq.simps(1) newton_seq_simp0 newton_seq_simp1
                newton_seq_simp3 not_nonzero_Zp option.simps(1) polynomial_is_continuous
                val_Zp_mult val_ord_Zp)
          have I05 :" ord_Zp (divide (f\<^emph>(ns l)) (f'\<^emph>(ns l))) = ord_Zp (f\<^emph> (ns l)) - ord_Zp (f'\<^emph>(ns l))"
            using I02 I03 I04  divide_id(3)
            by blast
          then show " ord_Zp (ns (Suc l) \<ominus> ns l) = ord_Zp (f\<^emph> (ns l)) - ord_Zp (f'\<^emph>(ns l))"
            using I01 by linarith
        qed
        have "\<forall>m. int(Suc n) + k0 + 1 \<le> int m \<longrightarrow> int (Suc n) \<le> ord_Zp_dist (newton_step (ns m)) (ns m)"
        proof
          fix m
          show "int (Suc n) + k0 + 1 \<le> int m \<longrightarrow> int (Suc n) \<le> ord_Zp_dist (newton_step (ns m)) (ns m)"
          proof
          assume A: "int (Suc n) + k0 + 1 \<le> int m "
          show " int (Suc n) \<le> ord_Zp_dist (newton_step (ns m)) (ns m)"
          proof-
            have 0: " ord_Zp_dist (newton_step (ns m)) (ns m) =  ord_Zp (f\<^emph> (ns m)) - ord_Zp (f'\<^emph>(ns m))"
              by (metis I0 newton_seq.simps(2))
            have 1: "ord_Zp (f\<^emph> (ns m)) - ord_Zp (f'\<^emph>(ns m)) > int n"
            proof-
              have "ord_Zp (f\<^emph> (ns m)) \<ge> (2*(ord_Zp f'a)) + (2^m)*t"
                using newton_seq_props_induct[of m] assms 
                by (metis G_ord(2) newton_seq_simp2 ord_Zp_def val_Zp_def)
              then have 10:"ord_Zp (f\<^emph> (ns m)) - ord_Zp (f'\<^emph>(ns m)) \<ge> (2*(ord_Zp f'a)) + (2^m)*t -  ord_Zp (f'\<^emph>(ns m))"
                by linarith
              have "2^m * t > m"
                by (smt Groups.mult_ac(2) mult_less_cancel_right2 of_nat_less_two_power t_pos zero_le_power)
              then have "2^m * t > int m"
                by blast
              then have "2^m * t >2 + (int n + k0)"
                using A 
                by linarith
              then have "2^m * t >1 + int n"
                using k0_def by linarith
              then have 11: "ord_Zp (f\<^emph> (ns m)) - ord_Zp (f'\<^emph>(ns m)) 
                                \<ge> (2*(ord_Zp f'a)) + 1 + int n -  ord_Zp (f'\<^emph>(ns m))"
                using "10" by linarith
              have 12: "ord_Zp (f'\<^emph>(ns m))  = ord_Zp (f'\<^emph>a) "
                by (smt continuous_is_closed divide_id'(1) f'_closed f'a_nonzero' 
                    fa_closed fa_nonzero hensel_factor_id hensel_hypothesis_weakened
                    is_closed_fun_simp mult_zero(1) newton_seq.simps(1) newton_seq_simp0 
                    newton_seq_simp1 newton_seq_simp3 option.simps(1) 
                    polynomial_is_continuous val_Zp_mult val_ord_Zp)
              then have 13: "ord_Zp (f\<^emph> (ns m)) - ord_Zp (f'\<^emph>(ns m)) 
                                \<ge> (2*(ord_Zp f'a)) + 1 + int n -  ord_Zp (f'a)"
                using 11 
                by linarith
              then have 14:"ord_Zp (f\<^emph> (ns m)) - ord_Zp (f'\<^emph>(ns m)) 
                                \<ge> 1 + int n +  ord_Zp (f'a)"
                by linarith
              have 15: "ord_Zp f'a \<ge>0"
                using f'a_closed f'a_nonzero ord_pos by blast
              then show ?thesis 
                using 14  
                by linarith
            qed
            then show ?thesis 
              using "0" by linarith
          qed
        qed
        qed
        then show ?thesis 
          using ord_Zp_def by auto
       qed
     qed
   qed
 qed
  qed
qed

lemma eventually_zero:
"f \<^emph> ns (k + m) = \<zero> \<Longrightarrow> f \<^emph> ns (k + Suc m) = \<zero>"
proof-
  assume A: "f \<^emph> ns (k + m) = \<zero>"
  have 0: "ns (k + Suc m) = ns (k + m) \<ominus> (divide (f \<^emph> ns (k + m)) (f' \<^emph> ns (k + m)))"
    by (simp add: newton_step_def)
  have 1: "(divide (f \<^emph> ns (k + m)) (f' \<^emph> ns (k + m))) = \<zero>"
    by (simp add: A divide_def)
  show "f \<^emph> ns (k + Suc m) = \<zero>"
    using A 0 1 
    by (metis Zp_is_cring Zp_minus_ominus a_minus_def add_zero(1) cring_def
        newton_seq_simp0 ring.r_right_minus_eq)
qed

lemma newton_seq_is_cauchy:
"is_cauchy ns"
proof(cases "\<forall>k. f\<^emph>(ns k) \<noteq>\<zero>")
  case True
  then show ?thesis using newton_seq_is_cauchy_0 
    by blast
next
  case False
  obtain k where k_def:"f\<^emph>(ns k) = \<zero>"
    using False by blast
  have 0: "\<And>m. (ns (m + k)) = (ns k)"
  proof-
    fix m
    show "(ns (m + k)) = (ns k)"
      apply(induction m)
      apply (simp add: k_def)
    proof-
      fix m
      assume IH: "ns (m + k) = ns k"
      show "(ns (Suc m + k)) = (ns k)" 
      proof-
        have "f \<^emph> ns (m + k) = \<zero>"
          by (simp add: IH k_def)
        then have "divide ( f \<^emph> ns (m + k)) (f' \<^emph> ns (m + k)) = \<zero>"
          by (simp add: divide_def)
        then show ?thesis using newton_step_def 
          by (metis IH Suc_inject Zero_not_Suc Zp_is_cring Zp_minus_ominus 
              \<open>f \<^emph> ns (m + k) = \<zero>\<close> a_minus_def add_Suc  add_zero(1) cring_def 
              k_def newton_seq.elims newton_seq_simp0 ring.r_right_minus_eq)
      qed
    qed
  qed
  show "is_cauchy ns"
    apply(rule is_cauchyI)
    apply simp
  proof-
    show "\<And>n.\<And>n. \<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> ns n0 n = ns n1 n"
    proof-
      fix n
      show "\<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> ns n0 n = ns n1 n"
      proof-
        have "\<forall>n0 n1. k < n0 \<and> k < n1 \<longrightarrow> ns n0 n = ns n1 n"
          apply auto 
        proof-
          fix n0 n1
          assume A0: "k < n0"
          assume A1: "k < n1"
          obtain m0 where m0_def: "n0 = k + m0"
            using A0 less_imp_add_positive by blast
          obtain m1 where m1_def: "n1 = k + m1"
            using A1 less_imp_add_positive by auto
          show "ns n0 n = ns n1 n"
            using 0 m0_def m1_def 
            by (metis add.commute)
        qed
        then show ?thesis by blast 
      qed
    qed
  qed
qed

lemma pre_full_hensel:
"val_Zp (a \<ominus> (ns n)) \<succeq>\<^bsub>G\<^esub> (Some 1) \<oplus>\<^bsub>G\<^esub> val_Zp (f'\<^emph>a)"
"\<exists>N. \<forall>n. n> N \<longrightarrow> (val_Zp (a \<ominus> (ns n)) = val_Zp (divide (f\<^emph>a) (f'\<^emph>a)))"
"val_Zp (f'\<^emph>(ns n)) = val_Zp (f'\<^emph>a)"
proof-

  show "val_Zp (a \<ominus> (ns n)) \<succeq>\<^bsub>G\<^esub> (Some 1) \<oplus>\<^bsub>G\<^esub> val_Zp (f'\<^emph>a)"
  proof(induction n)
    case 0
    then show ?case 
      by (metis G_ord(1) Zp_is_cring a_closed cring_def newton_seq.simps(1) ring.r_right_minus_eq val_Zp_def)
  next
    case (Suc n)
    fix n
    assume IH: "val_Zp (a \<ominus> (ns n)) \<succeq>\<^bsub>G\<^esub> (Some 1) \<oplus>\<^bsub>G\<^esub> val_Zp (f'\<^emph>a)"
    show "val_Zp (a \<ominus> (ns (Suc n))) \<succeq>\<^bsub>G\<^esub> (Some 1) \<oplus>\<^bsub>G\<^esub> val_Zp (f'\<^emph>a)"
    proof-
      have I0: "val_Zp ((ns (Suc n)) \<ominus> (ns n)) \<succeq>\<^bsub>G\<^esub> (Some 1) \<oplus>\<^bsub>G\<^esub> val_Zp (f'\<^emph>a)"
      proof(cases "(ns (Suc n)) = (ns n)")
        case True
        then show ?thesis 
          by (metis G_ord(1) Zp_is_cring cring_def newton_seq_simp0 ring.r_right_minus_eq val_Zp_def)
      next
        case False
        have "(ns (Suc n)) \<ominus> (ns n) = \<ominus>divide (f\<^emph>(ns n)) (f'\<^emph>(ns n))"
          using newton_step_def[of "ns n"]
          by (smt Zp_is_cring a_minus_def continuous_is_closed cring.cring_simprules(10)
              cring.cring_simprules(3) cring_def divide_id'(1) f'_closed f'a_nonzero' f_closed 
              fa_nonzero hensel_factor_id hensel_hypothesis_weakened is_closed_fun_simp mult_zero(1) 
              newton_seq.simps(1) newton_seq.simps(2) newton_seq_simp0 newton_seq_simp1 newton_seq_simp3 
              not_nonzero_Zp option.simps(1) polynomial_is_continuous ring.ring_simprules(18) val_Zp_mult 
              val_ord_Zp)
        then have 0: "ord_Zp((ns (Suc n)) \<ominus> (ns n)) = ord_Zp (divide (f\<^emph>(ns n)) (f'\<^emph>(ns n)))"
          by (smt Zp_is_cring Zp_minus_ominus continuous_is_closed cring.cring_simprules(21) 
              divide_id'(1) f'_closed f'a_nonzero f_closed fa_nonzero hensel_factor_id
              hensel_hypothesis_weakened is_closed_fun_simp mult_zero(1) newton_seq.simps(1) 
              newton_seq_simp0 newton_seq_simp1 newton_seq_simp3 not_nonzero_Zp option.simps(1) 
              ord_Zp_dist_sym polynomial_is_continuous val_Zp_mult val_ord_Zp)
        have 1: "(f\<^emph>(ns n)) \<in> nonzero Z\<^sub>p"
          by (metis (no_types, lifting) "0" False Zp_is_cring continuous_is_closed 
              cring.cring_simprules(4) cring_def divide_def f_closed is_closed_fun_simp
              newton_seq_simp0 ord_of_nonzero(2) ord_pos polynomial_is_continuous 
              ring.r_right_minus_eq)
        have 2: "f'\<^emph>(ns n) \<in> nonzero Z\<^sub>p"
          by (smt continuous_is_closed divide_id'(1) f'_closed f'a_nonzero fa_closed 
              fa_nonzero hensel_factor_id hensel_hypothesis_weakened is_closed_fun_simp 
              mult_zero(1) newton_seq.simps(1) newton_seq_simp0 newton_seq_simp1 
              newton_seq_simp3 not_nonzero_Zp option.simps(1) polynomial_is_continuous 
              val_Zp_mult val_ord_Zp)
        
        have "ord_Zp (f\<^emph>(ns n))  \<ge> ord_Zp (f'\<^emph>(ns n))"
          using Zp_nonzero_def(2) \<open>f \<^emph> ns n \<in> nonzero Z\<^sub>p\<close> newton_seq_simp4 by blast
        then have 3:"ord_Zp((ns (Suc n)) \<ominus> (ns n)) = ord_Zp (f\<^emph>(ns n)) - ord_Zp (f'\<^emph>(ns n))"
          using 0 1 2 divide_id(3)[of "f\<^emph>(ns n)" "f'\<^emph>(ns n)"] 
          by metis 
        have  "val_Zp (f \<^emph> ns n) \<succeq>\<^bsub>G\<^esub> Some ((2 * ord_Zp f'a) + 2 ^ n * t)"
          using newton_seq_simp2[of n] by metis  
        then have 4: "ord_Zp (f \<^emph> ns n) \<ge>((2 * ord_Zp f'a) + 2 ^ n * t)"
          using 1 
          by (metis G_ord(2)  Zp_nonzero_def(2) ord_Zp_def val_Zp_def)
        then have 5: "ord_Zp((ns (Suc n)) \<ominus> (ns n)) \<ge> ((2 * ord_Zp f'a) + 2 ^ n * t) - ord_Zp (f'\<^emph>(ns n))"
        proof-
          have  "ord_Zp (f \<^emph> ns n) - ord_Zp (f'\<^emph>(ns n))\<ge>((2 * ord_Zp f'a) + 2 ^ n * t) - ord_Zp (f'\<^emph>(ns n))"
            using 4  
            by linarith
          then show ?thesis using 0 3 
            by linarith
        qed
        have 6: "((ns (Suc n)) \<ominus> (ns n)) \<in> nonzero Z\<^sub>p"
          using False Zp_not_eq_diff_nonzero newton_seq_simp0 by blast
        then have "ord_Zp((ns (Suc n)) \<ominus> (ns n)) \<ge> ((2 * ord_Zp f'a) + 2 ^ n * t) - ord_Zp (f'a)"
          using 5 newton_seq_simp1 
          by (metis "2" Zp_nonzero_def(1) Zp_nonzero_def(2) f'a_closed 
              f'a_nonzero option.simps(1) val_ord_Zp)
        then have "ord_Zp((ns (Suc n)) \<ominus> (ns n)) \<ge> (ord_Zp f'a) + 2 ^ n * t"
          by presburger 
        then have "ord_Zp((ns (Suc n)) \<ominus> (ns n)) \<ge> (ord_Zp f'a) + 1"
          using t_pos 
          by (smt mult_less_cancel_right2 zero_less_power)
        then have "val_Zp((ns (Suc n)) \<ominus> (ns n)) \<succeq>\<^bsub>G\<^esub> *(ord_Zp f'a) + 1*"
          by (metis "6" G_ord(2) Zp_nonzero_def(1) Zp_nonzero_def(2) val_ord_Zp)
        then show ?thesis 
          by (smt G_mult(3) a_closed f'_vals_closed f'a_nonzero val_ord_Zp)
      qed
      have I1: "val_Zp ((ns n) \<ominus> (ns (Suc n))) \<succeq>\<^bsub>G\<^esub> (Some 1) \<oplus>\<^bsub>G\<^esub> val_Zp (f'\<^emph>a)"
        using I0 
        by (metis (no_types, lifting) Zp_is_cring cring.cring_simprules(4) 
            cring_def newton_seq_simp0 ord_Zp_dist_sym ring.r_right_minus_eq val_ord_Zp)
      show ?thesis 
      proof(cases  "(ns (Suc n)) = (ns n)")
        case True
        then show ?thesis 
          using IH by metis 
      next
        case False
        then  have F0: "((ns (Suc n)) \<ominus> (ns n)) \<in> nonzero Z\<^sub>p"
          using Zp_not_eq_diff_nonzero newton_seq_simp0 by blast
        have F1: " (a \<ominus> (ns n)) \<oplus> ((ns n) \<ominus> (ns (Suc n))) = (a \<ominus> (ns (Suc n)))"
          by (metis (no_types, lifting) Zp_diff_simp Zp_is_cring a_closed 
              cring.cring_simprules(10) cring.cring_simprules(4) newton_seq_simp0)
        then have "val_Zp (a \<ominus> (ns (Suc n))) \<succeq>\<^bsub>G\<^esub> Min\<^bsub>G\<^esub> (val_Zp (a \<ominus> (ns n))) (val_Zp ((ns n) \<ominus> (ns (Suc n))))"
          by (metis Zp_is_cring a_closed cring.cring_simprules(4) 
              newton_seq_simp0 val_Zp_ultrametric)
        then show ?thesis 
          by (smt G_ord_trans I1 IH)
      qed
    qed
  qed
  show "val_Zp (f'\<^emph>(ns n)) = val_Zp (f'\<^emph>a)"
    using newton_seq_simp1 by blast
  show "\<exists>N.\<forall>n. n> N \<longrightarrow> (val_Zp (a \<ominus> (ns n)) = val_Zp (divide (f\<^emph>a) (f'\<^emph>a)))"
  proof-
    have P: "\<And>m. m > 1 \<Longrightarrow> (val_Zp (a \<ominus> (ns m)) = val_Zp (divide (f\<^emph>a) (f'\<^emph>a)))"
    proof-
      fix n::nat
      assume AA: "n >1"
      show " (val_Zp (a \<ominus> (ns n)) = val_Zp (divide (f\<^emph>a) (f'\<^emph>a)))" 
      proof(cases "(ns 1) = a")
        case True
        have T0: "\<And>k. \<forall>n. n \<le> k \<longrightarrow>  ns n = a"
        proof-
          fix k
          show " \<forall>n. n \<le> k \<longrightarrow>  ns n = a"
          proof(induction k)
            case 0
            then show ?case 
              by simp 
          next
            case (Suc k)
            fix k
            assume IH: " \<forall>n\<le>k. ns n = a "
            show "\<forall>n\<le>Suc k. ns n = a "
              apply auto 
            proof-
              fix n
              assume A: "n \<le>Suc k"
              show "ns n = a"
              proof(cases "n < Suc k")
                case True
                then show ?thesis using IH by auto 
              next
                case False
                then have A0: "n = Suc k"
                  using A nat_less_le by blast
                have "ns  (Suc k) = ns k \<ominus> (divide (f\<^emph>(ns k)) (f'\<^emph>(ns k)))"
                  using newton_step_def[of "ns k"]
                  by auto 
                then have A1: "ns  (Suc k) = a \<ominus> (divide (f\<^emph>a) (f'\<^emph>a))"
                  by (simp add: IH)
                have A2: "(divide (f\<^emph>a) (f'\<^emph>a)) = \<zero>"
                proof-
                  have "ns 1 = a"
                    using True by auto 
                  then have "a = a \<ominus> divide fa f'a"
                    using newton_step_def 
                    by simp
                  then show "divide fa f'a = \<zero>"
                    by (metis (no_types, lifting) Zp_int_inc_zero Zp_int_mult_closed Zp_is_cring
                    Zp_one_car a_closed a_minus_def add_zero(1) cring.cring_simprules(3) 
                    cring_def divide_id'(1) f'a_nonzero' fa_closed newton_seq.simps(1)  
                    newton_seq_simp3 ring.ring_simprules(18))
                qed
                then show "ns  n = a"
                  using A1 A0  True newton_step_def 
                  by auto
              qed
            qed
          qed
        qed
        show "val_Zp (a \<ominus> ns n) = val_Zp (local.divide fa f'a)"
        proof-
          have "ns n = a"
            using T0 by blast 
          then have T00:"val_Zp (a \<ominus> ns n) = \<infinity>\<^bsub>G\<^esub>"
            by (metis Zp_is_cring a_closed cring_def ring.r_right_minus_eq val_Zp_def)
          have "val_Zp(local.divide fa f'a) = \<infinity>\<^bsub>G\<^esub>"
          proof-
            have "(local.divide fa f'a) = \<zero>"
            proof-
              have "ns 1 = a"
                using True by auto
              then have "a = a \<ominus> (local.divide fa f'a)"
                by  (simp add: newton_step_def)
              then show ?thesis 
                by (metis (no_types, lifting) Zp_int_inc_zero Zp_int_mult_closed Zp_is_cring Zp_one_car
                \<open>ns n = a\<close> a_closed a_minus_def add_zero(1) cring.cring_simprules(3) 
                cring_def divide_id'(1) f'a_nonzero' fa_closed newton_seq_simp3 
                ring.ring_simprules(18))
            qed
            then show ?thesis 
              using T00 
              by (simp add: val_Zp_def)
          qed
          then show ?thesis using T00 
            by (simp add: val_Zp_def)
        qed
      next
        show "ns 1 \<noteq> a \<Longrightarrow> val_Zp (a \<ominus> ns n) = val_Zp (local.divide fa f'a)"
        proof-   
          have F0: "(1::nat) \<le> n"
        using AA by simp 
        assume F1: " ns 1 \<noteq> a "
        show "val_Zp (a \<ominus> ns n) = val_Zp (local.divide fa f'a)"
        proof-
          have "fa \<noteq> \<zero>"
          proof
            assume C: "fa = \<zero>"
            then have "divide fa f'a = \<zero>"
              by simp
            then have "a = a \<ominus>divide fa f'a"
              using C fa_nonzero by blast
            then have "ns 1 = a "
              using C fa_nonzero by blast
            then show False 
              using F1 by blast
          qed
          have "\<And>k. val_Zp (a \<ominus> ns (Suc k)) = val_Zp (local.divide fa f'a)"
          proof-
            fix k
            show " val_Zp (a \<ominus> ns (Suc k)) = val_Zp (local.divide fa f'a)"
            proof(induction k)
              case 0
              have "(a \<ominus> ns (Suc 0)) = (local.divide fa f'a)"
              proof-
                have 00:"ns (Suc 0) = a \<ominus> (local.divide fa f'a)"
                  using newton_step_def 
                  by simp
                have 01: "(divide fa f'a) \<in> carrier Z\<^sub>p"
                  by (metis Zp_nonzero_def(2) divide_id(1) f'a_nonzero'
                      fa_nonzero' newton_seq.simps(1) newton_seq_simp4 ord_Zp_def)
                show ?thesis using 01 00 
                  by (metis (no_types, lifting) Zp_is_cring Zp_minus_ominus a_closed 
                      a_minus_def cring.cring_simprules(10) cring.cring_simprules(21) 
                      cring.cring_simprules(3) cring_def ring.ring_simprules(18))
              qed
              then show " val_Zp (a \<ominus> ns (Suc 0)) = val_Zp (local.divide fa f'a)" 
                by presburger
            next
              case (Suc k)
              fix k
              assume IH: " val_Zp (a \<ominus> ns (Suc k)) = val_Zp (local.divide fa f'a)"
              show " val_Zp (a \<ominus> ns (Suc (Suc k))) = val_Zp (local.divide fa f'a)"
              proof-
                have I0: "ns (Suc (Suc k)) = ns (Suc k) \<ominus> (divide (f\<^emph>(ns (Suc k))) (f'\<^emph>(ns (Suc k))))"
                  by (simp add: newton_step_def)
                have I1: "val_Zp (f\<^emph>(ns (Suc k))) \<succeq>\<^bsub>G\<^esub> val_Zp(f'\<^emph>(ns (Suc k)))"
                  using newton_seq_simp3 by blast
                have I2: "(divide (f\<^emph>(ns (Suc k))) (f'\<^emph>(ns (Suc k)))) \<in> carrier Z\<^sub>p"
                  by (metis G_EOAG I1 continuous_is_closed divide_id'(1) 
                      extended_ordered_abelian_group.infinity_distinct f'_closed f'a_nonzero' 
                      f_closed is_closed_fun_simp newton_seq_simp0 newton_seq_simp1
                      not_nonzero_Zp polynomial_is_continuous val_Zp_closed val_Zp_def)
                have I3: "ns (Suc (Suc k)) \<ominus> ns (Suc k) = \<ominus>(divide (f\<^emph>(ns (Suc k))) (f'\<^emph>(ns (Suc k))))"
                  using I0 I2 
                  by (metis Zp_is_cring a_minus_def cring.cring_simprules(10) 
                      cring.cring_simprules(3) cring_def newton_seq_simp0 ring.ring_simprules(18))
                then have "val_Zp (ns (Suc (Suc k)) \<ominus> ns (Suc k)) = val_Zp (divide (f\<^emph>(ns (Suc k))) (f'\<^emph>(ns (Suc k))))"
                  by (metis I2 Zp_is_cring Zp_minus_ominus cring.cring_simprules(21) cring_def 
                      newton_seq_simp0 ord_Zp_def ord_Zp_dist_sym ring.r_right_minus_eq val_Zp_def)
                then have "val_Zp (ns (Suc (Suc k)) \<ominus> ns (Suc k)) = (val_Zp (f\<^emph>(ns (Suc k))) \<ominus>\<^bsub>G\<^esub> val_Zp (f'\<^emph>(ns (Suc k))))"
                  by (metis G_EOAG I1 continuous_is_closed divide_id'(3) 
                      extended_ordered_abelian_group.infinity_distinct f'_closed f'a_nonzero'
                      f_closed is_closed_fun_simp newton_seq_simp0 newton_seq_simp1 
                      not_nonzero_Zp polynomial_is_continuous val_Zp_closed val_Zp_def)
                then have I4: "val_Zp (ns (Suc (Suc k)) \<ominus> ns (Suc k)) = val_Zp (f\<^emph>(ns (Suc k))) \<ominus>\<^bsub>G\<^esub> val_Zp (f'a)"
                  using newton_seq_simp1 by presburger
                show ?thesis 
                proof(cases "(ns (Suc (Suc k)) = ns (Suc k))")
                  case True
                  then show ?thesis using IH 
                    by presburger
                next
                  case False
                  then have F0: "(ns (Suc (Suc k)) \<ominus> ns (Suc k)) \<noteq>\<zero>"
                    by (meson Zp_is_cring cring_def newton_seq_simp0 ring.r_right_minus_eq)
                  have F1: "(f\<^emph>(ns (Suc k))) \<noteq>\<zero>"
                    by (metis (mono_tags, hide_lams) F0 G_EOAG I2 Zp_is_cring 
                        \<open>ns (Suc (Suc k)) \<ominus> ns (Suc k) = \<ominus> local.divide (f \<^emph> ns (Suc k)) (f' \<^emph> ns (Suc k))\<close> 
                        \<open>val_Zp (ns (Suc (Suc k)) \<ominus> ns (Suc k)) = val_Zp (local.divide (f \<^emph> ns (Suc k)) (f' \<^emph> ns (Suc k)))\<close>
                        cring.cring_simprules(3) divide_def extended_ordered_abelian_group.infinity_distinct
                         not_nonzero_Zp val_Zp_closed val_Zp_def)
                  have F2: "ord_Zp (ns (Suc (Suc k)) \<ominus> ns (Suc k)) = ord_Zp (f\<^emph>(ns (Suc k))) - ord_Zp (f'a)"
                  proof-
                    have F20: "val_Zp (f\<^emph>(ns (Suc k))) \<ominus>\<^bsub>G\<^esub> val_Zp (f'a) = *ord_Zp (f\<^emph>(ns (Suc k))) - ord_Zp (f'a)*"
                      using F1 gminus_minus ord_Zp_def val_Zp_def by auto
                    have F21: "val_Zp (ns (Suc (Suc k)) \<ominus> ns (Suc k)) = *ord_Zp (ns (Suc (Suc k)) \<ominus> ns (Suc k))*"
                      using F0 ord_Zp_def val_Zp_def by auto
                    show ?thesis using F20 F21 I4 
                      by (simp add: ord_Zp_def)
                  qed
                  have F3: "ord_Zp (a \<ominus> ( ns (Suc k))) = ord_Zp (local.divide fa f'a)"
                  proof-
                    have F30:"val_Zp (local.divide fa f'a) = * ord_Zp (local.divide fa f'a)*"
                      by (metis UP_domain_def Z\<^sub>p_x_is_UP_domain divide_id'(1) domain.integral_iff 
                          f'a_closed f'a_nonzero' fa_closed fa_nonzero hensel_factor_id 
                          newton_seq.simps(1) newton_seq_simp3 val_ord_Zp)
                    then have F31: "val_Zp (a \<ominus> ( ns (Suc k))) = *ord_Zp (a \<ominus> ( ns (Suc k)))*"
                    proof-
                      have "val_Zp (a \<ominus> ( ns (Suc k))) \<noteq> \<infinity>\<^bsub>G\<^esub>"
                        using F30 IH 
                        by (metis (mono_tags, hide_lams) False G_mult(1) G_mult(2) 
                            add.right_neutral eq_iff_diff_eq_0 gminus_minus gplus_plus  
                            of_nat_eq_0_iff option.simps(1) ord_Zp_def)
                        then show ?thesis 
                          using ord_Zp_def val_Zp_def 
                          by auto
                    qed
                    show ?thesis using F31 F30 
                      by (metis IH option.simps(1))
                  qed
                  have F4: "a \<ominus>  ns (Suc (Suc k)) = (a \<ominus> ( ns (Suc k))) \<oplus> (ns  (Suc k)) \<ominus> ns (Suc (Suc k))"
                    by (metis (no_types, lifting) Zp_is_cring a_closed a_minus_def 
                        cring.cring_simprules(1) cring.cring_simprules(10) cring.cring_simprules(3)
                        cring_def newton_seq_simp0 ring.ring_simprules(18))
                  have F5: "ord_Zp ((ns  (Suc k)) \<ominus> ns (Suc (Suc k))) > ord_Zp (a \<ominus> ( ns (Suc k)))"
                  proof-
                    have F50:  "ord_Zp ((ns  (Suc k)) \<ominus> ns (Suc (Suc k))) = ord_Zp (f\<^emph>(ns (Suc k))) - ord_Zp (f'a)"
                      by (metis F2 newton_seq_simp0 ord_Zp_dist_sym)
                    have F51: "ord_Zp (f\<^emph>(ns (Suc k))) > ord_Zp (fa)"
                    proof-
                      have F510: "ord_Zp (f\<^emph>(ns (Suc k))) \<ge>  (2*(ord_Zp f'a)) + (2^(Suc k))*t "
                        by (metis F1 G_ord(2)  newton_seq_simp2 ord_Zp_def val_Zp_def)
                      have "ord_Zp (f\<^emph>(ns (Suc k))) \<ge>  (2*(ord_Zp f'a)) + 2*t "
                      proof-
                        have "((2::int)^(Suc k)) = ((2::int)^k)*(2::int)"
                          by simp 
                        then have "((2::int)^(Suc k)) \<ge>(2::int)"
                          by simp
                        then have "( ((2::int)^(Suc k))*t) \<ge> (2::int)*t"
                          using t_pos by auto
                        then show ?thesis 
                          using F510 by linarith
                      qed
                      then have "ord_Zp (f\<^emph>(ns (Suc k))) \<ge>  (2*(ord_Zp f'a)) + 2*(ord_Zp fa - 2 * ord_Zp f'a) "
                        using hensel_factor_def  
                        by (simp add: ord_Zp_def)
                      then have "ord_Zp (f\<^emph>(ns (Suc k))) \<ge>  (ord_Zp fa) + (ord_Zp fa - 2 * ord_Zp f'a) "
                        by presburger 
                      then show ?thesis 
                        using hensel_hypothesis 
                        by linarith
                    qed
                    have F52: "ord_Zp ((ns  (Suc k)) \<ominus> ns (Suc (Suc k))) > ord_Zp (fa) - ord_Zp (f'a)"
                      using F50 F51 by linarith
                    have F53: "ord_Zp ((ns  (Suc k)) \<ominus> ns (Suc (Suc k))) > ord_Zp (divide (fa) (f'a))"
                    proof-
                      have "ord_Zp(divide (fa) (f'a)) = ord_Zp (fa) - ord_Zp (f'a)"
                        using divide_id(3) dual_order.strict_implies_order f'a_nonzero' fa_nonzero' hensel_hypothesis_weakened by blast
                      then show ?thesis using F52 
                        by (simp add: ord_Zp_def)
                    qed
                    then show ?thesis 
                      using F3 by linarith
                  qed
                  have F6: "ord_Zp (a \<ominus> ns (Suc (Suc k))) = ord_Zp (local.divide fa f'a)"
                    using F5 F4 F3 F2 
                      equal_ord'[of "(a \<ominus> ( ns (Suc k)))" " (a \<ominus> ( ns (Suc k))) " 
                                  "(ns  (Suc k)) \<ominus> ns (Suc (Suc k))"] 
                    by (smt UP_domain_def Z\<^sub>p_x_is_UP_domain Zp_diff_simp Zp_is_cring 
                        cring.cring_simprules(10) cring.cring_simprules(4) divide_id'(1) 
                        domain.integral_iff f'a_closed f'a_nonzero' fa_closed hensel_factor_id
                        hensel_hypothesis_weakened newton_seq.simps(1) newton_seq_simp0 
                        newton_seq_simp3 ord_of_nonzero(2) ord_pos)
                  then show ?thesis 
                    by (smt F5 UP_domain_def Z\<^sub>p_x_is_UP_domain Zp_is_cring cring.cring_simprules(4)
                        cring_def divide_id'(1) domain.integral_iff f'a_closed f'a_nonzero'
                        fa_closed fa_nonzero hensel_factor_id newton_seq.simps(1) newton_seq_simp0
                        newton_seq_simp3 ord_Zp_dist_sym ring.r_right_minus_eq val_ord_Zp)
                qed
              qed
            qed
          qed
          then show ?thesis 
            by (metis F0 One_nat_def Suc_le_D)
        qed
      qed
      qed
    qed
    have "\<forall>n>1. val_Zp (a \<ominus> ns n) = val_Zp (local.divide fa f'a)"
    proof
      fix n
      show "1 < n \<longrightarrow> val_Zp (a \<ominus> ns n) = val_Zp (local.divide fa f'a) "
        using P 
        by blast
    qed
    then show ?thesis by blast 
  qed
qed

lemma hensel_seq_pushforward:
 "res_lim ((fun_of f)\<^sub>*ns) = \<zero>"
proof-
  have A: "is_cauchy ((fun_of f)\<^sub>*ns)"
    using f_closed is_continuous_def newton_seq_is_cauchy polynomial_is_continuous_induct by blast
  have "converges_to ((fun_of f)\<^sub>*ns) \<zero>"
    apply(rule converges_toI)
    using A is_cauchy_def apply blast
     apply (simp add: cring.cring_simprules(2))
  proof-
    fix n
    show " \<exists>N. \<forall>k>N. (((fun_of f)\<^sub>*ns) k) n = \<zero> n"
    proof-
      have 0: "\<And>k. (k::nat)>3 \<longrightarrow>  val_Zp (f\<^emph>(ns k)) \<succeq>\<^bsub>G\<^esub> *k + 1*"
      proof
        fix k::nat
        assume A: "k >3"
        show "val_Zp (f\<^emph>(ns k)) \<succeq>\<^bsub>G\<^esub> *k + 1*"
        proof-
          have 0: " val_Zp (f\<^emph>(ns k)) \<succeq>\<^bsub>G\<^esub> * (2*(ord_Zp f'a)) + (2^k)*t *"
            using newton_seq_simp2 by blast   
          have 1: " * (2*(ord_Zp f'a)) + (2^k)*t * \<succeq>\<^bsub>G\<^esub>  *k + 1*"
          proof-
            have " (2*(ord_Zp f'a)) + (2^k)*t \<ge> (2^k) "
              by (smt f'a_closed f'a_nonzero mult.commute mult_less_cancel_right2 ord_pos t_pos zero_le_power)
            then have  " (2*(ord_Zp f'a)) + (2^k)*t \<ge> (of_nat k)+1"
              using A  of_nat_1 of_nat_add of_nat_less_two_power 
              by smt
            then show ?thesis 
              by (metis G_ord(2) of_nat_1 of_nat_add)
          qed
          show ?thesis using 0 1 
            using G_ord_trans by blast
        qed
      qed
      have 1: "\<And>k. (k::nat)>3 \<longrightarrow>  (f\<^emph>(ns k)) k = 0"
      proof
        fix k::nat
        assume B: "3<k"
        show " (f\<^emph>(ns k)) k = 0"
        proof-
          have B0: " val_Zp (f\<^emph>(ns k)) \<succeq>\<^bsub>G\<^esub> *k + 1*"
            using 0 B 
            by blast
          then show ?thesis 
          proof(cases "f\<^emph>(ns k) = \<zero>")
            case True
            then show ?thesis 
              by (simp add: zero_vals)
          next
            case False
            then have "ord_Zp (f\<^emph>(ns k)) \<ge> k+ 1"
              using B0  
              by (metis G_ord(2) ord_Zp_def val_Zp_def)
            then have "ord_Zp (f\<^emph>(ns k)) \<ge> k"
              by linarith 
            then show ?thesis 
              using zero_below_ord[of "(f\<^emph>(ns k))" k] continuous_is_closed f_closed 
                is_closed_fun_simp newton_seq_simp0 polynomial_is_continuous 
              by blast
          qed
        qed
      qed
      have "\<forall>k>(max 3 n). (((fun_of f)\<^sub>*ns) k) n = \<zero> n"
        apply auto
      proof-
        fix k::nat
        assume A: "3< k"
        assume A': "n < k"
        have A0: "(f\<^emph>(ns k)) k = 0"
          using 1[of k] A by auto 
        then have "(f\<^emph>(ns k)) n = 0"
          using A A'
          by (smt above_ord_nonzero continuous_is_closed f_closed is_closed_fun_simp 
              less_imp_of_nat_less max.strict_boundedE newton_seq_simp0 polynomial_is_continuous 
              zero_below_ord zero_vals)
        then show A1:  " (((fun_of f)\<^sub>*ns) k) n = \<zero> n"
          by (simp add: push_forward_def zero_vals)
      qed
      then show ?thesis by blast 
    qed
  qed
  then show ?thesis 
    by (metis converges_to_def unique_limit') 
qed

lemma full_hensels_lemma:
  obtains \<alpha> where
       "f\<^emph>\<alpha> = \<zero>" and 
       "val_Zp (a \<ominus> \<alpha>) \<succeq>\<^bsub>G\<^esub> (Some 1) \<oplus>\<^bsub>G\<^esub> val_Zp (f'\<^emph>a)"
       "(val_Zp (a \<ominus> \<alpha>) = val_Zp (divide (f\<^emph>a) (f'\<^emph>a)))"
       "val_Zp (f'\<^emph>\<alpha>) = val_Zp (f'\<^emph>a)"
proof(cases "\<exists>k. f\<^emph>(ns k) =\<zero>")
case True
  obtain k where k_def: "f\<^emph>(ns k) =\<zero>"
    using True by blast
  obtain N where N_def: "\<forall>n. n> N \<longrightarrow> (val_Zp (a \<ominus> (ns n)) = val_Zp (divide (f\<^emph>a) (f'\<^emph>a)))"
    using pre_full_hensel(2) by blast
  have Z: "\<And>n. n \<ge>k \<Longrightarrow> f\<^emph>(ns n) =\<zero>"
  proof-
    fix n
    assume A: "n \<ge>k"
    obtain l where l_def:"n = k + l"
      using A le_Suc_ex 
      by blast
    have "\<And>m. f\<^emph>(ns (k+m)) =\<zero>"
    proof-
      fix m
      show "f\<^emph>(ns (k+m)) =\<zero>"
        apply(induction m)
         apply (simp add: k_def)
        using  eventually_zero 
        by simp
    qed
    then show "f\<^emph>(ns n) =\<zero>"
      by (simp add: l_def)
  qed
  obtain M where M_def: "M = N + k"
    by simp 
  then have M_root: "f\<^emph>(ns M) =\<zero>"
    by (simp add: Z)
  obtain \<alpha> where alpha_def: "\<alpha>= ns M"
    by simp 
  have T0: "f\<^emph>\<alpha> = \<zero>"
    using alpha_def M_root 
    by auto
  have T1:    "val_Zp (a \<ominus> \<alpha>) \<succeq>\<^bsub>G\<^esub> (Some 1) \<oplus>\<^bsub>G\<^esub> val_Zp (f'\<^emph>a)"
    using alpha_def pre_full_hensel(1) by blast
  have T2: "(val_Zp (a \<ominus> \<alpha>) = val_Zp (divide (f\<^emph>a) (f'\<^emph>a)))"
    by (metis M_def N_def alpha_def fa_nonzero k_def 
        less_add_same_cancel1 newton_seq.elims zero_less_Suc)
  have T3:  "val_Zp (f'\<^emph>\<alpha>) = val_Zp (f'\<^emph>a)"
    using alpha_def newton_seq_simp1 by blast
  show ?thesis using T0 T1 T2 T3 
    using that by blast
next 
  case False
  then have Nz: "\<And>k. f\<^emph>(ns k) \<noteq>\<zero>"
    by blast
  have ns_cauchy: "is_cauchy ns"
    by (simp add: newton_seq_is_cauchy)
  have fns_cauchy: "is_cauchy ((fun_of f)\<^sub>*ns)"
    using f_closed is_continuous_def ns_cauchy polynomial_is_continuous by blast
  have F0: "res_lim ((fun_of f)\<^sub>*ns) = \<zero>"
  proof-
    show ?thesis 
      using hensel_seq_pushforward by auto 
  qed
  obtain \<alpha> where alpha_def: "\<alpha> = res_lim ns"
    by simp
  have F1: "(f\<^emph>\<alpha>)= \<zero>"
    using F0 alpha_def alt_seq_limit
      ns_cauchy polynomial_is_continuous res_lim_pushforward 
      res_lim_pushforward' by auto
  have F2: "val_Zp (a \<ominus> \<alpha>) \<succeq>\<^bsub>G\<^esub> Some 1 \<oplus>\<^bsub>G\<^esub> val_Zp f'a \<and>  val_Zp (a \<ominus> \<alpha>) = val_Zp (local.divide fa f'a)"
  proof-
    have F20: "val_Zp (a \<ominus> \<alpha>) \<noteq> \<infinity>\<^bsub>G\<^esub>"
      by (metis F1 G_EOAG Zp_not_eq_diff_nonzero a_closed alpha_def 
          extended_ordered_abelian_group.infinity_distinct fa_nonzero ns_cauchy 
          res_lim_in_Zp val_Zp_closed) 
    have "converges_to ns \<alpha>"
      by (simp add: alpha_def is_cauchy_imp_has_limit ns_cauchy)
    then obtain N where "(\<forall>m>N. ns m = \<alpha> \<or> (1+ (max (2 + ord_Zp f'a) (ord_Zp (\<alpha> \<ominus> a)))) \<le> ord_Zp_dist (ns m) \<alpha>)"
      using converges_to_def[of ns \<alpha>]  
      by blast
    obtain N' where N'_def: "\<forall>n>N'. val_Zp (a \<ominus> ns n) = val_Zp (local.divide fa f'a)"
      using pre_full_hensel(2) by blast 
    obtain K where K_def: "K = Suc (max N N')"
      by simp 
    then have F21: " ns K= \<alpha> \<or> (1+ (max (2 + ord_Zp f'a) (ord_Zp (\<alpha> \<ominus> a)))) \<le> ord_Zp_dist (ns K) \<alpha>"
      by (metis Suc_le_eq Suc_n_not_le_n
          \<open>\<forall>m>N. ns m = \<alpha> \<or> 1 + max (2 + ord_Zp f'a) (ord_Zp_dist \<alpha> a) \<le> ord_Zp_dist (ns m) \<alpha>\<close>
          linorder_not_less max_def)
    have F22: "a \<noteq> ns K"
    proof
      assume C: "a = ns K"
      then have C0: "(ord_Zp (\<alpha> \<ominus> a)) = ord_Zp_dist (ns K) \<alpha>"
        by (metis \<open>converges_to ns \<alpha>\<close> a_closed converges_to_def ord_Zp_dist_sym)
      have C1: "(ord_Zp (\<alpha> \<ominus> a)) \<noteq> ord_Zp_dist (ns K) \<alpha>"
      proof(cases "ns K = \<alpha> ")
        case True
        then show ?thesis 
          using C F1 fa_nonzero by metis 
      next
        case False
        then show ?thesis using F21 
          by linarith 
      qed
      show False using C0 C1 by metis  
    qed
    show ?thesis
    proof(cases "ns K = \<alpha>")
      case True
      then show ?thesis 
        using pre_full_hensel F1 False by blast
    next
      case False
      assume "ns K \<noteq> \<alpha>"
      show ?thesis
      proof-
        have P0: " (a \<ominus> \<alpha>) \<in> nonzero Z\<^sub>p"
          by (metis (mono_tags, hide_lams) F1 Zp_not_eq_diff_nonzero 
              \<open>converges_to ns \<alpha>\<close> a_closed converges_to_def fa_nonzero)
        have P1: "(\<alpha> \<ominus> (ns K)) \<in> nonzero Z\<^sub>p"
          using False Zp_not_eq_diff_nonzero \<open>converges_to ns \<alpha>\<close> 
            converges_to_def newton_seq_simp0
          by (metis (mono_tags, hide_lams))
        have P2: "a \<ominus> (ns K) \<in> nonzero Z\<^sub>p"
          using F22 Zp_not_eq_diff_nonzero 
                a_closed newton_seq_simp0 
          by blast
        have P3: "(a \<ominus> \<alpha>) = a \<ominus> (ns K) \<oplus> ((ns K) \<ominus> \<alpha>)"
          by (metis (no_types, hide_lams) Zp_diff_simp Zp_is_cring 
              \<open>converges_to ns \<alpha>\<close> a_closed converges_to_def cring.cring_simprules(10) 
              cring.cring_simprules(4) newton_seq_simp0)
        have P4: "ord_Zp (a \<ominus> \<alpha>) \<ge> min (ord_Zp (a \<ominus> (ns K))) (ord_Zp ((ns K) \<ominus> \<alpha>))"
          by (metis (full_types) False P0 P2 P3 Zp_not_eq_diff_nonzero \<open>converges_to ns \<alpha>\<close> 
              converges_to_def newton_seq_simp0 ord_Zp_def ord_Zp_ultrametric)
        have P5: "ord_Zp (a \<ominus> (ns K)) \<ge> (1 + ord_Zp f'a)"
          using pre_full_hensel(1)[of "K"] 
          by (metis G_mult(3) G_ord(2)  P2 Zp_nonzero_def(1) 
              Zp_nonzero_def(2) f'a_closed f'a_nonzero val_ord_Zp)
        have P6: "ord_Zp ((ns K) \<ominus> \<alpha>) \<ge> (1 + ord_Zp f'a)"
          using F21 False by linarith
        have P7: "ord_Zp (a \<ominus> \<alpha>) \<ge>  (1 + ord_Zp f'a)"
          using P4 P5 P6
          by linarith
        have P8:  "ord_Zp (a \<ominus> \<alpha>) = ord_Zp (local.divide fa f'a)"
        proof-
          have " 1 + max (2 + ord_Zp f'a) (ord_Zp_dist \<alpha> a) \<le> ord_Zp_dist (ns K) \<alpha>"
            using False F21  by blast 
          then have " ord_Zp_dist (ns K) \<alpha> >   max (2 + ord_Zp f'a) (ord_Zp_dist \<alpha> a)"
            by linarith
          then have "ord_Zp(\<alpha> \<ominus> (ns K)) >   max (2 + ord_Zp f'a) (ord_Zp_dist \<alpha> a)"
            by (metis \<open>converges_to ns \<alpha>\<close> converges_to_def newton_seq_simp0 ord_Zp_dist_sym)   
          then have "ord_Zp(\<alpha> \<ominus> (ns K)) > ord_Zp (a \<ominus> \<alpha>) "
            by (metis \<open>converges_to ns \<alpha>\<close> a_closed converges_to_def max_less_iff_conj ord_Zp_dist_sym)
          then have "ord_Zp (a \<ominus> \<alpha>) = ord_Zp (a \<ominus> (ns K))"
            by (metis (full_types) P0 P2 Zp_diff_simp Zp_minus_ominus a_closed a_minus_def 
                alpha_def equal_ord newton_seq_simp0 ns_cauchy ord_Zp_def 
                res_lim_in_Zp)
          then show ?thesis 
            by (smt F22 K_def N'_def P2 Suc_le_eq UP_domain_def Z\<^sub>p_x_is_UP_domain G_ord(2)
                Zp_is_cring Zp_nonzero_def(1) cring_def divide_id'(1) domain.integral_iff
                f'a_nonzero' fa_closed fa_nonzero hensel_factor_id less_imp_le_nat 
                linorder_not_less max_def newton_seq.simps(1) newton_seq_simp0 newton_seq_simp3 
                option.simps(1) ring.r_right_minus_eq val_ord_Zp)
        qed
        have P9: "val_Zp (a \<ominus> \<alpha>) = val_Zp (local.divide fa f'a)"
          by (metis F20 P0 P8 UP_domain_def Z\<^sub>p_x_is_UP_domain Zp_nonzero_def(1) 
              divide_id'(1) domain.integral_iff f'a_nonzero' fa_closed fa_nonzero 
              hensel_factor_id newton_seq.simps(1) newton_seq_simp3 val_Zp_def val_ord_Zp)
        have P10: "val_Zp (a \<ominus> \<alpha>) \<succeq>\<^bsub>G\<^esub> Some 1 \<oplus>\<^bsub>G\<^esub> val_Zp f'a"
          using P8 
          by (metis (full_types) P9 lessI pre_full_hensel(1) pre_full_hensel(2))
        show ?thesis using P9 P10 by blast 
      qed          
    qed
  qed
  have F3: "val_Zp (f' \<^emph> \<alpha>) = val_Zp f'a"
  proof-
    have F31: " (f' \<^emph> \<alpha>) = res_lim ((fun_of f') \<^sub>* ns)"
      using alpha_def alt_seq_limit ns_cauchy polynomial_is_continuous res_lim_pushforward res_lim_pushforward' by auto
    obtain N where N_def: "f'\<^emph>\<alpha> = f'\<^emph>(ns N)\<or> ord_Zp (f'\<^emph>\<alpha> \<ominus> f'\<^emph>(ns N)) > ord_Zp (f'a)"
       using cauchy_approaches_in_ord[of "((fun_of f') \<^sub>* ns)" "(f' \<^emph> \<alpha>)"] 
       by (metis F31 f'_closed is_continuous_def less_Suc_eq 
           ns_cauchy ord_Zp_def polynomial_is_continuous push_forward_def that)
     show ?thesis
     proof(cases "f'\<^emph>\<alpha> = f'\<^emph>(ns N)")
       case True
       then show ?thesis 
         using newton_seq_simp1 by presburger
     next
       case False
       then have 0: "ord_Zp (f'\<^emph>\<alpha> \<ominus> f'\<^emph>(ns N)) > ord_Zp (f'a)"
         using N_def by blast 
       have 1: "ord_Zp (f'\<^emph>(ns N)) = ord_Zp f'a"
         by (smt continuous_is_closed divide_id'(1) f'_closed f'a_nonzero' fa_closed fa_nonzero
             hensel_factor_id hensel_hypothesis_weakened is_closed_fun_simp mult_zero(1) 
             newton_seq.simps(1) newton_seq_simp0 newton_seq_simp1 newton_seq_simp3 
             option.simps(1) polynomial_is_continuous val_Zp_mult val_ord_Zp)
       have 2:  "ord_Zp (f' \<^emph> \<alpha>) = ord_Zp f'a"
         by (smt "1" N_def Zp_is_cring Zp_minus_ominus a_minus_def add_zero(1) alpha_def 
             continuous_is_closed cring_def equal_ord f'_closed f'a_closed f'a_nonzero' 
             is_closed_fun_simp newton_seq_simp0 ns_cauchy ord_Zp_dist_sym ord_of_nonzero(2)
             ord_pos polynomial_is_continuous res_lim_in_Zp ring.r_right_minus_eq) 
       then show ?thesis 
         by (metis F0 f'a_closed f'a_nonzero fns_cauchy ord_Zp_def
             ord_of_nonzero(1) ord_pos res_lim_in_Zp val_Zp_def)
     qed
  qed
  show ?thesis 
    using F1 F2 F3 that 
    by blast
qed

end


end

