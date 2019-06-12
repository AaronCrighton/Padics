theory padic_field_topology
imports full_hensel
begin
type_synonym padic_number = "((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set"

(*Section of the inclusion map Z\<^sub>p \<Rightarrow> Q\<^sub>p*)
definition(in padic_integers) to_Zp where 
"to_Zp a = (if (a \<in> \<O>\<^sub>p) then (SOME x. x \<in> carrier Z\<^sub>p \<and> \<iota> x = a) else \<zero>)"

lemma(in padic_integers) to_Zp_inc: 
  assumes "a \<in> \<O>\<^sub>p"
  shows "\<iota> (to_Zp a) = a"
proof-
  obtain c where c_def: "c = (SOME x. x \<in> carrier Z\<^sub>p \<and> \<iota> x = a)"
    by simp
  have "(\<exists> x. x \<in> carrier Z\<^sub>p \<and> \<iota> x = a)"
    using assms(1) 
    by blast
  then  have "c \<in> carrier Z\<^sub>p \<and> \<iota> c = a"
    using c_def 
    by (metis (mono_tags, lifting)  tfl_some)
  then show "\<iota> (to_Zp a) = a" 
    using to_Zp_def c_def assms(1) 
    by auto 
qed

lemma(in padic_integers) inc_to_Zp: 
 assumes "b \<in> carrier Z\<^sub>p"
 shows "to_Zp (\<iota> b) = b"
proof-
  have "\<iota> (to_Zp (\<iota> b)) = (\<iota> b)"
    using assms to_Zp_inc[of "\<iota> b"]
    by blast
  then show ?thesis using domain.inc_inj2[of Z\<^sub>p "to_Zp (\<iota> b)" b] \<iota>_def 
    by (metis (mono_tags, lifting) Zp_is_domain Zp_nat_inc_closed 
        Zp_nat_mult_zero assms tfl_some to_Zp_def)
qed

(**************************************************************************************************)
(**************************************************************************************************)
(*******************************Angular Component Maps into ***************************************)
(*******************************       Residue Rings        ***************************************)
(**************************************************************************************************)
(**************************************************************************************************)

definition(in padic_integers) ac :: "nat \<Rightarrow> padic_number \<Rightarrow> int" where
"ac n x = (if x = \<zero>\<^bsub>Q\<^sub>p\<^esub> then 0 else (angular_component x) n)"

lemma(in padic_integers) ac_in_res_ring:
  assumes "x \<in> nonzero Q\<^sub>p"
  shows "ac n x \<in> carrier (R n)"
  unfolding ac_def 
  using assms angular_component_closed[of x] 
  unfolding nonzero_def
  by (metis Qp_nonzero_def(2) Z\<^sub>p_def assms padic_set_simp0 partial_object.select_convs(1))

lemma(in padic_integers) ac_in_res_ring'[simp]:
  assumes "x \<in> carrier Q\<^sub>p"
  shows "ac n x \<in> carrier (R n)"
  apply(cases "x \<in> nonzero Q\<^sub>p")
  using ac_in_res_ring apply blast
  by (metis R_cring R_residues Res_0 ac_def assms cring.cring_simprules(2) 
      insert_iff neq0_conv not_nonzero_Qp residues.res_zero_eq)

lemma(in padic_integers) ac_mult':
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"
  shows "ac n (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = (ac n x) \<otimes>\<^bsub>R n\<^esub> (ac n y)"
  unfolding ac_def 
proof-
  have 0: "angular_component (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = angular_component x \<otimes> angular_component y"
    using assms angular_component_mult[of x y]
    by auto 
  show "(if x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y = \<zero>\<^bsub>Q\<^sub>p\<^esub> then 0 else angular_component (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) n) =
    (if x = \<zero>\<^bsub>Q\<^sub>p\<^esub> then 0 else angular_component x n) \<otimes>\<^bsub>R n\<^esub> (if y = \<zero>\<^bsub>Q\<^sub>p\<^esub> then 0 else angular_component y n)"
    using assms angular_component_closed[of x] angular_component_closed[of y]
          padic_mult_simp[of p "angular_component x" "angular_component y" n] 
    by (smt "0" Localization.submonoid.m_closed Qp_is_domain Qp_nonzero_def(2)
        Z\<^sub>p_def domain.nonzero_is_submonoid monoid.simps(1)) 
qed

lemma(in padic_integers) ac_mult:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "y \<in> carrier Q\<^sub>p"
  shows "ac n (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = (ac n x) \<otimes>\<^bsub>R n\<^esub> (ac n y)"
proof(cases "x \<in> nonzero Q\<^sub>p \<and> y \<in> nonzero Q\<^sub>p")
  case True

  then show ?thesis 
    by (simp add: True ac_mult')
next
  case False
  then have "(x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = \<zero>\<^bsub>Q\<^sub>p\<^esub>"
    by (metis Qp_is_domain assms(1) assms(2) domain.integral_iff not_nonzero_Qp)
  have "(ac n x) = 0 \<or> (ac n y) = 0"
    using False ac_def 
    by (meson assms(1) assms(2) not_nonzero_Qp)
  then  have 0: "(ac n x) = \<zero>\<^bsub>R n\<^esub> \<or> (ac n y) = \<zero>\<^bsub>R n\<^esub>"
    by (simp add: residue_ring_def)
  have 1: "(ac n x) \<in> carrier (R n) \<and> (ac n y) \<in> carrier (R n)"
    using assms ac_in_res_ring' by blast
  have "(ac n x) \<otimes>\<^bsub>R n\<^esub> (ac n y) = 0"   
    apply(cases "ac n x = 0")
     apply (simp add: residue_ring_def)
      by (metis "1" R_residues Res_0' \<open>ac n x = 0 \<or> ac n y = 0\<close> cring.cring_simprules(27) 
        neq0_conv  padic_integers.R_cring padic_integers_axioms residues.res_zero_eq)
    then show ?thesis 
      by (simp add: \<open>x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y = \<zero>\<^bsub>Q\<^sub>p\<^esub>\<close> ac_def)
qed

lemma(in padic_integers) ac_one[simp]:
  assumes "n \<ge> 1"
  shows "ac n \<one>\<^bsub>Q\<^sub>p\<^esub> = 1"
proof-
  have "ac n \<one>\<^bsub>Q\<^sub>p\<^esub> = \<one> n"
    unfolding ac_def
    using angular_component_one Qp_one_notzero
    by auto
  then show ?thesis 
    using padic_one_simp[of n] assms 
    by (simp add: Z\<^sub>p_def padic_one_def)
qed

lemma(in padic_integers) ac_one':
  assumes "n > 0"
  shows "ac n \<one>\<^bsub>Q\<^sub>p\<^esub> = \<one>\<^bsub>R n\<^esub>"
  using assms residue_ring_def 
  by auto

lemma(in padic_integers) ac_units:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "n > 0"
  shows "ac n x \<in> Units (R n)"
proof-
  obtain y where y_def: "y = inv\<^bsub>Q\<^sub>p\<^esub> x"
    by simp 
  have y_nz: "y \<in> nonzero Q\<^sub>p"
    by (metis Qp_Units_nonzero Qp_is_domain assms(1) domain.Units_inverse y_def)
  have 0: "ac n (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = (ac n x) \<otimes>\<^bsub>R n\<^esub> (ac n y)"
    using ac_mult' assms(1) y_nz by blast
  have 1: "x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y = \<one>\<^bsub>Q\<^sub>p\<^esub>" 
    by (metis Qp_is_field Qp_nonzero_def(1) Qp_nonzero_def(2) assms(1) field.field_inv(2) y_def)
  have 2: "(ac n x) \<otimes>\<^bsub>R n\<^esub> (ac n y) = \<one>\<^bsub>R n\<^esub>"
    using "0" "1" ac_one' assms(2) 
    by auto
  show ?thesis 
    by (metis (no_types, lifting) "1" Q\<^sub>p_def Qp_is_domain Qp_nonzero_def(1) 
        Qp_one_notzero Z\<^sub>p_def ac_def angular_component_unit assms(1)
        assms(2) domain.integral_iff gr0_conv_Suc padic_integers.angular_component_closed
        padic_integers.ord_Zp0_imp_unit0 padic_integers_axioms unit_imp_ord_Zp0 y_nz)
qed

lemma(in padic_integers) ac_inv:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "n > 0"
  shows "ac n (inv\<^bsub>Q\<^sub>p\<^esub> x) = inv\<^bsub>R n\<^esub> (ac n x)"
proof-
  have "x \<otimes>\<^bsub>Q\<^sub>p\<^esub> inv\<^bsub>Q\<^sub>p\<^esub> x = \<one>\<^bsub>Q\<^sub>p\<^esub>"
    by (simp add: Qp_Units_nonzero assms(1))
  then have "ac n (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> inv\<^bsub>Q\<^sub>p\<^esub> x) = \<one>\<^bsub>R n\<^esub>"
    by (simp add: \<open>(x \<div> x) = \<one>\<^bsub>Q\<^sub>p\<^esub>\<close> ac_one' assms(2))
  then have "ac n x \<otimes>\<^bsub>R n\<^esub> ac n (inv\<^bsub>Q\<^sub>p\<^esub> x) = \<one>\<^bsub>R n\<^esub>"
    by (metis Qp_nonzero_def(1) Qp_nonzero_def(2) ac_mult assms(1) inv_in_frac(3))
  then show ?thesis 
    by (metis Qp_Units_nonzero R_cring Units_inverse_Qp ac_in_res_ring
        assms(1) assms(2) comm_monoid.comm_inv_char cring_def)
qed

lemma(in padic_integers) ac_inv':
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "n > 0"
  shows "ac n (inv\<^bsub>Q\<^sub>p\<^esub> x) \<otimes>\<^bsub>R n\<^esub> (ac n x) = \<one>\<^bsub>R n\<^esub>"
  using ac_inv[of x n] ac_units[of x n] assms 
  by (smt R_cring Units_def comm_monoid.comm_inv_char cring_def mem_Collect_eq)

lemma(in padic_integers) ac_inv'':
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "n > 0"
  shows " (ac n x) \<otimes>\<^bsub>R n\<^esub> ac n (inv\<^bsub>Q\<^sub>p\<^esub> x)= \<one>\<^bsub>R n\<^esub>"
  by (metis Qp_nonzero_def(1) Qp_nonzero_def(2) ac_in_res_ring 
      ac_inv' assms(1) assms(2) cring.cring_simprules(14)
      inv_in_frac(3) padic_integers.R_cring padic_integers_axioms)

lemma(in padic_integers) ac_inv''':
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "n > 0"
  shows "(ac n x) \<otimes>\<^bsub>R n\<^esub> ac n (inv\<^bsub>Q\<^sub>p\<^esub> x)= 1"
        "ac n (inv\<^bsub>Q\<^sub>p\<^esub> x) \<otimes>\<^bsub>R n\<^esub> (ac n x) = 1"
  using R_residues ac_inv'' assms(1) assms(2) residues.res_one_eq 
  apply auto[1]
    using R_residues ac_inv' assms(1) assms(2) residues.res_one_eq
    by auto

lemma (in padic_integers) ac_val:
  assumes  "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> nonzero Q\<^sub>p"
  assumes "val a = val b"
  assumes "val (a \<ominus>\<^bsub>Q\<^sub>p\<^esub>b) \<succeq>\<^bsub>G\<^esub> val a \<oplus>\<^bsub>G\<^esub> *int n*"
  shows "ac n a = ac n b"
proof-
  obtain m where m_def: "m = ord a"
    by simp 
  have 0: "a = (\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>m) \<otimes>\<^bsub>Q\<^sub>p\<^esub> \<iota> (angular_component a)"
    by (simp add: angular_component_factors_x assms(1) m_def)
  have 1: "b = (\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>m) \<otimes>\<^bsub>Q\<^sub>p\<^esub> \<iota> (angular_component b)"
  proof-
    have "ord b = ord a"
      by (metis assms(1) assms(2) assms(3) option.inject val_ord)
    then show ?thesis 
      by (metis angular_component_factors_x assms(2) m_def)
  qed    
  have 2: "(a \<ominus>\<^bsub>Q\<^sub>p\<^esub>b) = (\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>m) \<otimes>\<^bsub>Q\<^sub>p\<^esub> \<iota> (angular_component a)
                      \<ominus>\<^bsub>Q\<^sub>p\<^esub>(\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>m) \<otimes>\<^bsub>Q\<^sub>p\<^esub> \<iota> (angular_component b)"
    using "0" "1" by auto
  have 3: "(a \<ominus>\<^bsub>Q\<^sub>p\<^esub>b) = (\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>m) \<otimes>\<^bsub>Q\<^sub>p\<^esub>( \<iota> (angular_component a)
                                     \<ominus>\<^bsub>Q\<^sub>p\<^esub> \<iota> (angular_component b))"
    using 2 assms 
    by (metis Qp_is_domain Z\<^sub>p_def Zp_one_nonzero \<iota>_def a_minus_def angular_component_closed 
        cring.cring_simprules(25) cring.cring_simprules(29) cring.cring_simprules(3) 
        domain.axioms(1) frac_closed p_intpow_closed(1) padic_integers.inc_def 
        padic_integers_axioms)
  have 4: "(a \<ominus>\<^bsub>Q\<^sub>p\<^esub>b) = (\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>m) \<otimes>\<^bsub>Q\<^sub>p\<^esub>( \<iota> ((angular_component a)
                                          \<ominus>(angular_component b)))"
    by (simp add: "3" assms(1) assms(2) inc_of_diff)
  have 5: "val (a \<ominus>\<^bsub>Q\<^sub>p\<^esub>b) = *m* \<oplus>\<^bsub>G\<^esub> val (( \<iota> ((angular_component a)
                                          \<ominus>(angular_component b))))"
    by (metis "4" Z\<^sub>p_def Zp_one_nonzero angular_component_closed assms(1) assms(2)
        cring.cring_simprules(4) frac_closed local.inc_def ord_p_pow_int p_intpow_closed(1)
        p_intpow_closed(2) Zp_is_domain domain_def padic_integers_axioms val_mult val_ord)
  have 6: "*m* = val a"
    using Q\<^sub>p_def assms(1) m_def by auto
  have 7: "*m* \<oplus>\<^bsub>G\<^esub> val (\<iota> (angular_component a \<ominus> angular_component b)) \<succeq>\<^bsub>G\<^esub> val a \<oplus>\<^bsub>G\<^esub> Some (int n)"
    using "5" assms(4) by presburger
  have 8: "*m* \<oplus>\<^bsub>G\<^esub> val (\<iota> (angular_component a \<ominus> angular_component b)) \<succeq>\<^bsub>G\<^esub> *m* \<oplus>\<^bsub>G\<^esub> Some (int n)"
    using "6" "7" by presburger
  have 9: "val (\<iota> (angular_component a \<ominus> angular_component b)) \<succeq>\<^bsub>G\<^esub> Some (int n)"
    using assms 8 gord_add_cancel''''[of "*int n*" "*m*"  "val ( \<iota> ((angular_component a)\<ominus>(angular_component b)))" ]
    by (metis G_mult(1) G_ord(1) G_ord(2) add_le_cancel_left gord_add_cancel''' 
        gplus_plus of_nat_le_0_iff option.inject rel_simps(93))
  have 10: "val_Zp (angular_component a \<ominus> angular_component b) \<succeq>\<^bsub>G\<^esub> Some (int n)"
    using 9 
    by (metis Z\<^sub>p_def angular_component_closed assms(1) assms(2) cring.cring_simprules(4)
        Zp_is_domain domain_def padic_integers_axioms val_of_inc)
  have 11: "(angular_component a \<ominus> angular_component b) n = \<zero>\<^bsub>R n\<^esub>"
    by (metis "9" G_ord(2) Z\<^sub>p_def angular_component_closed assms(1) assms(2) 
        cring.cring_simprules(4) ord_Zp_def Zp_is_domain domain_def padic_integers_axioms
        residue_ring_def ring.simps(1) val_Zp_def val_of_inc zero_below_ord zero_vals)
  have 12: "(angular_component a n) \<ominus>\<^bsub>R n\<^esub> (angular_component b n) = \<zero>\<^bsub>R n\<^esub>"
    using 11 unfolding a_minus_def 
    using padic_add_def[of p "angular_component a" "angular_component b"] Z\<^sub>p_def
          Q\<^sub>p_def assms(2) padic_add_def padic_integers.angular_component_closed
          padic_integers_axioms padic_inv prime by auto
  have 13: "(angular_component a n) = (angular_component b n)"
    using 12 
    by (smt Z\<^sub>p_def a_minus_def angular_component_closed angular_component_unit assms(1) assms(2)
        cring.cring_simprules(17) cring.cring_simprules(3) cring_def of_nat_0_less_iff
        padic_integers.R_cring padic_integers_axioms padic_set_simp0 partial_object.select_convs(1) 
        ring.ring_simprules(15) ring.ring_simprules(22) unit_imp_ord_Zp0 zero_below_ord)
  then show ?thesis 
    by (simp add: Qp_nonzero_def(2) ac_def assms(1) assms(2))
qed

(**************************************************************************************************)
(**************************************************************************************************)
(*******************************The Multiplicative Subgroups***************************************)
(*******************************          Qnm of Qp         ***************************************)
(**************************************************************************************************)
(**************************************************************************************************)


definition(in padic_integers) Q :: "nat \<Rightarrow> nat \<Rightarrow> padic_number set" where 
"Q n m = {x \<in> nonzero Q\<^sub>p. (ac n x = 1) \<and> (ord x) mod m = 0}"

lemma(in padic_integers) QnmI:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "ac n x = 1"
  assumes "(ord x) mod m = 0"
  shows "x \<in> Q n m"
  unfolding Q_def using assms by blast 

lemma(in padic_integers) QnmE:
  assumes "x \<in> Q n m"
  shows "ac n x = 1"
       "(ord x) mod m = 0"
  using Q_def assms apply blast
  using Q_def assms by blast

lemma(in padic_integers) Qnm_nonzero:
"Q n m \<subseteq> nonzero Q\<^sub>p"
  using Q_def[of n m]  
  by blast

lemma(in padic_integers) Qnm_nonzero'[simp]:
  assumes "a \<in> Q n m"
  shows "a \<in> nonzero Q\<^sub>p"
  using Qnm_nonzero assms by blast

lemma(in padic_integers) Qnm_closed_mult:
  assumes  "n \<noteq>0"
  assumes "m \<noteq>0"
  assumes "x \<in> Q n m"
  assumes "y \<in> Q n m"
  shows "x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y \<in> Q n m"
proof(rule QnmI)
  show "x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y \<in> nonzero Q\<^sub>p" 
    using assms 
    by (meson Localization.submonoid.m_closed Qnm_nonzero 
        Qp_is_domain domain.nonzero_is_submonoid subsetCE)
  show "ac n (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = 1"
  proof- 
    have "ac n (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = ac n x \<otimes>\<^bsub>R n\<^esub> ac n y"
      using ac_mult Qnm_nonzero' assms 
      by (meson ac_mult')
    then have "ac n (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = \<one>\<^bsub>R n\<^esub> \<otimes>\<^bsub>R n\<^esub> \<one>\<^bsub>R n\<^esub>"
      by (smt Q_def R_residues assms  mem_Collect_eq neq0_conv residues.res_one_eq)
    then show ?thesis 
      by (metis Qp_one_nonzero R_cring R_residues ac_in_res_ring ac_one'
          assms(1) cring.cring_simprules(12) neq0_conv residues.res_one_eq)
  qed
  show "ord (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) mod int m = 0" 
  proof-
    have "ord (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) mod int m = ((ord x) + (ord y)) mod int m"
      using ord_mult[of x y] assms 
      by (metis Qnm_nonzero')
    then have "ord (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) mod int m = ((ord x) mod (int m) + (ord y) mod int m) mod int m"
      by presburger
    then show ?thesis
      using assms QnmE(2)[of x n m] QnmE(2)[of y n m] 
      by auto 
  qed
qed

lemma(in padic_integers) Qnm_closed_inv:
  assumes "n \<noteq> 0"
  assumes "m \<noteq> 0"
  assumes "x \<in> Q n m"
  shows "inv\<^bsub>Q\<^sub>p\<^esub> x \<in> Q n m"
proof(rule QnmI)
  show "inv\<^bsub>Q\<^sub>p\<^esub> x \<in> nonzero Q\<^sub>p"
    using Qnm_nonzero Qp_nonzero_def(1) Qp_nonzero_def(2) assms(3) inv_in_frac(3) by blast
  show "ac n (inv\<^bsub>Q\<^sub>p\<^esub> x) = 1"
    using assms ac_inv[of x] QnmE[of x n m]
    by (metis Q\<^sub>p_def Qnm_nonzero' Qp_one_nonzero Z\<^sub>p_def Zp_one_car
        Zp_one_nonzero ac_inv ac_inv' ac_one' frac_inv inc_of_one
        local.inc_def neq0_conv padic_integers.ac_inv'''(2) padic_integers_axioms)
  show "ord (inv\<^bsub>Q\<^sub>p\<^esub> x) mod int m = 0"
    using ord_of_inv[of x] assms 
    by (metis QnmE(2) Qnm_nonzero' Qp_nonzero_def(1) Qp_nonzero_def(2) zmod_zminus1_not_zero)
qed

lemma(in padic_integers) Qnm_one:
  assumes "n \<noteq> 0"
  assumes "m \<noteq> 0"
  shows "\<one>\<^bsub>Q\<^sub>p\<^esub> \<in> Q n m"
  by (smt Q\<^sub>p_def QnmI Qp_is_comm_monoid Qp_is_domain Qp_one_car Qp_one_notzero Z\<^sub>p_def ac_mult
      assms(1) assms(2) comm_monoid.comm_inv_char cring.cring_simprules(12) domain.axioms(1)
      inv_in_frac(3) mod_pos_pos_trivial neq0_conv of_nat_le_0_iff ord_one 
      padic_integers.ac_inv'''(2) padic_integers_axioms)

(**************************************************************************************************)
(**************************************************************************************************)
(*******************************p-adic Cells in One Dimension***************************************)
(**************************************************************************************************)
(**************************************************************************************************)

abbreviation (in padic_integers)
 m_trans:: "padic_number set \<Rightarrow> padic_number \<Rightarrow> padic_number set" where
"m_trans S a \<equiv> {x \<in> carrier Q\<^sub>p. (inv\<^bsub>Q\<^sub>p\<^esub> a \<otimes>\<^bsub>Q\<^sub>p\<^esub> x) \<in> S}"

abbreviation (in padic_integers)
 a_trans:: "padic_number set \<Rightarrow> padic_number \<Rightarrow> padic_number set" where
"a_trans S a \<equiv> {x \<in> carrier Q\<^sub>p. (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> a) \<in> S}"

abbreviation (in padic_integers) aff_trans:: 
              "padic_number set \<Rightarrow> padic_number \<Rightarrow> padic_number \<Rightarrow> padic_number set" where
"aff_trans S a b \<equiv>  {x \<in> carrier Q\<^sub>p. (inv\<^bsub>Q\<^sub>p\<^esub> b)\<otimes>\<^bsub>Q\<^sub>p\<^esub> (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> a) \<in> S}"

definition (in padic_integers) interval ("I[_ _]") where
"interval \<alpha> \<beta> = {a \<in> carrier Q\<^sub>p. \<beta> \<preceq>\<^bsub>G\<^esub> val a \<and> val a \<preceq>\<^bsub>G\<^esub> \<alpha>}"

abbreviation (in padic_integers) basic_one_cell_at_zero where
"basic_one_cell_at_zero n m \<alpha> \<beta> \<equiv> I[\<alpha> \<beta>] \<inter> (Q n m)"

abbreviation (in padic_integers) one_cell_at_zero where
"one_cell_at_zero n m \<alpha> \<beta> a \<equiv> m_trans (basic_one_cell_at_zero n m \<alpha> \<beta>) a"

definition (in padic_integers) one_cell ("C\<^sub>1") where
"one_cell n m \<alpha> \<beta> a c = (a_trans (one_cell_at_zero n m \<alpha> \<beta> a) c)"

definition( in padic_integers) affine_shift where
"affine_shift a b x \<equiv> (a \<otimes>\<^bsub>Q\<^sub>p\<^esub> x) \<oplus>\<^bsub>Q\<^sub>p\<^esub> b"

lemma (in padic_integers) affine_shift_cell:
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  shows "one_cell n m \<alpha> \<beta> a c = (affine_shift a c) ` (basic_one_cell_at_zero n m \<alpha> \<beta>)"
proof
  show "one_cell n m \<alpha> \<beta> a c \<subseteq> affine_shift a c ` (I[\<alpha> \<beta>] \<inter> Q n m)"
  proof
  fix x
  assume "x \<in> one_cell n m \<alpha> \<beta> a c"
  then have "x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c \<in> (one_cell_at_zero n m \<alpha> \<beta> a)"
    unfolding one_cell_def by simp 
  then have 0: "(inv\<^bsub>Q\<^sub>p\<^esub> a) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (x \<ominus>\<^bsub>Q\<^sub>p\<^esub>c) \<in> (basic_one_cell_at_zero n m \<alpha> \<beta>)"
    by blast
  have "x = (affine_shift a c) ((inv\<^bsub>Q\<^sub>p\<^esub> a) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (x \<ominus>\<^bsub>Q\<^sub>p\<^esub>c))"
  proof-
    have "(affine_shift a c) ((inv\<^bsub>Q\<^sub>p\<^esub> a) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (x \<ominus>\<^bsub>Q\<^sub>p\<^esub>c)) 
            = a \<otimes>\<^bsub>Q\<^sub>p\<^esub>  ((inv\<^bsub>Q\<^sub>p\<^esub> a) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (x \<ominus>\<^bsub>Q\<^sub>p\<^esub>c)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> c "
      unfolding affine_shift_def  by simp
    then have  "(affine_shift a c) ((inv\<^bsub>Q\<^sub>p\<^esub> a) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (x \<ominus>\<^bsub>Q\<^sub>p\<^esub>c)) 
            = (x \<ominus>\<^bsub>Q\<^sub>p\<^esub>c) \<oplus>\<^bsub>Q\<^sub>p\<^esub> c "
      using assms 
      by (metis (no_types, lifting) IntD2 Qnm_nonzero' Qp_Units_nonzero Qp_is_domain
          Qp_nonzero_def(1) Units_prop \<open>x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c \<in> m_trans (I[\<alpha> \<beta>] \<inter> Q n m) a\<close> 
          domain.Units_inverse invI(2) inv_cancelR(1) mem_Collect_eq)
    then have  "(affine_shift a c) ((inv\<^bsub>Q\<^sub>p\<^esub> a) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (x \<ominus>\<^bsub>Q\<^sub>p\<^esub>c)) 
            = (x \<oplus>\<^bsub>Q\<^sub>p\<^esub>\<ominus>\<^bsub>Q\<^sub>p\<^esub>c) \<oplus>\<^bsub>Q\<^sub>p\<^esub> c "
      using assms a_minus_def[of Q\<^sub>p x c] Qp_is_field   
      by (simp add: \<open>a \<in> nonzero Q\<^sub>p\<close>)
    then have  "(affine_shift a c) ((inv\<^bsub>Q\<^sub>p\<^esub> a) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (x \<ominus>\<^bsub>Q\<^sub>p\<^esub>c)) 
            = x \<oplus>\<^bsub>Q\<^sub>p\<^esub>(\<ominus>\<^bsub>Q\<^sub>p\<^esub>c \<oplus>\<^bsub>Q\<^sub>p\<^esub> c)"
      by (metis (no_types, lifting) Qp_is_domain \<open>x \<in> one_cell n m \<alpha> \<beta> a c\<close> assms(2) 
          cring.cring_simprules(3) cring.cring_simprules(7) domain.axioms(1)
          mem_Collect_eq one_cell_def)
    then have "(affine_shift a c) ((inv\<^bsub>Q\<^sub>p\<^esub> a) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (x \<ominus>\<^bsub>Q\<^sub>p\<^esub>c)) 
            = x \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<zero>\<^bsub>Q\<^sub>p\<^esub>"
      using assms(2) 
      by (simp add: cring.cring_simprules(9) domain.axioms(1))
    then show ?thesis using assms 
      by (metis (no_types, lifting) Qp_is_domain \<open>x \<in> one_cell n m \<alpha> \<beta> a c\<close> 
          cring.cring_simprules(16) domain.axioms(1) mem_Collect_eq one_cell_def)
  qed
  then show "x \<in> affine_shift a c ` (I[\<alpha> \<beta>] \<inter> Q n m)" using 0 
    by blast
  qed
  show "affine_shift a c ` (I[\<alpha> \<beta>] \<inter> Q n m) \<subseteq> one_cell n m \<alpha> \<beta> a c"
  proof
    fix x
    assume "x \<in> affine_shift a c ` (I[\<alpha> \<beta>] \<inter> Q n m)"
    then obtain y where y_def: "y \<in>  (I[\<alpha> \<beta>] \<inter> Q n m) \<and> affine_shift a c y = x"
      by blast 
    then have "a \<otimes>\<^bsub>Q\<^sub>p\<^esub> y \<oplus>\<^bsub>Q\<^sub>p\<^esub> c = x"
      unfolding affine_shift_def by auto
    then have "x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c = a \<otimes>\<^bsub>Q\<^sub>p\<^esub> y"
      using assms(2) cring.cring_simprules[of Q\<^sub>p]
      by (metis (no_types, lifting) IntD2 Qnm_nonzero' Qp_is_domain 
          Qp_nonzero_def(1) assms(1) domain.axioms(1) y_def)
    then have "inv\<^bsub>Q\<^sub>p\<^esub> a \<otimes>\<^bsub>Q\<^sub>p\<^esub> (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) = y"    
      using assms 
      by (metis IntD2 Qnm_nonzero' Qp_Units_nonzero Qp_is_domain Qp_nonzero_def(1) 
          cring.cring_simprules(5) domain.axioms(1) inv_cancelR(1) y_def)
    then have "x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c \<in> one_cell_at_zero n m \<alpha> \<beta> a"
      using y_def  
      by (metis (no_types, lifting) IntD2 Qnm_nonzero' Qp_is_domain Qp_nonzero_def(1)
          \<open>x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c = a \<otimes>\<^bsub>Q\<^sub>p\<^esub> y\<close> assms(1) cring.cring_simprules(5) domain.axioms(1) mem_Collect_eq)
    then show "x \<in>  one_cell n m \<alpha> \<beta> a c"
      unfolding one_cell_def 
      using Qp_is_domain \<open>x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c = a \<otimes>\<^bsub>Q\<^sub>p\<^esub> y\<close> assms(2) cring.cring_simprules(1) 
        domain.axioms(1) y_def
      unfolding affine_shift_def by fastforce
  qed
qed

lemma (in padic_integers) affine_shift_cell':
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  shows "one_cell n m \<alpha> \<beta> a c = (affine_shift a c) ` (I[\<alpha> \<beta>] \<inter> Q n m)"
  using assms affine_shift_cell 
  by blast

definition (in padic_integers) c_ball :: "int \<Rightarrow> padic_number \<Rightarrow> padic_number set" ("B\<^bsub>_\<^esub>[_]") where
"c_ball n c = {x \<in> carrier Q\<^sub>p. val (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) \<succeq>\<^bsub>G\<^esub> *n*}"

lemma (in padic_integers) c_ballI: 
  assumes "x \<in> carrier Q\<^sub>p"
  assumes " val (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) \<succeq>\<^bsub>G\<^esub> *n*"
  shows "x \<in> c_ball n c"
  using assms c_ball_def 
  by blast

lemma (in padic_integers) c_ballE: 
  assumes "x \<in> c_ball n c"
  shows "x \<in> carrier Q\<^sub>p"
        " val (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) \<succeq>\<^bsub>G\<^esub> *n*"
  using assms c_ball_def apply blast
  using assms c_ball_def by blast

lemma (in padic_integers) c_ball_in_Qp: 
  "B\<^bsub>n\<^esub>[c] \<subseteq> carrier Q\<^sub>p"
  unfolding c_ball_def 
  by blast

definition  (in padic_integers) 
q_ball :: "nat \<Rightarrow> int \<Rightarrow> int  \<Rightarrow> padic_number \<Rightarrow> padic_number set" where
"q_ball n k m c = {x \<in> carrier Q\<^sub>p. (ac n (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) = k \<and> (ord (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c)) = m) }"

lemma (in padic_integers) q_ballI[simp]: 
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "ac n (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) = k" 
  assumes "(ord (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c)) = m"
  shows "x \<in> q_ball n k m c"
  using assms q_ball_def 
  by blast

lemma (in padic_integers) q_ballE[simp]: 
  assumes "x \<in> q_ball n k m c "
  shows "x \<in> carrier Q\<^sub>p"

  using assms q_ball_def by blast 

lemma (in padic_integers) q_ballE'[simp]: 
  assumes "x \<in> q_ball n k m c "
  shows  "ac n (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) = k" 
        "(ord (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c)) = m"
  using assms q_ball_def apply blast 
  using assms q_ball_def by blast 

lemma (in padic_integers) q_ball_in_Qp[simp]: 
  "q_ball n k m c  \<subseteq> carrier Q\<^sub>p"
  unfolding q_ball_def by blast 

lemma (in padic_integers) ac_ord_prop[simp]:
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> nonzero Q\<^sub>p"
  assumes "ord a = ord b"
  assumes "ord a = n"
  assumes "ac m a = ac m b"
  assumes "m > 0"
  shows "val (a \<ominus>\<^bsub>Q\<^sub>p\<^esub>b) \<succeq>\<^bsub>G\<^esub> *int m + n* "
proof-
  have 0: "a = (\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>n) \<otimes>\<^bsub>Q\<^sub>p\<^esub> \<iota> (angular_component a)"
    using angular_component_factors_x assms(1) assms(4) by blast
  have 1: "b = (\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>n) \<otimes>\<^bsub>Q\<^sub>p\<^esub> \<iota> (angular_component b)"
    using angular_component_factors_x assms(4) assms(2) assms(3) 
    by presburger
  have 2: "a \<ominus>\<^bsub>Q\<^sub>p\<^esub>b = (\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>n) \<otimes>\<^bsub>Q\<^sub>p\<^esub> \<iota> (angular_component a) \<ominus>\<^bsub>Q\<^sub>p\<^esub>
                     (\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>n) \<otimes>\<^bsub>Q\<^sub>p\<^esub> \<iota> (angular_component b) "
    using 0 1 by auto 
  have 3: "a \<ominus>\<^bsub>Q\<^sub>p\<^esub>b = (\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>n) \<otimes>\<^bsub>Q\<^sub>p\<^esub>( \<iota> (angular_component a) \<ominus>\<^bsub>Q\<^sub>p\<^esub>  \<iota> (angular_component b))"
  proof-
    have 30: "(\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>n) \<in> carrier Q\<^sub>p"
      by simp 
    have 31: " \<iota> (angular_component a)  \<in> carrier Q\<^sub>p"
      using Zp_one_nonzero angular_component_closed assms(1) frac_closed local.inc_def 
      by presburger
    have 32: " \<iota> (angular_component b)  \<in> carrier Q\<^sub>p"
      using Zp_one_nonzero angular_component_closed assms(2) frac_closed local.inc_def 
      by presburger
    show ?thesis 
      using 2 30 31 32 ring.ring_simprules(23)[of Q\<^sub>p "(\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>n)"]
      unfolding a_minus_def 
      by (metis Qp_is_domain cring.cring_simprules(25) cring.cring_simprules(29) 
          cring.cring_simprules(3) domain.axioms(1))
  qed
  have 4: "a \<ominus>\<^bsub>Q\<^sub>p\<^esub>b = (\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>n) \<otimes>\<^bsub>Q\<^sub>p\<^esub>( \<iota> ((angular_component a) \<ominus>  (angular_component b)))"
    using 3 
    by (simp add: assms(1) assms(2) inc_of_diff)
  have 5: "val_Zp ((angular_component a) \<ominus>  (angular_component b)) \<succeq>\<^bsub>G\<^esub>  *int m* "
  proof-
    have "((angular_component a) \<ominus> (angular_component b)) m = 0"
      using assms(5)
      unfolding ac_def 
      by (metis Qp_nonzero_def(2) Z\<^sub>p_def a_minus_def angular_component_closed assms(1) assms(2) 
          cring.cring_simprules(17) padic_add_def Zp_is_domain domain_def 
          padic_integers_axioms ring.simps(2) zero_vals)
    then show ?thesis 
      by (metis G_ord(1) G_ord(2) Z\<^sub>p_def angular_component_closed assms(1) assms(2) 
          cring.cring_simprules(4) domain.axioms(1) ord_Zp_def ord_Zp_geq 
          padic_integers.Zp_is_domain padic_integers_axioms val_Zp_def)
  qed
  have 6: "val (a \<ominus>\<^bsub>Q\<^sub>p\<^esub>b) \<succeq>\<^bsub>G\<^esub> *n* \<oplus>\<^bsub>G\<^esub> val ( \<iota> (angular_component a) \<ominus>\<^bsub>Q\<^sub>p\<^esub>  \<iota> (angular_component b))"
    using 3 
    by (metis G_eq Q\<^sub>p_def Qp_is_domain Z\<^sub>p_def Zp_one_nonzero a_minus_def angular_component_closed
        assms(1) assms(2) cring.cring_simprules(1) cring.cring_simprules(3) domain.axioms(1) 
        local.inc_def ord_p_pow_int p_intpow_closed(1) p_intpow_closed(2) padic_integers.frac_closed
        padic_integers_axioms val_mult val_ord)
  have 7: "*n* \<oplus>\<^bsub>G\<^esub> val ( \<iota> (angular_component a) \<ominus>\<^bsub>Q\<^sub>p\<^esub>  \<iota> (angular_component b)) 
          = *n* \<oplus>\<^bsub>G\<^esub> val_Zp ((angular_component a) \<ominus>  (angular_component b))"
    by (metis Z\<^sub>p_def angular_component_closed assms(1) assms(2) cring.cring_simprules(4) 
        domain.axioms(1) inc_of_diff padic_integers.Zp_is_domain padic_integers_axioms val_of_inc)
  have 8: "*n* \<oplus>\<^bsub>G\<^esub> val_Zp ( (angular_component a) \<ominus>(angular_component b)) 
                \<succeq>\<^bsub>G\<^esub> *n* \<oplus>\<^bsub>G\<^esub> *int m*"
    using 5 gord_plus'[of "*int m*" "val_Zp ( (angular_component a) \<ominus>(angular_component b))" ] 
    by blast
  then have 9: "*n* \<oplus>\<^bsub>G\<^esub> val ( \<iota> (angular_component a) \<ominus>\<^bsub>Q\<^sub>p\<^esub>  \<iota> (angular_component b)) 
                \<succeq>\<^bsub>G\<^esub> *n* \<oplus>\<^bsub>G\<^esub> *int m*"
    using "7" by presburger
  then show ?thesis 
    by (metis "6" "7" "8" G_ord_trans add.commute gplus_plus)
qed

lemma (in padic_integers) c_ball_q_ball: 
  assumes "b \<in> nonzero Q\<^sub>p"
  assumes "n > 0"
  assumes "k = ac n b"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "d \<in> q_ball n k m c"
  shows "q_ball n k m c = c_ball (m + n) d"
proof
  show "q_ball n k m c \<subseteq> B\<^bsub>m + int n\<^esub>[d]"
  proof
    fix x
    assume A0: "x \<in> q_ball n k m c"
    show "x \<in> B\<^bsub>m + int n\<^esub>[d]"
    proof-
      have A1: "(ac n (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) = k \<and> (ord (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c)) = m)"
        using A0 q_ball_def 
        by blast
      have "val (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> d) \<succeq>\<^bsub>G\<^esub> *m + int n*"
      proof-
        have A2: "(ac n (d \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) = k \<and> (ord (d \<ominus>\<^bsub>Q\<^sub>p\<^esub> c)) = m)"
          using assms(5) q_ball_def 
          by blast
        have A3: "(x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) \<in> nonzero Q\<^sub>p"
        proof-
          have "k \<noteq>0"
          using A2 assms(1) assms(3) assms(5) ac_units[of b n] 
          by (smt Q\<^sub>p_def Qp_nonzero_def(1) R_cring R_residues Z\<^sub>p_def ac_in_res_ring ac_inv'
              ac_inv'' ac_inv'''(2) assms(2) cring.cring_simprules(26) inv_in_frac(3) 
              padic_integers.Qp_nonzero_def(2) padic_integers_axioms residues.res_zero_eq)
          then show ?thesis 
          by (smt A0 Qp_is_domain ac_def assms(4) cring.cring_simprules(4) domain.axioms(1)
              mem_Collect_eq not_nonzero_Qp q_ball_def)
        qed
        have A4: "(d \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) \<in> nonzero Q\<^sub>p"
        proof-
          have "k \<noteq>0"
          using A2 assms(1) assms(3) assms(5) ac_units[of b n] 
          by (smt Q\<^sub>p_def Qp_nonzero_def(1) R_cring R_residues Z\<^sub>p_def ac_in_res_ring ac_inv'
              ac_inv'' ac_inv'''(2) assms(2) cring.cring_simprules(26) inv_in_frac(3) 
              padic_integers.Qp_nonzero_def(2) padic_integers_axioms residues.res_zero_eq)
          then show ?thesis 
            by (metis (no_types, lifting) A2 Qp_is_domain ac_def assms(4) assms(5) 
                cring.cring_simprules(4) domain.axioms(1) mem_Collect_eq not_nonzero_Qp q_ball_def)
        qed
        then have " val ((x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) \<ominus>\<^bsub>Q\<^sub>p\<^esub>(d \<ominus>\<^bsub>Q\<^sub>p\<^esub> c)) \<succeq>\<^bsub>G\<^esub>  *int n + m *"
          using ac_ord_prop[of "(x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c)" "(d \<ominus>\<^bsub>Q\<^sub>p\<^esub> c)" m n ] A1 A2 assms A3 
          by linarith
        then show ?thesis 
          by (smt A0 Qp_diff_diff assms(4) assms(5) q_ballE)
      qed
      then show ?thesis 
        by (metis (no_types, lifting) A0 c_ball_def mem_Collect_eq q_ball_def)
    qed
  qed
  show "B\<^bsub>m + int n\<^esub>[d] \<subseteq> q_ball n k m c"
  proof
    fix x
    assume A: "x \<in> B\<^bsub>m + int n\<^esub>[d]"
    show "x \<in> q_ball n k m c"
    proof-
      have A0: "val (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> d) \<succeq>\<^bsub>G\<^esub> *m + int n*"
        using A c_ball_def 
        by blast
      have A1: "ord (d \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) = m"
        using assms(5) q_ball_def 
        by blast
      have A2: "ac n (d \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) = k"
        using assms(5) q_ball_def 
        by blast 
      have A3: "(d \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) \<noteq>\<zero>\<^bsub>Q\<^sub>p\<^esub>" 
        using A2 assms 
        by (smt Qp_nonzero_def(1) Qp_nonzero_def(2) R_cring R_residues ac_def
            ac_in_res_ring ac_inv'''(2) cring.cring_simprules(27) inv_in_frac(3)
            residues.res_zero_eq)
      have A4: "val (d \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) =*m*"
        by (simp add: A1 A3 val_def)
      have A5: "val (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> d) \<succ>\<^bsub>G\<^esub> val (d \<ominus>\<^bsub>Q\<^sub>p\<^esub> c)"
        by (metis A0 A4 G_ord(2) G_ord_trans add_le_same_cancel1 assms(2) 
            neq0_conv of_nat_le_0_iff zle_iff_zadd)
      have A6: "val ((x \<ominus>\<^bsub>Q\<^sub>p\<^esub> d) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (d \<ominus>\<^bsub>Q\<^sub>p\<^esub> c)) = *m*"
        using A4 A0 A5  
        by (metis (no_types, lifting) A Q\<^sub>p_def Qp_is_domain Z\<^sub>p_def assms(4) assms(5)  
            cring.cring_simprules(4) domain.axioms(1) mem_Collect_eq padic_integers.c_ball_def 
            padic_integers_axioms q_ball_def val_ultrametric_noteq)
      have A7: "val (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) = *m*"
      proof-
        have "(x \<ominus>\<^bsub>Q\<^sub>p\<^esub> d) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (d \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) = ((x \<ominus>\<^bsub>Q\<^sub>p\<^esub> d) \<oplus>\<^bsub>Q\<^sub>p\<^esub> d) \<ominus>\<^bsub>Q\<^sub>p\<^esub> c"
          by (metis (no_types, lifting) A Qp_is_domain a_minus_def assms(4) assms(5)
              c_ball_def cring.cring_simprules(3) cring.cring_simprules(4) 
              cring.cring_simprules(7) domain.axioms(1) mem_Collect_eq q_ball_def)
        have "(x \<ominus>\<^bsub>Q\<^sub>p\<^esub> d) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (d \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) = (x \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<ominus>\<^bsub>Q\<^sub>p\<^esub> d \<oplus>\<^bsub>Q\<^sub>p\<^esub> d)) \<ominus>\<^bsub>Q\<^sub>p\<^esub> c"
          by (metis (no_types, lifting) A Q\<^sub>p_def Qp_is_domain Z\<^sub>p_def
              \<open>x \<ominus>\<^bsub>Q\<^sub>p\<^esub> d \<oplus>\<^bsub>Q\<^sub>p\<^esub> (d \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) = x \<ominus>\<^bsub>Q\<^sub>p\<^esub> d \<oplus>\<^bsub>Q\<^sub>p\<^esub> d \<ominus>\<^bsub>Q\<^sub>p\<^esub> c\<close> a_minus_def 
              assms(5) cring.cring_simprules(3) cring_def domain.axioms(1)
              mem_Collect_eq padic_integers.c_ball_def padic_integers.q_ball_def
              padic_integers_axioms ring.ring_simprules(7))
        then show ?thesis 
          by (metis (no_types, lifting) A A6 Qp_is_domain assms(5) c_ball_def 
              cring.cring_simprules(16) cring.cring_simprules(9) domain.axioms(1) 
              mem_Collect_eq q_ball_def)
      qed
      have A8: "ac n (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) = ac n (d \<ominus>\<^bsub>Q\<^sub>p\<^esub> c)"
      proof-
        have A80: "(x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) \<in> nonzero Q\<^sub>p"
          by (metis (no_types, lifting) A A4 A5 A7 Q\<^sub>p_def Qp_is_domain 
              Z\<^sub>p_def assms(4) cring.cring_simprules(4) domain.axioms(1) 
              mem_Collect_eq padic_integers.c_ball_def padic_integers_axioms val_nonzero)
        have A81: "(d \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) \<in> nonzero Q\<^sub>p"
          by (metis (no_types, lifting) A3 Qp_is_domain assms(4) assms(5) 
              cring.cring_simprules(4) domain.axioms(1) mem_Collect_eq not_nonzero_Qp q_ball_def)
        have A82: "Some (m + int n) = val (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) \<oplus>\<^bsub>G\<^esub> Some (int n)"
          by (simp add: A7)
        show ?thesis 
          using A0 A4 A7 ac_val[of "(x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c)" "(d \<ominus>\<^bsub>Q\<^sub>p\<^esub> c)" n] 
          by (metis A A80 A81 A82 Qp_diff_diff assms(4) assms(5) c_ballE(1) q_ballE)
      qed
      show ?thesis using A8 A3 A7 A2 q_ball_def[of n k m c] q_ballI[of x n c k m]   
        by (smt A A4 A5 Q\<^sub>p_def Qp_is_domain Z\<^sub>p_def cring.cring_simprules(2) domain.axioms(1) 
            mem_Collect_eq option.inject padic_integers.c_ball_def padic_integers_axioms
            val_def val_nonzero val_ord)
    qed
  qed
qed

definition (in padic_integers) is_ball :: "padic_number set \<Rightarrow> bool" where
"is_ball B = (\<exists>(m::int). \<exists> c \<in> carrier Q\<^sub>p. (B = B\<^bsub>m\<^esub>[c]))" 

lemma (in padic_integers) is_ball_imp_in_Qp[simp]:
  assumes "is_ball B"
  shows "B \<subseteq> carrier Q\<^sub>p"
  unfolding is_ball_def 
  using assms c_ball_in_Qp is_ball_def 
  by auto

lemma (in padic_integers) c_ball_centers[simp]:
  assumes "is_ball B"
  assumes "B = B\<^bsub>n\<^esub>[c]"
  assumes "d \<in> B"
  assumes "c \<in> carrier Q\<^sub>p"
  shows "B = B\<^bsub>n\<^esub>[d]"
proof
  show "B \<subseteq> B\<^bsub>n\<^esub>[d]"
  proof
    fix x
    assume A0: "x \<in> B"
    have "val (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> d) \<succeq>\<^bsub>G\<^esub> *n*"
    proof-
      have A00: "val (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) \<succeq>\<^bsub>G\<^esub> *n*"
        using A0 assms(2) c_ballE(2) by blast
      have A01: "val (d \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) \<succeq>\<^bsub>G\<^esub> *n*"
        using assms(2) assms(3) c_ballE(2) by blast
      then show ?thesis 
        using Qp_isosceles[of x c d "*n*"] assms A0 A00 c_ballE(1) 
        by blast
    qed
    then show "x \<in> B\<^bsub>n\<^esub>[d]" 
      using A0 assms(1) c_ballI is_ball_imp_in_Qp 
      by blast
  qed
  show "B\<^bsub>n\<^esub>[d] \<subseteq> B"
  proof
    fix x
    assume "x \<in> B\<^bsub>n\<^esub>[d]"
    show "x \<in> B"
      using Qp_isosceles[of x d c "*n*"]
            assms 
      unfolding c_ball_def
      by (metis (no_types, lifting) Q\<^sub>p_def Qp_is_domain Qp_isosceles Z\<^sub>p_def \<open>x \<in> B\<^bsub>n\<^esub>[d]\<close> 
          a_minus_def assms(2) c_ballE(2) c_ballI cring.cring_simprules(17) domain.axioms(1) 
          padic_integers.c_ballE(1) padic_integers_axioms)
  qed
qed

lemma (in padic_integers) c_ball_center_in[simp]:
  assumes "is_ball B"
  assumes "B = B\<^bsub>n\<^esub>[c]"
  assumes "c \<in> carrier Q\<^sub>p"
  shows "c \<in> B"
  using assms  unfolding c_ball_def
  by (metis (no_types, lifting) G_ord(1) Qp_is_domain a_minus_def assms(2) 
      c_ballI cring.cring_simprules(17) domain.axioms(1) local.val_zero)

lemma (in padic_integers)dist_nonempty:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "\<exists>b \<in> carrier Q\<^sub>p. val (b \<ominus>\<^bsub>Q\<^sub>p\<^esub>a) = *n*"
proof-
  obtain b where b_def: "b = (\<pp> e n) \<oplus>\<^bsub>Q\<^sub>p\<^esub> a"
    by simp 
  have "val (b \<ominus>\<^bsub>Q\<^sub>p\<^esub>a) = *n*"
    using b_def assms 
    by (metis (no_types, lifting) Qp_is_domain a_minus_def cring.cring_simprules(16)
        cring.cring_simprules(17) cring.cring_simprules(3) cring.cring_simprules(7)
        domain.axioms(1) ord_p_pow_int p_intpow_closed(1) p_intpow_closed(2) val_ord)
  then show ?thesis 
    by (metis Qp_is_domain assms b_def cring.cring_simprules(1) domain.axioms(1) p_intpow_closed(1))
qed

lemma (in padic_integers) ball_rad_0[simp]:
  assumes "is_ball B"
  assumes "B\<^bsub>m\<^esub>[c] \<subseteq> B\<^bsub>n\<^esub>[c]"
  assumes "c \<in> carrier Q\<^sub>p"
  shows "n \<le> m"
proof-
  obtain b where b_def: "b \<in> carrier Q\<^sub>p \<and> val (b \<ominus>\<^bsub>Q\<^sub>p\<^esub>c) = *m*"
    by (meson assms(3) dist_nonempty)
  then have "b \<in> B\<^bsub>n\<^esub>[c]"
    using assms  G_eq c_ballI 
    by blast
  then have "*m* \<succeq>\<^bsub>G\<^esub> *n*"
    using G_def Q\<^sub>p_def Z\<^sub>p_def b_def padic_integers.c_ballE(2) padic_integers_axioms 
    by force
  then show ?thesis 
    by (simp add: G_ord(2))
qed

lemma (in padic_integers) ball_rad[simp]:
  assumes "is_ball B"
  assumes "B = B\<^bsub>n\<^esub>[c]"
  assumes "B = B\<^bsub>m\<^esub>[c]"
  assumes "c \<in> carrier Q\<^sub>p"
  shows "n = m"
proof-
  have 0: "n \<ge>m"
    using assms ball_rad_0 
    by (metis order_refl)
  have 1: "m \<ge>n"
    using assms ball_rad_0 
    by (metis order_refl)
  show ?thesis 
    using 0 1 
    by auto
qed

definition (in padic_integers) radius :: "padic_number set \<Rightarrow> int" ("rad") where
"radius B = (SOME n. (\<exists>c \<in> carrier Q\<^sub>p . B = B\<^bsub>n\<^esub>[c]))"

lemma (in padic_integers) radius_of_ball:
  assumes "is_ball B"
  assumes "c \<in> B"
  shows "B = B\<^bsub>rad B\<^esub>[c]"
proof-
  obtain d m where d_m_def: "d \<in> carrier Q\<^sub>p \<and>  B = B\<^bsub>m\<^esub>[d]"
    using assms(1) is_ball_def 
    by blast
  then have "B = B\<^bsub>m\<^esub>[c]"
    using assms(1) assms(2) c_ball_centers by blast
  then have "rad B = m" 
  proof-
    have "\<exists>n. (\<exists>c \<in> carrier Q\<^sub>p . B = B\<^bsub>n\<^esub>[c])"
      using d_m_def by blast 
    then have "(\<exists>c \<in> carrier Q\<^sub>p . B = B\<^bsub>rad B\<^esub>[c])"
      using radius_def[of B] 
      by (smt someI_ex)
    then show ?thesis 
      using radius_def ball_rad[of B m ]
      by (metis (mono_tags, lifting) \<open>B = B\<^bsub>m\<^esub>[c]\<close> assms(1) assms(2) c_ballE(1) c_ball_centers)
  qed
  then show ?thesis 
    using \<open>B = B\<^bsub>m\<^esub>[c]\<close> by blast
qed

lemma (in padic_integers) ball_rad'[simp]:
  assumes "is_ball B"
  assumes "B = B\<^bsub>n\<^esub>[c]"
  assumes "B = B\<^bsub>m\<^esub>[d]"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "d \<in> carrier Q\<^sub>p"
  shows "n = m"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) ball_rad c_ball_center_in c_ball_centers)

lemma (in padic_integers) nested_balls[simp]:
  assumes "is_ball B"
  assumes "B = B\<^bsub>n\<^esub>[c]"
  assumes "B' = B\<^bsub>m\<^esub>[c]"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "d \<in> carrier Q\<^sub>p"
  shows "n \<ge>m \<longleftrightarrow> B \<subseteq> B'"
proof
  show "m \<le> n \<Longrightarrow> B \<subseteq> B'" 
  proof
    assume A0: "m \<le>n"
    then have A0': "*m* \<preceq>\<^bsub>G\<^esub> *n*"
      by (simp add: G_ord(2))
    fix x
    assume A1: "x \<in> B"
    show "x \<in> B'"
      using assms c_ballI[of x m c] A0' A1 c_ballE(2)[of x n c] G_ord_trans c_ball_in_Qp 
      by blast
  qed
  show "B \<subseteq> B' \<Longrightarrow> m \<le> n"
    using assms(1) assms(2) assms(3) assms(4) ball_rad_0 
    by blast
qed

lemma (in padic_integers) nested_balls':
  assumes "is_ball B"
  assumes "is_ball B'"
  assumes "B \<inter> B' \<noteq> {}"
  shows "B \<subseteq> B' \<or> B' \<subseteq> B"
proof-
  obtain b where b_def: "b \<in> B \<inter> B'"
    using assms(3) by blast
  show "B \<subseteq> B' \<or> B' \<subseteq> B"
  proof-
    have "\<not> B \<subseteq> B' \<Longrightarrow> B' \<subseteq> B"
    proof-
      assume A: "\<not> B \<subseteq> B' "
      have 0: "B = B\<^bsub>rad B\<^esub>[b]"
        using assms(1) b_def radius_of_ball by auto
      have 1: "B' = B\<^bsub>rad B'\<^esub>[b]"
        using assms(2) b_def radius_of_ball by auto
      show "B' \<subseteq> B" using 0 1 A nested_balls 
        by (smt IntD2 Q\<^sub>p_def Z\<^sub>p_def assms(1) assms(2) b_def
            padic_integers.c_ballE(1) padic_integers_axioms)
    qed
    then show ?thesis by blast 
  qed
qed

definition (in padic_integers) is_bounded:: "padic_number set \<Rightarrow> bool" where
"is_bounded S = (\<exists>n. \<exists>c \<in> carrier Q\<^sub>p. S \<subseteq> B\<^bsub>n\<^esub>[c] )"

lemma (in padic_integers) empty_is_bounded[simp]:
"is_bounded {}"
  using is_bounded_def Qp_one_car 
  by blast

definition (in padic_integers) is_open:: "padic_number set \<Rightarrow> bool" where
"is_open U \<equiv> (U \<subseteq> carrier Q\<^sub>p) \<and> (\<forall>c \<in> U. \<exists>n. B\<^bsub>n\<^esub>[c]\<subseteq> U )"

lemma (in padic_integers) is_openI:
  assumes "U \<subseteq>carrier Q\<^sub>p"
  assumes "\<And>c. c \<in> U \<Longrightarrow> \<exists>n. B\<^bsub>n\<^esub>[c]\<subseteq> U"
  shows "is_open U"
  by (simp add: assms(1) assms(2) is_open_def)

lemma(in padic_integers) ball_is_open[simp]:
  assumes "is_ball B"
  shows "is_open B"
  by (metis (mono_tags, lifting) assms padic_integers.is_ball_imp_in_Qp
      padic_integers.is_open_def padic_integers_axioms radius_of_ball subset_iff)

lemma (in padic_integers)  is_open_imp_in_Qp[simp]:
  assumes "is_open U"
  shows "U \<subseteq> carrier Q\<^sub>p"
  using assms unfolding is_open_def 
  by linarith

lemma (in padic_integers) is_open_imp_in_Qp'[simp]:
  assumes "is_open U"
  assumes " x \<in> U"
  shows "x \<in> carrier Q\<^sub>p"
  using assms(1) assms(2) is_open_imp_in_Qp 
  by blast

definition (in padic_integers)is_max_ball_of ::"padic_number set \<Rightarrow> padic_number set  \<Rightarrow> bool" where
"is_max_ball_of U B \<equiv> (is_ball B) \<and> (B \<subseteq> U) \<and> (\<forall>B'. ((is_ball B') \<and> (B' \<subseteq> U) \<and> B \<subseteq> B') \<longrightarrow> B' \<subseteq> B)"

lemma (in padic_integers) is_max_ball_ofI:
  assumes "U \<subseteq> carrier Q\<^sub>p"
  assumes "(B\<^bsub>m\<^esub>[c]) \<subseteq> U"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "\<forall>m'. m' < m \<longrightarrow> \<not> B\<^bsub>m'\<^esub>[c] \<subseteq> U"
  shows "is_max_ball_of U (B\<^bsub>m\<^esub>[c])"
proof(rule ccontr)
  assume " \<not> is_max_ball_of U B\<^bsub>m\<^esub>[c]"
  then have "\<not> (\<forall>B'. is_ball B' \<and> B' \<subseteq> U \<and> B\<^bsub>m\<^esub>[c] \<subseteq> B'\<longrightarrow> B' \<subseteq> B\<^bsub>m\<^esub>[c])"
    using assms is_max_ball_of_def[of U "B\<^bsub>m\<^esub>[c]" ] 
    unfolding is_ball_def
    by blast
  then obtain B' where B'_def: "is_ball B' \<and> B' \<subseteq> U \<and> B\<^bsub>m\<^esub>[c] \<subseteq> B' \<and> \<not> B' \<subseteq> B\<^bsub>m\<^esub>[c]"
  by auto
  obtain n where n_def: "B' = B\<^bsub>n\<^esub>[c]" 
    by (meson B'_def assms(3) c_ball_center_in is_ball_def radius_of_ball subset_iff)
  then show False 
    using assms 
    by (smt B'_def Q\<^sub>p_def Z\<^sub>p_def padic_integers.ball_rad_0 padic_integers_axioms)
qed

lemma int_prop:
  fixes P:: "int \<Rightarrow> bool"
  assumes "P n"
  assumes "\<forall>m. m \<le>N \<longrightarrow> \<not> P m"
  shows  "\<exists>n. P n \<and> (\<forall>n'. P n'\<longrightarrow> n' \<ge>n)"
proof-
  have "n > N"
    by (meson assms(1) assms(2) not_less)
  obtain k::nat  where k_def: "k = nat (n - N)"
    by blast
  obtain l::nat where l_def: "l = (LEAST M.  P (N + int M))"
    by simp 
  have 0: " P (N + int l)"
    by (metis (full_types) LeastI \<open>N < n\<close> add_left_cancel assms(1) l_def zless_iff_Suc_zadd)
  have 1: "l > 0"
    using "0" assms(2) of_nat_0_less_iff by fastforce
  have 2: "\<And>M. M < l \<longrightarrow> \<not> P (N + M)"
    by (metis Least_le l_def less_le_trans nat_less_le)
  obtain n where n_def: "n = (N + int l)"
    by simp 
  have "P n \<and> (\<forall>n'. P n'\<longrightarrow> n' \<ge> n)"
  proof-
    have "P n"
      by (simp add: "0" n_def)
    have "(\<forall>n'. P n'\<longrightarrow> n' \<ge> n)"
    proof
      fix n'
      show "P n' \<longrightarrow> n \<le> n'"
      proof
        assume "P n'"
        show  "n \<le>n'"
        proof(rule ccontr)
          assume " \<not> n \<le> n'"
          then have C: "n' < n"
            by auto
          show "False"
          proof(cases "n' \<ge> N")
            case True
            obtain M where M_def: "nat (n' - N) = M"
              by simp 
            then have M0: "n' = N + int M "
              using True by linarith
            have M1: "M < l"
              using n_def C M0 
              by linarith
            then show ?thesis using 2 M_def M0 M1 
              using \<open>P n'\<close> by auto
          next
            case False
            then show ?thesis using assms  
              using \<open>P n'\<close> by auto
          qed
        qed
      qed
    qed
    then show ?thesis 
      using \<open>P n\<close> by blast
  qed
  then show ?thesis by blast 
qed

lemma (in padic_integers) open_max_ball:
  assumes  "is_open U"
  assumes  "U \<noteq> carrier Q\<^sub>p"
  assumes "c \<in> U"
  shows "\<exists>B. is_max_ball_of U B \<and> c \<in> B"
proof-
  obtain B where B_def: "is_ball B \<and> B \<subseteq> U \<and> c \<in> B"
    by (meson assms(1) assms(3) c_ball_center_in is_ball_def is_open_imp_in_Qp' padic_integers.is_open_def padic_integers_axioms)
  show P: "\<exists>B. is_max_ball_of U B \<and> c \<in> B"
  proof(rule ccontr)
    assume C: "\<nexists>B. is_max_ball_of U B \<and> c \<in> B"
    show False
    proof-
      have C': "\<forall>B. c \<in> B \<longrightarrow> \<not>  is_max_ball_of U B "
        using C 
        by auto
      have C'': "\<forall>N. \<exists>m <N. B\<^bsub>m\<^esub>[c] \<subseteq> U "
      proof
        fix N
        show "\<exists>m<N. B\<^bsub>m\<^esub>[c] \<subseteq> U"
        proof(rule  ccontr)
          assume A: "\<not> (\<exists>m<N. B\<^bsub>m\<^esub>[c] \<subseteq> U)"
          obtain P where P_def: "P = (\<lambda> n. \<exists>m<n. B\<^bsub>m\<^esub>[c] \<subseteq> U)"
            by simp
          have A0: "\<exists>n. P n"
            by (metis B_def P_def gt_ex radius_of_ball)
          have A1: "\<forall>m. m \<le>N \<longrightarrow> \<not> P m"
            using A P_def by auto 
          have A2: "\<exists>n. P n \<and> (\<forall>n'. P n'\<longrightarrow> n' \<ge>n)"
            using A0 A1 int_prop 
            by auto
          obtain n where n_def: " P n \<and> (\<forall>n'. P n'\<longrightarrow> n' \<ge>n)"
            using A2 by blast 
          have " B\<^bsub>n\<^esub>[c] \<subseteq> U"
            by (smt B_def P_def c_ball_def is_ball_def mem_Collect_eq n_def nested_balls order_trans)
          obtain m where m_def: "m < n \<and>B\<^bsub>m\<^esub>[c] \<subseteq> U"
            using P_def n_def by blast
          have "m = n-1"
          proof-
            have "P (m +1)"
              using P_def m_def  
              by auto
            then have "m + 1 \<ge> n"
              using n_def by blast  
            then show ?thesis using m_def by auto  
          qed
          have "\<forall>m'. m' < m \<longrightarrow> \<not> B\<^bsub>m'\<^esub>[c] \<subseteq> U"
          proof
            fix m'
            show " m' < m \<longrightarrow> \<not> B\<^bsub>m'\<^esub>[c] \<subseteq> U"
            proof
              assume "m' < m"
              show "\<not> B\<^bsub>m'\<^esub>[c] \<subseteq> U"
              proof
                assume "B\<^bsub>m'\<^esub>[c] \<subseteq> U"
                then have "P (m' + 1)"
                  using P_def by auto
                have "m'+ 1 < n"
                  using \<open>m = n - 1\<close> \<open>m' < m\<close> by linarith
                then show False 
                  using n_def \<open>P (m' + 1)\<close> by auto
              qed
            qed
          qed
          then have "is_max_ball_of U B\<^bsub>m\<^esub>[c]"
            using is_max_ball_ofI  assms(1) assms(3) is_open_imp_in_Qp is_open_imp_in_Qp' m_def 
            by presburger
          then show False 
            using C assms(1) assms(3) c_ball_center_in is_open_imp_in_Qp'
              padic_integers.is_max_ball_of_def padic_integers_axioms 
            by blast
        qed
      qed
      have "U = carrier Q\<^sub>p"
      proof
        show "carrier Q\<^sub>p \<subseteq> U"
        proof
          fix x
          assume "x \<in> carrier Q\<^sub>p"
          show "x \<in> U"
          proof(cases "x = c")
            case True
            then show ?thesis using assms by auto 
          next
            case False
            obtain m where m_def: "*m* = val(x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c)"
              using False 
              by (metis (no_types, hide_lams) Qp_diff_diff Qp_is_domain \<open>x \<in> carrier Q\<^sub>p\<close> a_minus_def
                  assms(1) assms(3) cring.cring_simprules(16) cring.cring_simprules(17)
                  cring.cring_simprules(4) domain.axioms(1) is_open_imp_in_Qp' val_def val_minus)
            obtain m' where m'_def: "m' < m \<and>  B\<^bsub>m'\<^esub>[c] \<subseteq> U "
              using C'' 
              by blast
            have "val (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) \<succeq>\<^bsub>G\<^esub> *m'*"
              by (metis G_ord(2) linorder_le_cases linorder_not_less m'_def m_def)
            then have "x \<in> B\<^bsub>m'\<^esub>[c]"
              using \<open>x \<in> carrier Q\<^sub>p\<close> c_ballI by blast
            then show "x \<in> U"
              using m'_def by blast
          qed
        qed
        show "U \<subseteq> carrier Q\<^sub>p " 
          using assms by simp 
      qed
      then show False using assms by auto 
    qed
  qed
qed

definition (in padic_integers) interior where
"interior U = {a. \<exists>B. is_open B \<and> B \<subseteq> U \<and> a \<in> B}"

lemma (in padic_integers) interior_subset:
  assumes "U \<subseteq> carrier Q\<^sub>p"
  shows "interior U \<subseteq> U"
proof
  fix x
  assume "x \<in> interior U"
  show "x \<in> U"
  proof-
    obtain B where B_def: "is_open B \<and> B \<subseteq> U \<and> x \<in> B"
      using \<open>x \<in> interior U\<close> interior_def 
      by auto
    then show "x \<in> U"
      by blast
  qed
qed

lemma (in padic_integers) interior_open:
  assumes "U \<subseteq> carrier Q\<^sub>p"
  shows "is_open (interior U)"
proof(rule is_openI)
  show "interior U \<subseteq> carrier Q\<^sub>p"
    using assms interior_subset by blast
  show "\<And>c. c \<in> interior U \<Longrightarrow> \<exists>n. B\<^bsub>n\<^esub>[c] \<subseteq> interior U"
  proof-
    fix c
    assume "c \<in> interior U"
    show "\<exists>n. B\<^bsub>n\<^esub>[c] \<subseteq> interior U"
    proof-
    obtain B where B_def: "is_open B \<and> B \<subseteq> U \<and> c \<in> B"
      using \<open>c \<in> interior U\<close> padic_integers.interior_def padic_integers_axioms
      by auto
    then show ?thesis 
    proof -
      obtain ii :: "((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set \<Rightarrow> ((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set set \<Rightarrow> int" 
        where
        "B\<^bsub>ii c B\<^esub>[c] \<subseteq> B"
        by (meson B_def is_open_def)
      then show ?thesis
        using B_def padic_integers.interior_def padic_integers_axioms by auto
qed
  qed
  qed
qed

lemma (in padic_integers) max_ball_interior[simp]:
  assumes "U \<subseteq> carrier Q\<^sub>p"
  assumes "is_max_ball_of (interior U) B"
  shows "is_max_ball_of U B"
proof(rule ccontr)
  assume C: " \<not> is_max_ball_of U B"
  then obtain B' where B'_def: "is_ball B' \<and> B' \<subseteq> U \<and> B \<subseteq> B' \<and> B \<noteq> B'"
    by (metis (no_types, lifting) assms(1) assms(2) dual_order.trans 
        interior_subset padic_integers.is_max_ball_of_def padic_integers_axioms)
  then have "B' \<subseteq> interior U"
    using padic_integers.interior_def padic_integers_axioms 
    by auto
  then show False using assms B'_def is_max_ball_of_def[of "interior U" "B"]  
    by blast
qed

lemma (in padic_integers) open_max_ball':
  assumes  "U \<subseteq> carrier Q\<^sub>p"
  assumes  "U \<noteq> carrier Q\<^sub>p"
  assumes "c \<in> U"
  assumes "\<exists>B. B \<subseteq> U \<and> is_ball B \<and> c \<in> B"
  shows "\<exists>B'. is_max_ball_of U B' \<and> c \<in> B'"
proof-
  obtain B where " B \<subseteq> U \<and> is_ball B \<and> c \<in> B"
    using assms(4)
    by blast
  then have 0: "B \<subseteq> interior U"
    using ball_is_open interior_def by blast
  have 1: "c \<in> interior U"
    using "0" \<open>B \<subseteq> U \<and> is_ball B \<and> c \<in> B\<close> by blast
  then have "\<exists>B'. is_max_ball_of (interior U) B' \<and> c \<in> B'"
    using open_max_ball[of "interior U" c] assms(1) assms(2) interior_open interior_subset
    by blast
  then show ?thesis 
    using assms(1) max_ball_interior 
    by blast
qed

lemma (in padic_integers) max_balls_disjoint:
  assumes "U \<subseteq> carrier Q\<^sub>p"
  assumes "is_max_ball_of U B"
  assumes "is_max_ball_of U B'"
  assumes "B \<noteq>B'"
  shows "B \<inter> B' = {}"
  by (meson assms(2) assms(3) assms(4) nested_balls' padic_integers.is_max_ball_of_def 
      padic_integers_axioms subset_antisym)

definition (in padic_integers) max_balls :: "padic_number set \<Rightarrow> padic_number set set" where
"max_balls U = {B. is_max_ball_of U B }"

lemma (in padic_integers) max_balls_interior:
  assumes "U \<subseteq> carrier Q\<^sub>p"
  assumes "U \<noteq> carrier Q\<^sub>p"
  shows "interior U = {x \<in> carrier Q\<^sub>p. (\<exists>B \<in> (max_balls U). x \<in> B)}"
proof
  show "interior U \<subseteq> {x \<in> carrier Q\<^sub>p. \<exists>B\<in>max_balls U. x \<in> B}"
  proof
    fix x
    assume A: " x \<in> interior U"
    show "x \<in> {x \<in> carrier Q\<^sub>p. \<exists>B\<in>max_balls U. x \<in> B}"
      by (metis (mono_tags, lifting) A assms(1) assms(2) interior_open 
          interior_subset is_open_imp_in_Qp' max_ball_interior max_balls_def
          mem_Collect_eq open_max_ball subset_antisym)
  qed
  show "{x \<in> carrier Q\<^sub>p. \<exists>B\<in>max_balls U. x \<in> B} \<subseteq> interior U"
  proof
    fix x
    assume A: " x \<in> {x \<in> carrier Q\<^sub>p. \<exists>B\<in>max_balls U. x \<in> B} "
    show "x \<in> interior U"
    proof-
      obtain B where B_def: "B\<in>max_balls U \<and> x \<in> B"
        using A by blast
      then have "B \<subseteq> interior U"
        by (metis (no_types, lifting) interior_def is_max_ball_of_def mem_Collect_eq
            padic_integers.ball_is_open padic_integers.max_balls_def padic_integers_axioms subsetI)
      then show ?thesis 
        using B_def by blast
    qed
  qed
qed

lemma (in padic_integers) max_balls_interior':
  assumes "U \<subseteq> carrier Q\<^sub>p"
  assumes "U \<noteq> carrier Q\<^sub>p"
  assumes "B \<in> max_balls U"
  shows "B \<subseteq> interior U"
  using assms(1) assms(2) assms(3) is_max_ball_of_def max_balls_interior
        padic_integers.max_balls_def padic_integers_axioms 
  by auto

lemma (in padic_integers) max_balls_interior'':
  assumes "U \<subseteq> carrier Q\<^sub>p"
  assumes "U \<noteq> carrier Q\<^sub>p"
  assumes "a \<in> interior U"
  shows "\<exists>B \<in> max_balls U. a \<in> B"
  using assms(1) assms(2) assms(3) max_balls_interior
  by blast

lemma (in padic_integers) open_interior:
  assumes "is_open U"
  shows "interior U = U"
  unfolding interior_def using assms  
  by blast

lemma (in padic_integers) interior_idempotent[simp]:
  assumes "U \<subseteq> carrier Q\<^sub>p"
  shows "interior (interior U) = interior U"
  using assms interior_open[of U] open_interior[of "interior U"]
  by auto 




end