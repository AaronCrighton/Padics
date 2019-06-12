theory Qp_thing
imports padic_integers
begin

lemma(in padic_integers) Qp_nonzero_def:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "a \<in> carrier Q\<^sub>p"
        "a \<noteq>\<zero>\<^bsub>Q\<^sub>p\<^esub>"
  using assms nonzero_def apply force
  using assms nonzero_def by fastforce

lemma(in padic_integers) Qp_is_field[simp]:
"field Q\<^sub>p"
  by (simp add: Q\<^sub>p_def  domain.fraction_field_is_field) 

lemma(in padic_integers) Qp_is_domain[simp]:
"domain Q\<^sub>p"
  using Qp_is_field  
  by (simp add: field_def)

(*choice function for numerator and denominator*)

definition(in padic_integers) denom where
"denom = domain.denom Z\<^sub>p"

definition(in padic_integers) numer where
"numer = domain.numer Z\<^sub>p"

definition(in padic_integers) frac where
"frac = domain.frac Z\<^sub>p"     

(*Qp one isn't zero*)

lemma(in padic_integers) Qp_one_car:
"\<one>\<^bsub>Q\<^sub>p\<^esub> \<in> carrier Q\<^sub>p" 
  by (simp add: cring.cring_simprules(6) fieldE(1))

lemma(in padic_integers) Qp_one_notzero:
"\<one>\<^bsub>Q\<^sub>p\<^esub> \<noteq>\<zero>\<^bsub>Q\<^sub>p\<^esub>"
  by (simp add:  one_not_zero)

lemma(in padic_integers) Qp_one_nonzero:
"\<one>\<^bsub>Q\<^sub>p\<^esub> \<in> nonzero Q\<^sub>p" 
  by (simp add: Qp_one_car Qp_one_notzero nonzero_def)

(*name for the isomorphic copy of Zp living in Qp*)

abbreviation(in padic_integers) \<O>\<^sub>p where
"\<O>\<^sub>p \<equiv> \<iota> ` carrier Z\<^sub>p"

(*alternate definition of the map \<iota>:*)

lemma(in padic_integers) inc_def: 
  assumes "a \<in> carrier Z\<^sub>p"
  shows "\<iota> a = frac a \<one>" 
  using frac_def  Z\<^sub>p_def Q\<^sub>p_def domain.inc_equation 
    Zp_is_domain \<iota>_def assms by fastforce 

(*Properties of \<iota> :*)

lemma( in padic_integers) inc_of_nonzero:
  assumes "a \<in> nonzero Z\<^sub>p"
  shows "\<iota> a \<in> nonzero Q\<^sub>p"
  using Q\<^sub>p_def Zp_is_domain \<iota>_def assms domain.Frac_def 
    domain.eq_obj_rng_of_frac_nonzero domain.inc_def 
    domain.units_of_fraction_field eq_obj_rng_of_frac.one_over 
    nonzero_def 
  by (smt Zp_one_nonzero domain.frac_im domain.inc_inj1 
      local.frac_def local.inc_def mem_Collect_eq)

lemma(in padic_integers) inc_of_one:
"\<iota> \<one> = \<one>\<^bsub>Q\<^sub>p\<^esub>"
  by (simp add: Q\<^sub>p_def Zp_one_car Zp_one_nonzero \<iota>_def domain.frac_one domain.inc_equation)

lemma(in padic_integers) inc_of_sum:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  shows "\<iota> (a \<oplus> b) = (\<iota> a) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<iota> b)"
  by (simp add: Q\<^sub>p_def Zp_one_nonzero \<iota>_def assms(1) assms(2) cring.cring_simprules(1) 
      domain.axioms(1) domain.frac_add_common_denom domain.inc_equation)

lemma(in padic_integers) inc_of_prod:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  shows "\<iota> (a \<otimes> b) = (\<iota> a) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (\<iota> b)"
  using Localization.submonoid.one_closed Q\<^sub>p_def Zp_is_domain 
    assms(1) assms(2) cring.cring_simprules(5) domain.axioms(1)
    domain.i_mult domain.inc_equation domain.nonzero_is_submonoid
    local.frac_def local.inc_def 
  by metis

lemma(in padic_integers) inc_pow:
  assumes "a \<in> nonzero Z\<^sub>p"
  shows "\<iota> (a[^](n::nat)) = (\<iota> a)[^]\<^bsub>Q\<^sub>p\<^esub> n"
proof(induction n)
  case 0
  have P0: "(a[^](0::nat)) = \<one>" 
    by (simp add: assms domain.pow_0)
  have P1: "(\<iota> a) \<in> nonzero Q\<^sub>p" 
    by (simp add: assms inc_of_nonzero)
  have QD: "domain Q\<^sub>p" 
    by (simp add: field.axioms(1))
  have P2: "(\<iota> a)[^]\<^bsub>Q\<^sub>p\<^esub> (0::nat) = \<one>\<^bsub>Q\<^sub>p\<^esub>" 
    using QD P1 by (simp add: domain.pow_0)
  then show ?case 
    by (simp add: P0 inc_of_one)
next
  case (Suc n)
  fix n::nat
  have QD: "domain Q\<^sub>p" 
    by (simp add: field.axioms(1))
  have A: "a \<in> carrier Z\<^sub>p"
    using assms nonzero_def Zp_nonzero_def(1) by presburger
  have An: "(a[^]n) \<in> carrier Z\<^sub>p" 
    using Zp_nat_pow_nonzero Zp_nonzero_def(1) assms by blast
  have iA: "\<iota> a \<in> carrier Q\<^sub>p"
    by (simp add: Qp_nonzero_def(1) assms inc_of_nonzero)
  have iAn: "\<iota> (a[^]n) \<in> carrier Q\<^sub>p" 
    using Qp_nonzero_def(1) Zp_nat_pow_nonzero assms inc_of_nonzero 
    by blast
  assume "\<iota> (a[^]n) = (\<iota> a)[^]\<^bsub>Q\<^sub>p\<^esub> n"
  have "(a[^](Suc n)) = (a\<otimes> (a[^]n))" 
    by (simp add: A  domain.pow_suc)
  then have "\<iota> (a[^](Suc n)) = (\<iota> (a\<otimes> (a[^]n)))" 
    by simp
  then have "\<iota> (a[^](Suc n)) = (\<iota> a) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (\<iota>(a[^]n))" 
    using inc_of_prod A An by blast
  then have P: "\<iota> (a[^](Suc n)) = (\<iota> a) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (\<iota> a)[^]\<^bsub>Q\<^sub>p\<^esub>n" 
    by (simp add: \<open>\<iota> (a [^] n) = \<iota> a [^]\<^bsub>Q\<^sub>p\<^esub> n\<close>)
  have  "\<iota> a [^]\<^bsub>Q\<^sub>p\<^esub> (Suc n) = (\<iota> a) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (\<iota> a)[^]\<^bsub>Q\<^sub>p\<^esub>n" 
    by (simp add: iA  domain.pow_suc) 
  then show "\<iota> (a[^](Suc n)) = \<iota> a [^]\<^bsub>Q\<^sub>p\<^esub> (Suc n)" 
    by (simp add: P)
qed

lemma(in padic_integers) inc_of_diff:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  shows "\<iota> (a \<ominus>  b) = (\<iota> a) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (\<iota> b)"
  using assms unfolding a_minus_def 
  using inc_of_sum[of a "\<ominus> b"] 
  by (simp add: \<open>b \<in> carrier Z\<^sub>p\<close> Q\<^sub>p_def Zp_one_nonzero cring.cring_simprules(3) 
      domain.axioms(1) domain.frac_uminus local.frac_def local.inc_def)

lemma(in padic_integers) Units_nonzero_Qp[simp]:
assumes "u \<in> Units Q\<^sub>p"
shows "u \<in> nonzero Q\<^sub>p"
  by (simp add: assms domain.Units_nonzero field.axioms(1))

lemma(in padic_integers) Units_inverse_Qp[simp]:
  assumes "u \<in> Units Q\<^sub>p"
  shows "inv\<^bsub>Q\<^sub>p\<^esub> u \<in> Units Q\<^sub>p"
  by (simp add: assms domain.Units_inverse)

(*************************************************************************************************)
(*************************************************************************************************)
(*************************************     FACTS FROM       **************************************)
(*************************************   fractionfield.thy  **************************************)
(*************************************************************************************************)
(*************************************************************************************************)

lemma(in padic_integers) frac_add:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "d \<in> nonzero Z\<^sub>p"
  shows "(frac a b) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (frac c d) = (frac ((a \<otimes> d) \<oplus> (b \<otimes> c)) (b \<otimes> d))"
  by (simp add: Q\<^sub>p_def assms(1) assms(2) assms(3) assms(4) domain.frac_add local.frac_def)

lemma(in padic_integers) frac_add_common_denom:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "c \<in> nonzero Z\<^sub>p"
  shows "(frac a c) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (frac b c) = frac (a \<oplus> b) c"
  by (simp add: Q\<^sub>p_def assms(1) assms(2) assms(3) domain.frac_add_common_denom local.frac_def)

lemma(in padic_integers) frac_mult:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "d \<in> nonzero Z\<^sub>p"
  shows "(frac a b) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (frac c d) = (frac (a \<otimes> c) (b \<otimes> d))"
  by (simp add: Q\<^sub>p_def assms(1) assms(2) assms(3) assms(4) domain.frac_mult local.frac_def)

lemma(in padic_integers) frac_one:
  assumes "a \<in> nonzero Z\<^sub>p"
  shows "frac a a = \<one>\<^bsub>Q\<^sub>p\<^esub>"
  by (simp add: Q\<^sub>p_def assms domain.frac_one local.frac_def)

lemma(in padic_integers)  frac_closed:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  shows "frac a b \<in> carrier Q\<^sub>p"
  by (simp add: Q\<^sub>p_def assms(1) assms(2) domain.frac_im local.frac_def)

lemma(in padic_integers) inv_in_frac:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "a \<noteq>\<zero>\<^bsub>Q\<^sub>p\<^esub>"
  shows "inv\<^bsub>Q\<^sub>p\<^esub> a \<in> carrier Q\<^sub>p"
        "inv\<^bsub>Q\<^sub>p\<^esub> a \<noteq>\<zero>\<^bsub>Q\<^sub>p\<^esub>"
        "inv\<^bsub>Q\<^sub>p\<^esub> a \<in> nonzero Q\<^sub>p"
proof-
  have "a \<in> Units Q\<^sub>p" using assms Units_def domain.units_of_fraction_field 
    using Diff_iff Q\<^sub>p_def Zp_is_domain by fastforce
  then show 0:"inv\<^bsub>Q\<^sub>p\<^esub> a \<in> carrier Q\<^sub>p" 
    by (meson Qp_is_field cring_def fieldE(1) monoid.Units_inv_closed ring_def)
  show 1: "inv\<^bsub>Q\<^sub>p\<^esub> a \<noteq>\<zero>\<^bsub>Q\<^sub>p\<^esub>" 
    by (metis Q\<^sub>p_def Qp_is_field Zp_is_domain assms(1) assms(2)
        cring.cring_simprules(27) domain.one_not_zero 
        domain.units_of_fraction_field0(2) field.axioms(1) fieldE(1))
  show  "inv\<^bsub>Q\<^sub>p\<^esub> a \<in> nonzero Q\<^sub>p"
    by (simp add: "0" "1" nonzero_def)
qed

lemma(in padic_integers) nonzero_numer_imp_nonzero_fraction:
  assumes "a \<in> nonzero Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  shows "frac a b \<noteq> \<zero>\<^bsub>Q\<^sub>p\<^esub>"
  by (simp add: Q\<^sub>p_def assms(1) assms(2) domain.nonzero_fraction local.frac_def)

lemma(in padic_integers) nonzero_fraction_imp_numer_not_zero:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  assumes "frac a b \<noteq> \<zero>\<^bsub>Q\<^sub>p\<^esub>"
  shows "a \<noteq> \<zero>"
proof
  assume "a = \<zero>"
  then have  "frac a b = frac \<zero> \<one>" 
    by (metis Q\<^sub>p_def Qp_is_field Zp_is_domain \<iota>_def assms(1) assms(2)
        cring.cring_simprules(26) domain.axioms(1) domain.frac_im 
        domain.i_mult domain.nat_0 domain.nat_inc_rep field.axioms(1) local.frac_def local.inc_def)
  then show False 
    by (metis Q\<^sub>p_def Qp_is_field Zp_is_domain assms(3) 
        domain.nat_0 domain.nat_inc_rep field.axioms(1) local.frac_def)
qed

lemma(in padic_integers) nonzero_fraction_imp_nonzero_numer:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  assumes "frac a b \<noteq> \<zero>\<^bsub>Q\<^sub>p\<^esub>"
  shows "a \<in> nonzero Z\<^sub>p"
proof-
  have "a \<noteq> \<zero>"
    using assms(1) assms(2) assms(3) nonzero_fraction_imp_numer_not_zero 
    by blast
  then show ?thesis 
    using assms(1) nonzero_def by (simp add: nonzero_def) 
qed

lemma(in  padic_integers) frac_inv:
  assumes "a \<in> nonzero Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p" 
  shows "inv\<^bsub>Q\<^sub>p\<^esub> (frac a b) = (frac b a)"
  by (simp add: Q\<^sub>p_def  assms(1) assms(2) domain.frac_inv local.frac_def)

lemma(in  padic_integers) frac_inv_id:
  assumes "a \<in> nonzero Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p" 
  assumes "c \<in> nonzero Z\<^sub>p"
  assumes "d \<in> nonzero Z\<^sub>p" 
  assumes "frac a b = frac c d"
  shows "frac b a = frac d c"
  using frac_inv assms  by metis  

lemma(in  padic_integers) frac_uminus:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  shows "\<ominus>\<^bsub>Q\<^sub>p\<^esub> (frac a b) = frac (\<ominus> a) b" 
  by (simp add: Q\<^sub>p_def  assms(1) assms(2) domain.frac_uminus local.frac_def)

lemma(in  padic_integers) frac_cancel_l:
  assumes "a \<in>nonzero Z\<^sub>p"
  assumes "b \<in>nonzero Z\<^sub>p"
  assumes "c \<in>carrier Z\<^sub>p"
  shows "frac (a \<otimes>c) (a \<otimes>b) = frac c b" 
  by (simp add:  assms(1) assms(2) assms(3) domain.frac_cancel_l local.frac_def)

lemma(in  padic_integers) frac_cancel_r:
  assumes "a \<in>nonzero Z\<^sub>p"
  assumes "b \<in>nonzero Z\<^sub>p"
  assumes "c \<in>carrier Z\<^sub>p"
  shows "frac (c \<otimes>a) (b \<otimes>a) = frac c b"
  by (simp add:  assms(1) assms(2) assms(3) domain.frac_cancel_r local.frac_def)

lemma(in  padic_integers) frac_cancel_lr:
  assumes "a \<in>nonzero Z\<^sub>p"
  assumes "b \<in>nonzero Z\<^sub>p"
  assumes "c \<in>carrier Z\<^sub>p"
  shows "frac (a \<otimes>c) (b \<otimes>a) = frac c b"
  by (simp add: assms(1) assms(2) assms(3) domain.frac_cancel_lr local.frac_def)

lemma(in  padic_integers) frac_cancel_rl:
  assumes "a \<in>nonzero Z\<^sub>p"
  assumes "b \<in>nonzero Z\<^sub>p"
  assumes "c \<in>carrier Z\<^sub>p"
  shows "frac (c \<otimes>a) (a \<otimes>b) = frac c b"
  by (simp add: assms(1) assms(2) assms(3) domain.frac_cancel_rl local.frac_def)

lemma(in  padic_integers) i_mult:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "d \<in> nonzero Z\<^sub>p"
  shows "(\<iota> a) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (frac c d) = frac (a \<otimes> c) d"
  by (simp add: Q\<^sub>p_def  \<iota>_def assms(1) assms(2) assms(3) domain.i_mult local.frac_def)

lemma(in padic_integers) numer_denom_facts:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "(numer a) \<in> carrier Z\<^sub>p"
        "(denom a) \<in> nonzero Z\<^sub>p"
        "a \<noteq>  \<zero>\<^bsub>Q\<^sub>p\<^esub> \<Longrightarrow> numer a \<noteq> \<zero> "
        "a \<otimes>\<^bsub>Q\<^sub>p\<^esub> (\<iota> (denom a)) = \<iota> (numer a)"
        "a = frac (numer a) (denom a)"
  using Q\<^sub>p_def assms domain.numer_denom_facts(1) numer_def 
      apply force
  using Q\<^sub>p_def assms denom_def domain.numer_denom_facts(2) 
     apply (metis Zp_is_domain)
  using Q\<^sub>p_def assms domain.numer_denom_facts(3) numer_def 
    apply force
  using Q\<^sub>p_def \<iota>_def assms denom_def domain.numer_denom_facts(4) numer_def 
    apply force
  using Q\<^sub>p_def assms denom_def domain.numer_denom_facts(5) local.frac_def numer_def 
  by force

lemma(in padic_integers) get_common_denominator:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "y \<in> carrier Q\<^sub>p"
  obtains a b c where
    "a \<in> carrier Z\<^sub>p"
    "b \<in> carrier Z\<^sub>p" 
    "c \<in> nonzero Z\<^sub>p"
    "x = frac a c"
    "y = frac b c"
  using Q\<^sub>p_def Zp_is_domain assms(1) assms(2) domain.common_denominator local.frac_def that 
  by metis

abbreviation(in padic_integers) fract :: "_ \<Rightarrow> _ \<Rightarrow> _" (infixl "\<div>" 50) where
"(fract a b) \<equiv> (a \<otimes>\<^bsub>Q\<^sub>p\<^esub> (inv\<^bsub>Q\<^sub>p\<^esub> b))"

(*fract generalizes frac*)

lemma(in padic_integers) fract_frac:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  shows "(frac a b) = (\<iota> a \<div> \<iota> b)" 
proof-
  have B: "b \<in> carrier Z\<^sub>p" 
    using assms(2) nonzero_def  Zp_nonzero_def(1) 
    by presburger
  have P0:"(inv\<^bsub>Q\<^sub>p\<^esub> (\<iota> b)) = frac \<one> b" 
    using B inc_def frac_inv  Zp_one_nonzero assms(2) 
    by presburger
  have P1: "(frac a b) = (\<iota> a) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (frac \<one> b)" 
    by (metis B Localization.submonoid.one_closed Zp_is_domain assms(1)
        assms(2) cring.cring_simprules(12) cring.cring_simprules(6)
        domain.axioms(1) domain.nonzero_is_submonoid frac_cancel_rl i_mult)
  show ?thesis 
    by (simp add: P0 P1)
qed

lemma(in padic_integers) frac_eq:
  assumes "a \<in> nonzero Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  assumes "frac a b = \<one>\<^bsub>Q\<^sub>p\<^esub>"
  shows "a = b"
proof-
  have "frac a b = frac b b"
    by (simp add: assms(2) assms(3) frac_one)
  then have "frac a \<one> = frac b \<one>"
    by (metis (no_types, lifting) Q\<^sub>p_def Qp_is_domain Z\<^sub>p_def
        Zp_nonzero_def(1) Zp_one_nonzero assms(1) assms(2) assms(3)
        cring.cring_simprules(11) cring.cring_simprules(12) cring.cring_simprules(14) 
        domain.axioms(1) fract_frac local.inc_def padic_integers.frac_closed 
        padic_integers.frac_inv padic_integers_axioms)
  then show ?thesis 
    using Zp_is_domain Zp_nonzero_def(1) \<iota>_def assms(1) assms(2) 
      domain.inc_inj2 local.inc_def by metis 
qed


lemma(in padic_integers) Qp_nat_pow_nonzero:
  assumes "x \<in> nonzero Q\<^sub>p"
  shows "x[^]\<^bsub>Q\<^sub>p\<^esub>(n::nat) \<in> nonzero Q\<^sub>p"
  by (simp add: assms domain.nat_pow_nonzero)

lemma(in padic_integers) pow_p_frac_0:
  assumes "(m::int) \<ge> n"
  assumes "n \<ge>0"
  shows "(frac (\<p>[^]m) (\<p>[^]n)) = \<iota> (\<p>[^](m-n))"
proof-
  have 0: "\<p>\<in>carrier Z\<^sub>p" 
    by (simp add: Zp_nat_inc_closed) 
  have 1: "m - n \<ge>0" 
    using assms(1) by auto 
  have 2: "nat (m - n) + (nat n) = nat m" 
    using "1" assms(2) by linarith 
  have 3: "m \<ge>0" 
    using assms by auto
  then have "(\<p>[^] (nat (m-n))) \<otimes> (\<p>[^](nat n)) = (\<p>[^] (nat m))" 
    using Zp_is_domain 0 1 2 3 monoid.nat_pow_mult
    by (metis "0" Z\<^sub>p_def cring_def monoid.nat_pow_mult padic_int_is_cring prime ring_def)
  then have "(\<p>[^] (m-n)) \<otimes> (\<p>[^]n) = (\<p>[^]m)" 
    using int_pow_int 1 3 assms(2) int_nat_eq by metis  
  then have P0: "(frac (\<p>[^]m) (\<p>[^]n)) = frac ((\<p>[^](m-n))\<otimes> (\<p>[^]n)) (\<p>[^]n)"
    by simp 
  have "\<p> \<in>carrier Z\<^sub>p" 
    by (simp add: "0") 
  have "(\<p>[^](nat n)) = [(p^(nat n))] \<cdot> \<one>" 
    by (simp add: p_pow_rep0) 
  then have "(\<p>[^](nat n)) \<in> carrier Z\<^sub>p" 
    by (simp add: Zp_nat_inc_closed) 
  then have "(\<p>[^]n) \<in> carrier Z\<^sub>p" 
    using assms(2) by (metis int_nat_eq int_pow_int) 
  then have P1: "(frac (\<p>[^]m) (\<p>[^]n)) = frac ((\<p>[^](m-n))\<otimes> (\<p>[^]n)) ((\<one> \<otimes> (\<p>[^]n)))"
    using Zp_is_domain P0 
    by (simp add: cring.cring_simprules(12) domain_def) 
  have P2: "(\<p>[^](m-n)) \<in> carrier Z\<^sub>p" 
    using "1" p_pow_car by blast 
  have P3: "(\<p>[^]n) \<in> carrier Z\<^sub>p" 
    using \<open>\<p> [^] n \<in> carrier Z\<^sub>p\<close> by blast 
  have P4: "(\<p>[^]n) \<in> nonzero Z\<^sub>p" 
    by (metis assms(2) int_eq_iff int_pow_int p_pow_nonzero) 
  have P5: "\<one> \<in> nonzero Z\<^sub>p" 
    using nonzero_def Zp_one_nonzero 
    by blast
  have "(frac (\<p>[^](m-n)) \<one>) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (frac (\<p>[^]n) (\<p>[^]n)) 
        = frac ((\<p>[^](m-n))\<otimes> (\<p>[^]n)) ((\<one> \<otimes> (\<p>[^]n)))"
    using Zp_is_domain  P2 P4 P3 P5 frac_def Q\<^sub>p_def  frac_mult
    by blast 
  then have "frac ((\<p>[^](m-n))\<otimes> (\<p>[^]n)) ((\<one> \<otimes> (\<p>[^]n))) = (frac (\<p>[^](m-n)) \<one>) "
    by (simp add: domain.frac_cancel_r P2 P4 P5 local.frac_def)  
  then have P6: "(frac (\<p>[^]m) (\<p>[^]n)) = (frac (\<p>[^](m-n)) \<one>) " 
    using P1 by blast 
  have "(frac (\<p>[^](m-n)) \<one>) = \<iota> (\<p>[^](m-n))" 
    using inc_def  by (simp add: P2) 
  then show ?thesis 
    using P6 by blast
qed

lemma(in padic_integers) pow_p_frac:
  assumes "(m::int) \<le> n"
  assumes "m \<ge>0"
  shows "(frac (\<p>[^]m) (\<p>[^]n)) = frac \<one> (\<p>[^](n-m))"
proof-
  have "(frac (\<p>[^]n) (\<p>[^]m)) = \<iota> (\<p>[^](n-m))" 
    by (simp add: assms(1) assms(2) pow_p_frac_0) 
  then have P0:"(frac (\<p>[^]n) (\<p>[^]m)) = frac (\<p>[^](n-m)) \<one>" 
    by (simp add: assms(1) local.inc_def) 
  have P1: "\<one>\<in>nonzero Z\<^sub>p" 
    by (simp add: Zp_one_nonzero)
  have P2: "\<p>[^]n \<in> nonzero Z\<^sub>p" 
    by (metis assms(1) assms(2) diff_ge_0_iff_ge diff_mono 
        eq_iff_diff_eq_0 int_eq_iff int_nat_eq int_pow_int p_pow_nonzero)
  have P3: "\<p>[^]m \<in> nonzero Z\<^sub>p" 
    by (metis assms(2) int_eq_iff int_pow_int p_pow_nonzero) 
  have P4: "(\<p>[^](n-m)) \<in> nonzero Z\<^sub>p" 
    by (metis assms(1) diff_ge_0_iff_ge int_eq_iff 
        int_pow_int ord_Zp_def ord_Zp_p_pow ord_of_nonzero(2) p_pow_car) 
  show " frac (\<p>[^]m) (\<p>[^]n) = frac \<one> (\<p>[^](n-m))"
    using P0 P1 P2 P3 P4 p_pow_nonzero domain.frac_inv_id frac_def Zp_is_domain 
    by (metis (mono_tags, lifting)) 
qed



(**********************************************************************************************************)


(*The copy of the prime p living in Q\<^sub>p*)

abbreviation(in padic_integers) \<pp> where
"\<pp> \<equiv> [p] \<cdot>\<^bsub>Q\<^sub>p\<^esub> \<one>\<^bsub>Q\<^sub>p\<^esub>"

abbreviation(in padic_integers) exp (infixl "e" 50) where
"exp a n \<equiv> a [^]\<^bsub>Q\<^sub>p\<^esub> n"

lemma(in padic_integers) p_inc:
"\<pp> = \<iota> \<p>"
proof-
  have "\<pp> = frac \<p> \<one>" 
    by (simp add: domain.nat_inc_rep Q\<^sub>p_def local.frac_def)
  then show ?thesis 
    by (simp add: local.inc_def Zp_nat_inc_closed)
qed

lemma(in padic_integers) p_nonzero[simp]:
"\<pp>\<in>nonzero Q\<^sub>p"
  using Z\<^sub>p_def Zp_nat_inc_closed inc_of_nonzero ord_Zp_p p_inc 
      padic_integers.ord_of_nonzero(2) padic_integers_axioms 
  by auto

lemma(in padic_integers) p_natpow_inc:
  fixes n::nat
  shows "\<pp> e n = \<iota> (\<p> [^] n)"
  by (metis Zp_nat_inc_closed inc_pow not_nonzero_Zp p_inc 
      p_pow_nonzero_0(2) p_pow_rep0 power_Suc0_right)

lemma(in padic_integers) p_intpow_inc:
  fixes n::int
  assumes "n \<ge>0"
  shows "\<pp> e n = \<iota> (\<p> [^] n)"
  using p_natpow_inc  
  by (metis assms int_nat_eq int_pow_int)

lemma(in padic_integers) p_intpow:
  fixes n::int
  assumes "n < 0"
  shows "\<pp> e n = (frac \<one> (\<p> [^] (-n)))"
proof-
  have U0: "(\<pp> e (nat (-n))) \<in> Units Q\<^sub>p" using Qp_is_field 
    by (metis Diff_iff Localization.submonoid.one_closed Q\<^sub>p_def Z\<^sub>p_def
        Zp_is_domain \<iota>_def domain.frac_im domain.inc_inj1 domain.nonzero_is_submonoid
        domain.units_of_fraction_field local.frac_def local.inc_def
        padic_integers.p_natpow_inc padic_integers.p_pow_car_nat
        padic_integers.p_pow_nonzero_0(2) padic_integers_axioms singletonD)
  have E0: "(\<pp> e (nat (-n))) = (\<pp> e (-n))" 
    using assms  by (simp add: int_pow_def nat_pow_def)
  then have U1: "(\<pp> e  (-n)) \<in> Units Q\<^sub>p" using U0 
    by simp
  have "(\<pp> e n) = inv \<^bsub>Q\<^sub>p\<^esub> (\<pp> e (nat (-n)))"
    using assms by (simp add: int_pow_def nat_pow_def)
  then have "(\<pp> e n) = inv \<^bsub>Q\<^sub>p\<^esub> (\<pp> e (-n))" 
    using E0 by simp
  then have "(\<pp> e n) = inv \<^bsub>Q\<^sub>p\<^esub> \<iota> (\<p> [^](-n))" 
    using assms p_intpow_inc by auto
  then have E1: "(\<pp> e n) = inv \<^bsub>Q\<^sub>p\<^esub>  frac (\<p> [^](-n)) \<one>" 
    using assms local.inc_def p_pow_car by auto
  have A: "(\<p> [^](-n)) \<in> nonzero Z\<^sub>p"
   using assms p_pow_nonzero 
   by (metis (mono_tags) add.inverse_inverse diff_0 
       int.lless_eq int_nat_eq int_pow_int  neg_0_le_iff_le )
  then show ?thesis using A frac_inv inc_def  
    using E1 Zp_one_nonzero 
    by blast
qed

lemma(in padic_integers) p_natpow_closed[simp]:
  fixes n::nat
  shows "(\<pp> e n) \<in> (carrier Q\<^sub>p)"
        "(\<pp> e n) \<in> (nonzero Q\<^sub>p)"
  using Qp_nat_pow_nonzero Qp_nonzero_def(1) p_nonzero 
  apply blast
    using Qp_nat_pow_nonzero p_nonzero by blast



lemma(in padic_integers) Zp_is_subring:
"subring \<O>\<^sub>p Q\<^sub>p"
  by (simp add: Q\<^sub>p_def  \<iota>_def domain.inc_im_is_subring)


lemma(in padic_integers) p_pow_diff: 
  fixes n::int 
  fixes m::int 
  assumes "n \<ge>0"
  assumes "m \<ge>0"
  shows "\<pp> e (n - m) = frac (\<p>[^] n) (\<p>[^]m)"
proof-
  have 0: "comm_monoid Q\<^sub>p"
    using Qp_is_domain cring_def domain_def by blast
  have 1: "\<pp> \<in> Units Q\<^sub>p"
    by (metis Qp_is_domain Qp_is_field Qp_nonzero_def(1) Qp_nonzero_def(2) field.field_inv(2) 
        inv_in_frac(1) is_UnitI(1) p_nonzero)
  have 2: "\<pp> e (n - m) = (\<pp> e n) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (\<pp> e -m)"
    using int_pow_add[of Q\<^sub>p \<pp> n "-m"]
    by (simp add: "0" "1")
  have 3: "\<pp> e (n - m) = (\<pp> e n) \<otimes>\<^bsub>Q\<^sub>p\<^esub> inv\<^bsub>Q\<^sub>p\<^esub>(\<pp> e m)"
    using 0 2 
    by (simp add: "1" int_pow_inv')
  then show ?thesis using assms 
    using fract_frac p_int_pow_nonzero p_intpow_inc p_pow_car by presburger
qed

lemma(in padic_integers) Qp_is_comm_monoid[simp]:
"comm_monoid Q\<^sub>p"
  using Qp_is_domain cring_def domain_def by blast

lemma(in padic_integers) Qp_Units_nonzero:
"(a \<in> (Units Q\<^sub>p)) \<longleftrightarrow> (a \<in> ( nonzero Q\<^sub>p))"
  unfolding nonzero_def using Qp_is_field  
  by (simp add: Q\<^sub>p_def domain.units_of_fraction_field)

lemma(in padic_integers)  Qp_int_pow_add: 
  fixes n::int 
  fixes m::int
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "a [^]\<^bsub>Q\<^sub>p\<^esub> (n + m) = (a [^]\<^bsub>Q\<^sub>p\<^esub> n) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (a [^]\<^bsub>Q\<^sub>p\<^esub> m)"
  using int_pow_add[of Q\<^sub>p a n m]  Qp_Units_nonzero Qp_is_comm_monoid assms 
  by blast

lemma(in padic_integers) p_intpow_closed[simp]:
  fixes n::int
  shows "(\<pp> e n) \<in> (carrier Q\<^sub>p)"
        "(\<pp> e n) \<in> (nonzero Q\<^sub>p)"
   apply (meson Qp_Units_nonzero Qp_is_comm_monoid Qp_nonzero_def(1) int_pow_unit_closed p_nonzero)
  by (meson Qp_Units_nonzero Qp_is_comm_monoid int_pow_unit_closed p_nonzero)

(*************************************************************************************************)
(*************************************************************************************************)
(************************************* THE VALUATION ON Qp  **************************************)
(*************************************************************************************************)
(*************************************************************************************************)

definition(in padic_integers) ord where
"ord x = (ord_Zp (numer x)) - (ord_Zp (denom x))"

definition(in padic_integers) val where
"val x = (if (x = \<zero>\<^bsub>Q\<^sub>p\<^esub>) then \<infinity>\<^bsub>G\<^esub> else (Some (ord x)))"

lemma(in padic_integers) val_ord[simp]:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "val a = *ord a*"
  using assms nonzero_def val_def by force

(**************************************************************************************************)
(**************************************************************************************************)
(*********************************                             ************************************)
(*********************************  PROPERTIES OF VAL AND ORD  ************************************)
(*********************************                             ************************************)
(**************************************************************************************************)
(**************************************************************************************************)

lemma(in padic_integers) ord_of_frac:
  assumes "a \<in> nonzero Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  shows "ord (frac a b) = (ord_Zp a) - (ord_Zp b)"
proof-
  have "frac a b = frac (numer (frac a b)) (denom (frac a b))"
    using Q\<^sub>p_def Zp_is_domain assms(1) assms(2) domain.frac_im 
      local.frac_def Zp_nonzero_def(1) numer_denom_facts(5) 
    by metis
  then have "a \<otimes> (denom (frac a b)) = b \<otimes> (numer (frac a b))"
    by (metis Zp_is_domain Zp_nonzero_def(1) assms(1) assms(2) domain.frac_eq 
        frac_closed local.frac_def numer_denom_facts(1) numer_denom_facts(2))
  then have "(ord_Zp a) - (ord_Zp b) =  (ord_Zp (numer (frac a b))) - (ord_Zp (denom (frac a b)))"
    using ord_Zp_eq_frac 
    by (metis Q\<^sub>p_def Z\<^sub>p_def Zp_is_domain assms(1) assms(2) domain.frac_im domain.nonzero_fraction 
        local.frac_def Zp_nonzero_def(1) numer_denom_facts(1) numer_denom_facts(3) ord_of_nonzero(2)
        ord_pos padic_integers.numer_denom_facts(2) padic_integers_axioms)
  then show ?thesis 
    using ord_def 
    by presburger
qed

lemma(in padic_integers) val_zero:
"val (\<zero>\<^bsub>Q\<^sub>p\<^esub>) = \<infinity>\<^bsub>G\<^esub>" by (simp add: val_def)

lemma(in padic_integers) ord_one[simp]:
"ord (\<one>\<^bsub>Q\<^sub>p\<^esub>) = 0"
  using ord_of_frac[of \<one> \<one>] frac_one[of \<one>] Zp_one_nonzero 
  by (metis (mono_tags, hide_lams) diff_self  local.frac_def)

lemma(in padic_integers) val_one[simp]:
"val (\<one>\<^bsub>Q\<^sub>p\<^esub>) = \<zero>\<^bsub>G\<^esub>"
  using ord_one by (simp add:  gzero_id one_not_zero val_def)

lemma(in padic_integers) val_of_frac:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  shows "val (frac a b) = (val_Zp a) \<ominus>\<^bsub>G\<^esub> (val_Zp b)"
proof(cases "a = \<zero>")
  case True
  then show ?thesis 
    using G_mult(1) assms(1) assms(2)  local.val_zero Zp_nonzero_def(2) val_Zp_def 
          nonzero_fraction_imp_numer_not_zero by metis 
next
  case False
  then have "a \<in> nonzero Z\<^sub>p" 
    by (simp add: assms(1) nonzero_def)
  then show ?thesis using ord_of_frac 
    using  assms(2) gminus_minus Zp_nonzero_def(1) Zp_nonzero_def(2)  val_def val_ord_Zp 
    by (metis nonzero_numer_imp_nonzero_fraction)
qed

lemma(in padic_integers) Zp_division_Qp_0[simp]:
  assumes "u \<in> Units Z\<^sub>p"
  assumes "v \<in> Units Z\<^sub>p"
  shows "frac (u \<otimes> (inv\<^bsub>Z\<^sub>p\<^esub> v))  \<one> = frac u v"
proof-  
  have 0: "frac v v = \<one>\<^bsub>Q\<^sub>p\<^esub>" 
    using frac_one
    by (meson Units_nonzero_Zp assms(2))
  have 1:"(inv\<^bsub>Z\<^sub>p\<^esub> v) \<in> carrier Z\<^sub>p"
    using assms  Zp_is_domain  by (metis cring_def domain_def monoid.Units_inv_closed ring_def)
  have 2:"frac (u \<otimes> (inv\<^bsub>Z\<^sub>p\<^esub> v))  \<one>  \<in> carrier Q\<^sub>p"
    using 1 assms  Units_nonzero_Zp Zp_is_domain cring.cring_simprules(5)
      domain.axioms(1) frac_closed Zp_nonzero_def(1) Zp_one_nonzero 
    by (metis (mono_tags, hide_lams)   local.frac_def )
  have 3: "frac (u \<otimes> (inv\<^bsub>Z\<^sub>p\<^esub> v))  \<one> =  (frac (u \<otimes> (inv\<^bsub>Z\<^sub>p\<^esub> v))  \<one>) \<otimes>\<^bsub>Q\<^sub>p\<^esub> frac v v"
    using Qp_is_field 0 2 
    by (metis "1" Units_nonzero_Zp Zp_is_domain assms(1) cring.cring_simprules(5)
        domain.axioms(1) frac_inv fract_frac inc_of_one local.inc_def
        Zp_nonzero_def(1) Zp_one_nonzero)
  then have 4:  "frac (u \<otimes> (inv\<^bsub>Z\<^sub>p\<^esub> v))  \<one> =  (frac ((u \<otimes> (inv\<^bsub>Z\<^sub>p\<^esub> v)) \<otimes> v)  v)"
    by (metis "1" Units_nonzero_Zp Zp_is_domain assms(1) assms(2)
        cring.cring_simprules(5) domain.axioms(1) i_mult local.inc_def Zp_nonzero_def(1))
  then have 4:  "frac (u \<otimes> (inv\<^bsub>Z\<^sub>p\<^esub> v))  \<one> =  (frac (u \<otimes> ((inv\<^bsub>Z\<^sub>p\<^esub> v) \<otimes> v))  v)"
    by (simp add: "1"   assms(1) assms(2) cring.cring_simprules(11) 
        domain.axioms(1) Zp_nonzero_def(1))
  have 5:"(inv\<^bsub>Z\<^sub>p\<^esub> v) \<otimes> v = \<one>" 
    by (meson Zp_is_domain assms(2) cring_def domain_def monoid.Units_l_inv ring_def)
  then show  "frac (u \<otimes> (inv\<^bsub>Z\<^sub>p\<^esub> v))  \<one> =  (frac u  v)"
    using 4 
    by (metis "1" Units_nonzero_Zp Zp_is_domain Zp_nonzero_def(1) Zp_one_notzero 
        assms(1) assms(2) domain.integral_iff frac_cancel_rl not_nonzero_Zp)
qed

lemma(in padic_integers) Zp_division_Qp_1:
  assumes "u \<in> Units Z\<^sub>p"
  assumes "v \<in> Units Z\<^sub>p"
  obtains w where "w \<in> Units Z\<^sub>p"
                  "\<iota> w = frac u v"
proof-
  have " (inv\<^bsub>Z\<^sub>p\<^esub> v) \<in> Units Z\<^sub>p" 
    using Zp_is_domain domain_def cring_def ring_def assms(2) Units_inverse_Zp
    by blast
  then have "(u \<otimes> (inv\<^bsub>Z\<^sub>p\<^esub> v)) \<in> Units Z\<^sub>p" 
    using assms Zp_is_domain 
    by (metis Units_closed)
  then show ?thesis using  Zp_division_Qp_0
    by (metis (mono_tags, hide_lams) Zp_is_domain \<iota>_def assms(1) assms(2) 
        cring_def domain.axioms(1) domain.inc_equation local.frac_def
        monoid.Units_closed ring_def that)
qed

(*Showing that the image of Zp in Qp is a valuation ring*)

lemma(in padic_integers) Zp_ord_criterion[simp]:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "a \<noteq> \<zero>\<^bsub>Q\<^sub>p\<^esub>"
  assumes "ord a \<ge> 0"
  shows "a \<in> \<O>\<^sub>p"
proof-
  obtain c d where P0: "a = frac c d" and P1: "c \<in> nonzero Z\<^sub>p" and P2: "d \<in> nonzero Z\<^sub>p"
    using Q\<^sub>p_def Zp_is_domain assms(1) domain.numer_denom_facts(1)
      domain.numer_denom_facts(2) domain.numer_denom_facts(5) local.frac_def 
    by (metis assms(2) domain.numer_denom_facts(3) ord_of_nonzero(2) ord_pos)
  obtain m n where P3: "m = ord_Zp c" and P4:"n = ord_Zp d"
    by metis 
  obtain u where "u = ac_Zp c" 
    by simp
  have P5:"c = (\<p>[^]m) \<otimes> u" and P6:"u \<in> Units Z\<^sub>p"
     apply (metis P1 P3 \<open>u = ac_Zp c\<close> ac_Zp_factors_x int_pow_int Zp_nonzero_def(1) Zp_nonzero_def(2) ord_nat)
    using P1 Zp_nonzero_def(1) Zp_nonzero_def(2) \<open>u = ac_Zp c\<close> ac_Zp_is_Unit 
    by blast
  obtain v where "v = ac_Zp d" by simp
  have  P7:"d = (\<p>[^]n) \<otimes> v" and P8:"v \<in> Units Z\<^sub>p"
     apply (metis P2 P4 \<open>v = ac_Zp d\<close> ac_Zp_factors_x int_pow_int Zp_nonzero_def(1) Zp_nonzero_def(2) ord_nat)
    using P2 Zp_nonzero_def(1) Zp_nonzero_def(2) \<open>v = ac_Zp d\<close> ac_Zp_is_Unit by blast
  have P9: "a = frac ((\<p>[^]m) \<otimes> u) ((\<p>[^]n) \<otimes> v)" 
  by (simp add: P0 P5 P7)
  have P10: "(\<p>[^]m) \<in> carrier Z\<^sub>p"
    using P1 P3 Z\<^sub>p_def ord_pos Zp_nonzero_def padic_integers.p_pow_car padic_integers_axioms by blast
  have P11: "(\<p>[^]n) \<in> nonzero Z\<^sub>p" 
    by (metis P2 P4 int_nat_eq int_pow_int ord_Zp_def ord_pos Zp_nonzero_def p_pow_nonzero)
  have P12: "u \<in> carrier Z\<^sub>p"
    using P6 Units_def Units_nonzero_Zp Zp_nonzero_def(1) 
    by presburger
  have P13: "v \<in> nonzero Z\<^sub>p"
    using P8 Units_def ord_of_nonzero(2) unit_imp_ord_Zp0 
    by (simp add: Units_def)
  have P14: "a = (frac (\<p>[^]m) (\<p>[^]n)) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (frac u v)"
    using P12 P13 P10 P9 P11 Q\<^sub>p_def frac_def frac_mult by metis 
  have P15: "m \<ge> n" 
  proof-
    have "ord_Zp c \<ge> ord_Zp d" 
      using P0 P1 P2 assms(3) ord_of_frac[of c d] 
      by (metis P3 P4 antisym eq_iff eq_iff_diff_eq_0 le_cases le_iff_diff_le_0 ord_Zp_def) 
    then show ?thesis 
      using P3 P4 by blast
  qed
  have P16: "n \<ge> 0" 
    using P2 P4 Z\<^sub>p_def  padic_integers_axioms Zp_nonzero_def(1) Zp_nonzero_def(2) ord_pos by blast
  have P17: "a = (frac (\<p>[^](m-n)) \<one>) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (frac u v)" 
    by (simp add: P14 P15 P16 local.inc_def  pow_p_frac_0)
  obtain w where P18: "w \<in> Units Z\<^sub>p" and P19: "\<iota> w = frac u v "
    using  Zp_division_Qp_1 P6 P8 by blast
  have P20: "w \<in> carrier Z\<^sub>p" 
    using P18 Units_def Units_nonzero_Zp Zp_nonzero_def(1) 
    by presburger
  have P21:  "a = \<iota> (\<p>[^](m-n)) \<otimes>\<^bsub>Q\<^sub>p\<^esub> \<iota> w" 
    by (simp add: P15 P17 P19 local.inc_def)
  have P22:  "a = (frac (\<p>[^](m-n)) \<one>) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (frac w \<one>)" 
    using P17 P19 P20 local.inc_def by auto
  have P23: "\<p>[^](m-n) \<in> carrier Z\<^sub>p" 
    by (simp add: P15)
  have P24: "a = (frac ((\<p>[^](m-n)) \<otimes> w) \<one>)" 
    using P20 P22 P23 frac_mult Zp_is_domain  
    by (metis Zp_one_nonzero i_mult local.inc_def)
  have P24:  "a = \<iota>((\<p>[^](m-n)) \<otimes> w)" 
    by (simp add: P20 P23 P24  cring.cring_simprules(5) domain.axioms(1) local.inc_def)
  then show ?thesis 
    by (meson P20 P23 Zp_is_domain cring.cring_simprules(5) domain.axioms(1) image_iff)
qed

lemma(in padic_integers) ord_of_inv:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "a \<noteq> \<zero>\<^bsub>Q\<^sub>p\<^esub>"
  shows "ord (inv\<^bsub>Q\<^sub>p\<^esub> a) = - (ord a)"
proof-
  obtain b c where 
   Frac: "a = frac b c" and 
   Car: "b \<in> carrier Z\<^sub>p" and 
   Nz_c: "c \<in> nonzero Z\<^sub>p"
      using Q\<^sub>p_def Zp_is_domain assms(1) domain.numer_denom_facts(1)
      domain.numer_denom_facts(2) domain.numer_denom_facts(5) 
      local.frac_def 
      by metis
    have Nz_b: "b \<in> nonzero Z\<^sub>p" 
      using Frac Car Nz_c  assms(2) nonzero_fraction_imp_nonzero_numer by metis 
    then have "(inv\<^bsub>Q\<^sub>p\<^esub> a) = frac c b" 
      using Frac Nz_c frac_inv by metis 
    then show ?thesis using Frac Nz_b Nz_c ord_of_frac[of b c] ord_of_frac[of c b]  
      by (simp add: nonzero_def ord_Zp_def)
  qed

lemma(in padic_integers) val_of_inv:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "a \<noteq> \<zero>\<^bsub>Q\<^sub>p\<^esub>"
  shows "val (inv\<^bsub>Q\<^sub>p\<^esub> a) = neg (val a)"
  by (simp add: assms(1) assms(2) g_uminus_minus inv_in_frac(2) ord_of_inv val_def)

(*Zp is a valuation ring in Qp*)

lemma(in padic_integers) Zp_mem:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "a \<in> \<O>\<^sub>p \<or> (inv\<^bsub>Q\<^sub>p\<^esub> a \<in> \<O>\<^sub>p)"
proof(cases "inv\<^bsub>Q\<^sub>p\<^esub>a \<in> \<O>\<^sub>p \<or> a = \<zero>\<^bsub>Q\<^sub>p\<^esub>")
  case True
  then show ?thesis 
    using Zp_is_subring subringE(2) by auto
next
  case False
  then have Nz: "a \<noteq> \<zero>\<^bsub>Q\<^sub>p\<^esub>" by auto 
  have "\<not> (ord a < 0)"
  proof
    assume "ord a < 0"
    then have "ord (inv\<^bsub>Q\<^sub>p\<^esub> a) >0" 
      by (simp add: assms(1) Nz ord_of_inv)
    then have 0: "ord (inv\<^bsub>Q\<^sub>p\<^esub> a) \<ge>0"
      by auto
    have 1: "(inv\<^bsub>Q\<^sub>p\<^esub> a) \<in> carrier Q\<^sub>p"
      by (simp add: assms(1) Nz inv_in_frac)
    have 2: "(inv\<^bsub>Q\<^sub>p\<^esub> a) \<noteq>\<zero>\<^bsub>Q\<^sub>p\<^esub>" 
      by (simp add: assms(1) Nz inv_in_frac(2))
    then have "(inv\<^bsub>Q\<^sub>p\<^esub> a) \<in> \<O>\<^sub>p" 
      using  Zp_ord_criterion  by (simp add: "0" "1")
    then show False 
      using False by blast
  qed
  then show ?thesis 
    using Zp_ord_criterion assms(1) Nz by auto
qed 

lemma(in padic_integers) Zp_val_criterion[simp]:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "val a \<succeq>\<^bsub>G\<^esub> \<zero>\<^bsub>G\<^esub>"
  shows "a \<in> \<O>\<^sub>p"
proof(cases "a = \<zero>\<^bsub>Q\<^sub>p\<^esub>")
  case True
  then show ?thesis 
    by (simp add: Zp_is_subring subringE(2))
next
  case False
  have " 0 \<le> ord a" 
    using False assms(1) G_ord(2)[of 0  "ord a"] assms(2) 
    by (metis gzero_id val_def)
  then show ?thesis 
    using False assms(1) Zp_ord_criterion[of a] by auto 
qed
   
(*Criterion for determining when an element in Qp is zero*)

lemma (in padic_integers) val_nonzero[simp]:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "s \<succ>\<^bsub>G\<^esub> val a"
  shows "a \<in> nonzero Q\<^sub>p"
proof-
  have "val a \<noteq> \<infinity>\<^bsub>G\<^esub>"
    by (metis assms(2) infinity_not_less)
  then show ?thesis 
    using assms 
    by (metis (mono_tags, hide_lams) local.val_zero  not_nonzero_Qp)
qed

(*function for division of a padic_integer by a power of n*)

definition(in padic_integers) divide where 
"divide a b = (if a = \<zero> then \<zero> else (THE c. c \<in> carrier Z\<^sub>p \<and> \<iota> c = frac a b))"

lemma(in padic_integers) divide_id[simp]:
assumes "a \<in> nonzero Z\<^sub>p"
assumes "b \<in> nonzero Z\<^sub>p"
assumes "ord_Zp a \<ge> ord_Zp b"
shows "divide a b \<in> carrier Z\<^sub>p"
      "(divide a b) \<otimes> b = a"
      "ord_Zp (divide a b) = ord_Zp a - ord_Zp b"
proof-
  have  "(frac a b) \<in> \<O>\<^sub>p"
    using frac_closed[of a b] assms ord_of_frac[of a b]
      Zp_ord_criterion[of "frac a b"] Zp_nonzero_def(1)
      nonzero_numer_imp_nonzero_fraction diff_ge_0_iff_ge local.frac_def 
    by (metis (mono_tags, hide_lams))
  then obtain c where c_def: "c \<in> carrier Z\<^sub>p \<and> \<iota> c = frac a b"
    by auto 
  obtain P where P_def: "P = (\<lambda>x. x \<in> carrier Z\<^sub>p \<and> \<iota> x = frac a b)"
    by simp 
  have 0: "(THE x. P x) = c"
  proof(rule the_equality)
    show "P c" using P_def c_def by auto 
    show " \<And>x. P x \<Longrightarrow> x = c" 
      using P_def domain.inc_inj2[of Z\<^sub>p _ c] Zp_is_domain  \<iota>_def c_def 
      by simp
  qed
  have 1: "c \<otimes> b = a"
  proof-
    have "frac (c \<otimes> b) a = (frac c \<one>) \<otimes>\<^bsub>Q\<^sub>p\<^esub> frac b a"
      using assms c_def  Zp_nonzero_def(1) i_mult local.inc_def by metis 
    then have "frac (c \<otimes> b) a = (frac a b) \<otimes>\<^bsub>Q\<^sub>p\<^esub> frac b a" 
      using c_def \<iota>_def local.inc_def by auto
    then have "frac (c \<otimes> b) a = \<one>\<^bsub>Q\<^sub>p\<^esub>" 
      using assms(1) assms(2) 
      by (simp add: \<open>a \<in> nonzero Z\<^sub>p\<close> \<open>b \<in> nonzero Z\<^sub>p\<close> Zp_nonzero_def(1)
          frac_cancel_lr frac_mult frac_one)
    then show ?thesis using assms c_def 
      by (metis Qp_one_notzero Zp_is_domain Zp_nonzero_def(1) cring.cring_simprules(5)
          domain.axioms(1) local.frac_eq nonzero_fraction_imp_nonzero_numer)
  qed
  have "a \<noteq>\<zero>"
    by (simp add: assms(1) Zp_nonzero_def(2))
  then have 2: "c = divide a b"
    using 0 P_def divide_def[of a b] by auto 
  show "divide a b \<in> carrier Z\<^sub>p" using c_def 2 by auto 
  show "divide a b \<otimes> b = a" using 1 2 by auto 
  show "ord_Zp (divide a b) = ord_Zp a - ord_Zp b"
  proof-
    have "divide a b \<in> nonzero Z\<^sub>p"
      using "1" "2" Zp_is_domain Zp_nonzero_def(1) \<open>a \<noteq> \<zero>\<close> assms(2)
        c_def domain.integral_iff not_nonzero_Zp by metis 
    then have "ord_Zp (divide a b) + ord_Zp b = ord_Zp a"
      by (metis "1" "2" assms(2) ord_Zp_mult)
    then show ?thesis 
      by linarith
  qed
qed

lemma(in padic_integers) divide_id'[simp]:
assumes "a \<in> carrier Z\<^sub>p"
assumes "b \<in> nonzero Z\<^sub>p"
assumes "val_Zp b \<preceq>\<^bsub>G\<^esub> val_Zp a"
shows "divide a b \<in> carrier Z\<^sub>p"
      "(divide a b) \<otimes> b = a"
      "val_Zp (divide a b) = val_Zp a \<ominus>\<^bsub>G\<^esub> val_Zp b"
proof-
  show C0: "(divide a b) \<otimes> b = a"
  proof(cases "a = \<zero>")
    case True
    have "divide a b = \<zero>" 
      by (simp add: True divide_def)
    then show ?thesis 
      by (simp add: True Zp_nonzero_def(1) assms(2) cring.cring_simprules(26) domain.axioms(1))
  next
    case False
    then have 0: "a \<in> nonzero Z\<^sub>p" 
      by (simp add: False assms(1) nonzero_def)
    have 1: "ord_Zp b \<le> ord_Zp a"  using 0 assms 
      by (metis G_ord(2) Zp_nonzero_def(2) ord_Zp_def val_Zp_def)
    then show ?thesis using divide_id assms 0 1 
      by blast 
  qed
  show C1: "divide a b \<in> carrier Z\<^sub>p"
  proof(cases "a = \<zero>")
    case True
    then have "divide a b = \<zero>"
      by (simp add: divide_def)
    then show ?thesis 
      using True assms(1) by auto
  next
    case False
    then have 0: "a \<in> nonzero Z\<^sub>p" 
      by (simp add: False assms(1) nonzero_def)
    have 1: "ord_Zp b \<le> ord_Zp a"  using 0 assms 
      by (metis G_ord(2) Zp_nonzero_def(2) ord_Zp_def val_Zp_def)
    then show ?thesis using divide_id assms 0 1 
      by blast
  qed
  show C2: "val_Zp (divide a b) = val_Zp a \<ominus>\<^bsub>G\<^esub> val_Zp b"
  proof-
    have "(divide a b) \<otimes> b = a \<otimes> \<one>"
      using Zp_is_domain Zp_one_car \<open>local.divide a b \<otimes> b = a\<close> assms(1) 
            cring.cring_simprules(12) cring.cring_simprules(14) domain.axioms(1) 
      by metis
    then have "(val_Zp (divide a b)) \<ominus>\<^bsub>G\<^esub> (val_Zp \<one>) = (val_Zp a) \<ominus>\<^bsub>G\<^esub>(val_Zp b)"
      using val_Zp_eq_frac_0 
      by (metis   Zp_one_nonzero \<open>local.divide a b \<in> carrier Z\<^sub>p\<close> \<open>local.divide a b \<otimes> b = a\<close>
          assms(1) assms(2) frac_cancel_r frac_cancel_rl  val_of_frac)
    then have 0: "(val_Zp (divide a b)) \<ominus>\<^bsub>G\<^esub> \<zero>\<^bsub>G\<^esub> = (val_Zp a) \<ominus>\<^bsub>G\<^esub>(val_Zp b)"
      using Z\<^sub>p_def Zp_one_car Zp_one_notzero gzero_id ord_Zp_one 
            padic_integers.val_ord_Zp padic_integers_axioms 
      by fastforce
    have "(val_Zp (divide a b)) \<ominus>\<^bsub>G\<^esub> \<zero>\<^bsub>G\<^esub> = (val_Zp (divide a b))"
    proof(cases "(divide a b) = \<zero>")
      case True
      then show ?thesis 
        by (simp add: val_Zp_def)
    next
      case False
      then show ?thesis 
        by (meson C1 gzero_simps(1) not_nonzero_Zp val_Zp_closed)
    qed
    then show ?thesis using 0  
      by metis 
  qed
qed

(*ord and val of negatives*)

lemma (in padic_integers) ord_minus:
  assumes "a \<in>  nonzero Q\<^sub>p"
  shows "ord a = ord (\<ominus>\<^bsub>Q\<^sub>p\<^esub>a)"
proof-
  have "\<ominus>\<^bsub>Q\<^sub>p\<^esub> a = \<ominus>\<^bsub>Q\<^sub>p\<^esub> (frac (numer a) (denom a))"
    using assms Qp_nonzero_def(1) numer_denom_facts(5) 
    by presburger
  then have "\<ominus>\<^bsub>Q\<^sub>p\<^esub> a = (frac (\<ominus> (numer a)) (denom a))"
    using Qp_nonzero_def(1) assms frac_uminus numer_denom_facts(1) numer_denom_facts(2) 
    by blast
  then show ?thesis 
    by (metis (no_types, lifting) Qp_is_domain Qp_nonzero_def(1) Zp_is_domain assms 
        cring.cring_simprules(21) cring.cring_simprules(22) cring.cring_simprules(3) 
        domain.axioms(1) nonzero_fraction_imp_nonzero_numer numer_denom_facts(1) 
        numer_denom_facts(2) ord_Zp_of_ominus ord_def ord_of_frac)
qed

lemma (in padic_integers) val_minus:
  assumes "a \<in>  carrier Q\<^sub>p"
  shows "val a = val (\<ominus>\<^bsub>Q\<^sub>p\<^esub>a)"
proof(cases "a = \<zero>\<^bsub>Q\<^sub>p\<^esub>")
  case True
  then show ?thesis 
    by (metis Qp_is_domain cring.cring_simprules(22) domain.axioms(1)) 
next
  case False
  then show ?thesis 
    by (metis Qp_is_domain assms cring.cring_simprules(21)
        cring.cring_simprules(22) domain.axioms(1) not_nonzero_Qp 
        ord_minus val_def) 
qed

(*Ultrametric inequality on Qp*)

lemma(in padic_integers) ord_ultrametric[simp]:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"
  assumes "x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y \<in> nonzero Q\<^sub>p"
  shows "ord (x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y) \<ge> min (ord x) (ord y)"
proof-
  have 0:"x \<in> carrier Q\<^sub>p" using assms by(simp add:nonzero_def)
  have 1:"y \<in>carrier Q\<^sub>p" using assms by(simp add:nonzero_def)
  obtain a b c where
   A: "a \<in> carrier Z\<^sub>p" and
   B: "b \<in> carrier Z\<^sub>p" and
   C: "c \<in> nonzero Z\<^sub>p" and
   Fx: "x = frac a c" and
   Fy: "y = frac b c" 
    using  0 1  get_common_denominator by blast
  have An: "a \<in> nonzero Z\<^sub>p" 
    using A C Fx assms(1) Qp_nonzero_def(2) nonzero_fraction_imp_nonzero_numer by metis 
  have Bn: " b \<in> nonzero Z\<^sub>p" 
    using B C Fy assms(2)  Qp_nonzero_def(2) nonzero_fraction_imp_nonzero_numer by metis 
  have Fxy: "x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y = frac (a \<oplus> b) c" using 0 1  
    by (simp add: A B C Fx Fy frac_add_common_denom)
  have ABn: " a \<oplus> b \<in> nonzero Z\<^sub>p" 
  proof-
    have "a \<oplus> b \<in> carrier Z\<^sub>p" 
      using A B Z\<^sub>p_def padic_add_closed prime by blast
    then show ?thesis 
      using Fxy C assms(3) Qp_nonzero_def(2) nonzero_fraction_imp_nonzero_numer 
      by (metis (mono_tags, hide_lams) local.frac_def not_nonzero_Zp)
  qed
  have Ordx: "ord x = ord_Zp a - ord_Zp c"
      using Fx An C ord_of_frac by metis 
  have Ordy: "ord y = ord_Zp b - ord_Zp c" 
    using Fy Bn C ord_of_frac by metis   
  have Ordxy: "ord (x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y) = ord_Zp (a \<oplus> b) - ord_Zp c"
    using Fxy ABn C ord_of_frac by metis   
  then show ?thesis
    using Ordx Ordy Ordxy ord_Zp_ultrametric[of a b] ABn An Bn 
    by linarith
qed

lemma(in padic_integers) ord_ultrametric'[simp]:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"
  assumes "x \<ominus> \<^bsub>Q\<^sub>p\<^esub> y \<in> nonzero Q\<^sub>p"
  shows "ord (x \<ominus> \<^bsub>Q\<^sub>p\<^esub> y) \<ge> min (ord x) (ord y)"
proof-
  have "ord y = ord (\<ominus>\<^bsub>Q\<^sub>p\<^esub>y)"
    using assms(2) ord_minus by blast
  then show ?thesis 
    using assms ord_ultrametric[of x "\<ominus>\<^bsub>Q\<^sub>p\<^esub>y"]
    unfolding a_minus_def 
    by (smt Qp_is_domain Qp_nonzero_def(1) cring.cring_simprules(16)
      cring.cring_simprules(3) domain.axioms(1) not_nonzero_Qp)
qed

lemma(in padic_integers) val_ultrametric0[simp]:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"
  assumes "x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y \<in> nonzero Q\<^sub>p"
  shows " Min\<^bsub>G\<^esub> (val x) (val y) \<preceq>\<^bsub>G\<^esub> val (x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y)  "
proof-
  have 0: "val (x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y) = *ord (x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y)*" 
    using assms(3) nonzero_def val_def[of "(x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y)"] by fastforce
  have 1: "val x = *ord x*" 
    using assms(1) nonzero_def val_def by force
  have 2: "val y = *ord y*" 
    using assms(2) nonzero_def val_def by force
  have 3: "ord (x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y) \<ge> min (ord x) (ord y)" 
    by (simp add: assms(1) assms(2) assms(3) )
  then show ?thesis 
    using  Min_min[of "ord x" "ord y"] 
           G_ord(2)[of "min (ord x) (ord y)" "ord (x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y)"]  
           0 1 2 3 
    by presburger 
qed

lemma(in padic_integers) val_ultrametric[simp]:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "y \<in> carrier Q\<^sub>p"
  shows " Min\<^bsub>G\<^esub> (val x) (val y) \<preceq>\<^bsub>G\<^esub> val (x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y)"
proof(cases "x = \<zero>\<^bsub>Q\<^sub>p\<^esub> \<or> y = \<zero>\<^bsub>Q\<^sub>p\<^esub>")
  case True
  then show ?thesis
  proof(cases "x = \<zero>\<^bsub>Q\<^sub>p\<^esub>")
    case True
    then have T0: "Min\<^bsub>G\<^esub> (val x) (val y) = (val y)" 
      by (simp add: G_def val_def) 
    have T1: "val (x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y) = val y"
      using True Qp_is_field  
      by (metis Qp_is_domain assms(2) cring.cring_simprules(8) domain.axioms(1))
    then show ?thesis 
      using T0 T1 G_def 
      by (metis (full_types) G_eq)
  next 
    case False 
    then have F0:" Min\<^bsub>G\<^esub> (val x) (val y) = (val x)" 
      using G_ord(1) True val_def 
      by (simp add: G_ord(1) val_def)
    have F1: "val (x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y) = val x"
      using False True Qp_is_field field_def assms(1) 
        cring.cring_simprules(16) domain.axioms(1) 
      by metis
    then show ?thesis 
      using F0 F1 G_eq 
      by presburger
  qed
next
  case False 
    have Px: "x \<in> nonzero Q\<^sub>p"
      using False assms(1)  
      by (metis (mono_tags, hide_lams) not_nonzero_Qp)
    have Py: "y \<in> nonzero Q\<^sub>p"
      using False assms(2)  
      by (metis (mono_tags, hide_lams) not_nonzero_Qp)
    show ?thesis
    proof(cases "x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y = \<zero>\<^bsub>Q\<^sub>p\<^esub>")
      case True
      then show ?thesis 
        using G_ord(1) local.val_zero by presburger
    next
      case False
      have Pxy: "x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y \<in> nonzero Q\<^sub>p" 
        by (simp add: False assms(1)  assms(2) cring.cring_simprules(1) fieldE(1) nonzero_def)
      then show ?thesis using Px Py val_ultrametric0 
        by blast
  qed
qed

lemma(in padic_integers) val_ultrametric'[simp]:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "y \<in> carrier Q\<^sub>p"
  shows " Min\<^bsub>G\<^esub> (val x) (val y) \<preceq>\<^bsub>G\<^esub> val (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> y)"
  using val_ultrametric[of x "\<ominus>\<^bsub>Q\<^sub>p\<^esub>y"]
        val_minus[of y]
        assms 
  by (metis Qp_is_domain a_minus_def cring.cring_simprules(3) domain.axioms(1))

(*Alternate versions of the triangle inequality*)

lemma(in padic_integers) ord_ultrametric_noteq[simp]:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"
  assumes "x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y \<in> nonzero Q\<^sub>p"
  assumes "ord x > ord y"
  shows "ord (x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y) = (ord y)"
proof(rule ccontr)
  assume "ord (x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y) \<noteq> ord y"
  then have 0: "ord (x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y) > ord y"
    using assms(1) assms(2) assms(3) assms(4) ord_ultrametric[of x y]
    by linarith
  have 1: "((y \<oplus>\<^bsub>Q\<^sub>p\<^esub> x) \<ominus>\<^bsub>Q\<^sub>p\<^esub> x) = y"
    by (metis (no_types, lifting) Qp_is_domain Qp_nonzero_def(1) a_minus_def assms(1) 
        assms(2) cring.cring_simprules(1) cring.cring_simprules(10) cring.cring_simprules(19)
        cring.cring_simprules(3) domain.axioms(1))
  have 2: "ord ((y \<oplus>\<^bsub>Q\<^sub>p\<^esub> x) \<ominus>\<^bsub>Q\<^sub>p\<^esub> x) \<ge> min (ord (y \<oplus>\<^bsub>Q\<^sub>p\<^esub> x)) (ord x) "
    using 1 assms ord_ultrametric'[of "(y \<oplus>\<^bsub>Q\<^sub>p\<^esub> x)" x] 
    by (metis Qp_is_domain Qp_nonzero_def(1) cring.cring_simprules(10) domain.axioms(1))
  have 3:  "ord y \<ge> min (ord x) (ord (x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y))"
    using 2 1 Q\<^sub>p_def Qp_is_domain Z\<^sub>p_def assms(1) assms(2) cring.cring_simprules(10) 
          domain.axioms(1) padic_integers.Qp_nonzero_def(1) padic_integers_axioms 
    by fastforce
  show False 
    using 3 0 assms 
    by linarith
qed

lemma(in padic_integers) ord_ultrametric_noteq'[simp]:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"
  assumes "x \<ominus>\<^bsub>Q\<^sub>p\<^esub> y \<in> nonzero Q\<^sub>p"
  assumes "ord x > ord y"
  shows "ord (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> y) = (ord y)"
  using assms ord_ultrametric_noteq[of x "\<ominus>\<^bsub>Q\<^sub>p\<^esub>y"]
  by (metis Qp_is_domain Qp_nonzero_def(1) a_minus_def cring.cring_simprules(21)
      cring.cring_simprules(22) cring.cring_simprules(3) domain.axioms(1) not_nonzero_Qp ord_minus)

lemma(in padic_integers) val_ultrametric_noteq[simp]:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "y \<in> carrier Q\<^sub>p"
  assumes "val x \<succ>\<^bsub>G\<^esub> val y"
  shows "val (x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y) = val y"
proof(cases "x = \<zero>\<^bsub>Q\<^sub>p\<^esub>")
  case True
  then show ?thesis 
    by (metis Qp_is_domain assms(2) cring.cring_simprules(8) domain.axioms(1))
next
  case False
  have F0: "y \<in> nonzero Q\<^sub>p"
    using False assms 
    by (meson val_nonzero)
  have F1: "x \<in> nonzero Q\<^sub>p"
    by (simp add: False assms(1) nonzero_def)
  have F2: "(x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y) \<in> nonzero Q\<^sub>p"
    by (metis (no_types, lifting) Qp_is_domain assms(1) assms(2) assms(3) cring.cring_simprules(1) 
        cring.cring_simprules(17) cring.cring_simprules(19) cring.cring_simprules(3) 
        domain.axioms(1) not_nonzero_Qp val_minus)
  then show ?thesis 
    using ord_ultrametric_noteq[of x y] F0 F1
    by (smt G_ord(2) assms(3) val_ord)
qed

lemma(in padic_integers) val_ultrametric_noteq'[simp]:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "y \<in> carrier Q\<^sub>p"
  assumes "val x \<succ>\<^bsub>G\<^esub> val y"
  shows "val (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> y) = val y"
  using assms       val_ultrametric_noteq[of x "\<ominus>\<^bsub>Q\<^sub>p\<^esub>y"]
  by (metis Qp_is_domain a_minus_def cring.cring_simprules(3) domain.axioms(1) val_minus)

(*useful simprules for reasoning about distances*)

lemma (in padic_integers) Qp_diff_diff:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "d \<in> carrier Q\<^sub>p"
  shows "(x \<ominus>\<^bsub>Q\<^sub>p\<^esub>c) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (d \<ominus>\<^bsub>Q\<^sub>p\<^esub>c) = x \<ominus>\<^bsub>Q\<^sub>p\<^esub> d "
  by (smt Qp_is_domain a_minus_def assms(1) assms(2) assms(3) cring.cring_simprules(10) 
      cring.cring_simprules(19) cring.cring_simprules(3) cring.cring_simprules(4) 
      cring.cring_simprules(7) domain.axioms(1))

(*"All triangles in Qp are isosceles"*)

lemma (in padic_integers) Qp_isosceles[simp]:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "d \<in> carrier Q\<^sub>p"
  assumes "val (x \<ominus>\<^bsub>Q\<^sub>p\<^esub>c) \<succeq>\<^bsub>G\<^esub> v"
  assumes "val (d \<ominus>\<^bsub>Q\<^sub>p\<^esub>c) \<succeq>\<^bsub>G\<^esub> v"
  shows "val (x \<ominus>\<^bsub>Q\<^sub>p\<^esub>d) \<succeq>\<^bsub>G\<^esub> v"
proof-
  have "val (x \<ominus>\<^bsub>Q\<^sub>p\<^esub>d) \<succeq>\<^bsub>G\<^esub> Min\<^bsub>G\<^esub> (val (x \<ominus>\<^bsub>Q\<^sub>p\<^esub>c)) (val (d \<ominus>\<^bsub>Q\<^sub>p\<^esub>c))"
    using assms Qp_diff_diff[of x c d]
    by (metis Qp_is_domain cring.cring_simprules(4) domain.axioms(1) val_ultrametric')
  then show ?thesis using assms 
    by (smt G_ord_trans)
qed

(*val and ord are multiplicative*)

lemma(in padic_integers) ord_mult[simp]:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"
  shows "(ord (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y)) = (ord x) + (ord y)"
proof-
  have 0:"x \<in> carrier Q\<^sub>p" using assms by(simp add:nonzero_def)
  have 1:"y \<in>carrier Q\<^sub>p" using assms by(simp add:nonzero_def)
  obtain a b c where
   A: "a \<in> carrier Z\<^sub>p" and
   B: "b \<in> carrier Z\<^sub>p" and
   C: "c \<in> nonzero Z\<^sub>p" and
   Fx: "x = frac a c" and
   Fy: "y = frac b c" 
    using get_common_denominator 0 1 by blast
  have An: "a \<in> nonzero Z\<^sub>p"
    using A C Fx assms(1) Qp_nonzero_def(2) nonzero_fraction_imp_nonzero_numer by blast
  have Bn: " b \<in> nonzero Z\<^sub>p" 
    using B C Fy assms(2) Qp_nonzero_def(2) nonzero_fraction_imp_nonzero_numer by blast
  have Fxy: "x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y = frac (a \<otimes> b) (c \<otimes>c)" 
    by (simp add: A B C Fx Fy frac_mult)
  have Cn: "c \<otimes>c \<in> nonzero Z\<^sub>p" 
    using C Localization.submonoid.m_closed Zp_is_domain domain.nonzero_is_submonoid 
    by metis
  have Ordxy0: "ord (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = ord_Zp (a \<otimes> b) - ord_Zp (c \<otimes>c)"
    by (metis An Bn Cn Fxy Localization.submonoid.m_closed Z\<^sub>p_def 
        domain.nonzero_is_submonoid ord_of_frac padic_integers.Zp_is_domain padic_integers_axioms)
  have Ordxy1: "ord (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = (ord_Zp a) + (ord_Zp b) - ((ord_Zp c) + (ord_Zp c))" 
    using  An Bn C Ordxy0 ord_Zp_mult 
    by presburger
  show ?thesis 
  proof-
    have "ord x + ord y = (ord_Zp a) - (ord_Zp c) + ((ord_Zp b) - (ord_Zp c))"
      using An Bn C Fx Fy ord_of_frac[of a c] ord_of_frac[of b c] by presburger 
    then show ?thesis 
      using Ordxy1 
      by presburger 
  qed
qed

lemma(in padic_integers) val_mult0[simp]:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"
  shows "(val (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y)) = (val x) \<oplus>\<^bsub>G\<^esub> (val y)"
proof-
  have 0: "(val x) = *(ord x)*" 
    using assms(1) val_ord by metis  
  have 1: "(val y) = *(ord y)*" 
    using assms(2) val_ord by metis   
  have "(x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) \<noteq> \<zero>\<^bsub>Q\<^sub>p\<^esub>"
    using Qp_is_field assms(1) assms(2) integral nonzero_def 
    by (smt mem_Collect_eq) 
  then have 2: "val (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = *ord (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y)*" 
    by (simp add:  val_def) 
  have 3: "(val x) \<otimes>\<^bsub>G\<^esub> (val y) = *(ord x) + (ord y)* "
    by (metis "0" "1" G_mult(3)) 
  have 4: "val (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = *ord  (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y)*" 
    using "2" by auto 
  then show ?thesis using 3 4 ord_mult assms nonzero_def 
    by (simp add: nonzero_def)   
qed  

(*val is multiplicative everywhere*)

lemma(in padic_integers) val_mult[simp]:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "y \<in> carrier Q\<^sub>p"
  shows "(val (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y)) = (val x) \<otimes>\<^bsub>G\<^esub> (val y)"
proof(cases "x = \<zero>\<^bsub>Q\<^sub>p\<^esub> \<or> y = \<zero>\<^bsub>Q\<^sub>p\<^esub>")
  case True
  then show ?thesis 
    using G_mult(1) G_mult(2) Qp_is_field assms(1) assms(2) 
      domain.integral_iff field.axioms(1) val_def 
    by (metis (no_types, lifting)) 
next
  case False
  have Px: "x \<in> nonzero Q\<^sub>p" 
    using False assms(1)  
    by (metis (mono_tags, hide_lams) not_nonzero_Qp) 
  have Py: "y \<in> nonzero Q\<^sub>p" 
    using False assms(2) 
    by (metis (mono_tags, hide_lams) not_nonzero_Qp) 
  then show ?thesis 
    by (simp add: Px)
qed

(*val and ord are compatible with \<iota>*)


lemma(in padic_integers) ord_of_inc:
assumes "x \<in> nonzero Z\<^sub>p"
shows "ord_Zp x = ord(\<iota> x)" 
proof-
  have "\<iota> x = frac x \<one>"
    using assms(1) Zp_nonzero_def(1) local.inc_def 
    by blast
  then have "ord ( \<iota> x) = ord_Zp x - ord_Zp \<one>"
    using assms(1) ord_of_frac Zp_one_nonzero 
    by presburger
  then show ?thesis
    using ord_Zp_one 
    by (simp add: ord_Zp_def)
qed

lemma(in padic_integers) val_of_inc:
assumes "x \<in> carrier Z\<^sub>p"
shows "val_Zp x = val (\<iota> x)" 
proof(cases "x \<in> nonzero Z\<^sub>p")
  case True
  then show ?thesis 
    using inc_of_nonzero nonzero_def ord_Zp_def ord_of_inc val_Zp_def val_ord 
    by (simp add: nonzero_def)
next
  case False
  then show ?thesis 
    by (metis (mono_tags, hide_lams) Zp_nat_mult_zero Zp_one_nonzero assms local.frac_def
        local.inc_def nonzero_fraction_imp_numer_not_zero not_nonzero_Zp val_Zp_def val_def)
qed

lemma(in padic_integers) Qp_inc_id:
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "ord a \<ge>0"
  obtains b where "b \<in> nonzero Z\<^sub>p" and "a = \<iota> b"
  using assms 
  by (smt Q\<^sub>p_def Qp_nonzero_def(2) Z\<^sub>p_def \<iota>_def imageE local.inc_def 
      nonzero_fraction_imp_nonzero_numer padic_integers.Qp_nonzero_def(1) 
      padic_integers.Zp_one_nonzero padic_integers.Zp_ord_criterion padic_integers_axioms)

(*ord and val on powers of p*)

lemma(in padic_integers) ord_p:
"ord \<pp> = 1"
  using p_nonzero ord_Zp_p ord_of_inc p_inc 
  by (metis (mono_tags, hide_lams) Zp_nat_inc_closed ord_of_nonzero(2) zero_le_one)

lemma(in padic_integers) ord_p_pow_nat:
"ord (\<pp> e (n::nat)) = n"
  using p_pow_nonzero ord_Zp_p ord_of_inc p_inc ord_Zp_p_pow p_natpow_inc 
  by presburger

lemma(in padic_integers) ord_p_pow_int:
"ord (\<pp> e (n::int)) = n"
proof(cases "n \<ge>0")
  case True
  then show ?thesis 
    by (metis int_nat_eq int_pow_int ord_p_pow_nat)
next
  case False
  then have Neg: "n <0" by auto 
  then have 0: "\<pp> e n = frac \<one> (\<p>[^](-n))" 
    using p_intpow by auto
  have "(\<p>[^](-n)) \<in> nonzero Z\<^sub>p"
    using False p_int_pow_nonzero 
    by (simp add: nonzero_def)
  then have "ord (\<pp> e (n::int)) = ord_Zp \<one> - ord_Zp (\<p>[^](-n))" 
    using "0" ord_of_frac Zp_one_nonzero 
    by presburger
  then have "ord (\<pp> e (n::int)) = - ord_Zp (\<p>[^](-n))" 
    using ord_Zp_one by linarith
  then have "ord (\<pp> e (n::int)) = -(-n)" 
    using Neg ord_Zp_p_int_pow 
    by (metis int.lless_eq neg_0_le_iff_le)
  then show ?thesis 
    by auto 
qed

lemma(in padic_integers) ord_nonneg:
  assumes "x \<in>  \<O>\<^sub>p"
  assumes "x \<noteq> \<zero>\<^bsub>Q\<^sub>p\<^esub>"
  shows "ord x \<ge>0"
proof-
  obtain a where A: "x = \<iota> a \<and> a \<in> carrier Z\<^sub>p" 
    using assms(1) by blast
  then have "a \<in> nonzero Z\<^sub>p" using assms(2) Zp_one_nonzero 
      local.inc_def nonzero_fraction_imp_numer_not_zero not_nonzero_Zp by blast
  then have "ord_Zp a \<ge>0" 
    using A Zp_nonzero_def(2) ord_pos by metis 
  then show ?thesis 
    using A \<open>a \<in> nonzero Z\<^sub>p\<close> ord_of_inc by metis 
qed

lemma(in padic_integers) val_p:
"(val \<pp>) = (1\<^sub>v)"
  by (simp add: ord_p  val_of_def)

(*The angular component function on Qp*)

definition(in padic_integers) angular_component where 
"angular_component a = (ac_Zp (numer a)) \<otimes>  (inv\<^bsub>Z\<^sub>p\<^esub> ac_Zp (denom a))"

lemma(in padic_integers) ac_fract:
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "a \<in> nonzero Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  assumes "c = frac a b"
  shows "angular_component c = (ac_Zp a)\<otimes> inv(ac_Zp b)"
proof-
  have "(numer c) \<otimes> b = (denom c) \<otimes> a"
    by (metis Q\<^sub>p_def Zp_is_domain Zp_nonzero_def(1) assms(1) assms(2) assms(3) assms(4) denom_def 
        domain.frac_eq domain.numer_denom_facts(1) domain.numer_denom_facts(2)
        domain.numer_denom_facts(5) local.frac_def numer_def)
  then have "ac_Zp ((numer c) \<otimes> b) = ac_Zp ((denom c) \<otimes> a)"
    by simp
  then have "(ac_Zp (numer c)) \<otimes> (ac_Zp b) = (ac_Zp (denom c)) \<otimes> (ac_Zp a)"
    by (metis Q\<^sub>p_def Zp_is_domain ac_Zp_mult assms(1) assms(2) assms(3) assms(4) 
        domain.numer_denom_facts(1) domain.numer_denom_facts(3) nonzero_numer_imp_nonzero_fraction 
        not_nonzero_Zp numer_def numer_denom_facts(2))
  then have "(inv (ac_Zp (denom c))) \<otimes> (ac_Zp (numer c)) \<otimes> (ac_Zp b) =  (ac_Zp a)"
    using ac_Zp_is_Unit[of "ac_Zp (denom c)"] Zp_is_domain inv_cancelR(1) 
    by (metis (no_types, lifting) Q\<^sub>p_def Units_nonzero_Zp Z\<^sub>p_def Zp_nonzero_def(1) Zp_nonzero_def(2)
       ac_Zp_is_Unit assms(1) assms(2) assms(3) assms(4) cring.cring_simprules(11) 
       cring.cring_simprules(5) denom_def domain.Units_inverse domain.axioms(1) 
       domain.numer_denom_facts(2) nonzero_numer_imp_nonzero_fraction 
       padic_integers.numer_denom_facts(1) padic_integers.numer_denom_facts(3) padic_integers_axioms)
  then have "(inv (ac_Zp (denom c))) \<otimes> (ac_Zp (numer c))  =  (ac_Zp a) \<otimes> inv (ac_Zp b)"
    using ac_Zp_is_Unit[of "ac_Zp b"] Zp_is_domain inv_cancelL(2) 
    by (metis Q\<^sub>p_def Units_nonzero_Zp Z\<^sub>p_def Zp_nonzero_def(1) Zp_nonzero_def(2) assms(1) 
        assms(2) assms(3) assms(4) cring.cring_simprules(5) domain.Units_inverse domain.axioms(1)
        nonzero_numer_imp_nonzero_fraction numer_denom_facts(2) numer_denom_facts(3)
        padic_integers.ac_Zp_is_Unit padic_integers.numer_denom_facts(1) padic_integers_axioms)
  then show ?thesis 
    by (metis Units_nonzero_Zp Zp_is_domain Zp_nonzero_def(1) Zp_nonzero_def(2) ac_Zp_is_Unit
        angular_component_def  assms(1) assms(2) assms(3) assms(4) cring.cring_simprules(14) domain.Units_inverse
        domain.axioms(1) nonzero_numer_imp_nonzero_fraction numer_denom_facts(1) 
        numer_denom_facts(2) numer_denom_facts(3))
qed


lemma(in padic_integers) angular_component_closed[simp]: 
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "angular_component a \<in> carrier Z\<^sub>p"
  by (metis Localization.submonoid.m_closed Q\<^sub>p_def Qp_nonzero_def(1) Qp_nonzero_def(2)
      Units_nonzero_Zp Z\<^sub>p_def Zp_is_domain Zp_nonzero_def(1) Zp_nonzero_def(2) 
      ac_Zp_is_Unit angular_component_def assms denom_def domain.nonzero_is_submonoid 
      domain.numer_denom_facts(2) domain.numer_denom_facts(3) numer_def numer_denom_facts(1)
      padic_integers.Units_inverse_Zp padic_integers_axioms)
 
lemma(in padic_integers) angular_component_unit[simp]: 
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "angular_component a \<in> Units Z\<^sub>p"
  by (smt Q\<^sub>p_def Qp_nonzero_def(1) Qp_nonzero_def(2) Units_nonzero_Zp Z\<^sub>p_def 
      Zp_is_domain Zp_nonzero_def(1) Zp_nonzero_def(2) angular_component_def
      assms cring.cring_simprules(5) domain.axioms(1) numer_denom_facts(2) 
      ord_Zp_0_imp_unit ord_Zp_mult padic_integers.Units_inverse_Zp 
      padic_integers.ac_Zp_is_Unit padic_integers.numer_denom_facts(1) 
      padic_integers.numer_denom_facts(3) padic_integers_axioms unit_imp_ord_Zp0)

lemma(in padic_integers) angular_component_factors_x:
  assumes "x \<in> nonzero Q\<^sub>p"
  shows "x = (\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>(ord x)) \<otimes>\<^bsub>Q\<^sub>p\<^esub> \<iota> (angular_component x)"
proof-
  have 0: "angular_component x = (ac_Zp (numer x)) \<otimes>  (inv\<^bsub>Z\<^sub>p\<^esub> ac_Zp (denom x))"
    by (simp add: angular_component_def)
  have 1:  "(numer x) = (\<p>[^](ord_Zp (numer x))) \<otimes> (ac_Zp (numer x))"
  proof-
    have "numer x \<in> nonzero Z\<^sub>p"
      by (metis Q\<^sub>p_def Qp_nonzero_def(2) Z\<^sub>p_def Zp_is_domain assms
          domain.numer_denom_facts(3) not_nonzero_Zp numer_def
          padic_integers.Qp_nonzero_def(1) padic_integers.numer_denom_facts(1)
          padic_integers_axioms)
    then show ?thesis using ac_Zp_factors_x[of "numer x"]
      by (metis Zp_nonzero_def(1) Zp_nonzero_def(2) int_pow_int ord_nat)
  qed
  have 2: "(denom x) = (\<p>[^](ord_Zp (denom x))) \<otimes> (ac_Zp (denom x))"
  proof-
    have "denom x \<in> nonzero Z\<^sub>p"
      using Qp_nonzero_def(1) assms numer_denom_facts(2) 
      by blast 
    then show ?thesis 
      using ac_Zp_factors_x[of "denom x"]
      by (metis Zp_nonzero_def(1) Zp_nonzero_def(2) int_pow_int ord_nat)
  qed
  have 3: "\<iota> (angular_component x) = frac (ac_Zp (numer x)) (ac_Zp (denom x))"
    by (metis "0" Q\<^sub>p_def Qp_nonzero_def(1) Qp_nonzero_def(2) Z\<^sub>p_def Zp_division_Qp_0 
        Zp_nonzero_def(1) Zp_nonzero_def(2) angular_component_closed assms local.inc_def 
        numer_denom_facts(1) numer_denom_facts(2) padic_integers.ac_Zp_is_Unit 
        padic_integers.numer_denom_facts(3) padic_integers_axioms)
  have 4: "(\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>((ord x))) \<otimes>\<^bsub>Q\<^sub>p\<^esub> \<iota> (angular_component x) = 
           (\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>((ord_Zp (numer x)) - (ord_Zp (denom x)))) \<otimes>\<^bsub>Q\<^sub>p\<^esub> frac (ac_Zp (numer x)) (ac_Zp (denom x))"
    using "3" ord_def by presburger
  have 5: "(\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>((ord x))) \<otimes>\<^bsub>Q\<^sub>p\<^esub> \<iota> (angular_component x) = 
           frac (\<p>[^]((ord_Zp (numer x)))) (\<p>[^] (ord_Zp (denom x))) \<otimes>\<^bsub>Q\<^sub>p\<^esub> frac (ac_Zp (numer x)) (ac_Zp (denom x))"
  proof-
    have "(\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>((ord_Zp (numer x)) - (ord_Zp (denom x)))) 
        =  frac (\<p>[^]((ord_Zp (numer x)))) (\<p>[^] (ord_Zp (denom x)))"
      using p_pow_diff[of "(ord_Zp (numer x))" "(ord_Zp (denom x))"] Qp_nonzero_def(1) 
            Qp_nonzero_def(2) Zp_nonzero_def(1) Zp_nonzero_def(2) 
            assms numer_denom_facts(1) numer_denom_facts(2) numer_denom_facts(3) ord_pos 
      by presburger
    then show ?thesis using 4 by metis 
  qed
  have 6: "(\<pp>[^]\<^bsub>Q\<^sub>p\<^esub>((ord x))) \<otimes>\<^bsub>Q\<^sub>p\<^esub> \<iota> (angular_component x) = 
           frac (\<p>[^]((ord_Zp (numer x))) \<otimes> (ac_Zp (numer x))) (\<p>[^] (ord_Zp (denom x)) \<otimes>  (ac_Zp (denom x)))"
    using 5 
    by (metis "2" Q\<^sub>p_def Qp_nonzero_def(1) Qp_nonzero_def(2) Z\<^sub>p_def Zp_is_domain Zp_nonzero_def(1)
        Zp_nonzero_def(2) assms domain.integral_iff frac_mult not_nonzero_Zp numer_denom_facts(1)
        numer_denom_facts(2) ord_pos p_int_pow_nonzero padic_integers.ac_Zp_in_Zp
        padic_integers.numer_denom_facts(3) padic_integers_axioms)
  then show ?thesis 
    using "1" "2" Qp_nonzero_def(1) assms numer_denom_facts(5) 
    by presburger
qed

lemma(in padic_integers) angular_component_mult:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"
  shows "angular_component (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = (angular_component  x) \<otimes> (angular_component  y)"
proof-
  obtain a b where "a = numer x" and
                   "b = denom x" and 
                   a_nz: "a \<in> nonzero Z\<^sub>p" and
                   b_nz: "b \<in> nonzero Z\<^sub>p" and
                   x_frac: "x = frac a b"
    by (metis Q\<^sub>p_def Qp_nonzero_def(1) Qp_nonzero_def(2) Z\<^sub>p_def assms(1) 
         not_nonzero_Zp numer_denom_facts(1) numer_denom_facts(3) numer_denom_facts(5)
         padic_integers.numer_denom_facts(2) padic_integers_axioms)

  obtain c d where "c = numer y" and
                   "d = denom y" and 
                   c_nz: "c \<in> nonzero Z\<^sub>p" and
                   d_nz: "d \<in> nonzero Z\<^sub>p" and 
                   y_frac: "y = frac c d"
    by (metis Q\<^sub>p_def Qp_nonzero_def(1) Qp_nonzero_def(2) Z\<^sub>p_def assms(2) not_nonzero_Zp
        numer_denom_facts(1) numer_denom_facts(3) numer_denom_facts(5) 
        padic_integers.numer_denom_facts(2) padic_integers_axioms)
  have 0: "(x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = frac (a \<otimes> c) (b \<otimes> d)"
    by (simp add: Zp_nonzero_def(1) a_nz b_nz c_nz d_nz frac_mult x_frac y_frac)
  have 1: "angular_component (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = (ac_Zp (a \<otimes> c)) \<otimes> inv (ac_Zp (b \<otimes> d))"
    by (metis (mono_tags, hide_lams) "0" Localization.submonoid.m_closed Qp_is_domain 
        Qp_nonzero_def(1) Zp_is_domain a_nz ac_fract assms(1) assms(2) b_nz c_nz 
        cring.cring_simprules(5) d_nz domain.nonzero_is_submonoid domain_def)
  have 2: "angular_component (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = (ac_Zp a) \<otimes> (ac_Zp c) \<otimes> inv ((ac_Zp b) \<otimes> (ac_Zp d))"
    by (simp add: "1" a_nz ac_Zp_mult b_nz c_nz d_nz)
  have 3: "angular_component (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = (ac_Zp a) \<otimes> (ac_Zp c) \<otimes> inv (ac_Zp b) \<otimes> inv (ac_Zp d)"
    by (metis (no_types, lifting) "1" Units_nonzero_Zp Z\<^sub>p_def Zp_is_comm_monoid 
        Zp_is_domain Zp_nonzero_def(1) Zp_nonzero_def(2) a_nz ac_Zp_mult b_nz c_nz
        cring.cring_simprules(11) cring.cring_simprules(5) d_nz domain.axioms(1)
        inv_of_prod padic_integers.Units_inverse_Zp padic_integers.ac_Zp_is_Unit 
        padic_integers_axioms)
  have 4: "angular_component (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = (ac_Zp a) \<otimes>  inv (ac_Zp b) \<otimes>  (ac_Zp c) \<otimes> inv (ac_Zp d)"
    by (smt "3" Units_inverse_Zp Units_nonzero_Zp Zp_is_comm_monoid Zp_nonzero_def(1) 
        Zp_nonzero_def(2) a_nz ac_Zp_is_Unit b_nz c_nz comm_monoid.m_ac(1) comm_monoid.m_comm)
  have 5: "angular_component (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = ((ac_Zp a) \<otimes>  inv (ac_Zp b)) \<otimes> ( (ac_Zp c) \<otimes> inv (ac_Zp d))"
    using 4 
    by (metis Units_nonzero_Zp Z\<^sub>p_def Zp_is_domain Zp_nonzero_def(1) Zp_nonzero_def(2) 
        a_nz ac_fract angular_component_closed assms(1) b_nz c_nz cring.cring_simprules(11)
        d_nz domain.axioms(1) frac_closed padic_integers.Units_inverse_Zp 
        padic_integers.ac_Zp_is_Unit padic_integers_axioms x_frac)
  then show ?thesis 
    by (simp add: Z\<^sub>p_def \<open>a = numer x\<close> \<open>b = denom x\<close> \<open>c = numer y\<close> \<open>d = denom y\<close>
        padic_integers.angular_component_def padic_integers_axioms)
qed

lemma(in padic_integers) angular_component_inv:
  assumes "x \<in> nonzero Q\<^sub>p"
  shows "angular_component (inv\<^bsub>Q\<^sub>p\<^esub> x) = inv\<^bsub>Z\<^sub>p\<^esub> (angular_component x)"
  by (metis Qp_is_field Qp_nonzero_def(1) Qp_nonzero_def(2) Qp_one_car Zp_is_domain 
      Zp_one_car Zp_one_nonzero ac_Zp_one ac_fract angular_component_closed 
      angular_component_mult assms cring.cring_simprules(12) domain.axioms(1)
      field.field_inv(1) inc_of_one invI(2) inv_in_frac(3) local.inc_def)


lemma(in padic_integers) angular_component_one: 
"angular_component \<one>\<^bsub>Q\<^sub>p\<^esub> = \<one>"
  by (metis Qp_one_car Zp_is_comm_monoid Zp_is_domain Zp_one_car Zp_one_nonzero 
      ac_Zp_one ac_fract comm_monoid.comm_inv_char cring.cring_simprules(12) 
      domain.axioms(1) inc_of_one local.inc_def)

lemma(in padic_integers) angular_component_ord_zero:
  assumes "ord x = 0"
  assumes "x \<in> nonzero Q\<^sub>p"
  shows "\<iota> (angular_component x) = x"
proof-
  have 0: "ord x \<ge>0"
    using assms by auto 
  have 1: "x \<in> nonzero Q\<^sub>p"
  proof-
    have "x \<noteq> \<zero>\<^bsub>Q\<^sub>p\<^esub>"
      using Qp_nonzero_def(2) assms(2) by blast
    then show ?thesis 
      by (simp add: assms(2))
  qed
  obtain a where a_def: "a \<in> nonzero Z\<^sub>p \<and> \<iota> a = x"
    using 0 1 assms Qp_inc_id[of x] 
    by metis
  then have "x = frac a \<one>"
    using local.inc_def Zp_nonzero_def(1) 
    by blast
  then have "angular_component x = ac_Zp a \<otimes> inv (ac_Zp \<one>)"
    using ac_fract[of x a \<one>]  "1" Qp_nonzero_def(1) Zp_one_nonzero a_def
    by blast
  then have "angular_component x = ac_Zp a \<otimes> inv \<one>"
    by (simp add: ac_Zp_one)
  then have "angular_component x = ac_Zp a \<otimes> \<one>"
    by (metis Units_nonzero_Zp Zp_is_domain Zp_nonzero_def(1) 
        Zp_one_car cring.cring_simprules(12) domain.Units_inverse
        domain.axioms(1) inv_cancelL(1) ord_Zp_0_imp_unit ord_Zp_one)
  then show ?thesis 
    by (metis (mono_tags, hide_lams) "1" Zp_division_Qp_0 Zp_nonzero_def(1) Zp_one_car 
        \<open>angular_component x = ac_Zp a \<otimes> inv \<one>\<close> \<open>x = local.frac a \<one>\<close> a_def ac_Zp_of_Unit
        angular_component_closed assms(1)  local.inc_def
        ord_Zp_0_imp_unit ord_Zp_one ord_of_inc)
qed


lemma(in padic_integers) res_uminus:
  assumes "k > 0"
  assumes "f \<in> carrier Z\<^sub>p"
  assumes "c \<in> carrier (R k)"
  assumes "c = \<ominus>\<^bsub>R k\<^esub> (f k)"
  shows "c = ((\<ominus> f) k)"
  using Z\<^sub>p_def assms(2) assms(4)  padic_inv prime by auto

(*
lemma(in padic_integers) val_p_pow_nat:
"val (\<pp> e (n::int)) = *n*"
proof-
  have 
  using ord_p_pow_int val_ord p_pow_nonzero  sledgehammer
 *)
end