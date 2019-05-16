theory Zp_poly
imports "~~/src/HOL/Algebra/UnivPoly" padic_sequences
begin



context padic_integers
begin

type_synonym padic_int_poly = "nat \<Rightarrow> padic_int"


lemma monom_term_car:
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "x \<in> carrier Z\<^sub>p"
  shows "c \<otimes> x[^](n::nat) \<in> carrier Z\<^sub>p"
  using assms Zp_is_cring monoid.nat_pow_closed 
  by (simp add: monoid.nat_pow_closed cring.cring_simprules(5) cring_def ring_def)


definition Zp_x where
"Zp_x = UP Z\<^sub>p"


lemma Zp_x_is_UP_ring:
"UP_ring Z\<^sub>p"
  by (metis UP_ring.intro Zp_is_cring cring_def)

definition degree:: "padic_int_poly \<Rightarrow> nat" where
"degree f =  deg Z\<^sub>p f"

definition cf :: "padic_int_poly \<Rightarrow> nat \<Rightarrow> padic_int" where
"cf  = coeff Zp_x "

lemma cf_f:
  assumes "f \<in> carrier Zp_x"
  shows "cf f = f"
proof-
  have "cf = (\<lambda>f \<in> up Z\<^sub>p. f)"
    using cf_def Zp_x_def  by (simp add: UP_def)
  then show ?thesis using assms Zp_x_def by (simp add: UP_def) 
qed

lemma coeff_simp0:
  assumes "f \<in> carrier Zp_x"
  shows "coeff Zp_x  f = f "
  using assms  cf_f cf_def by auto  

lemma coeff_simp1:
  assumes "f \<in> carrier Zp_x"
  shows "coeff (UP Z\<^sub>p)  f = f "
  using coeff_simp0  Zp_x_def assms by auto

lemma Zp_x_fact0:
  assumes "f \<in> carrier Zp_x"
  shows "f n \<in> carrier Z\<^sub>p"
proof-
  have "coeff Zp_x f n \<in> carrier Z\<^sub>p"
    using assms Zp_x_def by (simp add: UP.coeff_closed)
  then show ?thesis 
    using assms coeff_simp0 by auto  
qed

definition lt  where
"lt f = monom Zp_x (f (degree f)) (degree f)"

lemma lt_in_car:
  assumes "f \<in> carrier Zp_x"
  shows "lt f \<in> carrier Zp_x"
  unfolding lt_def
  using UP_ring.monom_closed Zp_x_is_UP_ring  UP.coeff_closed 
    UP_ring.monom_closed Zp_x_def Zp_x_is_UP_ring assms cf_def cf_f by fastforce 

lemma lt_coeffs0:
  assumes "f \<in> carrier Zp_x"
  shows "coeff Zp_x (lt f) n  = (if (n = degree f) then (f (degree f)) else \<zero>)"
    unfolding lt_def
    apply(simp add: UP_ring.coeff_monom)
    using UP_ring.coeff_monom UP_ring.lcoeff_closed Zp_x_def Zp_x_is_UP_ring
      assms cf_def cf_f degree_def by fastforce

lemma lt_coeffs:
  assumes "f \<in> carrier Zp_x"
  shows "(lt f) n  = (if (n = degree f) then (f (degree f)) else \<zero>)"
proof-
  have "coeff Zp_x (lt f) n  = (if (n = degree f) then (f (degree f)) else \<zero>)"
    using assms lt_coeffs0 by blast
  then have "cf (lt f) n  = (if (n = degree f) then (f (degree f)) else \<zero>)"
    unfolding cf_def by auto 
  then show ?thesis 
    by (simp add: assms cf_f lt_in_car)
qed

lemma lt_coeff_above:
  assumes "f \<in> carrier Zp_x"
  assumes "n > degree f"
  shows "lt f n = \<zero>"
proof-
  have "coeff Zp_x  (lt f) n = (if (n = degree f) then (f (degree f)) else \<zero>)"
    using lt_coeffs0 assms by auto 
  then have "coeff Zp_x  (lt f) n = \<zero>"
    using assms(2) by auto 
  then have "cf (lt f) n = \<zero>"
    unfolding cf_def by auto 
  then show ?thesis
    using cf_f assms lt_in_car by simp
qed

lemma degree_leading_term:
  assumes "f \<in> carrier Zp_x"
  shows "degree (lt f) = degree f"
  using UP_ring.deg_monom 
  by (metis UP_ring.deg_zero_impl_monom UP_ring.lcoeff_closed
      UP_ring.lcoeff_nonzero_deg Zp_x_def Zp_x_is_UP_ring assms cf_def cf_f degree_def lt_def)



lemma leading_term_decomp0:
  assumes "f \<in> carrier Zp_x"
  assumes "degree f = Suc n"
  shows "degree (f \<ominus>\<^bsub>Zp_x\<^esub> (lt f)) \<le> n"
  unfolding degree_def
proof(rule UP_ring.deg_aboveI)
  show C0: "UP_ring Z\<^sub>p" 
    by (simp add: Zp_x_is_UP_ring)
  show C1: "f \<ominus>\<^bsub>Zp_x\<^esub> lt f \<in> carrier (UP Z\<^sub>p)"
    using assms lt_in_car 
    by (simp add: UP_ring.UP_ring Zp_x_def Zp_x_is_UP_ring ring.ring_simprules(4))
  show C2: "\<And>m. n < m \<Longrightarrow> coeff (UP Z\<^sub>p) (f \<ominus>\<^bsub>Zp_x\<^esub> lt f) m = \<zero>"
  proof-
    fix m
    assume A: "n<m"
    show "coeff (UP Z\<^sub>p) (f \<ominus>\<^bsub>Zp_x\<^esub> lt f) m = \<zero>"
      apply(auto  simp: Zp_x_def)
    proof(cases " m = Suc n")
      case True
      have B: "f m \<in> carrier Z\<^sub>p" 
        using UP.coeff_closed Zp_x_def assms(1) cf_def cf_f by fastforce
      have "m = degree f"
        using True by (simp add: assms(2))
      then have "f m = (lt f) m" 
        using lt_coeffs assms(1) by auto 
      then have "(f m) \<ominus>\<^bsub>Z\<^sub>p\<^esub>( lt f) m = \<zero>"
        using Zp_is_cring B UP_ring_def Zp_x_is_UP_ring ring.r_right_minus_eq by fastforce
      then have "(f \<ominus>\<^bsub>UP Z\<^sub>p\<^esub> lt f) m = \<zero>"
        using  UP_ring.coeff_minus coeff_simp1 
        by (metis C1 Zp_x_def Zp_x_is_UP_ring assms(1) lt_in_car)
      then show "coeff (UP Z\<^sub>p) (f \<ominus>\<^bsub>UP Z\<^sub>p\<^esub> lt f) m = \<zero>" 
        using coeff_simp1 
        using C1 Zp_x_def by auto
    next
      case False
      have D0: "m > degree f" using False 
        using A assms(2) by linarith
       have B: "f m \<in> carrier Z\<^sub>p" 
        using UP.coeff_closed Zp_x_def assms(1) cf_def cf_f by fastforce
      have "f m = (lt f) m" 
      proof-
        have "coeff (UP Z\<^sub>p) f m = \<zero>" 
          using D0  degree_def[of f] 
            Zp_x_is_UP_ring assms(1) UP_ring.deg_aboveD[of Z\<^sub>p f m]  
          by (simp add: Zp_x_def)
        then have 0: "f m = \<zero>" 
          using assms coeff_simp1 by auto 
        have "(lt f) m = \<zero>" 
          using D0 assms(1) lt_coeff_above by auto  
        then show ?thesis using 0 by auto 
      then have "(f m) \<ominus>\<^bsub>Z\<^sub>p\<^esub>( lt f) m = \<zero>"
        using Zp_is_cring B UP_ring_def Zp_x_is_UP_ring ring.r_right_minus_eq by fastforce
      then have "(f \<ominus>\<^bsub>UP Z\<^sub>p\<^esub> lt f) m = \<zero>"
        using  UP_ring.coeff_minus coeff_simp1 
        by (metis C1 Zp_x_def Zp_x_is_UP_ring assms(1) lt_in_car)
    qed
      then show "coeff (UP Z\<^sub>p) (f \<ominus>\<^bsub>UP Z\<^sub>p\<^esub> lt f) m = \<zero>" 
        using coeff_simp1  C1 Zp_x_def 
        by (metis B UP_ring.coeff_minus UP_ring_def
            Zp_x_is_UP_ring assms(1) lt_in_car ring.r_right_minus_eq)
    qed
  qed
qed

lemma leading_term_decomp:
  assumes "f \<in> carrier Zp_x"
  assumes "degree f >(0::nat)"
  obtains g where "g \<in> carrier Zp_x \<and> f = g \<oplus>\<^bsub>Zp_x\<^esub> (lt f) \<and> degree g < degree f"
proof-
  obtain k where k_def: "Suc k = degree f" 
    using assms  by (metis gr0_implies_Suc)
  obtain g where g_def: "g = (f \<ominus>\<^bsub>Zp_x\<^esub> (lt f))" 
    by simp
  have 0:  "degree g \<le> k"
    using assms leading_term_decomp0 k_def g_def by auto  
  have 1: "g \<in> carrier Zp_x" 
    using assms g_def lt_in_car 
    by (simp add: UP_ring.UP_ring Zp_x_def Zp_x_is_UP_ring ring.ring_simprules(4))
  have 2: "f = g \<oplus>\<^bsub>Zp_x\<^esub> (lt f)" 
  proof-
    have P0: "ring Zp_x" 
      using Zp_x_is_UP_ring UP_ring.UP_ring Zp_x_def by auto   
    have P1: " g \<oplus>\<^bsub>Zp_x\<^esub> (lt f) = (f \<ominus>\<^bsub>Zp_x\<^esub> (lt f)) \<oplus>\<^bsub>Zp_x\<^esub> (lt f)" 
      using g_def by auto 
    have P2: " g \<oplus>\<^bsub>Zp_x\<^esub> (lt f) = (f \<oplus>\<^bsub>Zp_x\<^esub> ((\<ominus>\<^bsub>Zp_x\<^esub> (lt f)) \<oplus>\<^bsub>Zp_x\<^esub> (lt f)))"    
      by (simp add: P0 a_minus_def assms(1) g_def lt_in_car ring.ring_simprules(3)
          ring.ring_simprules(7))
    then show ?thesis 
      using assms(1) lt_in_car[of f] 1 P0 
      by (metis (no_types, lifting) ring.ring_simprules(10) 
          ring.ring_simprules(18) ring.ring_simprules(3) ring.ring_simprules(7))
  qed
  show ?thesis 
    using 0 1 2 k_def  that by fastforce
qed

definition fun_of :: "_ \<Rightarrow> padic_int_fun" where
"fun_of f  = (\<lambda>s .eval Z\<^sub>p Z\<^sub>p (\<lambda>x. x) s f)"

lemma fun_of_formula:
  assumes "f \<in> carrier Zp_x"
  assumes "x \<in> carrier Z\<^sub>p"
  shows "fun_of f x = (\<Oplus>i \<in> {..degree f}. (cf f i) \<otimes> x [^] i)"
proof-
  have "f \<in> carrier (UP Z\<^sub>p)"
    using assms Zp_x_def by auto 
  then  have "eval Z\<^sub>p Z\<^sub>p (\<lambda>x. x) x f =  (\<Oplus>\<^bsub>Z\<^sub>p\<^esub>i\<in>{..deg Z\<^sub>p f}. (\<lambda>x. x) (coeff (UP Z\<^sub>p) f i) \<otimes>\<^bsub>Z\<^sub>p\<^esub> x [^]\<^bsub>Z\<^sub>p\<^esub> i)"
    apply(simp add:UnivPoly.eval_def) done
  then have "fun_of f x = (\<Oplus>\<^bsub>Z\<^sub>p\<^esub>i\<in>{..deg Z\<^sub>p f}. (\<lambda>x. x) (coeff (UP Z\<^sub>p) f i) \<otimes>\<^bsub>Z\<^sub>p\<^esub> x [^]\<^bsub>Z\<^sub>p\<^esub> i)"
    using fun_of_def assms by simp
  then show ?thesis using cf_def by (simp add: degree_def Zp_x_def)
qed

lemma fun_of_formula':
  assumes "f \<in> carrier Zp_x"
  assumes "x \<in> carrier Z\<^sub>p"
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
  by (simp add: UP_cring_def Zp_is_cring id_is_hom)

lemma fun_of_fun_sum:
  assumes "f \<in> carrier Zp_x"
  assumes "g \<in> carrier Zp_x"
  assumes "h = f \<oplus>\<^bsub>Zp_x\<^esub> g"
  shows "fun_sum (fun_of f) (fun_of g) \<doteq> fun_of h" 
  unfolding eq_on_Zp_def
  apply(auto)
proof-
  fix x
  assume A: "x \<in> carrier Z\<^sub>p"
  show "fun_sum (fun_of f) (fun_of g) x = fun_of h x "
    unfolding fun_sum_def
    unfolding fun_of_def
  proof-
    have "(eval Z\<^sub>p Z\<^sub>p (\<lambda>x. x)) x \<in> (ring_hom Zp_x Z\<^sub>p)"
      using UP_pre_univ_prop_fact A UP_pre_univ_prop.eval_ring_hom[of Z\<^sub>p Z\<^sub>p "(\<lambda>x. x)" x]  Zp_x_def by auto   
    then show "eval Z\<^sub>p Z\<^sub>p (\<lambda>x. x) x f \<oplus> eval Z\<^sub>p Z\<^sub>p (\<lambda>x. x) x g = eval Z\<^sub>p Z\<^sub>p (\<lambda>x. x) x h "
      using assms ring_hom_add by fastforce
  qed
qed

lemma fun_of_monom:
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "c \<noteq>\<zero>"
  assumes "x \<in> carrier Z\<^sub>p"
  shows "fun_of (monom Zp_x c (n::nat)) x = c \<otimes> x [^] n"
proof-
  have 0: "(monom Zp_x c n) \<in> carrier Zp_x "
    using Zp_x_def UP_ring.intro UP_ring.monom_closed Zp_is_cring assms cring_def by fastforce
  then have 1: "fun_of (monom Zp_x c n) x =  (\<Oplus>i \<in> {..degree (monom Zp_x c n) }. (cf (monom Zp_x c n)  i) \<otimes> x [^] i)"
    using assms fun_of_formula by simp 
  have 2: "\<And>i. (cf (monom Zp_x c n)  i) = (if i=n then c else \<zero>)" 
  proof-
    fix i
    show "(cf (monom Zp_x c n)  i) = (if i=n then c else \<zero>)" 
    proof-
      have 0: "cf (monom Zp_x c n) = (monom Zp_x c n)" 
        using 0 cf_f by auto 
      have "monom Zp_x = (\<lambda>a\<in>(carrier Z\<^sub>p). \<lambda>n i. if i = n then a else \<zero>)"
        by (simp add: UP_def Zp_x_def)
      then have "monom Zp_x c = (\<lambda>n i. if i = n then c else \<zero>)"
        using assms by auto 
      then show ?thesis 
        using 0 by auto 
    qed
  qed
  have 3: "degree (monom Zp_x c n) = n" 
    using degree_def assms Zp_x_is_UP_ring Zp_x_def by (simp add: UP_ring.deg_monom)
  then have 4: "fun_of (monom Zp_x c n) x =  (\<Oplus>i \<in> {..n}. (cf (monom Zp_x c n)  i) \<otimes> x [^] i)"
    using 1 by auto
  then have 5: "fun_of (monom Zp_x c n) x =  (\<Oplus>i \<in> {..n}. (if i=n then c else \<zero>) \<otimes> x [^] i)"
    using 2 by auto 
  show ?thesis 
  proof(cases "n=0")
    case True
    then have A0: "fun_of (monom Zp_x c n) x = (\<Oplus>i \<in> {(0::nat)}. (if i=n then c else \<zero>) \<otimes> x [^] i)"
      using 5  by simp
    have A1:"abelian_monoid Z\<^sub>p" 
      using Zp_is_cring abelian_group_def cring_def ring_def by blast
    have "\<And>i.( (cf (monom Zp_x c n)  i) \<otimes> x [^] i) \<in> carrier Z\<^sub>p"
    proof-
      fix i
      have P0: "(cf (monom Zp_x c n)  i) \<in> carrier Z\<^sub>p" 
        using assms  "2" Zp_is_cring cring.cring_simprules(2) by auto
      have P1: " (x [^] i) \<in> carrier Z\<^sub>p" 
        using assms Zp_is_cring monoid.nat_pow_closed  by (metis cring.axioms(1) ring_def)
      show "( (cf (monom Zp_x c n)  i) \<otimes> x [^] i) \<in> carrier Z\<^sub>p"
        using assms P0 P1 Zp_is_cring   by (simp add: cring.cring_simprules(5))
    qed
    then have A2: "(\<lambda>i. (cf (monom Zp_x c n)  i) \<otimes> x [^] i) \<in> ({0::nat} \<rightarrow> carrier Z\<^sub>p)" 
      by simp 
    have A3: "(\<Oplus>i \<in> {0}.  (cf (monom Zp_x c n) i) \<otimes> x [^] i) = finsum Z\<^sub>p (\<lambda>i. (cf (monom Zp_x c n)  i) \<otimes> x [^] i) {..0}"
      by simp
    have "finsum Z\<^sub>p (\<lambda>i. (cf (monom Zp_x c n)  i) \<otimes> x [^] i) {..0} = (\<lambda>i. (cf (monom Zp_x c n)  i) \<otimes> x [^] i) 0"
      using A1 A2 abelian_monoid.finsum_0  by blast
    then have A4: "(\<Oplus>i \<in> {0}.  (cf (monom Zp_x c n) i) \<otimes> x [^] i) = (\<lambda>i. (cf (monom Zp_x c n)  i) \<otimes> x [^] i) 0"
      using A3  True by auto
    have "(\<lambda>i. (cf (monom Zp_x c n)  i) \<otimes> x [^] i) (0::nat) = (cf (monom Zp_x c n)  (0::nat)) \<otimes> x [^] (0::nat)"
      by auto
    then have "(\<Oplus>i \<in> {0::nat}.  (cf (monom Zp_x c n) i) \<otimes> x [^] i) =(cf (monom Zp_x c n) ( 0::nat)) \<otimes> x [^] (0::nat)"
      using A4  by blast
    then show ?thesis using A0  "2" True by auto
  next
    case False
    then obtain k where k_def: "n = Suc k" 
      by (meson lessI less_Suc_eq_0_disj)
    have A0: "abelian_monoid Z\<^sub>p" 
      using Zp_is_cring abelian_group_def cring_def ring_def by auto
    have A1: "(\<lambda>i. (if i=n then c else \<zero>) \<otimes> x [^] i) \<in> ({..Suc k} \<rightarrow> (carrier Z\<^sub>p))"
    proof 
      fix a
      assume "a \<in> {..Suc k}"  
      show "(if a = n then c else \<zero>) \<otimes> x [^] a \<in> carrier Z\<^sub>p"
      proof-
        have P0: "(if a = n then c else \<zero>) \<in> carrier Z\<^sub>p"
          by (simp add: A0 abelian_monoid.zero_closed assms(1))
        have P1: " x [^] a \<in> carrier Z\<^sub>p" 
          by (meson Zp_is_cring assms(3) cring_def monoid.nat_pow_closed ring_def)
        show ?thesis using P0 P1 
          by (simp add: Zp_is_cring cring.cring_simprules(5))
      qed
    qed
    obtain g where g_def: "g = (\<lambda>i. (if i=n then c else \<zero>) \<otimes> x [^] i)"
      by simp
    have "g \<in>  ({..Suc k} \<rightarrow> (carrier Z\<^sub>p))" 
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
          have B1: "x [^] (i::nat) \<in> carrier Z\<^sub>p" 
            using Zp_is_cring assms(3)   by (simp add: monoid.nat_pow_closed cring_def ring_def)
          then show " g i=\<zero>" 
            using B0 B1  by (simp add: Zp_is_cring cring.cring_simprules(26)) 
        qed
      qed
      then show ?thesis 
        using  A0 abelian_monoid.finsum_cong'[of Z\<^sub>p "{..k}" "{..k}" "(\<lambda>i. \<zero>)" g ]    
        by (simp add: abelian_monoid.zero_closed finsum_def)
    qed
    then have "(\<Oplus>(i::nat) \<in> {..Suc k}. g i) = (g (Suc k)) \<oplus> \<zero>" 
      using A0 A2 abelian_monoid.finsum_zero[of Z\<^sub>p "{..k}"] by auto  
    then have "(\<Oplus>(i::nat) \<in> {..Suc k}. g i) = (g (Suc k))" 
      by (metis A0 PiE Suc_le_eq \<open>g \<in> {..Suc k} \<rightarrow> carrier Z\<^sub>p\<close> abelian_monoid.r_zero atMost_iff lessI)
    then show ?thesis using 5 k_def g_def  by simp
  qed
qed

lemma fun_of_monom_is_monom0:
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "c \<noteq>\<zero>"
  assumes "f = monom Zp_x c n"
  assumes "x \<in> carrier Z\<^sub>p"
  shows "fun_of f x = mon c n x"
proof-
  have 1: "fun_of f x = c \<otimes> x [^] n"
    using fun_of_monom assms by auto
  show ?thesis
    unfolding mon_def scalar_mult_def X_pow_Zp_def
    apply auto 
    apply (metis "1" Zp_is_cring cring.axioms(1) monoid.nat_pow_0 ring_def)
    using 1  by simp
qed

lemma fun_of_monom_is_monom:
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "f = monom Zp_x c n"
  shows "fun_of f \<doteq> mon c n"
proof(cases "c = \<zero>")
  case True
  have H: "f = (\<lambda> i. \<zero>)"
    apply(auto simp: assms(2))
    unfolding Zp_x_def
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
    by (simp add: UP_ring.monom_closed Zp_x_def Zp_x_is_UP_ring assms(1) assms(2) cf_f)
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
      have C2: "f \<in> carrier Zp_x"
        apply(auto simp: assms(2))
        unfolding Zp_x_def
        using assms(1) Zp_x_is_UP_ring UP_ring.monom_closed[of Z\<^sub>p c n] apply simp
        done
      have C3: "fun_of f x = (\<Oplus>i \<in> {..degree f}. (cf f i) \<otimes> x [^] i)" 
        using  A  C2 fun_of_formula by auto 
      show ?thesis 
        apply(auto simp: C3 H1 )
        apply(auto simp: H)
        apply(auto simp: C1)
        apply(auto simp: C0 abelian_monoid.finsum_zero)
        done
    qed
    show "fun_of f x = c \<otimes> (if n = 0 then \<one> else x [^] n) "
      apply(auto simp: P0)
       apply (simp add: True Zp_is_cring Zp_one_car cring.cring_simprules(26))
      using A assms(1) monom_term_car[of c x] 
      by (metis True Zp_is_cring cring.cring_simprules(26)
          cring_def monoid.nat_pow_closed ring_def)
  qed
next
  case False
  then show ?thesis 
    unfolding eq_on_Zp_def
    apply(auto)
    by (simp add: assms(1) assms(2) fun_of_monom_is_monom0)
qed

lemma monom_poly_is_continuous:
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "f = monom Zp_x c n"
  shows "is_continuous (fun_of f)"
proof-
  have 0: "is_continuous (mon c n)"
    unfolding mon_def using assms(1) 
    by (simp add: X_pow_Zp_is_continuous scalar_mult_is_continuous)
  have 1: "fun_of f \<doteq> mon c n" 
    by (simp add: assms(1) assms(2) fun_of_monom_is_monom)
  show ?thesis using 0 1 is_continuous_eq eq_on_Zp_def by auto
qed

lemma degree_0_imp_constant0:
  assumes "f \<in> carrier Zp_x"
  assumes "degree f = 0"
  obtains c where "c \<in> carrier Z\<^sub>p" and  "\<And>x.  x \<in> carrier Z\<^sub>p \<Longrightarrow> (fun_of f) x = c"
proof-
  obtain c where c_def: "c = f 0"
    by simp
  have 0: "c \<in> carrier Z\<^sub>p" using c_def assms(1) 
    by (simp add: Zp_x_fact0)
  have 1:  "\<And>x.  x \<in> carrier Z\<^sub>p \<Longrightarrow> (fun_of f) x = c"
  proof-
    fix x
    assume A: "x \<in> carrier Z\<^sub>p"
    have ab: "abelian_monoid Z\<^sub>p" 
      using Zp_is_cring  by (simp add: abelian_group_def cring_def ring_def)
    have d: "(\<lambda>i. f i \<otimes> x [^] i) \<in> {0::nat} \<rightarrow> carrier Z\<^sub>p "
    proof
      fix a
      assume "a \<in> {0::nat}"
      show "((f a) \<otimes> (x[^] a)) \<in> carrier Z\<^sub>p"
        by (simp add: A Zp_x_fact0 assms(1) monom_term_car)
    qed
    have "(fun_of f) x = (\<Oplus>i\<in>{..degree f}. f i \<otimes> x [^] i)"
      using fun_of_formula' assms A by auto 
    then have P0: "(fun_of f) x = (\<Oplus>i\<in>{..0}. f i \<otimes> x [^] i)"
      by(simp add: assms)
    have "(\<Oplus>i\<in>{..0}. f i \<otimes> x [^] i) =  f 0 \<otimes> x [^] (0::nat)" 
      using ab d abelian_monoid.finsum_0[of Z\<^sub>p "(\<lambda>i::nat. f i \<otimes> x [^] i)"] by auto  
    then have "(fun_of f) x = f 0 \<otimes> x [^] (0::nat)" 
      using P0   by simp
    then have P1: "(fun_of f) x = c\<otimes> x [^] (0::nat)" 
      by(simp add: c_def)
    then have "(fun_of f) x = c\<otimes> \<one>" 
    proof-
      have "\<one> =  x [^] (0::nat)"  
        using A Zp_is_cring  by (simp add: monoid.nat_pow_0 cring_def ring_def)
      then show ?thesis using P1  by simp
    qed
    then show "(fun_of f) x = c" using Zp_is_cring 
      using "0" Zp_one_car cring.cring_simprules(12) cring.cring_simprules(14) by fastforce
  qed
  then show ?thesis 
    using 0 1 that by auto
qed

lemma degree_0_imp_constant1:
  assumes "f \<in> carrier Zp_x"
  assumes "degree f = 0"
  obtains g where "is_constant_fun g" and "g \<doteq> fun_of f"
proof- 
  obtain c where c0: "c \<in> carrier Z\<^sub>p" and  c1: "\<And>x.  x \<in> carrier Z\<^sub>p \<Longrightarrow> (fun_of f) x = c"
    using degree_0_imp_constant0  assms(1) assms(2) by blast
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

lemma degree_0_imp_continuous:
  assumes "f \<in> carrier Zp_x"
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

lemma polynomial_is_continuous0:
  fixes n::nat
  shows "\<And>f. f \<in> carrier Zp_x \<Longrightarrow> degree f \<le> n \<Longrightarrow> is_continuous (fun_of f)"
proof(induction n)
case 0
  then show ?case 
    using degree_0_imp_continuous by blast
next
  case (Suc n)
  fix n
  assume IH: "\<And>f. f \<in> carrier Zp_x \<Longrightarrow> (degree f \<le> n \<Longrightarrow> is_continuous (fun_of f))"
  show "\<And>f. f \<in> carrier Zp_x \<Longrightarrow> degree f \<le> Suc n \<Longrightarrow> is_continuous (fun_of f) "
  proof-
    fix f
    assume A0:"f \<in> carrier Zp_x"
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
      obtain g where g_def: "g \<in> carrier Zp_x \<and> f = g \<oplus>\<^bsub>Zp_x\<^esub> (lt f) \<and> degree g < degree f"
        using E0 A0 leading_term_decomp[of f]  by blast
      have g0: "g \<in> carrier Zp_x"
        using g_def by auto 
      have g1: "f = g \<oplus>\<^bsub>Zp_x\<^esub> (lt f)" 
        using g_def by auto 
      have g2: "degree g < degree f" 
        using g_def by auto 
      have LS: "is_continuous (fun_of g)" 
        using E g0 g1 g2 IH by auto 
      have RS: "is_continuous (fun_of (lt f))"
        using monom_poly_is_continuous lt_def A0  UP_ring.lcoeff_closed
          Zp_x_def Zp_x_is_UP_ring coeff_simp1 degree_def by fastforce
      have "fun_of f \<doteq>  fun_sum (fun_of g) (fun_of (lt f))"
        using  fun_of_fun_sum g0 A0 g1  eq_on_Zp_def lt_in_car by auto
      then show ?thesis
        using LS RS sum_of_cont_is_cont 
        by (metis eq_on_Zp_def is_continuous_eq)
    qed
  qed
qed

lemma polynomial_is_continuous:
  assumes "f \<in> carrier Zp_x"
  shows "is_continuous (fun_of f)"
proof-
  obtain n where n_def: "n = degree f" 
    by simp
  then show ?thesis 
    using assms polynomial_is_continuous0 by auto 
qed


end
end