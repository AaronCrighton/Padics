theory cring_poly
imports "~~/src/HOL/Algebra/UnivPoly" 
begin


context UP_cring
begin

lemma monom_term_car:
  assumes "c \<in> carrier R"
  assumes "x \<in> carrier R"
  shows "c \<otimes> x[^](n::nat) \<in> carrier R"
  using assms monoid.nat_pow_closed 
  by blast

(*Univariate polynomial ring over R*)



lemma P_is_UP_ring:
"UP_ring R"
  by (simp add: UP_ring_axioms)

(*Degree function*)
definition degree  where
"degree f =  deg R f"

(*Coefficient function*)
definition cf  where
"cf  = coeff P "

(*This function is redundant*)
lemma cf_f:
  assumes "f \<in> carrier P"
  shows "cf f = f"
proof-
  have "cf = (\<lambda>f \<in> up R. f)"
    using cf_def P_def  by (simp add: UP_def)
  then show ?thesis using assms P_def by (simp add: UP_def) 
qed

(*So is coeff from UNIVPOLY*)
lemma coeff_simp0:
  assumes "f \<in> carrier P"
  shows "coeff P  f = f "
  using assms  cf_f cf_def by auto  

lemma coeff_simp1:
  assumes "f \<in> carrier P"
  shows "coeff (UP R)  f = f "
  using coeff_simp0  P_def assms by auto

(*Coefficients are in R*)
lemma P_fact0:
  assumes "f \<in> carrier P"
  shows "f n \<in> carrier R"
proof-
  have "coeff P f n \<in> carrier R"
    using assms P_def by (simp add: UP.coeff_closed)
  then show ?thesis 
    using assms coeff_simp0 by auto  
qed

(*Leading term function*)
definition lt  where
"lt f = monom P (f (degree f)) (degree f)"

(*leading term is a polynomial*)
lemma lt_in_car:
  assumes "f \<in> carrier P"
  shows "lt f \<in> carrier P"
  unfolding lt_def
  using UP_ring.monom_closed P_is_UP_ring  UP.coeff_closed 
    UP_ring.monom_closed P_def P_is_UP_ring assms cf_def cf_f by fastforce 

(*Simplified coefficient function description for leading term*)
lemma lt_coeffs0:
  assumes "f \<in> carrier P"
  shows "coeff P (lt f) n  = (if (n = degree f) then (f (degree f)) else \<zero>)"
    unfolding lt_def
    apply(simp add: UP_ring.coeff_monom)
    using UP_ring.coeff_monom UP_ring.lcoeff_closed P_def P_is_UP_ring
      assms cf_def cf_f degree_def by fastforce

lemma lt_coeffs:
  assumes "f \<in> carrier P"
  shows "(lt f) n  = (if (n = degree f) then (f (degree f)) else \<zero>)"
proof-
  have "coeff P (lt f) n  = (if (n = degree f) then (f (degree f)) else \<zero>)"
    using assms lt_coeffs0 by blast
  then have "cf (lt f) n  = (if (n = degree f) then (f (degree f)) else \<zero>)"
    unfolding cf_def by auto 
  then show ?thesis 
    by (simp add: assms cf_f lt_in_car)
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
    unfolding cf_def by auto 
  then show ?thesis
    using cf_f assms lt_in_car by simp
qed

(*leading term of f has the same degree as f*)
lemma degree_leading_term:
  assumes "f \<in> carrier P"
  shows "degree (lt f) = degree f"
  using UP_ring.deg_monom 
  by (metis UP_ring.deg_zero_impl_monom UP_ring.lcoeff_closed
      UP_ring.lcoeff_nonzero_deg P_def P_is_UP_ring assms cf_def cf_f degree_def lt_def)


(*f minus its leading term has smaller degree*)
lemma leading_term_decomp0:
  assumes "f \<in> carrier P"
  assumes "degree f = Suc n"
  shows "degree (f \<ominus>\<^bsub>P\<^esub> (lt f)) \<le> n"
  unfolding degree_def
proof(rule UP_ring.deg_aboveI)
  show C0: "UP_ring R" 
    by (simp add: P_is_UP_ring)
  show C1: "f \<ominus>\<^bsub>P\<^esub> lt f \<in> carrier (UP R)"
    using assms lt_in_car 
    by (simp add: UP_ring.UP_ring P_def P_is_UP_ring ring.ring_simprules(4))
  show C2: "\<And>m. n < m \<Longrightarrow> coeff (UP R) (f \<ominus>\<^bsub>P\<^esub> lt f) m = \<zero>"
  proof-
    fix m
    assume A: "n<m"
    show "coeff (UP R) (f \<ominus>\<^bsub>P\<^esub> lt f) m = \<zero>"
      apply(auto  simp: P_def)
    proof(cases " m = Suc n")
      case True
      have B: "f m \<in> carrier R" 
        using UP.coeff_closed P_def assms(1) cf_def cf_f by fastforce
      have "m = degree f"
        using True by (simp add: assms(2))
      then have "f m = (lt f) m" 
        using lt_coeffs assms(1) by auto 
      then have "(f m) \<ominus>\<^bsub>R\<^esub>( lt f) m = \<zero>"
        using B UP_ring_def P_is_UP_ring 
          B R.add.r_inv R.is_abelian_group abelian_group.minus_eq by fastforce
      then have "(f \<ominus>\<^bsub>UP R\<^esub> lt f) m = \<zero>"
        using  UP_ring.coeff_minus coeff_simp1 
        by (metis C1 P_def P_is_UP_ring assms(1) lt_in_car)
      then show "coeff (UP R) (f \<ominus>\<^bsub>UP R\<^esub> lt f) m = \<zero>" 
        using coeff_simp1 
        using C1 P_def by auto
    next
      case False
      have D0: "m > degree f" using False 
        using A assms(2) by linarith
       have B: "f m \<in> carrier R" 
        using UP.coeff_closed P_def assms(1) cf_def cf_f by fastforce
      have "f m = (lt f) m" 
      proof-
        have "coeff (UP R) f m = \<zero>" 
          using D0  degree_def[of f] 
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
        by (metis C1 P_def P_is_UP_ring assms(1) lt_in_car)
    qed
      then show "coeff (UP R) (f \<ominus>\<^bsub>UP R\<^esub> lt f) m = \<zero>" 
        using coeff_simp1  C1 P_def 
        by (metis B D0 P_is_UP_ring R.is_abelian_group UP_cring.lt_in_car UP_cring_axioms 
            UP_cring_def UP_ring.coeff_minus abelian_group.minus_eq assms(1)
            cring.cring_simprules(22) cring.cring_simprules(8) lt_coeff_above)
    qed
  qed
qed

lemma leading_term_decomp:
  assumes "f \<in> carrier P"
  assumes "degree f >(0::nat)"
  obtains g where "g \<in> carrier P \<and> f = g \<oplus>\<^bsub>P\<^esub> (lt f) \<and> degree g < degree f"
proof-
  obtain k where k_def: "Suc k = degree f" 
    using assms  by (metis gr0_implies_Suc)
  obtain g where g_def: "g = (f \<ominus>\<^bsub>P\<^esub> (lt f))" 
    by simp
  have 0:  "degree g \<le> k"
    using assms leading_term_decomp0 k_def g_def by auto  
  have 1: "g \<in> carrier P" 
    using assms g_def lt_in_car 
    by (simp add: UP_ring.UP_ring P_def P_is_UP_ring ring.ring_simprules(4))
  have 2: "f = g \<oplus>\<^bsub>P\<^esub> (lt f)" 
  proof-
    have P0: "ring P" 
      using P_is_UP_ring UP_ring.UP_ring P_def by auto   
    have P1: " g \<oplus>\<^bsub>P\<^esub> (lt f) = (f \<ominus>\<^bsub>P\<^esub> (lt f)) \<oplus>\<^bsub>P\<^esub> (lt f)" 
      using g_def by auto 
    have P2: " g \<oplus>\<^bsub>P\<^esub> (lt f) = (f \<oplus>\<^bsub>P\<^esub> ((\<ominus>\<^bsub>P\<^esub> (lt f)) \<oplus>\<^bsub>P\<^esub> (lt f)))"    
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

(*Turning a polynomial into a function on R*)

definition eq_on_car (infixl "\<sim>" 70) where
"eq_on_car f g = (\<forall>x. x \<in> carrier R \<longrightarrow> f x = g x)"

lemma eq_on_car_simp:
  assumes "f \<sim> g"
  assumes "x \<in> carrier R"
  shows "f x = g x"
  using eq_on_car_def assms by blast 

definition fun_sum where
"fun_sum f g = (\<lambda>x. (f x) \<oplus> (g x))"

definition fun_prod where
"fun_prod f g = (\<lambda>x. (f x) \<otimes> (g x))"

(*Turning a polynomial into a function on R*)
definition fun_of  where
"fun_of f  = (\<lambda>s .eval R R (\<lambda>x. x) s f)"

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
    using fun_of_def assms by simp
  then show ?thesis using cf_def by (simp add: degree_def P_def)
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

(*P addition commutes with evaluation addition*)
lemma fun_of_fun_sum:
  assumes "f \<in> carrier P"
  assumes "g \<in> carrier P"
  assumes "h = f \<oplus>\<^bsub>P\<^esub> g"
  shows "fun_sum (fun_of f) (fun_of g) \<sim> fun_of h" 
  unfolding eq_on_car_def
  apply(auto)
proof-
  fix x
  assume A: "x \<in> carrier R"
  show "fun_sum (fun_of f) (fun_of g) x = fun_of h x "
    unfolding fun_sum_def
    unfolding fun_of_def
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
    using degree_def assms P_is_UP_ring P_def by (simp add: UP_ring.deg_monom)
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



end
end