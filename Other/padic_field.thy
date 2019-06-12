theory padic_field
  imports padic_construction
          Localization
          Extended_OAG
          extended_int
          fraction_field
          "~~/src/HOL/Algebra/Subrings"
          "HOL-Number_Theory.Residues"
          "HOL-Algebra.Multiplicative_Group"
begin

locale padic_integers =
fixes Z\<^sub>p:: "_ ring" (structure)
fixes Q\<^sub>p:: "_ ring" (structure)
fixes p
fixes G (structure)
fixes \<iota>
defines "G \<equiv> int_eoag"
defines "Z\<^sub>p \<equiv> padic_int p"
defines "Q\<^sub>p \<equiv> domain.Frac Z\<^sub>p"
defines "\<iota> \<equiv> domain.inc Z\<^sub>p"
assumes prime: "prime p"

(*************************************************************************************************)
(*************************************************************************************************)

section \<open>Notation and Facts About the Value Group\<close>

(*************************************************************************************************)
(*************************************************************************************************) 

lemma(in padic_integers) G_EOAG:
"extended_ordered_abelian_group G"
  using G_def int_eoag_is_eoag by blast

lemma(in padic_integers) G_is_comm_group:
"comm_group G" 
  using G_EOAG extended_ordered_abelian_group_def 
   comm_group.axioms(2) ordered_abelian_group.ab by blast

lemma(in padic_integers) G_is_group:
"group G" 
  by (simp add: G_is_comm_group comm_group.axioms(2))

abbreviation(in padic_integers) val_geq (infixl "\<succeq>\<^bsub>G\<^esub>" 50) where
"(val_geq a b) \<equiv> (b \<preceq>\<^bsub>G\<^esub> a)"

abbreviation(in padic_integers) val_gr (infixl "\<succ>\<^bsub>G\<^esub>" 70) where 
"val_gr a b \<equiv> (b \<preceq>\<^bsub>G\<^esub> a) \<and> b \<noteq> a"

abbreviation(in padic_integers) val_le (infixl "\<prec>\<^bsub>G\<^esub>" 70) where 
"val_le a b \<equiv> (a \<preceq>\<^bsub>G\<^esub> b) \<and> b \<noteq> a"

lemma(in padic_integers) G_mult[simp]:
"\<infinity>\<^bsub>G\<^esub> \<otimes>\<^bsub>G\<^esub> x  = \<infinity>\<^bsub>G\<^esub>"
"x \<otimes>\<^bsub>G\<^esub> \<infinity>\<^bsub>G\<^esub>  = \<infinity>\<^bsub>G\<^esub>"
"(Some a) \<otimes>\<^bsub>G\<^esub> (Some b) = Some (a + b)"
apply (metis G_def extended_mult.elims extended_mult.simps(3) 
          extended_ordered_monoid.select_convs(1) monoid.select_convs(1))
   apply (metis G_def extended_mult.elims extended_ordered_monoid.select_convs(1)
           monoid.select_convs(1) option.distinct(1)) 
      using extended_mult.simps(4)[of _ a b ] 
      by (simp add: G_def) 
 
text{*Additive notation for the value group*}

abbreviation(in padic_integers) gplus (infixl "\<oplus>\<^bsub>G\<^esub>" 65) where
"gplus x y \<equiv> x \<otimes>\<^bsub>G\<^esub> y"

abbreviation(in padic_integers) gminus (infixl "\<ominus>\<^bsub>G\<^esub>" 65) where
"gminus x y \<equiv> x \<oplus>\<^bsub>G\<^esub> (inv\<^bsub>G\<^esub> y)"

abbreviation(in padic_integers) g_uminus ("neg") where
"g_uminus y \<equiv>  (inv\<^bsub>G\<^esub> y)"

abbreviation(in padic_integers) gzero ("\<zero>\<^bsub>G\<^esub>") where
"gzero \<equiv> \<one>\<^bsub>G\<^esub>"

text{*Notation for int options*}

abbreviation(in padic_integers) int_val:: "int \<Rightarrow> int option" ("*_*") where
"int_val n \<equiv> Some n"

lemma(in padic_integers) gplus_plus:
"*n* \<oplus>\<^bsub>G\<^esub> *m* = *n+m*" 
  by simp

lemma (in padic_integers) gplus_comm:
"a \<oplus>\<^bsub>G\<^esub> b = b \<oplus>\<^bsub>G\<^esub> a"
proof(cases "a = \<infinity>\<^bsub>G\<^esub> \<or> b = \<infinity>\<^bsub>G\<^esub>")
  case True
  then show ?thesis 
    by auto
next
  case False
  then show ?thesis 
    using G_def by auto
qed

lemma(in padic_integers) gzero_id:
"\<zero>\<^bsub>G\<^esub> = *0*"
  by (simp add: G_def)

lemma(in padic_integers) gminus_minus:
"*n* \<ominus>\<^bsub>G\<^esub> *m* =  *n-m*"
proof-
  have "*-m* = inv\<^bsub>G\<^esub> *m*" 
  proof- 
     have "Some (-m) \<oplus>\<^bsub>G\<^esub> (Some m) = \<zero>\<^bsub>G\<^esub>"       
       by (simp add: gplus_plus gzero_id)
     then show ?thesis 
       by (metis G_def G_is_group UNIV_I group.inv_equality image_eqI partial_object.select_convs(1)) 
   qed
  then show ?thesis 
     by (metis diff_conv_add_uminus gplus_plus)
 qed

lemma(in padic_integers) g_uminus_minus:
"neg (Some n) = *-n*"
  using G_def G_is_group G_mult(3) add.left_inverse group.inv_equality 
  by fastforce

lemma(in padic_integers) G_ord:
"x \<preceq>\<^bsub>G\<^esub> \<infinity>\<^bsub>G\<^esub>"
"((Some a) \<preceq>\<^bsub>G\<^esub> (Some b)) \<longleftrightarrow> (a \<le> b)"
  using G_def extended_order.elims(3) apply auto[1] 
  by (simp add: G_def) 

lemma(in padic_integers) G_ord_trans[simp]:
"x \<preceq>\<^bsub>G\<^esub> y \<and> y \<preceq>\<^bsub>G\<^esub> w \<Longrightarrow> x \<preceq>\<^bsub>G\<^esub>w"
proof(cases "w = \<infinity>\<^bsub>G\<^esub>")
  case True
  then show ?thesis 
    by (simp add: G_ord(1))
next
  case False
  assume A: "x \<preceq>\<^bsub>G\<^esub> y \<and> y \<preceq>\<^bsub>G\<^esub> w"
  show " x \<preceq>\<^bsub>G\<^esub>w"
  proof-
  obtain w0 where w0_def: "w = *w0*"
    using False G_def by auto
  obtain x0 where x0_def: "x = *x0*"
    by (metis A False G_def extended_order.elims(2)
        extended_ordered_monoid.simps(1) ordered_monoid.select_convs(1))
  obtain y0 where y0_def: "y = *y0*"
    using A False G_def by fastforce
  show ?thesis using A w0_def x0_def y0_def 
    by (simp add: G_def)
  qed
qed

lemma(in padic_integers) G_eq[simp]:
  assumes "x = y"
  shows "x \<succeq>\<^bsub>G\<^esub> y"
  using G_def assms extended_order.elims(3) by fastforce

lemma(in padic_integers) Min_min[simp]:
"Min\<^bsub>G\<^esub> (Some n) (Some m) = *(min n m)*"
  by (metis G_ord(2) le_cases min.absorb2 min.commute)

lemma(in padic_integers) gzero_simps[simp]:
  assumes "a \<in> carrier G"
  shows "a \<ominus>\<^bsub>G\<^esub> \<zero>\<^bsub>G\<^esub> = a"
        "a \<oplus>\<^bsub>G\<^esub> \<zero>\<^bsub>G\<^esub> = a"
        "\<zero>\<^bsub>G\<^esub> \<ominus>\<^bsub>G\<^esub> a = neg a"
        "\<zero>\<^bsub>G\<^esub> \<oplus>\<^bsub>G\<^esub> a = a" 
  using G_is_comm_group G_is_group assms comm_groupE(2) g_uminus_minus group.l_cancel_one gzero_id
  apply fastforce
  using G_is_comm_group G_is_group assms comm_groupE(2) group.l_cancel_one' 
  apply fastforce
  apply (simp add: G_is_comm_group G_is_group assms comm_groupE(5))
  by (simp add: G_is_comm_group assms comm_groupE(5))

lemma(in padic_integers) gord_minus:
assumes "a \<succeq>\<^bsub>G\<^esub> b"
assumes "c \<noteq> \<infinity>\<^bsub>G\<^esub>"
shows "a \<ominus>\<^bsub>G\<^esub>c \<succeq>\<^bsub>G\<^esub> b \<ominus>\<^bsub>G\<^esub> c"
proof(cases "a = \<infinity>\<^bsub>G\<^esub>")
  case True
  then show ?thesis 
    by (simp add:  G_ord(1))
next
  case False
  obtain a0 where a0_def: "a = *a0*"
    using False G_def by auto
  obtain b0 where b0_def: "b = *b0*"
    using False G_def  assms(1) by fastforce
  obtain c0 where c0_def: "c = *c0*"
    using assms G_def by auto
  show ?thesis using a0_def b0_def c0_def assms 
    using G_EOAG G_def G_is_comm_group G_is_group comm_groupE(4)
      extended_ordered_abelian_group.axioms(1) group.inv_closed
      ordered_abelian_group.le_resp_mult1 by fastforce
qed

lemma (in padic_integers) gord_plus[simp]:
  assumes "a \<succeq>\<^bsub>G\<^esub> b"
  shows "a \<oplus>\<^bsub>G\<^esub> c \<succeq>\<^bsub>G\<^esub> b \<oplus>\<^bsub>G\<^esub> c"
proof(cases "c = \<infinity>\<^bsub>G\<^esub>")
  case True
  then show ?thesis 
    using G_eq G_mult(2) by presburger
next
  case F: False
  then show ?thesis
  proof(cases "a = \<infinity>\<^bsub>G\<^esub>")
    case True
    then show ?thesis 
      by (simp add: G_ord(1))
  next
    case False
    obtain n where n_def: "a = *n*"
      using False G_def by auto
    obtain m where m_def: "b = *m*"
      using False G_def assms by force
    obtain k where k_def: "c = *k*"
      using F G_def by auto
    show ?thesis 
      using assms n_def m_def k_def 
      by (simp add: G_def)
  qed
qed

lemma (in padic_integers) gord_plus'[simp]:
  assumes "a \<succeq>\<^bsub>G\<^esub> b"
  shows "c \<oplus>\<^bsub>G\<^esub> a \<succeq>\<^bsub>G\<^esub> c \<oplus>\<^bsub>G\<^esub> b"
proof- 
  have "a \<oplus>\<^bsub>G\<^esub> c \<succeq>\<^bsub>G\<^esub> b \<oplus>\<^bsub>G\<^esub> c"
    using assms gord_plus by blast
  then show ?thesis using gplus_comm by metis 
qed

(*Rules for infinity*)

lemma (in padic_integers) infinity_not_less[simp]:
"\<not> (a \<succ>\<^bsub>G\<^esub> \<infinity>\<^bsub>G\<^esub>)"
  using G_def extended_order.elims(2) by auto

lemma (in padic_integers) gord_add_cancel:
  assumes "a \<oplus>\<^bsub>G\<^esub> b = a \<oplus>\<^bsub>G\<^esub> c"
  assumes "a \<noteq> \<infinity>\<^bsub>G\<^esub>"
  shows "b = c"
proof(cases "b = \<infinity>\<^bsub>G\<^esub>")
  case True
  then show ?thesis 
    by (metis G_def G_mult(2) G_mult(3) assms(1) assms(2) extended_order.elims(2)
        extended_ordered_monoid.simps(1) monoid.simps(2) option.simps(3)
        ordered_monoid.simps(1) padic_integers.G_ord(1)   padic_integers_axioms
        partial_object.select_convs(1))
next
  case False
  obtain n where n_def: "b = *n*"
    using False G_def by auto
  obtain m where m_def: "a = *m*"
    using G_def assms(2) by auto
  obtain k where n_def: "c = *k*"
    using G_def assms(1) assms(2) n_def 
    by fastforce
  then show ?thesis 
    using \<open>\<And>thesis. (\<And>n. b = Some n \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assms(1) m_def 
    by force
qed

lemma (in padic_integers) gord_add_cancel':
  assumes "a \<oplus>\<^bsub>G\<^esub> b = c \<oplus>\<^bsub>G\<^esub> a"
  assumes "a \<noteq> \<infinity>\<^bsub>G\<^esub>"
  shows "b = c"
  using assms(1) assms(2) gord_add_cancel gplus_comm 
  by auto

lemma (in padic_integers) gord_add_cancel'':
  assumes "b \<oplus>\<^bsub>G\<^esub> a = c \<oplus>\<^bsub>G\<^esub> a"
  assumes "a \<noteq> \<infinity>\<^bsub>G\<^esub>"
  shows "b = c"
  using assms(1) assms(2) gord_add_cancel' gplus_comm 
  by auto

lemma (in padic_integers) gord_add_cancel''':
  assumes "a \<oplus>\<^bsub>G\<^esub> b \<succeq>\<^bsub>G\<^esub>  a \<oplus>\<^bsub>G\<^esub> c"
  assumes "a \<noteq> \<infinity>\<^bsub>G\<^esub>"
  shows "b \<succeq>\<^bsub>G\<^esub>  c"
  apply(cases "b = \<infinity>\<^bsub>G\<^esub>")
   apply (simp add: G_ord(1))
proof-
  show "b \<noteq> \<infinity>\<^bsub>G\<^esub> \<Longrightarrow> b \<succeq>\<^bsub>G\<^esub> c"
  proof-
    assume "b \<noteq> \<infinity>\<^bsub>G\<^esub>"
  obtain n where n_def: "b = *n*"
    using G_def \<open>b \<noteq> \<infinity>\<^bsub>G\<^esub>\<close> by auto 
  obtain m where m_def: "a = *m*"
    using G_def assms(2) by auto
  obtain k where k_def: "c = *k*"
    by (metis G_def  G_mult(2) assms(1) extended_ordered_monoid.simps(1) 
          gord_add_cancel' infinity_not_less m_def monoid.simps(2)
          n_def option.exhaust partial_object.select_convs(1))
  have " *m + n* \<succeq>\<^bsub>G\<^esub> *m + k*"
    using assms n_def m_def k_def G_mult(3)[of m k]  G_mult(3)[of m n] G_ord(2)  
    by (simp add: \<open>\<And>b a. (Some b \<succeq>\<^bsub>G\<^esub> Some a) = (a \<le> b)\<close>)
  then have " *n* \<succeq>\<^bsub>G\<^esub> *k*"
    by (simp add: G_ord(2))
  then show "b \<succeq>\<^bsub>G\<^esub> c" 
    by (simp add: \<open>Some n \<succeq>\<^bsub>G\<^esub> Some k\<close> k_def n_def) 
  qed
qed

lemma (in padic_integers) gord_add_cancel'''':
  assumes "b \<oplus>\<^bsub>G\<^esub> a \<succeq>\<^bsub>G\<^esub>  c \<oplus>\<^bsub>G\<^esub> a"
  assumes "a \<noteq> \<infinity>\<^bsub>G\<^esub>"
  shows "b \<succeq>\<^bsub>G\<^esub>  c"
proof-
  have 0: "b \<oplus>\<^bsub>G\<^esub> a = a \<oplus>\<^bsub>G\<^esub> b"
    using gplus_comm by blast
  have 1: "b \<oplus>\<^bsub>G\<^esub> c = c \<oplus>\<^bsub>G\<^esub> b"
    by (simp add: gplus_comm)
  show ?thesis 
    using assms gord_add_cancel'''[of a c b] 0 1 
    by (metis gplus_comm)
qed

(*************************************************************************************************)
(*********************************** FACTS ABOUT RESIDUE RINGS ***********************************)
(*************************************************************************************************)
(*************************************************************************************************)

lemma(in field) field_inv[simp]:
  assumes "a \<in> carrier R"
  assumes "a \<noteq>\<zero>"
  shows "inv\<^bsub>R\<^esub> a \<otimes> a = \<one>"
        "a \<otimes> inv\<^bsub>R\<^esub> a = \<one>"
        "inv \<^bsub>R\<^esub> a \<in> carrier R"
proof-
  have "a \<in> Units R"
    using assms by (simp add: local.field_Units)
  then show "inv\<^bsub>R\<^esub> a \<otimes> a = \<one>" 
    by simp
  show "a \<otimes> inv a = \<one>" 
    using \<open>a \<in> Units R\<close> by auto
  show "inv \<^bsub>R\<^esub> a \<in> carrier R"
    by (simp add: \<open>a \<in> Units R\<close>)
qed

(*Maps between residue rings*)

abbreviation(in padic_integers) r:: "nat \<Rightarrow> int \<Rightarrow> _" where
"r m n \<equiv> res (p^m) n"

(*Lemmas for reasoning about residue maps*)

lemma(in padic_integers) r_def:
"r m n = n mod (p^m)"
  using res_def by blast 

lemma(in padic_integers) r_range:
"r m n \<in> {0..p^m - 1}"
  using r_def int_ops(6) prime prime_gt_0_nat by auto 

lemma(in padic_integers) r_mod[simp]:
  assumes "m > k"
  shows "r k (r m n)  = r k n"  
  by (metis (mono_tags, lifting) r_def assms le_imp_power_dvd 
      less_imp_le mod_mod_cancel of_nat_power) 

(*Compatibility of r with elements of Z\<^sub>p*)

lemma(in padic_integers) r_Zp:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "m \<ge> k"
  shows "r k (x m) = x k"
  using Z\<^sub>p_def assms(1) assms(2) padic_set_simp1 prime by auto 

(*Definition of residue rings*)

abbreviation(in padic_integers) Res:: "nat \<Rightarrow> _ ring" ("R _")where
"(Res n) \<equiv> residue_ring (int (p^n))"

lemma(in padic_integers) r_range':
"r m n \<in> carrier (R m)"
  using r_range  residue_ring_def prime prime_gt_0_nat r_def by fastforce

(*First residue ring is a field*)

lemma(in padic_integers) Res_1_field:
"field (R 1)"
proof-
  have "residues_prime p"
    by (simp add: prime residues_prime.intro) 
  then show ?thesis using  residues_prime.is_field 
    by (simp ) 
qed

(*0th residue ring is the zero ring*)

lemma(in padic_integers) Res_0:
"carrier (R 0) = {0}" 
  by (simp add:  residue_ring_def) 

lemma(in padic_integers) Res_0':
  assumes "x \<in> carrier (R 0)"
  shows "x = 0"
  using Res_0 assms by blast 

(*If m>0 then R m is an instance of the residues locale*)

lemma(in padic_integers) R_residues:
  assumes "m >0"
  shows "residues (p^m)"
proof-
  have "p^m > 1" 
    using assms one_less_power prime prime_nat_iff by blast 
  then show ?thesis 
    using less_imp_of_nat_less residues.intro by fastforce 
qed

(*If m>0 then (R m) is a commutative ring*)

lemma(in padic_integers) R_cring:
  assumes "m >0"
  shows "cring (R m)"
  using R_residues  assms residues.cring by auto 

(*Rules for reasoning about the padic zero object*)

lemma(in padic_integers) zero_rep:
"\<zero> = (\<lambda>m. (r m 0))"  
proof
  fix m
  show " \<zero> m = r m 0 " using Z\<^sub>p_def padic_zero_def  
    by (metis abelian_groupE(2) eq_iff padic_is_abelian_group
        padic_set_simp1 partial_object.select_convs(1) prime ring_record_simps(11)) 
qed

lemma(in padic_integers) zero_vals:
"\<zero> n = 0"
  using r_def zero_rep by auto 

lemma(in padic_integers) res_mult_zero[simp]:
  assumes "k >0"
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "a k = 0"
  shows "(a \<otimes>b) k = 0" "(b \<otimes>a) k = 0"
   apply (metis Z\<^sub>p_def assms(3) assms(4) cring.cring_simprules(26)
      monoid.simps(1) padic_int_is_cring padic_mult_simp prime zero_vals)
    by (metis Z\<^sub>p_def assms(3) assms(4) cring.cring_simprules(27) monoid.simps(1) 
        padic_int_is_cring padic_integers.zero_vals padic_integers_axioms padic_mult_simp prime)

lemma(in padic_integers) res_add_zero[simp]:
  assumes "k >0"
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "a k = 0"
  shows "(a \<oplus> b) k = b k" "(b \<oplus> a) k = b k"
proof-
  have "(a \<oplus> b) k = (a k) \<oplus>\<^bsub>R k\<^esub> (b k)"
    by (simp add:  Z\<^sub>p_def padic_add_simp)
  then have "(a \<oplus> b) k = \<zero>\<^bsub>R k\<^esub> \<oplus>\<^bsub>R k\<^esub> (b k)"
    using R_residues  assms(1) assms(4) residues.res_zero_eq by auto
  then show 1: "(a \<oplus> b) k = b k"
    by (metis R_cring  Z\<^sub>p_def assms(1) assms(3) 
        cring.cring_simprules(8) padic_set_simp0 partial_object.select_convs(1))
  show "(b \<oplus> a) k = b k" 
    using assms 1  Z\<^sub>p_def padic_add_comm prime 
    by auto
qed

lemma(in padic_integers) res_mult_closed[simp]:
  assumes "k> 0"
  assumes "a \<in> carrier (R k)"
  assumes "b \<in> carrier (R k)"
  shows "a \<otimes>\<^bsub>R k\<^esub> b \<in> carrier (R k)"
  by (meson R_cring assms(1) assms(2) assms(3) cring.cring_simprules(5)) 

lemma(in padic_integers) res_add_closed[simp]:
  assumes "k> 0"
  assumes "a \<in> carrier (R k)"
  assumes "b \<in> carrier (R k)"
  shows "a \<oplus>\<^bsub>R k\<^esub> b \<in> carrier (R k)"
  by (meson R_cring assms(1) assms(2) assms(3) cring.cring_simprules(1)) 

(*************************************************************************************************)
(*************************************************************************************************)
(************************************ FACTS ABOUT Zp AND Qp **************************************)
(*************************************************************************************************)
(*************************************************************************************************)

(*nonzero_def simplified*)

lemma(in padic_integers) Zp_nonzero_def:
  assumes "a \<in> nonzero Z\<^sub>p"
  shows "a \<in> carrier Z\<^sub>p"
        "a \<noteq>\<zero>"
  using assms nonzero_def apply force
  using assms nonzero_def by fastforce

lemma(in padic_integers) Qp_nonzero_def:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "a \<in> carrier Q\<^sub>p"
        "a \<noteq>\<zero>\<^bsub>Q\<^sub>p\<^esub>"
  using assms nonzero_def apply force
  using assms nonzero_def by fastforce

(*Z\<^sub>p is an integral domain*)

lemma(in padic_integers) Zp_is_domain[simp]:
"domain Z\<^sub>p" 
  using  padic_integers_axioms padic_int_is_domain prime  Z\<^sub>p_def by blast  

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

(*Zp one isn't zero*)

lemma(in padic_integers) Zp_one_car:
"\<one> \<in> carrier Z\<^sub>p" 
  by (simp add: cring.cring_simprules(6) domain.axioms(1))

lemma(in padic_integers) Zp_one_notzero:
"\<one> \<noteq>\<zero>"
  by (simp add: domain.one_not_zero)

lemma(in padic_integers) Zp_one_nonzero:
"\<one> \<in> nonzero Z\<^sub>p" 
  by (simp add: Localization.submonoid.one_closed domain.nonzero_is_submonoid)

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
  by (simp add: Localization.submonoid.one_closed Q\<^sub>p_def 
      cring.cring_simprules(6) domain.axioms(1)
      domain.frac_one domain.nonzero_is_submonoid local.frac_def local.inc_def)

lemma(in padic_integers) inc_of_sum:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  shows "\<iota> (a \<oplus> b) = (\<iota> a) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<iota> b)"
  by (simp add: Localization.submonoid.one_closed Q\<^sub>p_def assms(1)
      assms(2) cring.cring_simprules(1) domain.axioms(1) domain.frac_add_common_denom
      domain.nonzero_is_submonoid local.frac_def local.inc_def)

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
    using assms nonzero_def by fastforce
  have An: "(a[^]n) \<in> carrier Z\<^sub>p" 
    by (meson A Zp_is_domain cring_def domain.axioms(1) monoid.nat_pow_closed ring_def)
  have iA: "\<iota> a \<in> carrier Q\<^sub>p"
    by (simp add: A Localization.submonoid.one_closed Q\<^sub>p_def
        domain.frac_im domain.nonzero_is_submonoid 
        local.frac_def local.inc_def) 
  have iAn: "\<iota> (a[^]n) \<in> carrier Q\<^sub>p" 
    by (simp add: An Localization.submonoid.one_closed 
        Q\<^sub>p_def domain.frac_im domain.nonzero_is_submonoid
        local.frac_def local.inc_def)
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
(*Units are always nonzero*)

lemma(in domain) Units_nonzero:
assumes "u \<in> Units R"
shows "u \<in> nonzero R"
proof-
  have "u \<in>carrier R" 
    using Units_closed assms by auto
  have "u \<noteq>\<zero>" 
    by (metis (full_types) Units_r_inv_ex assms l_null zero_not_one)
  then show ?thesis 
    by (simp add: \<open>u \<in> carrier R\<close> nonzero_def)
qed

lemma(in padic_integers) Units_nonzero_Zp[simp]:
assumes "u \<in> Units Z\<^sub>p"
shows "u \<in> nonzero Z\<^sub>p"
  by (simp add: assms domain.Units_nonzero)

lemma(in padic_integers) Units_nonzero_Qp[simp]:
assumes "u \<in> Units Q\<^sub>p"
shows "u \<in> nonzero Q\<^sub>p"
  by (simp add: assms domain.Units_nonzero field.axioms(1))

lemma(in domain) Units_inverse[simp]:
  assumes "u \<in> Units R"
  shows "inv u \<in> Units R"
  by (simp add: assms)

lemma(in padic_integers) Units_inverse_Zp[simp]:
  assumes "u \<in> Units Z\<^sub>p"
  shows "inv u \<in> Units Z\<^sub>p"
  using Zp_is_domain assms 
  by (simp add: domain.Units_inverse)

lemma(in padic_integers) Units_inverse_Qp[simp]:
  assumes "u \<in> Units Q\<^sub>p"
  shows "inv\<^bsub>Q\<^sub>p\<^esub> u \<in> Units Q\<^sub>p"
  by (simp add: assms domain.Units_inverse)

lemma Units_prop[simp]:
  assumes "domain R"
  assumes "u \<in> Units R"
  shows "u \<otimes>\<^bsub>R\<^esub> inv\<^bsub>R\<^esub> u = \<one>\<^bsub>R\<^esub>"
  by (meson assms(1) assms(2) cring_def domain.axioms(1) monoid.Units_r_inv ring_def)

lemma(in padic_integers) Units_prop_Zp[simp]:
  assumes "u \<in> Units Z\<^sub>p"
  shows "u \<otimes> inv u = \<one>"
        "inv u \<otimes> u = \<one>"
   apply (simp add: assms)
    by (meson Zp_is_domain assms cring_def domain.axioms(1) monoid.Units_l_inv ring_def)

lemma invI:
  assumes "domain R"
  assumes "x \<in> carrier R"
  assumes "y \<in> carrier R"
  assumes "x \<otimes>\<^bsub>R\<^esub> y = \<one>\<^bsub>R\<^esub>"
  shows "y = inv \<^bsub>R\<^esub> x"
        "x = inv \<^bsub>R\<^esub> y"
  using assms(1) assms(2) assms(3) assms(4) comm_monoid.comm_inv_char cring_def domain_def 
  apply fastforce
  
    using assms(1) assms(2) assms(3) assms(4) comm_monoid.comm_inv_char cring.cring_simprules(14) 
          cring_def domain.axioms(1) 
    by fastforce

lemma is_UnitI[simp]:
  assumes "domain R"
  assumes "x \<in> carrier R"
  assumes "y \<in> carrier R"
  assumes "x \<otimes>\<^bsub>R\<^esub> y = \<one>\<^bsub>R\<^esub>"
  shows "x \<in> Units R" "y \<in> Units R"
   apply (metis (mono_tags, lifting) Units_def assms(1) assms(2) assms(3) assms(4)
          cring.cring_simprules(14) domain.axioms(1) mem_Collect_eq)
    using Units_def assms(1) assms(2) assms(3) assms(4) cring.cring_simprules(14) domain.axioms(1) 
    by fastforce

lemma inv_cancelR:
  assumes "domain R"
  assumes "x \<in> Units R"
  assumes "y \<in> carrier R"
  assumes "z \<in> carrier R"
  assumes "y = x \<otimes>\<^bsub>R\<^esub> z"
  shows "inv\<^bsub>R\<^esub> x \<otimes>\<^bsub>R\<^esub> y = z"
        "y \<otimes>\<^bsub>R\<^esub> (inv\<^bsub>R\<^esub> x)  = z"
   apply (metis (no_types, lifting) Units_def assms(1) assms(2) assms(4) assms(5) 
      cring.cring_simprules(11) cring.cring_simprules(12)
      cring_def domain.axioms(1) mem_Collect_eq monoid.Units_inv_closed monoid.Units_l_inv ring_def)
  by (metis Units_prop assms(1) assms(2) assms(4) assms(5) cring.cring_simprules(11)
      cring.cring_simprules(14) cring_def domain.Units_inverse domain.axioms(1)
      monoid.Units_closed monoid.r_one ring_def)

lemma inv_cancelL:
  assumes "domain R"
  assumes "x \<in> Units R"
  assumes "y \<in> carrier R"
  assumes "z \<in> carrier R"
  assumes "y = z \<otimes>\<^bsub>R\<^esub> x"
  shows "inv\<^bsub>R\<^esub> x \<otimes>\<^bsub>R\<^esub> y = z"
        "y \<otimes>\<^bsub>R\<^esub> (inv\<^bsub>R\<^esub> x)  = z"
  using assms inv_cancelR[of R x y z]
   apply (meson cring.cring_simprules(14) cring_def domain_def monoid.Units_closed ring_def)
  using assms inv_cancelR[of R x y z]
  by (metis (mono_tags, hide_lams) domain.Units_nonzero domain.frac_eq)

lemma Units_closed[simp]:
  assumes "domain R"
  assumes  "a \<in> Units R"
  assumes "b \<in> Units R"
  assumes "c = a \<otimes>\<^bsub>R\<^esub> b"
  shows "c \<in> Units R"
  by (metis assms(1) assms(2) assms(3) assms(4) cring_def domain.axioms(1) 
      monoid.Units_m_closed ring_def)
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
    using assms(1) assms(2) assms(3) nonzero_fraction_imp_numer_not_zero by auto
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
     apply force
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
    using assms(2) nonzero_def by force
  have P0:"(inv\<^bsub>Q\<^sub>p\<^esub> (\<iota> b)) = frac \<one> b" 
    using B inc_def frac_inv by (simp add: Localization.submonoid.one_closed  
         assms(2) domain.nonzero_is_submonoid)
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


lemma(in domain) nat_pow_nonzero:
  assumes "x \<in>nonzero R"
  shows "x[^](n::nat) \<in> nonzero R"
proof(induction n)
  case 0
  then show ?case 
    by (simp add: nonzero_def)
next
  case (Suc n)
  then show ?case 
    by (simp add: Localization.submonoid.m_closed assms nonzero_is_submonoid)
qed

lemma(in padic_integers) Zp_nat_pow_nonzero:
  assumes "x \<in> nonzero Z\<^sub>p"
  shows "x[^](n::nat) \<in> nonzero Z\<^sub>p"
  by (simp add:  assms domain.nat_pow_nonzero)

lemma(in padic_integers) Qp_nat_pow_nonzero:
  assumes "x \<in> nonzero Q\<^sub>p"
  shows "x[^]\<^bsub>Q\<^sub>p\<^esub>(n::nat) \<in> nonzero Q\<^sub>p"
  by (simp add: assms domain.nat_pow_nonzero)


(*************************************************************************************************)
(*************************************************************************************************)
(*************************************  INTEGER AND NAT     **************************************)
(*************************************  INCLUSIONS IN Zp    **************************************)
(*************************************************************************************************)
(*************************************************************************************************)

(*inclusion of the integers in Z\<^sub>p*)

lemma(in padic_integers) Zp_int_inc_zero':
  assumes "x \<in> carrier Z\<^sub>p"
  shows "[(0::int)] \<cdot> x = \<zero>" 
proof-
  have "group (add_monoid Z\<^sub>p)" 
    using Z\<^sub>p_def abelian_group.a_group padic_is_abelian_group prime by blast  
  then show ?thesis 
    by (simp add: add_pow_def group.int_pow_0) 
qed

lemma(in padic_integers) Zp_int_inc_zero:
"[(0::int)]\<cdot> \<one> = \<zero>" 
  using Zp_is_domain cring.cring_simprules(6) domain_def Zp_int_inc_zero' by blast 

lemma(in padic_integers) Zp_nat_inc_zero:
"[(0::nat)]\<cdot> \<one> = \<zero>" 
  using Zp_int_inc_zero Zp_is_domain  domain_def 
  by (metis abelian_group_def abelian_monoid.a_monoid add_pow_def
      cring.axioms(1) domain.axioms(1) monoid.nat_pow_0 monoid.simps(2) ring_def) 

lemma(in padic_integers) Zp_nat_mult_zero:
"[(0::nat)]\<cdot> x = \<zero>" 
  using Zp_int_inc_zero Zp_is_domain  domain_def 
  by (metis abelian_group_def abelian_monoid.a_monoid add_pow_def
      cring.axioms(1) domain.axioms(1) monoid.nat_pow_0 monoid.simps(2) ring_def) 

(*Zp is closed under nat inclusions*)

lemma(in padic_integers) Zp_nat_inc_closed:
  fixes n::nat
  shows "[n] \<cdot> \<one> \<in> carrier Z\<^sub>p"
proof(induction n)
  case 0
  then show ?case 
    using Zp_is_domain cring.cring_simprules(2) domain_def Zp_nat_inc_zero by metis 
next
  case (Suc n)
  then show ?case 
    using Zp_is_domain domain_def 
    by (metis abelian_group_def abelian_monoid.a_monoid add_pow_def cring.axioms(1) 
        cring.cring_simprules(6) domain.axioms(1) monoid.nat_pow_closed
        partial_object.select_convs(1) ring_def) 
qed

(*Zp is closed under nat multiples*)

lemma(in padic_integers) Zp_nat_mult_closed:
  fixes n::nat
  assumes "x \<in> carrier Z\<^sub>p"
  shows "[n] \<cdot> x \<in> carrier Z\<^sub>p"
proof(induction n)
  case 0
  then show ?case 
    using Zp_is_domain cring.cring_simprules(2) domain_def Zp_nat_mult_zero by metis 
next
  case (Suc n)
  then show ?case 
    using Zp_is_domain domain_def 
    by (metis abelian_group_def abelian_monoid.a_monoid add_pow_def assms(1) cring.axioms(1) 
         domain.axioms(1) monoid.nat_pow_closed
        partial_object.select_convs(1) ring_def) 
qed

(*Zp is closed under int inclusions*)

lemma(in padic_integers) Zp_int_inc_closed:
  fixes n::int
  shows "[n] \<cdot> \<one> \<in> carrier Z\<^sub>p"
proof(cases "n \<ge> 0")
  case True
  then show ?thesis using Zp_nat_inc_closed  
    by (simp add: add_pow_int_ge)
next
  case False
  then have 0: "[(-n)] \<cdot> \<one> \<in> carrier Z\<^sub>p" 
    using Zp_nat_inc_closed by (simp add: add_pow_int_ge)
  have 1: "n <0" 
    using False by auto 
  then show ?thesis
    using 0 1 Zp_is_domain 
    by (simp add: add_pow_int_lt add_pow_int_ge cring.cring_simprules(3) domain.axioms(1))
qed

lemma(in padic_integers) Zp_int_mult_closed:
  fixes n::int
  assumes "x \<in> carrier Z\<^sub>p"
  shows "[n] \<cdot> x \<in> carrier Z\<^sub>p"
proof(cases "n \<ge>0")
  case True
  then show ?thesis 
    by (simp add: Zp_nat_mult_closed add_pow_int_ge assms)
next
  case False
  then show ?thesis 
    using Zp_nat_mult_closed add_pow_int_lt Zp_is_domain 
    by (metis abelian_group.a_group add_pow_def assms cring.axioms(1)
        cring.cring_simprules(3) domain.axioms(1) group.int_pow_def2 ring_def)
qed


(*Concrete description of the inclusion of a natural number in Zp*)

lemma(in padic_integers) Zp_nat_inc_rep:
  fixes n::nat
  shows "[n] \<cdot> \<one> = (\<lambda> m. r m n)" 
proof(induction n)
  case 0
  then show ?case  using Zp_nat_inc_zero zero_rep 
    by simp 
next
  case (Suc n)
  fix n
  assume A: "[n] \<cdot> \<one> = (\<lambda>m. r m (int n))"
  have "[Suc n] \<cdot> \<one>  = [n]\<cdot>\<one> \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub> \<one>" using Zp_is_domain  monoid.nat_pow_Suc
    by (metis Z\<^sub>p_def abelian_group_def abelian_monoid.a_monoid add_pow_def padic_is_abelian_group prime) 
  then have 0: "[Suc n] \<cdot> \<one>  = [n]\<cdot>\<one> \<oplus> \<one>" by auto 
  show "[Suc n] \<cdot> \<one> = (\<lambda>m. r m (Suc n))"
  proof fix m
    show "([Suc n] \<cdot> \<one>) m = r m (int (Suc n)) "
    proof(cases "m=0")
      case True
      have 0: "([Suc n] \<cdot> \<one>) m \<in> carrier (R m)" 
        using Zp_nat_inc_closed padic_set_simp0 by (simp add:  Z\<^sub>p_def)
      then have "([Suc n] \<cdot> \<one>) m = 0"
        using Res_0 True by blast 
      then show ?thesis 
        by (simp add: True res_1_zero) 
      next
        case False
        then have R: "residues (p^m)" 
          by (metis (mono_tags, hide_lams) One_nat_def linorder_neqE_linordered_idom 
              nat_int nat_le_iff nat_one_as_int nat_power_eq_Suc_0_iff not_less 
              not_prime_1 one_le_power prime prime_ge_1_nat residues_def) 
        have "([Suc n] \<cdot> \<one>) m  = ([n]\<cdot>\<one> \<oplus> \<one>) m" 
          by (simp add: "0") 
        then have P0: "([Suc n] \<cdot> \<one>) m  =  r m (int n) \<oplus>\<^bsub>R m\<^esub> \<one>\<^bsub>R m\<^esub>" 
          using A False Z\<^sub>p_def padic_add_simp padic_one_def 
            \<open>residues (int (p ^ m))\<close> residues.res_one_eq  by auto 
        then have P1:"([Suc n] \<cdot> \<one>) m =  r m (int n) \<oplus>\<^bsub>R m\<^esub> r m (1::int)"
          using \<open>residues (int (p ^ m))\<close> res_def residues.one_cong  by auto
        have P2: "r m (int n) \<oplus>\<^bsub>R m\<^esub> r m 1 = ((int n) mod (p^m)) \<oplus>\<^bsub>R m\<^esub> 1" 
          using R P0 P1 res_def residues.res_one_eq  by auto 
        have P3:"((int n) mod (p^m)) \<oplus>\<^bsub>R m\<^esub> 1 = ((int n) + 1) mod (p^m)" 
          using R residue_ring_def  by (simp add:  mod_add_left_eq) 
        have "r m (int n) \<oplus>\<^bsub>R m\<^esub> r m 1 = (int (Suc n)) mod (p^m)"
          by (metis  P2 P3 int_ops(4) res_def zmod_int)
        then show ?thesis
          using False R by (simp add: P1 res_def)
    qed
  qed
qed

(*Nat inclusion is multiplciative*)


lemma(in padic_integers) Zp_nat_inc_prod:
  fixes n::nat
  fixes m::nat
  shows "[m]\<cdot>([n] \<cdot> \<one>) = [(m*n)]\<cdot>\<one>"
proof
  fix k
  show "([m] \<cdot> ([n] \<cdot> \<one>)) k = ([(m * n)] \<cdot> \<one>) k"
  proof(induction m)
    case 0
  then show ?case 
    by (simp add: Zp_nat_mult_zero)
next
  case (Suc m)
  fix m
  assume P: "([m] \<cdot> ([n] \<cdot> \<one>)) k = ([(m * n)] \<cdot> \<one>) k"
  have A: "([Suc m] \<cdot> ([n] \<cdot> \<one>)) = ([m] \<cdot> ([n] \<cdot> \<one>))  \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub>  ([n] \<cdot> \<one>) " 
    using  Zp_is_domain domain_def cring_def by (simp add: nat_pow_def add_pow_def) 
  show " ([Suc m] \<cdot> ([n] \<cdot> \<one>)) k = ([((Suc m) * n)] \<cdot> \<one>) k" 
  proof-
    have L0:  "([Suc m] \<cdot> ([n] \<cdot> \<one>)) k = (([m] \<cdot> ([n] \<cdot> \<one>)) \<oplus>  ([n] \<cdot> \<one>)) k "
      using A by simp 
    then have L1: "([Suc m] \<cdot> ([n] \<cdot> \<one>)) k = (([m] \<cdot> ([n] \<cdot> \<one>)) k) \<oplus>\<^bsub>R k\<^esub> ( ([n] \<cdot> \<one>) k) "
      using Z\<^sub>p_def padic_add_def by (simp add: ) 
    then have L2: "([Suc m] \<cdot> ([n] \<cdot> \<one>)) k = ([(m*n)]\<cdot> \<one>) k \<oplus>\<^bsub>R k\<^esub> ( ([n] \<cdot> \<one>) k) " 
      by (simp add: P) 
    then have L3: "([Suc m] \<cdot> ([n] \<cdot> \<one>)) k = r k (m*n) \<oplus>\<^bsub>R k\<^esub> r k n "
      by (simp add: Zp_nat_inc_rep)
    then have L4: "([Suc m] \<cdot> ([n] \<cdot> \<one>)) k = (( r k (m*n)) + (r k n)) mod (p^k)"
      using residue_ring_def  by auto 
    then have L5: "([Suc m] \<cdot> ([n] \<cdot> \<one>)) k = (((m*n) mod (p^k)) + (n mod (p^k))) mod (p^k)"
      using r_def by (simp add: L4 add.commute mod_add_eq zmod_int) 
    then have L6: "([Suc m] \<cdot> ([n] \<cdot> \<one>)) k = ((m*n) + n) mod (p^k)"
      by (simp add: mod_add_eq) 
    then have L7: "([Suc m] \<cdot> ([n] \<cdot> \<one>)) k = ((Suc m)*n) mod (p^k)"
      by (simp add: add.commute) 
    then show ?thesis  
      by (simp add: Zp_nat_inc_rep res_def zmod_int)
    qed
  qed
qed

(*
lemma(in padic_integers) Zp_nat_mult_prod:
  fixes n::nat
  fixes m::nat
  assumes "x \<in> carrier Z\<^sub>p"
  shows "[m]\<cdot>([n] \<cdot> x) = [(m*n)]\<cdot>x"
*)

(*Concrete description of the inclusion of an integer in Zp*)

lemma(in padic_integers) int_inc_rep:
  fixes n::int
  shows  "[n] \<cdot> \<one> = (\<lambda> m. r m n )" 
proof(induction n)
  case (nonneg n)
  then show ?case using Zp_nat_inc_rep 
    by (simp add: add_pow_int_ge) 
next
  case (neg n)
  show "\<And>n. [(- int (Suc n))] \<cdot> \<one> = (\<lambda>m. r m (- int (Suc n)))"
  proof
    fix n
    fix m
    show "([(- int (Suc n))] \<cdot> \<one>) m =  r m (- int (Suc n))"
    proof-
      have "[(- int (Suc n))] \<cdot> \<one> = \<ominus> ([(int (Suc n))] \<cdot> \<one>)" 
        by (metis Zp_is_domain a_inv_def abelian_group.a_group add.inverse_inverse 
            add_pow_def cring.axioms(1) domain_def  group.int_pow_def2  
            negative_zless_0 of_nat_less_0_iff ring_def)
      then have "([(- int (Suc n))] \<cdot> \<one>) m = (\<ominus> ([(int (Suc n))] \<cdot> \<one>)) m" 
        by simp 
      have "\<one> \<in> carrier Z\<^sub>p" 
        using Zp_is_domain cring.cring_simprules(6) domain_def by blast 
      have "([(int (Suc n))] \<cdot> \<one>) = ([(Suc n)] \<cdot> \<one>)" 
        using Zp_is_domain by (metis add_pow_def int_pow_int)
      then have "([(int (Suc n))] \<cdot> \<one>) \<in> carrier Z\<^sub>p" using Zp_nat_inc_closed 
        by simp 
      then have P0: "([(- int (Suc n))] \<cdot> \<one>) m =  \<ominus>\<^bsub>R m\<^esub> (([(int (Suc n))] \<cdot> \<one>) m)"
        using Z\<^sub>p_def prime padic_inv  \<open>[(- int (Suc n))] \<cdot> \<one> = \<ominus> ([int (Suc n)] \<cdot> \<one>)\<close>
            by auto
      have "(([(int (Suc n))] \<cdot> \<one>) m) = (r m (Suc n))" 
        using Zp_nat_inc_rep by (simp add: add_pow_int_ge) 
      then have P1: "([(- int (Suc n))] \<cdot> \<one>) m =  \<ominus>\<^bsub>R m\<^esub>(r m (Suc n))" 
        using P0 by auto
      have  "\<ominus>\<^bsub>R m\<^esub>(r m (Suc n)) =  r m (- int (Suc n))" 
        proof(cases "m=0")
          case True
          then have 0:"\<ominus>\<^bsub>R m\<^esub>(r m (Suc n)) =\<ominus>\<^bsub>R 0\<^esub>(r 0 (Suc n))" 
            by blast 
          then have 1:"\<ominus>\<^bsub>R m\<^esub>(r m (Suc n)) =\<ominus>\<^bsub>R 0\<^esub> (res 1 (Suc n))" 
            by simp
          then have 2:"\<ominus>\<^bsub>R m\<^esub>(r m (Suc n)) =\<ominus>\<^bsub>R 0\<^esub> 0" 
            by (simp add: res_1_zero) 
          then have 3:"\<ominus>\<^bsub>R m\<^esub>(r m (Suc n)) =0" 
            using res_1_prop 
            by (metis  One_nat_def Totient.of_nat_eq_1_iff True 
                nat_power_eq_Suc_0_iff padic_zero_def padic_zero_simp) 
          have 4: "r m (- int (Suc n)) \<in> carrier (R 0)" 
            using Res_0 True res_1_zero by auto
          then show ?thesis 
            using "3" True res_1_zero by auto
        next
          case False
          then have R: "residues (p^m)" 
            using padic_integers.R_residues padic_integers_axioms by blast 
          have "\<ominus>\<^bsub>R m\<^esub> r m (int (Suc n)) = \<ominus>\<^bsub>R m\<^esub> (int (Suc n)) mod (p^m) " 
            using R res_def residues.neg_cong residues.res_neg_eq  by auto 
          then have "\<ominus>\<^bsub>R m\<^esub> r m (int (Suc n)) = (-(int (Suc n))) mod (p^m)" 
            using R residues.res_neg_eq  by auto 
          then show ?thesis 
            by (simp add: res_def) 
        qed
      then show ?thesis  
        using P1  by linarith 
    qed
  qed
qed

(*The copy of the prime p living in Z\<^sub>p*)

abbreviation(in padic_integers) \<p> where
"\<p> \<equiv> [p] \<cdot> \<one>"

lemma(in padic_integers) p_natpow_prod:
"\<p>[^](n::nat) \<otimes> \<p>[^](m::nat) = \<p>[^](n + m)"
  using Zp_is_domain Zp_nat_inc_closed Zp_one_car domain.axioms(1) monoid.nat_pow_mult
  by (metis  cring.axioms(1) domain_def ring_def)

lemma(in padic_integers) p_natpow_prod_Suc:
"\<p> \<otimes> \<p>[^](m::nat) = \<p>[^](Suc m)"
"\<p>[^](m::nat)  \<otimes> \<p> = \<p>[^](Suc m)"
proof-
  have "\<p> \<otimes> \<p>[^](m::nat) = \<p>[^](1::nat) \<otimes>\<p>[^](m::nat) "
    by (metis Zp_is_domain Zp_nat_inc_closed cring_def
        domain.axioms(1) int_pow_int monoid.nat_pow_eone of_nat_1 ring_def)
    then have "\<p> \<otimes> \<p>[^](m::nat) = \<p>[^]((1::nat) + m)"
      using p_natpow_prod by auto
    then show 0: "\<p> \<otimes> \<p>[^](m::nat) = \<p>[^](Suc m)"
      by auto
    then show "\<p>[^](m::nat)  \<otimes> \<p> = \<p>[^](Suc m)"
    proof-
      have "\<p>[^](m::nat)  \<otimes> \<p> =  \<p> \<otimes> \<p>[^](m::nat) "
        using Zp_is_domain Zp_one_car  domain.axioms(1) monoid.nat_pow_Suc
        by (metis "0" cring_def ring_def)
      then show ?thesis using 0 by auto 
    qed
qed

(*************************************************************************************************)
(*************************************************************************************************)
(************************************* THE VALUATION ON ZP  **************************************)
(*************************************************************************************************)
(*************************************************************************************************)

(*ad hoc inverse for option constructor*)

fun fromSome :: "'a option \<Rightarrow> 'a" where
  "fromSome (Some x) = x"

(*The padic valuation on Zp*)

definition(in padic_integers) val_Zp  where
"val_Zp = (\<lambda>x. (if (x = \<zero>) then (\<infinity>\<^bsub>G\<^esub>) else (Some (padic_val p x))))"

(*Integer-valued valuation on the nonzero elements of Zp, for simplified reasoning*)

definition(in padic_integers) ord_Zp where
"ord_Zp = padic_val p"

lemma(in padic_integers) val_Zp_closed[simp]:
  assumes "a \<in> nonzero Z\<^sub>p"
  shows "val_Zp a \<in> carrier G"
  by (simp add: G_def Zp_nonzero_def(2) assms val_Zp_def)


(*ord of additive inverse*)
lemma(in padic_integers) ord_Zp_of_ominus:
  assumes "a \<in> nonzero Z\<^sub>p"
  shows "ord_Zp a = ord_Zp (\<ominus>a)" 
  using ord_Zp_def  Z\<^sub>p_def assms padic_integers.Zp_nonzero_def(1)
    padic_integers_axioms padic_val_add_inv prime by auto

(*ord-based criterion for being nonzero*)

lemma(in padic_integers) ord_of_nonzero:
  assumes "x \<in>carrier Z\<^sub>p"
  assumes "ord_Zp x \<ge>0" 
  shows "x \<noteq> \<zero>"
        "x \<in> nonzero Z\<^sub>p"
proof-
  show "x \<noteq> \<zero>"
  proof
    assume "x = \<zero>"
    then have "ord_Zp x = -1" 
      using ord_Zp_def padic_val_def Z\<^sub>p_def by simp 
    then show False using assms(2) by auto 
  qed
  then show "x \<in> nonzero Z\<^sub>p" 
    using nonzero_def assms(1) 
    by (simp add: nonzero_def) 
qed

lemma(in padic_integers) not_nonzero_Zp:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "x \<notin> nonzero Z\<^sub>p"
  shows "x = \<zero>"
  using assms(1) assms(2) nonzero_def by fastforce

lemma(in padic_integers) not_nonzero_Qp:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "x \<notin> nonzero Q\<^sub>p"
  shows "x = \<zero>\<^bsub>Q\<^sub>p\<^esub>"
  using assms(1) assms(2) nonzero_def by force

(*Relationship between val and ord*)

lemma(in padic_integers) val_ord_Zp:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "a \<noteq> \<zero>"
  shows "Some (ord_Zp a) = val_Zp a" 
  by (simp add: assms(2) ord_Zp_def val_Zp_def) 

(*If x isn't zero, its ord is nonnegative*)

lemma(in padic_integers) ord_pos:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "x \<noteq>\<zero>"
  shows "ord_Zp x \<ge> 0"
proof-
  have "x \<noteq>padic_zero p" 
    using Z\<^sub>p_def assms(2) by auto 
  then have "ord_Zp x = int (LEAST k. x (Suc k) \<noteq> \<zero>\<^bsub>residue_ring (int (p ^ Suc k))\<^esub>)"
    using ord_Zp_def padic_val_def by auto  
  then show ?thesis 
    by linarith 
qed

(*For passing between nat and int castings of ord*)

lemma(in padic_integers) ord_nat[simp]:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "x \<noteq>\<zero>"
  shows "int (nat (ord_Zp x)) = ord_Zp x"
  using ord_pos by (simp add: assms(1) assms(2)) 

(*Renaming Some for application to ord_Zp values*)

definition(in padic_integers) val_of :: "int \<Rightarrow> int option" ("_\<^sub>v") where
"val_of n = Some n"

(*Lemmas for reasoning about ord:*)

lemma(in padic_integers) zero_below_ord:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "n \<le> ord_Zp x"
  shows  "x n =  0"
proof-
  have "x n =  \<zero>\<^bsub>residue_ring (p^n)\<^esub>" 
    using ord_Zp_def zero_below_val Z\<^sub>p_def assms(1) assms(2) prime by auto 
  then show ?thesis using residue_ring_def 
    by simp 
qed

lemma(in padic_integers) below_ord_zero:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "x (Suc n) \<noteq>  0"
  shows  "n \<ge> ord_Zp x"
proof-
  have 0: "x \<in> padic_set p" 
    using Z\<^sub>p_def assms(1) by auto 
  have 1: "x (Suc n) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc n))\<^esub>" 
    using residue_ring_def assms(2) by auto  
  have "of_nat n \<ge> (padic_val p x )" 
    using 0 1 below_val_zero prime by auto 
  then show ?thesis using ord_Zp_def by auto 
qed

lemma(in padic_integers) ord_suc_nonzero:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "x \<noteq>\<zero>"
  assumes "ord_Zp x = n"
  shows "x (Suc n) \<noteq> 0"
proof-   
  have 0:"ord_Zp x = int (LEAST k. x (Suc k) \<noteq> \<zero>\<^bsub>residue_ring (int (p ^ Suc k))\<^esub>)"
    using ord_Zp_def padic_val_def assms(1) assms(2) Z\<^sub>p_def by simp 
  have 1:"\<not> \<not>( \<exists> k. x (Suc k) \<noteq> \<zero>\<^bsub>residue_ring (int (p ^ Suc k))\<^esub>)" 
  proof
    assume "\<nexists>k. x (Suc k) \<noteq> \<zero>\<^bsub>residue_ring (int (p ^ Suc k))\<^esub>"
    then have P: "\<forall>k. x (Suc k) = \<zero>\<^bsub>residue_ring (int (p ^ Suc k))\<^esub>" 
      by blast 
    have "\<And> k. x k = 0"
    proof-
      fix k
      show "x k = 0"
      proof(cases "k=0")
        case True
        then show ?thesis 
          using Z\<^sub>p_def assms(1) assms(3) padic_integers.zero_below_ord
            padic_integers_axioms by auto 
      next
        case False
        obtain m where M: "k = Suc m" 
          using False old.nat.exhaust by auto 
        then have "x (Suc m) = \<zero>\<^bsub>residue_ring (int (p ^ Suc m))\<^esub>"
          using P by blast
        then show ?thesis using M residue_ring_def by auto 
      qed
    qed
    then have "\<And> k. x k = \<zero> k"
      using Z\<^sub>p_def padic_zero_def by simp
    then have "x = \<zero>"   by blast 
    then show False
      using assms(2) by linarith 
  qed
  then have "{ k. x (Suc k) \<noteq> \<zero>\<^bsub>residue_ring (int (p ^ Suc k))\<^esub>} \<noteq>{}" 
    by blast 
  then have "x (Suc n) \<noteq> \<zero>\<^bsub>residue_ring (int (p ^ Suc n))\<^esub>"
    using 0 by (metis (mono_tags, lifting) Collect_empty_eq LeastI_ex assms(3) of_nat_eq_iff)  
  then show ?thesis 
    using residue_ring_def by simp 
qed

lemma(in padic_integers) above_ord_nonzero:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "x \<noteq>\<zero>"
  assumes "n>ord_Zp x"
  shows "x n \<noteq> 0"
proof-
  have P0: "n \<ge> (Suc (nat (ord_Zp x)))" 
    by (simp add: Suc_le_eq assms(1) assms(2) assms(3) nat_less_iff ord_pos)
  then have P1: "r (Suc (nat (ord_Zp x))) (x n) = x (Suc (nat (ord_Zp x)))" 
    using assms(1) r_Zp by blast
  then have P2: "r (Suc (nat (ord_Zp x))) (x n) \<noteq> 0" 
    using Z\<^sub>p_def assms(1) assms(2) ord_nat padic_integers.ord_suc_nonzero
      padic_integers_axioms by auto
  then show ?thesis 
    using P0 P1 assms(1) r_Zp r_def by fastforce
qed

lemma(in padic_integers) ord_Zp_geq:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "x n = 0"
  assumes "x \<noteq>\<zero>"
  shows "ord_Zp x \<ge> n"
proof(rule ccontr)
  assume "\<not> int n \<le> ord_Zp x"
  then show False using assms 
    using above_ord_nonzero by auto
qed

lemma(in padic_integers) ord_equals:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "x (Suc n) \<noteq> 0"
  assumes "x n = 0"
  shows "ord_Zp x = n"
proof-
  have  "n \<ge> ord_Zp x" 
    by (simp add: assms(1) assms(2) below_ord_zero) 
  have "\<not> n > ord_Zp x"
  proof
    assume A: "ord_Zp x < int n"
    let ?n = "ord_Zp x"
    have "x \<noteq> \<zero>" 
    proof
      assume "x = \<zero>"
      then have "x (Suc n) = 0" 
        using Z\<^sub>p_def padic_zero_def by simp 
      then show False 
        using assms(2) by simp 
    qed 
    then have C: "x (Suc (nat ?n)) \<noteq> 0" 
      using ord_Zp_def padic_val_def Z\<^sub>p_def
      assms(1) ord_suc_nonzero by auto 
    have "?n < n"
      using A by simp  
    then have "?n + 1 \<le> n"
      by linarith 
    then have "(Suc (nat ?n)) \<le> n"
      using assms(2) ord_Zp_def padic_val_def padic_zero_def by auto
    then have "x (Suc (nat ?n)) = res (p^(Suc (nat ?n))) (x n)"
      using assms(1) Z\<^sub>p_def padic_set_def
        \<open>x (Suc (nat (ord_Zp x))) \<noteq> 0\<close> assms(3) le_eq_less_or_eq by fastforce 
    then have  "x (Suc (nat ?n)) = 0" 
      using assms(1) res_def by (simp add: assms(3)) 
    then show False using C by auto 
  qed
  then show ?thesis 
    using \<open>ord_Zp x \<le> int n\<close> by auto 
qed

lemma(in padic_integers) ord_Zp_p:
"ord_Zp \<p> = 1"
proof-
  have P0: "\<p> =  (\<lambda> m. r m p )" 
    by (simp add: Zp_nat_inc_rep) 
  then have "\<p> 1 = r 1 p" 
    by simp 
  then have "\<p> 1 = p mod p" 
    by (simp add: res_def) 
  then have "\<p> 1 = 0"  
    by simp 
  then have 0: "\<p> 1 = \<zero>\<^bsub>R 1\<^esub>"  
    using padic_zero_def padic_zero_simp  by presburger  
  have P1: "\<p> (2::nat) = r 2 p " using P0 
    by simp 
  have P2: "(p mod p^2) \<noteq> (0 mod p^2)" 
    using prime by (metis One_nat_def ex_power_ivl2 le_iff_add less_imp_le_nat 
        linorder_neqE_nat mod_0 mod_less nat_power_less_imp_less not_less_zero
        power_0 power_one_right  prime_gt_0_nat prime_power_inj prime_power_inj''
        two_is_prime_nat  zero_neq_one) 
  then have 2: "r 2 p \<noteq> r 2 0" 
    using res_def by presburger 
  then have X: "\<p> (2::nat) \<noteq> 0" 
    by (simp add: P1 res_def) 
  have "\<zero>\<^bsub>R 2\<^esub> = \<zero>\<^bsub>residue_ring (p^2)\<^esub>"
     by simp 
  then have "\<zero>\<^bsub>R 2\<^esub> = 0" 
    using residue_ring_def by simp 
  then have 3: "\<p> (2::nat) \<noteq> \<zero>\<^bsub>R 2\<^esub>" 
    using X by linarith 
  then have 4:"ord_Zp \<p> \<le> 1"     
    using ord_Zp_def prime below_val_zero 
    by (metis  One_nat_def Z\<^sub>p_def int_ops(2) numeral_2_eq_2
        padic_integers.Zp_nat_inc_closed padic_integers_axioms partial_object.select_convs(1))  
  have 5: "\<p> (Suc 0) = \<zero>\<^bsub>residue_ring (int(p^(Suc 0)))\<^esub>" 
    using 0  by simp 
  then have 7: "ord_Zp \<p> \<noteq> 0" using ord_Zp_def padic_val_def 
    by (metis (no_types, hide_lams) One_nat_def \<open>\<p> 1 = 0\<close> Zp_nat_inc_closed of_nat_0_le_iff
        of_nat_eq_0_iff ord_of_nonzero(1) ord_suc_nonzero) 
  show ?thesis 
      using ord_Zp_def padic_val_def 7 4 X padic_zero_def by auto 
qed

lemma(in padic_integers) ord_Zp_one:
"ord_Zp \<one> = 0"
proof-
  have "ord_Zp \<one> = ord_Zp (\<one> \<otimes> \<one>)" 
    by (simp add: cring.cring_simprules(12) cring.cring_simprules(6) domain.axioms(1)) 
  then have "ord_Zp \<one> = (ord_Zp \<one>) + (ord_Zp \<one>)" 
    by (metis Z\<^sub>p_def Zp_is_domain cring.cring_simprules(6) 
        domain.axioms(1) domain.one_not_zero monoid.select_convs(1)
        ord_Zp_def partial_object.select_convs(1) prime ring_record_simps(11) val_prod) 
  then show ?thesis by presburger
qed

(*ord is multiplicative on nonzero elements of Zp*)

lemma(in padic_integers) ord_Zp_mult:
  assumes "x \<in> nonzero Z\<^sub>p"
  assumes "y \<in> nonzero Z\<^sub>p"
  shows "(ord_Zp (x \<otimes>\<^bsub>Z\<^sub>p\<^esub> y)) = (ord_Zp x) + (ord_Zp y)"
proof-
  have 0: "x \<in> padic_set p"
  proof -
    have "x \<in> carrier Z\<^sub>p"
      using assms(1) nonzero_def by fastforce
    then show ?thesis
      by (metis (lifting) Z\<^sub>p_def  partial_object.select_convs(1))
  qed
  have 1: "y \<in> padic_set p"
  proof-
    have "y \<in> carrier Z\<^sub>p"
      using assms(2) nonzero_def by fastforce
    then show ?thesis
      by (metis (lifting) Z\<^sub>p_def  partial_object.select_convs(1))
  qed 
  have 2: "x \<noteq> (padic_zero p)" 
  proof -
    have "\<zero> \<noteq> x"
      using assms(1) nonzero_def by fastforce
    then show ?thesis
      by (metis (no_types) Z\<^sub>p_def ring_record_simps(11))
  qed
  have 3: "y \<noteq> (padic_zero p)"
  proof -
    have "\<zero> \<noteq> y"
      using assms(2) nonzero_def by fastforce
    then show ?thesis
      by (metis (no_types) Z\<^sub>p_def  ring_record_simps(11))
  qed

  show ?thesis using 0 1 2 3 prime val_prod ord_Zp_def  
    by (metis monoid.select_convs(1) Z\<^sub>p_def) 
qed

lemma(in padic_integers) ord_Zp_pow[simp]:
  assumes "x \<in> nonzero Z\<^sub>p"
  shows "ord_Zp (x[^](n::nat)) = n*(ord_Zp x)"
proof(induction n)
  case 0
  have "x[^](0::nat) = \<one>" 
    using assms(1) nonzero_def by (simp add: domain.pow_0)
  then show ?case 
    by (simp add: ord_Zp_one)
next
  case (Suc n)
  fix n 
  assume IH: "ord_Zp (x [^] n) = int n * ord_Zp x "
  have N: "(x [^] n) \<in> nonzero Z\<^sub>p"
  proof-
    have "ord_Zp x \<ge> 0"
      using assms 
      by (simp add: assms Zp_nonzero_def(1) Zp_nonzero_def(2) ord_pos)
    then have "ord_Zp (x [^] n) \<ge> 0"
      using IH assms by simp
    then have 0: "(x [^] n) \<noteq> \<zero>" 
      by (metis Zp_int_inc_closed Zp_int_inc_zero ord_of_nonzero(1))
    have 1: "(x [^] n) \<in> carrier Z\<^sub>p" 
      by (meson Zp_is_domain Zp_nonzero_def(1) assms cring.axioms(1)
          domain.axioms(1) monoid.nat_pow_closed ring_def)
    then show ?thesis 
      using "0" not_nonzero_Zp by blast
  qed
  have "x[^](Suc n) = x \<otimes>(x[^]n)" 
    by (simp add: Zp_nonzero_def(1) assms domain.pow_suc)
  then have "ord_Zp (x[^](Suc n)) =(ord_Zp x) + ord_Zp (x[^]n)" 
    using N Z\<^sub>p_def assms padic_integers.ord_Zp_mult padic_integers_axioms by auto
  then have "ord_Zp (x[^](Suc n)) =(ord_Zp x) +(int n * ord_Zp x)" 
    by (simp add: IH)
  then have "ord_Zp (x[^](Suc n)) =(1*(ord_Zp x)) +(int n) * (ord_Zp x)" 
    by simp
  then have "ord_Zp (x[^](Suc n)) =(1+ (int n)) * ord_Zp x" 
    by (simp add: comm_semiring_class.distrib)
  then show "ord_Zp (x[^](Suc n)) = int (Suc n)*ord_Zp x" 
    by simp
qed

lemma(in padic_integers) val_Zp_pow[simp]:
  assumes "x \<in> nonzero Z\<^sub>p"
  shows "val_Zp (x[^](n::nat)) = *(n*(ord_Zp x))*"
  using Z\<^sub>p_def Zp_nat_pow_nonzero Zp_nonzero_def(2) assms ord_Zp_def
    padic_integers.ord_Zp_pow padic_integers_axioms val_Zp_def by fastforce 

lemma(in padic_integers) ord_Zp_p_pow:
"ord_Zp (\<p>[^](n::nat)) = n"
  using ord_Zp_pow ord_Zp_p Z\<^sub>p_def Zp_nat_inc_closed 
    padic_integers.ord_of_nonzero(2) padic_integers_axioms by auto

lemma(in padic_integers) ord_Zp_p_int_pow:
  assumes "n \<ge>0"
  shows "ord_Zp (\<p>[^](n::int)) = n"
  by (metis assms int_nat_eq int_pow_int ord_Zp_def ord_Zp_p_pow)

lemma(in padic_integers) val_Zp_p:
"(val_Zp \<p>) = (1\<^sub>v)"
 using Z\<^sub>p_def ord_Zp_def padic_val_def val_Zp_def val_of_def ord_Zp_p by auto 

lemma(in padic_integers) val_Zp_p_pow:
"val_Zp (\<p>[^](n::nat)) = Some n"
proof-
  have "(\<p>[^](n::nat)) \<noteq> \<zero>" 
    by (metis Zp_is_domain cring.cring_simprules(2) domain.axioms(1)
        int_eq_iff ord_Zp_def ord_Zp_p_pow ord_of_nonzero(1))
  then show ?thesis  
    using ord_Zp_p_pow  by (simp add: ord_Zp_def val_Zp_def)
qed

lemma(in padic_integers) p_pow_factor[simp]:
  assumes "h \<in> carrier Z\<^sub>p"
  assumes "(n::nat) \<ge> m"
  shows "(h \<otimes> (\<p>[^]n)) m = 0"
proof(cases "h = \<zero>")
  case True
  then show ?thesis 
    using Z\<^sub>p_def Zp_is_domain Zp_nat_inc_closed Zp_nat_pow_nonzero domain.axioms(1) ord_Zp_p
      padic_integers.Zp_nonzero_def(1) padic_integers.ord_of_nonzero(2)
      padic_integers_axioms zero_vals
    by (metis assms(1) cring_def domain.integral_iff domain_def monoid.nat_pow_closed ring_def)
next
  case False
  then have "ord_Zp (h \<otimes> (\<p>[^]n)) \<ge> int m"
    using assms Z\<^sub>p_def Zp_nat_inc_closed Zp_nat_pow_nonzero ord_Zp_p
          ord_Zp_p_pow ord_pos padic_integers.ord_Zp_mult 
          padic_integers.ord_of_nonzero(2) padic_integers_axioms 
    by fastforce
  then show ?thesis 
    by (metis (mono_tags) Zp_is_domain Zp_nat_inc_closed Zp_nat_pow_nonzero assms(1) 
        cring.cring_simprules(5) domain_def mem_Collect_eq nonzero_def 
        ord_Zp_p ord_of_nonzero(2) zero_below_ord zero_le_one)
qed

(*Ultrametric inequality for ord*)

lemma(in padic_integers) ord_Zp_ultrametric:
  assumes "x \<in> nonzero Z\<^sub>p"
  assumes "y \<in> nonzero Z\<^sub>p"
  assumes "x \<oplus> y \<in> nonzero Z\<^sub>p"
  shows "ord_Zp (x \<oplus> y) \<ge> min (ord_Zp x) (ord_Zp y)"
proof-
  have 0:"x \<in> carrier (padic_int p)"
       "y \<in> carrier (padic_int p)"
       "x \<noteq> \<zero>\<^bsub>padic_int p\<^esub>"
       "y \<noteq> \<zero>\<^bsub>padic_int p\<^esub>"
       "x \<oplus> y \<noteq> \<zero>\<^bsub>padic_int p\<^esub>"
    using assms(1) 
     apply(simp add: Z\<^sub>p_def nonzero_def) 
    using  assms(2)
     apply(simp add: Z\<^sub>p_def nonzero_def)
    using assms(1) 
     apply(simp add: Z\<^sub>p_def nonzero_def)  
    using assms(2)
     apply(simp add: Z\<^sub>p_def nonzero_def) 
    using assms(3)
     apply(simp add: Z\<^sub>p_def nonzero_def) 
    done
  have 1: "min (padic_val p x) (padic_val p y) \<le> padic_val p (x \<oplus>\<^bsub>padic_int p\<^esub> y) \<Longrightarrow> ?thesis"
    apply(simp add: ord_Zp_def)
    apply(simp add: Z\<^sub>p_def)
    done
  show ?thesis proof(rule 1)
    show "min (padic_val p x) (padic_val p y) \<le> padic_val p (x \<oplus>\<^bsub>padic_int p\<^esub> y)" 
      using ultrametric 0 1 prime  by (simp add: local.Z\<^sub>p_def) 
  qed
qed

(*val is multiplicative on nonzero elements*)

lemma(in padic_integers) val_Zp_mult0:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "x \<noteq>\<zero>"
  assumes "y \<in> carrier Z\<^sub>p"
  assumes "y \<noteq>\<zero>"
  shows "(val_Zp (x \<otimes>\<^bsub>Z\<^sub>p\<^esub> y)) = (val_Zp x) \<otimes>\<^bsub>G\<^esub> (val_Zp y)"
proof-
  have 0:" Some (ord_Zp x) =(val_Zp x) " 
    using assms(1) assms(2) val_ord_Zp  by blast 
  have 1:"(val_Zp y) = Some (ord_Zp y)" 
    by (simp add: assms(3) assms(4) val_ord_Zp) 
  have "(x \<otimes>\<^bsub>Z\<^sub>p\<^esub> y) \<noteq> \<zero>"
    by (simp add: assms(1) assms(2) assms(3) assms(4) domain.integral_iff) 
  then have 2: "val_Zp (x \<otimes>\<^bsub>Z\<^sub>p\<^esub> y) = Some (ord_Zp (x \<otimes>\<^bsub>Z\<^sub>p\<^esub> y))" 
    by (simp add: ord_Zp_def val_Zp_def) 
  have 3: "(val_Zp x) \<otimes>\<^bsub>G\<^esub> (val_Zp y) = Some ((ord_Zp x) + (ord_Zp y))"
    by (metis "0" "1" G_mult(3)) 
  have 4: "val_Zp (x \<otimes>\<^bsub>Z\<^sub>p\<^esub> y) = Some (ord_Zp  (x \<otimes>\<^bsub>Z\<^sub>p\<^esub> y))" 
    using "2" by auto 
  then show ?thesis using 3 4 ord_Zp_mult assms nonzero_def 
    by (simp add: nonzero_def)   
qed  


(*val is multiplicative everywhere*)
lemma(in padic_integers) val_Zp_mult:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "y \<in> carrier Z\<^sub>p"
  shows "(val_Zp (x \<otimes>\<^bsub>Z\<^sub>p\<^esub> y)) = (val_Zp x) \<otimes>\<^bsub>G\<^esub> (val_Zp y)"
proof(cases "x = \<zero> \<or> y = \<zero>")
  case True
  then have T0: "(x \<otimes>\<^bsub>Z\<^sub>p\<^esub> y) = \<zero>" 
    by (simp add:  assms(1) assms(2) domain.integral_iff) 
  then have "(val_Zp (x \<otimes>\<^bsub>Z\<^sub>p\<^esub> y)) = \<infinity>\<^bsub>G\<^esub>"
    by (simp add: val_Zp_def) 
  then show ?thesis 
    using G_mult(1) G_mult(2) T0 True by auto 
next
  case False
  have F0: "x \<in> carrier Z\<^sub>p" 
    by (simp add: assms(1)) 
  have F1: "x \<noteq>\<zero>" 
    using False by auto 
  have F2: "y \<in> carrier Z\<^sub>p" 
    by (simp add: assms(2)) 
  have F3: "y \<noteq>\<zero>"
    using False by auto 
  then show ?thesis using F0 F1 F2 F3 
    by (simp add: val_Zp_mult0) 
qed

(*ultrametric inequality holds when a, b, and a+b are nonzero:*)

lemma(in padic_integers) val_Zp_ultrametric0:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "x \<noteq>\<zero>"
  assumes "y \<in> carrier Z\<^sub>p"
  assumes "y \<noteq>\<zero>"
  assumes "x \<oplus> y \<noteq> \<zero>"
  shows " Min\<^bsub>G\<^esub> (val_Zp x) (val_Zp y)\<preceq>\<^bsub>G\<^esub>val_Zp (x \<oplus> y) "
proof-
  have Nx: "x \<in> nonzero Z\<^sub>p" 
using assms  by (simp add: nonzero_def) 
  have Ny: "y \<in>nonzero Z\<^sub>p"
using assms  by (simp add: nonzero_def) 
  have "x \<oplus>y \<in>carrier Z\<^sub>p" using assms 
    by (simp add:  cring.cring_simprules(1) domain.axioms(1)) 
  then have Nxy: "x \<oplus>y \<in>nonzero Z\<^sub>p"
    using assms by (simp add: nonzero_def)   
  have 0: "val_Zp (x \<oplus> y) = Some (ord_Zp (x \<oplus> y))"
    using assms val_ord_Zp nonzero_def  
    by (simp add: ord_Zp_def val_Zp_def)  
  have 1: "Min\<^bsub>G\<^esub> (val_Zp x) (val_Zp y) = Some (min (ord_Zp x) (ord_Zp y))"
    by (metis G_ord(2)  assms(2) assms(4)  min_def ord_Zp_def val_Zp_def)
  have 2: "(min (ord_Zp x) (ord_Zp y)) \<le> (ord_Zp (x \<oplus> y))"
    using Nx Ny Nxy ord_Zp_ultrametric by blast  
  show ?thesis 
    using G_ord 0 1 2 by presburger
qed

(*unconstrained ultrametric inequality*)

lemma(in padic_integers) val_Zp_ultrametric:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "y \<in> carrier Z\<^sub>p"
  shows " Min\<^bsub>G\<^esub> (val_Zp x) (val_Zp y) \<preceq>\<^bsub>G\<^esub> val_Zp (x \<oplus> y)"
proof(cases "x = \<zero> \<or> y = \<zero>")
  case True
  then show ?thesis
  proof(cases "x = \<zero>")
    case True
    then have T0:" Min\<^bsub>G\<^esub> (val_Zp x) (val_Zp y) = (val_Zp y)" 
      by (simp add: G_def val_Zp_def) 
    have T1: "val_Zp (x \<oplus> y) = val_Zp y"
      using True by (simp add:  assms(2) cring.cring_simprules(8) domain.axioms(1)) 
    then show ?thesis using T0 T1 
      using G_def extended_order.elims(3) by fastforce   
  next
    case False 
    then have F0:" Min\<^bsub>G\<^esub> (val_Zp x) (val_Zp y) = (val_Zp x)" 
      using G_ord(1) True val_Zp_def 
      by (simp add: G_ord(1))
    have F1: "val_Zp (x \<oplus> y) = val_Zp x"
      using False True Zp_is_domain assms(1) cring.cring_simprules(16) domain.axioms(1) by metis  
    then show ?thesis 
      using F0 F1 G_def extended_order.elims(3) 
      by fastforce
  qed
next
  case False 
  then show ?thesis 
    using val_Zp_ultrametric0 assms G_ord(1) val_Zp_def 
  proof -
    show ?thesis
      by (metis (no_types) False G_ord(1) assms(1) assms(2) val_Zp_def val_Zp_ultrametric0)
  qed
qed

(*Elements with valuation 0 in Zp are the units*)

lemma(in padic_integers) ord_Zp_0_criterion[simp]:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "x 1 \<noteq> 0"
  shows "ord_Zp x = 0"
proof-
  have 0:"x 0 = 0" 
    using Z\<^sub>p_def assms(1) padic_set_simp2 prime by auto
  have 1: "x (Suc 0) \<noteq>0"
    using assms(2) by auto
  show ?thesis 
    using 0 1 assms(1) ord_equals by auto
qed

(*Units in Zp have ord 0*)

lemma(in padic_integers) unit_imp_ord_Zp0[simp]:
  assumes "x \<in> Units Z\<^sub>p"
  shows "ord_Zp x = 0"
proof-
  let ?y = "inv x"
  have "x \<otimes> ?y = \<one>" 
    by (meson Zp_is_domain assms cring_def
        domain.axioms(1) monoid.Units_r_inv ring_def) 
  then have 0:"(ord_Zp x) + (ord_Zp ?y) = 0" 
    by (metis (no_types, lifting) Z\<^sub>p_def Zp_is_domain assms cring.axioms(1)
        domain.axioms(1) domain.integral_iff domain.one_not_zero monoid.Units_inv_Units
        monoid.Units_inv_closed monoid.Units_inv_inv monoid.select_convs(1)
        ord_Zp_def ord_Zp_one partial_object.select_convs(1) 
        prime ring_def ring_record_simps(11) val_prod) 
  have 1:"x \<noteq>\<zero>" using assms 
    by (metis Zp_is_domain cring.cring_simprules(27)
        cring_def domain.axioms(1) domain_axioms_def
        domain_def monoid.Units_l_inv_ex ring_def) 
  have 2: "?y \<noteq>\<zero>" 
    by (metis Zp_is_domain \<open>x \<otimes> inv x = \<one>\<close> assms cring.cring_simprules(27) 
        cring_def domain.axioms(1) domain.one_not_zero monoid.Units_closed ring_def) 
  have 3: "ord_Zp x \<ge>0" using 1 
    by (simp add: Z\<^sub>p_def ord_Zp_def padic_val_def) 
  have 4: "ord_Zp ?y \<ge>0" using 2 
    by (simp add: Z\<^sub>p_def ord_Zp_def padic_val_def) 
  show ?thesis using 3 4 0 
    by linarith 
qed

(*Units in Zp have val 0*) 

lemma(in padic_integers) unit_imp_val_Zp0[simp]:
  assumes "x \<in> Units Z\<^sub>p"
  shows "val_Zp x = Some 0"
  using unit_imp_ord_Zp0 val_ord_Zp G_def
    Z\<^sub>p_def assms ord_Zp_def padic_val_def val_Zp_def by force

(*elements in Zp with ord 0 are units*)

lemma(in padic_integers) ord_Zp0_imp_unit0[simp]:
  assumes "ord_Zp x = 0"
  assumes "x \<in> carrier Z\<^sub>p"
  fixes n::nat
  shows "(x (Suc n)) \<in> Units (R (Suc n))"
proof-
  have Res: "residues (p^(Suc n))" 
    by (metis One_nat_def cancel_comm_monoid_add_class.diff_cancel linorder_neqE_linordered_idom
        nat_int nat_one_as_int  not_prime_0 of_nat_le_0_iff  old.nat.distinct(2)
        power_not_zero prime prime_power_eq_one_iff residues_def zle_diff1_eq) 
  have "\<And> n. coprime (x (Suc n)) p"
  proof-
    fix n
    show "coprime (x (Suc n)) p"
    proof-
      have "\<not> \<not> coprime (x (Suc n)) p"
      proof
        assume "\<not> coprime (x (Suc n)) (int p)" 
        then have "p dvd (x (Suc n))" using prime 
          by (meson coprime_commute prime_imp_coprime prime_nat_int_transfer) 
        then obtain k where "(x (Suc n)) = k*(int p)"  
          by fastforce 
        then have S:"x (Suc n) mod p = 0" 
          by simp 
        have "x 1 = 0"
        proof-
          have "Suc n \<ge> 1" 
            by simp 
          then have "x 1 = r 1 (x (Suc n))"
            using r_Zp assms(2) by presburger 
          then show ?thesis using S 
            by (metis r_def power_one_right) 
        qed
        have "x \<noteq>\<zero>" 
        proof-
          have "ord_Zp x \<noteq> ord_Zp \<zero>" 
            using Z\<^sub>p_def ord_Zp_def padic_val_def assms(1) by simp 
          then show ?thesis 
            by blast 
        qed
        then have "x 1 \<noteq>0" using assms(1) assms(2)  ord_suc_nonzero 
          by (simp ) 
        then show False 
          using \<open>x 1 = 0\<close> by blast 
      qed
      then show ?thesis 
        by auto 
    qed
  qed
  then have "\<And> n. coprime (x (Suc n)) (p^(Suc n))"
    by simp 
  then have "coprime (x (Suc n)) (p^(Suc n))"
    by blast 
  then show ?thesis using residues.res_units_eq  Res  
    by (metis (no_types, lifting) r_Zp r_def assms(2) 
        le_eq_less_or_eq residues.m_gt_one residues.mod_in_res_units)  
qed

lemma(in padic_integers) ord_Zp_0_imp_unit[simp]:
  assumes "ord_Zp x = 0"
  assumes "x \<in> carrier Z\<^sub>p"
  shows "x \<in> Units Z\<^sub>p"
proof-
  let ?y = "\<lambda>n. (if n=0 then 0 else (m_inv (R n) (x n)))"
  have 1: "?y \<in> padic_set p"
  proof(rule padic_set_mem)
    show " \<And>m. (if m = 0 then 0 else inv\<^bsub>R m\<^esub> x m) \<in> carrier (residue_ring (int p ^ m))" 
    proof-
      fix m
      show "?y m \<in> carrier (residue_ring (int p ^ m))"
      proof(cases "m=0")
        case True
        then show ?thesis 
          using Res_0  by auto 
      next
        case False
        have "p^m > 1" 
          by (metis False less_le one_le_power prime prime_ge_1_nat prime_power_eq_one_iff) 
        then have Res: "residues (p^m)"   
          using less_imp_of_nat_less residues.intro by fastforce 
        have  "(x m) \<in> Units (R m)" 
          using False ord_Zp0_imp_unit0 assms gr0_implies_Suc by blast 
        then have U: "(x m) \<in> Units (residue_ring (p^m))"
          by simp 
        have I:"?y m = m_inv (residue_ring (p^m)) (x m)"
          using False  by (simp add: ) 
        show ?thesis using residues.cring U I Res 
          by (metis False  \<open>x m \<in> Units R m\<close> cring_def
              monoid.Units_inv_closed of_nat_power ring_def) 
      qed
    qed
    show " \<And>m n. m < n \<Longrightarrow> res (int p ^ m) (if n = 0 then 0 else inv\<^bsub>R n\<^esub> x n) = (if m = 0 then 0 else inv\<^bsub>R m\<^esub> x m)"
    proof-
      fix m n::nat
      assume  "m < n"
      show "res (int p ^ m) (if n = 0 then 0 else inv\<^bsub>R n\<^esub> x n) = (if m = 0 then 0 else inv\<^bsub>R m\<^esub> x m)"
      proof(cases "m = 0")
        case True
        then show ?thesis 
          by (simp add: res_def) 
      next
        case False
        have "(p^m) > 1" 
          using False one_less_power prime prime_gt_1_nat by blast 
        then have Rm: "residues (p^m)" 
          by (metis nat_int nat_less_eq_zless nat_one_as_int residues.intro zero_le_one) 
        have "(p^n)>1" 
          using \<open>m < n\<close> le0 le_less_trans one_less_power prime prime_gt_1_nat by blast 
        then have Rn: "residues (p^n)" 
          using less_imp_of_nat_less residues.intro by fastforce
        have Um: "(x m) \<in> Units (residue_ring (p^m))" 
          by (metis False  Z\<^sub>p_def assms(1) assms(2) gr0_implies_Suc 
              linorder_neqE_nat not_less0 padic_integers.ord_Zp0_imp_unit0 padic_integers_axioms) 
        have Un: "(x n) \<in> Units (residue_ring (p^n))" 
          by (metis  Z\<^sub>p_def \<open>m < n\<close> assms(1) assms(2)
              lessE padic_integers.ord_Zp0_imp_unit0 padic_integers_axioms) 
        have Yn: "?y n = m_inv (residue_ring (p^n)) (x n)" 
          using  \<open>m < n\<close> by auto 
        have Ym: "?y m = m_inv (residue_ring (p^m)) (x m)" 
          by (simp add: False ) 
        have XYn: "(?y n) * (x n) mod (p^n)  = 1"
        proof-
          have "cring (residue_ring (p^n))"
            using Rn residues.cring by auto 
          then have "monoid  (residue_ring (p^n))" 
            using cring_def ring_def by blast 
          then have "(?y n) \<otimes>\<^bsub>residue_ring (p^n)\<^esub>(x n) = \<one>\<^bsub>residue_ring (p^n)\<^esub>"
            using Un Yn  by (simp add: monoid.Units_l_inv)   
          then show ?thesis
            using residue_ring_def by simp 
        qed
        have XYm: "(?y m) * (x m) mod (p^m)  = 1"
        proof-
          have "cring (residue_ring (p^m))"
            using Rm residues.cring by auto 
          then have "monoid  (residue_ring (p^m))" 
            using cring_def ring_def by blast 
          then have "(?y m) \<otimes>\<^bsub>residue_ring (p^m)\<^esub>(x m) = \<one>\<^bsub>residue_ring (p^m)\<^esub>"
            using Um Ym  by (simp add: monoid.Units_l_inv)   
          then show ?thesis
            using residue_ring_def by simp 
        qed          
        have 0:"res (int p ^ m) ((x n)* (?y n))
        = ((res (int p ^ m) (x n))*(res (int p ^ m) (?y n))) mod (p^m)" 
          using res_def    by (simp add: mod_mult_eq) 
        then have "((res (int p ^ m) (x n))*(res (int p ^ m) (?y n))) mod (p^m) = 1"  
          by (metis XYm XYn r_def r_mod \<open>m < n\<close> mod_mod_trivial mult.commute of_nat_power) 
        then have 1: "(x m)*(res (int p ^ m) (?y n)) mod (p^m) = 1"  
          using r_Zp \<open>m < n\<close> assms(2) by auto 
        then have 1:  "(x m) \<otimes>\<^bsub>residue_ring (p^m)\<^esub>(res (int p ^ m) (?y n)) = \<one>\<^bsub>residue_ring (p^m)\<^esub>"  
          using Rm residues.res_mult_eq residues.res_one_eq by auto 
        show "(res (int p ^ m) (?y n)) = (?y m)" 
        proof-
          have "cring (residue_ring (p^m))" 
            using Rm residues.cring by auto 
          then have "monoid (residue_ring (p^m))" 
            using cring_def ring_def by blast 
          then show ?thesis  using XYm Um Ym Rm 1 
            by (metis (no_types, lifting) r_def \<open>cring (residue_ring (int (p ^ m)))\<close> 
                cring.cring_simprules(14) monoid.Units_closed monoid.inv_unique'  
                of_nat_power residues.mod_in_carrier)   
        qed
      qed
    qed
  qed
  have 2: "?y \<otimes> x = \<one>"
  proof
    fix m
    show "(?y \<otimes> x) m = \<one> m"
    proof(cases "m=0")
      case True
      then have L: "(?y \<otimes> x) m  = 0"  
        using  Z\<^sub>p_def "1" assms(2) padic_mult_closed padic_set_simp2 prime by auto 
      have R: "\<one> m = 0" 
        by (simp add: True cring.cring_simprules(6) domain.axioms(1) ord_Zp_one zero_below_ord) 
      then show ?thesis using L R by auto 
      next
        case False
        have P: "(?y \<otimes> x) m = (?y m) \<otimes>\<^bsub>residue_ring (p^m)\<^esub> (x m)"
          using Z\<^sub>p_def by (simp add: padic_mult_simp) 
        have "(?y m) \<otimes>\<^bsub>residue_ring (p^m)\<^esub> (x m) = 1"
        proof-
          have "p^m > 1" using False 
            by (metis less_le one_le_power prime prime_ge_1_nat prime_power_eq_one_iff) 
          then have "residues (p^m)"  
            using less_imp_of_nat_less residues.intro by fastforce 
          have "cring (residue_ring (p^m))" 
            using \<open>residues (int (p ^ m))\<close> residues.cring by blast 
          then have M: "monoid (residue_ring (p^m))" 
            using cring_def ring_def by blast 
          have U: "(x m) \<in> Units (residue_ring (p^m))" 
            by (metis (mono_tags, hide_lams) False  
                assms(1) assms(2) old.nat.exhaust ord_Zp0_imp_unit0 ord_Zp_def)
          have I: "?y m = m_inv (residue_ring (p^m)) (x m)" 
            by (simp add: False ) 
          have "(?y m) \<otimes>\<^bsub>residue_ring (p^m)\<^esub> (x m) = \<one>\<^bsub>residue_ring (p^m)\<^esub>"
            using M U I by (simp add: monoid.Units_l_inv) 
          then show ?thesis
            using residue_ring_def by simp 
        qed
        then show ?thesis 
          using P Z\<^sub>p_def by (simp add: False padic_one_def) 
    qed
  qed
  have 3: "?y \<in> carrier Z\<^sub>p"
    using 1 by (simp add: Z\<^sub>p_def) 
  have "\<exists>y\<in>carrier Z\<^sub>p. x \<otimes>y = \<one> \<and> y \<otimes> x = \<one>" 
    using 1 2 3 Zp_is_domain assms(2) cring.cring_simprules(14) domain.axioms(1) 
    by (metis (no_types, lifting)) 
  then show ?thesis 
    using Units_def assms(2)   by force
qed

(*Definition of ord on a fraction is independent of the choice of representatives*)

lemma(in padic_integers) ord_Zp_eq_frac:
  assumes "a \<in> nonzero Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  assumes "c \<in> nonzero Z\<^sub>p"
  assumes "d \<in> nonzero Z\<^sub>p"
  assumes "a \<otimes> d = b \<otimes> c"
  shows "(ord_Zp a) - (ord_Zp b) = (ord_Zp c) - (ord_Zp d)"
proof-
  have "ord_Zp (a \<otimes> d) = ord_Zp (b \<otimes> c)"
    using assms 
    by presburger
  then have "(ord_Zp a) + (ord_Zp  d) = (ord_Zp b) + (ord_Zp c)"
    using assms(1) assms(2) assms(3) assms(4) ord_Zp_mult by metis  
  then show ?thesis 
    by linarith 
qed

lemma(in padic_integers) val_Zp_eq_frac_0:
  assumes "a \<in> nonzero Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  assumes "c \<in> nonzero Z\<^sub>p"
  assumes "d \<in> nonzero Z\<^sub>p"
  assumes "a \<otimes> d = b \<otimes> c"
  shows "(val_Zp a) \<ominus>\<^bsub>G\<^esub> (val_Zp b) = (val_Zp c) \<ominus>\<^bsub>G\<^esub> (val_Zp d)"
proof- 
  have 0:"(val_Zp a) \<ominus>\<^bsub>G\<^esub> (val_Zp b) = *(ord_Zp a) - (ord_Zp b)*" 
    by (metis assms(1) assms(2) gminus_minus Zp_nonzero_def(1) Zp_nonzero_def(2) val_ord_Zp) 
  have 1: "(val_Zp c) \<ominus>\<^bsub>G\<^esub> (val_Zp d) = *(ord_Zp c) - (ord_Zp d)*" 
    by (simp add: assms(3) assms(4) gminus_minus Zp_nonzero_def(2) ord_Zp_def val_Zp_def)
  then show ?thesis 
    using "0" assms(1) assms(2) assms(3) assms(4) assms(5) ord_Zp_eq_frac 
    by presburger
qed


(*Showing that the image of Zp in Qp is a subring*)

lemma(in padic_integers) p_pow_rep0:
  fixes n::nat
  shows "\<p>[^]n = [(p^n)]\<cdot>\<one>"
proof(induction n)
  case 0
  have "\<p> \<noteq> \<zero>"
  proof
    assume "\<p> = \<zero>"
    then have 0: "ord_Zp \<p> = ord_Zp \<zero>" 
      by presburger
    have 1: "ord_Zp \<p> = 1" 
      by (simp add: ord_Zp_p) 
    have 2: "ord_Zp \<zero> = -1" 
      using ord_Zp_def padic_val_def Z\<^sub>p_def by simp
    then show False 
      using "0" ord_Zp_p 
      by (simp add: "2" ord_Zp_p)
  qed
  then have L:"\<p>[^](0::nat) = \<one>" using nat_pow_def  
    by (metis int_ops(1) int_pow_int old.nat.simps(6)) 
  have "[(p^0)]\<cdot>\<one> = [(1::nat)]\<cdot>\<one>" 
    by simp 
  have "[(1::nat)]\<cdot>\<one> = \<one> [^]\<^bsub>add_monoid Z\<^sub>p\<^esub> (1 :: nat)" 
    by (simp add: add_pow_def) 
  then have "[(1::nat)]\<cdot>\<one>  = rec_nat \<one>\<^bsub>add_monoid Z\<^sub>p\<^esub> (\<lambda>u b. b \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub> \<one>) (1:: nat)"   
    using nat_pow_def Z\<^sub>p_def  by (simp add: nat_pow_def) 
  then have "[(1::nat)]\<cdot>\<one>  = [(0::nat)]\<cdot>\<one> \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub> \<one>" 
    by (simp add: Zp_nat_inc_zero) 
  then have "[(1::nat)]\<cdot>\<one> = \<zero> \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub> \<one>" 
    using Zp_nat_inc_zero by auto 
  then have "[(1::nat)]\<cdot>\<one> =  \<one>" using Zp_is_domain domain_def 
    by (simp add: domain_def cring.cring_simprules(6) cring.cring_simprules(8)) 
  then show ?case 
    by (simp add: L) 
next
  case (Suc n)
  fix n
  assume A: "\<p> [^] n = [(p ^ n)] \<cdot> \<one>"
  show "\<p> [^] Suc n = [(p ^ Suc n)] \<cdot> \<one>"
  proof
    fix x
    show "(\<p> [^] Suc n) x = ([(p ^ Suc n)] \<cdot> \<one>) x "
    proof(cases "x = 0")
      case True
      have "(\<p> [^] Suc n) \<in> carrier Z\<^sub>p" using Zp_is_domain 
        by (simp add: cring_def domain_def monoid.nat_pow_closed Zp_nat_inc_closed ring_def) 
      then have "(\<p> [^] Suc n) x  = 0" using True 
        by (simp add: ord_Zp_p_pow zero_below_ord)
      then show ?thesis using Zp_is_domain 
        using True Zp_nat_inc_rep res_1_zero by auto 
    next
      case False
      have 0: " [(p ^ n)] \<cdot> \<one> \<in> carrier Z\<^sub>p"
         by (simp add: Zp_nat_inc_closed) 
      have "\<p> [^] Suc n = \<p> \<otimes> \<p> [^] n" 
        by (metis A Zp_is_domain cring_def domain_def monoid.nat_pow_Suc2 Zp_nat_inc_closed ring_def) 
      then have L: "\<p> [^] Suc n = \<p> \<otimes>  [(p ^ n)] \<cdot> \<one>" 
        by (simp add: A) 
      then have "\<p> [^] Suc n = ([p]\<cdot>\<one>) \<otimes>  [(p ^ n)] \<cdot> \<one>" 
        by blast 
      then have "(\<p> [^] Suc n) x = (([p]\<cdot>\<one>) \<otimes>  [(p ^ n)] \<cdot> \<one>) x" 
        by simp  
      then have "(\<p> [^] Suc n) x = ([p]\<cdot>\<one>) x  \<otimes>\<^bsub>R x\<^esub> ([(p ^ n)] \<cdot> \<one>) x" 
        using Z\<^sub>p_def  by (simp add: padic_mult_def) 
      then have "(\<p> [^] Suc n) x =  r x p  \<otimes>\<^bsub>R x\<^esub> r x (p ^ n)" 
        using Zp_nat_inc_rep  by simp 
      then have "(\<p> [^] Suc n) x =  ( p  * (p ^ n)) mod (p^x)" 
        using  r_def residue_ring_def  by (simp add: mod_mult_eq of_nat_mod) 
      then have "(\<p> [^] Suc n) x =  (p^(Suc n)) mod (p^x)" 
        by simp 
      then show ?thesis 
        using Zp_nat_inc_rep r_def by (simp add: of_nat_mod) 
    qed
  qed
qed

lemma(in padic_integers) p_pow_nonzero_0[simp]:
  shows "(\<p>[^](n::nat)) \<in> carrier Z\<^sub>p"
        "(\<p>[^](n::nat)) \<noteq> \<zero>"
  apply (simp add: Zp_nat_inc_closed p_pow_rep0)
  apply (simp add: Zp_nat_inc_closed p_pow_rep0)
  using Zp_nat_inc_closed ord_Zp_p_pow ord_of_nonzero(1) p_pow_rep0 
  by (simp add: Z\<^sub>p_def)

lemma(in padic_integers) p_pow_nonzero[simp]:
  shows "(\<p>[^](n::nat)) \<in> nonzero Z\<^sub>p"
  using nonzero_def p_pow_nonzero_0 
  by (simp add: nonzero_def)


lemma(in padic_integers) p_pow_rep:
  fixes n::nat
  shows "(\<p>[^]n) k = (p^n) mod (p^k)"
  by (metis Zp_nat_inc_rep of_nat_mod p_pow_rep0 r_def)


lemma(in padic_integers) p_pow_car_nat[simp]:
  fixes n::nat
  shows "(\<p>[^]n) \<in> carrier Z\<^sub>p"
  by simp

lemma(in padic_integers) p_pow_car[simp]:
  assumes " (n::int)\<ge> 0"
  shows "(\<p>[^]n) \<in> carrier Z\<^sub>p"
proof-
  have "(\<p>[^]n) = (\<p>[^](nat n))" 
    by (metis assms int_nat_eq int_pow_int) 
  then show ?thesis using p_pow_car_nat 
    by simp 
qed

lemma(in padic_integers) p_int_pow_nonzero[simp]:
  assumes "(n::int) \<ge>0"
  shows "(\<p>[^]n) \<in> nonzero Z\<^sub>p"
  by (metis assms int_eq_iff int_pow_int p_pow_nonzero)

(*Every element of Zp is a unit times a power of p.*)

lemma(in padic_integers) res_factor_unique:
  assumes "k>0"
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "u \<in> carrier (R k) \<and> (u* p^m) = (x (m+k))"
  shows "u = (THE u. u \<in> carrier (R k) \<and> (u* p^m) = (x (m+k)))"
proof-
  obtain P where 
    P_def: "P = (\<lambda> u.  u \<in> carrier (R k) \<and> (u* p^m) = (x (m+k)))"
    by simp
  have 0: "P u" 
    using P_def assms(3) by blast
  have 1: "\<And> v. P v \<Longrightarrow> v = u" 
    by (metis P_def assms(3) mult_cancel_right nat_int 
        nat_zero_as_int not_prime_0 power_not_zero prime)
  have "u =  (THE u. P u)" 
    by (metis 0 1 the_equality)
  then show ?thesis using P_def 
    by blast
qed

lemma(in padic_integers) res_factor_exists:
  assumes "m = nat (ord_Zp x)"
  assumes "k > 0"
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "x \<noteq>\<zero>"
  obtains u where "u \<in> carrier (R k) \<and> (u* p^m) = (x (m+k))"
proof-
  have X0: "(x (m+k)) \<in> carrier (R (m+k)) " 
    using Z\<^sub>p_def assms(3) padic_set_simp0 by auto 
  then have X1: "(x (m+k)) \<ge> 0" 
    using R_residues  assms(2) residues.res_carrier_eq  by simp
  then have X2: "(x (m+k)) > 0"  
    using assms(1) assms(2) assms(3) assms(4) above_ord_nonzero 
    by (metis add.right_neutral add_cancel_right_right 
        add_gr_0 int_nat_eq less_add_same_cancel1 
        less_imp_of_nat_less not_gr_zero of_nat_0_less_iff of_nat_add ord_pos)
  have 0: "x m = 0" 
    using  Z\<^sub>p_def assms(1) assms(3) zero_below_val  ord_nat zero_below_ord[of x m] zero_vals 
           assms(4) ord_Zp_def by auto
  then have 1: "x (m +k) mod int (p ^ m) = 0" 
    using assms(2) assms(3) r_Zp res_def by auto
  then have "\<exists> u.  u*(int p^m) = (x (m+k))" 
    by auto
 then obtain u where U0: " u*(int p^m) = (x (m+k))" 
   by blast
  have I: "(int p^m) > 0  " 
    using prime prime_gt_0_nat by auto
  then have U1: "(u* p^m) = (x (m+k))" 
    by (simp add: U0)
  have U2: "u \<ge> 0" 
    using I U1 X1 
    by (metis U0 less_imp_triv mult.right_neutral mult_less_cancel_left
        of_nat_zero_less_power_iff power.simps(1) times_int_code(1))
  have X3: "(x (m+k)) < p^(m+k)" 
    using assms(3) X0  R_residues assms(2) residues.res_carrier_eq by auto
  have U3: "u < p^k" 
  proof(rule ccontr)
    assume "\<not> u < (p ^ k)"
    then have "(p^k) \<le> u" 
      by simp
    then have " (int (p^k) * int (p^m)) \<le> u*(p^m)" 
      using I by simp
    then have "p^(m + k) \<le> (x (m+k))" 
      by (simp add: U0 add.commute semiring_normalization_rules(26))
    then show False 
      using X3 by linarith
  qed
  then have "u \<in> carrier (R k)" 
    using assms(2)  R_residues residues.res_carrier_eq U3 U2 by auto
  then show ?thesis using U1  that by blast
qed

definition(in padic_integers) normalizer where 
"normalizer m x = (\<lambda>k. if (k=0) then 0 else (THE u. u \<in> carrier (R k) \<and> (u* p^m) = (x (m + k)) ) )"

definition(in padic_integers) ac_Zp where 
"ac_Zp x = normalizer (nat (ord_Zp x)) x"

lemma(in padic_integers) ac_Zp_equation:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "x \<noteq>\<zero>"
  assumes "k > 0"
  assumes "m = nat (ord_Zp x)"
  shows "(ac_Zp x k) \<in> carrier (R k) \<and> (ac_Zp x k)*(p^m) = (x (m+k))" 
proof-
  have K0: "k >0" 
    using assms nat_neq_iff by blast
  have KM: "m+ k > m" 
    using assms(3) assms(4) by linarith
  obtain u where U0: "u \<in> carrier (R k) \<and> (u* p^m) = (x (m+k))"
    using assms(1) assms(2) assms(3) assms(4) res_factor_exists by blast
  have RHS: "ac_Zp x k = (THE u. u \<in> carrier (R k) \<and> u*(p^m) = (x (m+k)))" 
  proof-
    have K: "k \<noteq>0" 
      by (simp add: K0)
    have "ac_Zp x k = normalizer (nat (ord_Zp x)) x k" 
      using ac_Zp_def by presburger
    then have "ac_Zp x k = normalizer m x k" 
      using assms by blast
    then show "ac_Zp x k = (THE u. u \<in> carrier (R k) \<and> (u* p^m) = (x (m + k)) ) "
      using normalizer_def K by simp   
  qed
  have LHS:"u = (THE u. u \<in> carrier (R k) \<and> u*(p^m) = (x (m+k)))" 
    using assms U0 K0 assms(1) res_factor_unique[of k x u m] by metis    
  then have "u = ac_Zp x k" 
    by (simp add: RHS)
  then show ?thesis using U0 by auto  
qed

lemma(in padic_integers) ac_Zp_res[simp]:
  assumes "m >k"
  assumes "n = nat (ord_Zp x)"
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "x \<noteq>\<zero>"
  shows "r k (ac_Zp x m) = (ac_Zp x k)"
proof(cases "k =0")
  case True
  then show ?thesis 
    by (metis ac_Zp_def mod_by_1 normalizer_def of_nat_1 power.simps(1) r_def)
next
  case False
  then have K0: "k >0" by simp
  obtain uk where Uk0: "uk = (ac_Zp x k)" 
    by simp
  obtain um where Um0: "um = (ac_Zp x m)" 
    by simp
  have Uk1: "uk \<in> carrier (R k) \<and> uk*(p^n) = (x (n+k))" 
    using K0 Uk0 ac_Zp_equation assms(2) assms(3) assms(4) by metis 
  have Um1: "um \<in> carrier (R m) \<and> um*(p^n) = (x (n+m))" 
    using Uk1 Um0 ac_Zp_equation assms(1) assms(3) assms(4) assms(2) 
    by (metis neq0_conv not_less0) 
  have "um mod (p^k) = uk"
  proof-
    have "(x (n+m)) mod (p^(n + k)) = (x (n+k))"
      using assms(1) assms(3) r_Zp r_def by auto
    then have "(p^(n + k)) dvd (x (n+m)) - (x (n+k))" 
      by (metis dvd_minus_mod)
    then obtain d where "(x (n+m)) - (x (n+k)) = (int (p^(n+k)))*d" 
      using dvd_def by blast
    then have "((um*(p^n)) - (uk*(p^n))) =  (int (p^(n+k)))*d" 
      using Uk1 Um1 by auto
    then have "((um - uk)*(p^n)) =  (int (p^(n+k)))*d"
      by (simp add: left_diff_distrib)
    then have "((um - uk)*(p^n)) =  ((p^k)*d)*(p^n)" 
      by (simp add: power_add)
    then have "(um - uk) =  ((p^k)*d)" 
      using prime by auto
    then have "um mod p^k = uk mod p^k" 
      by (simp add: mod_eq_dvd_iff)
    then show ?thesis  using Uk1  
      by (metis of_nat_0_le_iff r_def res_id)
  qed
  then show ?thesis 
    by (simp add: Uk0 Um0 res_def)
qed

lemma(in padic_integers) ac_Zp_in_Zp[simp]:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "x \<noteq>\<zero>"
  shows "ac_Zp x \<in> carrier Z\<^sub>p"
proof-
  have "ac_Zp x \<in> padic_set p"
  proof(rule padic_set_mem)
    show "\<And>m. ac_Zp x m \<in> carrier (residue_ring (int p ^ m))"
    proof- 
      fix m
      show "ac_Zp x m \<in> carrier (residue_ring (int p ^ m))"
      proof(cases "m = 0")
        case True
        then have "ac_Zp x m = 0" 
          using ac_Zp_def normalizer_def 
          by (simp add: ord_Zp_def)
        then show ?thesis 
          by (simp add: True residue_ring_def)
      next
        case False
        then have "m>0" 
          by blast
        then show ?thesis 
          using ac_Zp_equation 
          by (metis assms(1) assms(2) of_nat_power)
      qed
    qed
    show "\<And>m n. m < n \<Longrightarrow> res (int p ^ m) (ac_Zp x n) = ac_Zp x m"
    proof-
      fix m n::nat
      assume A: "m < n"
      have "int p^m = int (p^m)"
        by auto 
      then show " res (int p ^ m) (ac_Zp x n) = ac_Zp x m"
        using A assms(1) assms(2) ac_Zp_res[of m n "nat (ord_Zp x)" x] 
        unfolding res_def r_def 
        by metis 
    qed
  qed
  show ?thesis 
    by (simp add: Z\<^sub>p_def \<open>ac_Zp x \<in> padic_set p\<close>)
qed

lemma(in padic_integers) ac_Zp_is_Unit[simp]:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "x \<noteq>\<zero>"
  shows "ac_Zp x \<in> Units Z\<^sub>p"
proof(rule ord_Zp_0_imp_unit)
  show "ac_Zp x \<in> carrier Z\<^sub>p" 
    by (simp add: assms(1) assms(2))
  obtain m where M: "m = nat (ord_Zp x)"
    by blast
  have AC1: "(ac_Zp x 1)*(p^m) = (x (m+1))"
    using M ac_Zp_equation assms(1) assms(2) 
    by (metis One_nat_def lessI)
  have "(x (m+1)) \<noteq>0" 
    using M assms 
    by (metis Suc_eq_plus1 Suc_le_eq nat_int nat_mono nat_neq_iff ord_Zp_geq)
  then have "(ac_Zp x 1) \<noteq> 0" 
    using AC1 by auto
  then show "ord_Zp (ac_Zp x) = 0"
    by (simp add: assms(1) assms(2))
qed

lemma(in padic_integers) ac_Zp_factors_x:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "x \<noteq>\<zero>"
  shows "x = (\<p>[^](nat (ord_Zp x))) \<otimes> (ac_Zp x)"
proof
  fix k
  show "x k = ((\<p>[^](nat (ord_Zp x))) \<otimes> (ac_Zp x)) k"
  proof(cases "k=0")
    case True
    then show ?thesis 
      by (metis Z\<^sub>p_def Zp_is_domain ac_Zp_in_Zp assms(1) assms(2) cring.cring_simprules(5)
          domain.axioms(1) p_pow_car_nat padic_set_simp2 partial_object.select_convs(1) prime)
  next
    case False
    show ?thesis
    proof(cases "k \<le> ord_Zp x")
      case True
      have 0: "x k = 0" 
        using True assms(1) zero_below_ord by blast
      have 1: "(\<p>[^](nat (ord_Zp x))) k = 0" 
        using True ord_Zp_p_pow p_pow_car_nat zero_below_ord 
              assms(1) assms(2) ord_nat by presburger
      have "((\<p>[^](nat (ord_Zp x))) \<otimes> (ac_Zp x)) k = (\<p>[^](nat (ord_Zp x))) k * (ac_Zp x) k mod p^k" 
        using Z\<^sub>p_def padic_mult_simp residue_ring_def by simp
      then have "((\<p>[^](nat (ord_Zp x))) \<otimes> (ac_Zp x)) k = 0" 
        by (meson "1" False ac_Zp_in_Zp assms(1) assms(2) nat_neq_iff
            not_less0 p_pow_car_nat res_mult_zero(1))
      then show ?thesis using 0 
        by metis 
    next
      case False
      obtain n where N: "n = nat (ord_Zp x)" 
        by metis 
      obtain m where M0: "k = n + m" 
        using False N le_Suc_ex ord_Zp_def by fastforce
      have M1: "m >0" 
        using M0 False N assms(1) assms(2) ord_nat 
        by (metis Nat.add_0_right gr0I le_refl less_eq_int_code(1) 
            nat_eq_iff2 neq0_conv of_nat_eq_0_iff of_nat_mono)
      have E1: "(ac_Zp x m)*(p^n) = (x k)" 
        using M0 M1 N ac_Zp_equation assms(1) assms(2) by blast
      have E2: "(ac_Zp x k)*(p^n) = (x (n + k))" 
        using M0 M1 N ac_Zp_equation assms(1) assms(2) add_gr_0 
        by presburger
      have E3: "((ac_Zp x k) mod (p^k))*((p^n) mod p^k) mod (p^k) = (x (n + k)) mod (p^k)"
        by (metis E2 mod_mult_left_eq mod_mult_right_eq of_nat_mod)
      have E4: "((ac_Zp x k) mod (p^k))*(p^n) mod (p^k) = (x k)" 
        by (metis E2 assms(1) le_add2 mod_mult_left_eq r_Zp r_def)
      have E5: "(ac_Zp x k)*((p^n) mod p^k) mod (p^k) = (x k)" 
        using E2 assms(1) r_Zp r_def by (metis E3 E4 mod_mult_left_eq)
      have E6: "(ac_Zp x k) \<otimes>\<^bsub>(R  k)\<^esub> ((p^n) mod p^k)  = (x k)" 
        using E5 M0 M1 R_residues  residues.res_mult_eq by auto
      have E7: " ((p^n) mod p^k) \<otimes>\<^bsub>(R  k)\<^esub>(ac_Zp x k)   = (x k)" 
        by (metis E5 M0 M1 R_residues  add_gr_0 mult_of_nat_commute residues.res_mult_eq)
      have E8: "((\<p>[^](nat (ord_Zp x))) k) \<otimes>\<^bsub>(R  k)\<^esub> (ac_Zp x k) = (x k)" 
        using E7 N p_pow_rep 
        by metis 
      then show ?thesis 
        by (simp add:  Z\<^sub>p_def padic_mult_simp)
    qed
  qed
qed

lemma(in padic_integers) ac_Zp_mult:
  assumes "x \<in> nonzero Z\<^sub>p"
  assumes "y \<in> nonzero Z\<^sub>p"
  shows "ac_Zp (x \<otimes> y) = (ac_Zp x) \<otimes> (ac_Zp y)"
proof-
  have P0: "x = (\<p>[^](nat (ord_Zp x))) \<otimes> (ac_Zp x)"
    using Zp_nonzero_def(1) Zp_nonzero_def(2) ac_Zp_factors_x assms(1) by blast
  have P1: "y = (\<p>[^](nat (ord_Zp y))) \<otimes> (ac_Zp y)"
    using Zp_nonzero_def(1) Zp_nonzero_def(2) ac_Zp_factors_x assms(2) by blast
  have "x \<otimes> y = (\<p>[^](nat (ord_Zp (x \<otimes> y)))) \<otimes> (ac_Zp (x \<otimes> y))"
  proof-
    have "x \<otimes> y \<in> nonzero Z\<^sub>p"
      by (meson Localization.submonoid.m_closed Zp_is_domain
          assms(1) assms(2) domain.nonzero_is_submonoid)
    then show ?thesis 
      using Zp_nonzero_def(1) Zp_nonzero_def(2) ac_Zp_factors_x 
      by blast
  qed
  then have "x \<otimes> y =  (\<p>[^](nat ((ord_Zp x) + (ord_Zp y)))) \<otimes> (ac_Zp (x \<otimes> y))"
    using assms ord_Zp_mult[of x y]   
    by (simp add: Z\<^sub>p_def)
  then have "x \<otimes> y =  (\<p>[^]((nat (ord_Zp x)) + nat (ord_Zp y))) \<otimes> (ac_Zp (x \<otimes> y))"
    by (metis (no_types, lifting) Zp_is_domain Zp_nonzero_def(1) Zp_nonzero_def(2)
        assms(1) assms(2) cring.cring_simprules(5) domain.axioms(1) domain.integral_iff
        int_pow_int of_nat_add ord_Zp_mult ord_nat)
  then have "x \<otimes> y =  (\<p>[^](nat (ord_Zp x))) \<otimes> (\<p>[^](nat(ord_Zp y))) \<otimes> (ac_Zp (x \<otimes> y))"
    using p_natpow_prod 
    by metis 
  then have "(\<p>[^](nat (ord_Zp x))) \<otimes> (\<p>[^](nat(ord_Zp y))) \<otimes> (ac_Zp (x \<otimes> y))
            = ((\<p>[^](nat (ord_Zp x))) \<otimes> (ac_Zp x)) \<otimes> ((\<p>[^](nat (ord_Zp y))) \<otimes> (ac_Zp y))"
    using P0 P1 
    by metis  
  then have "(\<p>[^](nat (ord_Zp x))) \<otimes> (\<p>[^](nat(ord_Zp y))) \<otimes> (ac_Zp (x \<otimes> y))
            = ((\<p>[^](nat (ord_Zp x))) \<otimes> ((\<p>[^](nat (ord_Zp y))) \<otimes> (ac_Zp x)) \<otimes> (ac_Zp y))"
    using Zp_is_domain domain_def cring.cring_simprules 
    by (smt Zp_nonzero_def(1) Zp_nonzero_def(2) ac_Zp_in_Zp assms(1) assms(2) p_pow_car_nat)
  then have "((\<p>[^](nat (ord_Zp x))) \<otimes> (\<p>[^](nat(ord_Zp y)))) \<otimes> (ac_Zp (x \<otimes> y))
            =((\<p>[^](nat (ord_Zp x))) \<otimes> (\<p>[^](nat(ord_Zp y)))) \<otimes> ((ac_Zp x) \<otimes> (ac_Zp y))"
    by (metis Zp_is_domain Zp_nonzero_def(1) Zp_nonzero_def(2) ac_Zp_in_Zp assms(1) 
        assms(2) cring.cring_simprules(11) cring.cring_simprules(5) domain.axioms(1) p_pow_car_nat)
  then show ?thesis 
    using Zp_is_domain
    by (metis (no_types, lifting) Zp_nonzero_def(1) Zp_nonzero_def(2) ac_Zp_in_Zp assms(1) assms(2)
        cring.cring_simprules(5) domain.axioms(1) domain.integral domain.m_lcancel
        p_pow_car_nat p_pow_nonzero_0(2))
qed

lemma(in padic_integers) ac_Zp_inv:
  assumes "x \<in> Units Z\<^sub>p"
  shows "ac_Zp (inv\<^bsub>Z\<^sub>p\<^esub> x) = inv\<^bsub>Z\<^sub>p\<^esub> (ac_Zp x)"
proof-
  have "x \<otimes> (inv\<^bsub>Z\<^sub>p\<^esub> x) = \<one>"
    using assms 
    by (meson Zp_is_domain cring_def domain_def monoid.Units_r_inv ring_def)
  then have "(ac_Zp x) \<otimes> (ac_Zp (inv\<^bsub>Z\<^sub>p\<^esub> x)) = ac_Zp \<one>"
    using ac_Zp_mult[of x "(inv x)"]  assms Units_inverse_Zp Units_nonzero_Zp 
    by presburger
  then show ?thesis 
    by (smt Units_inverse_Zp Units_nonzero_Zp Zp_is_domain Zp_nonzero_def(1) Zp_one_nonzero 
        Zp_one_notzero ac_Zp_factors_x ac_Zp_in_Zp ac_Zp_mult assms cring.cring_simprules(12) 
        domain.axioms(1) domain.integral_iff domain.m_rcancel invI(1) p_pow_car_nat)
qed

lemma(in padic_integers) ac_Zp_one: 
"ac_Zp \<one> = \<one>"
  by (metis Units_prop Zp_is_domain Zp_one_car Zp_one_nonzero Zp_one_notzero ac_Zp_inv
      ac_Zp_is_Unit ac_Zp_mult cring.cring_simprules(12) domain.axioms(1) invI(1) 
      ord_Zp_0_imp_unit ord_Zp_one)

lemma(in padic_integers) ac_Zp_of_Unit:
  assumes "ord_Zp x = 0"
  assumes "x \<in> carrier Z\<^sub>p"
  shows "ac_Zp x = x"
  by (metis Units_nonzero_Zp Zp_is_domain Zp_nonzero_def(2) Zp_one_car ac_Zp_factors_x 
      ac_Zp_mult ac_Zp_one assms(1) assms(2) cring.cring_simprules(12) cring.cring_simprules(14)
      domain.axioms(1) ord_Zp_0_imp_unit ord_Zp_one p_pow_car_nat)

lemma(in padic_integers) Zp_is_subring:
"subring \<O>\<^sub>p Q\<^sub>p"
  by (simp add: Q\<^sub>p_def  \<iota>_def domain.inc_im_is_subring) 

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

lemma  int_pow_add_0: 
  fixes n::int 
  fixes m::int
  assumes "comm_monoid R"
  assumes "a \<in> Units R"
  assumes "n \<ge>0"
  shows "a [^]\<^bsub>R\<^esub> (n + m) = (a [^]\<^bsub>R\<^esub> n) \<otimes>\<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> m)"
proof(cases "m \<ge> 0")
  case True
  then have "n + m \<ge> 0 " 
    by (simp add: assms(3))
  then have "a [^]\<^bsub>R\<^esub> (n + m) = a [^]\<^bsub>R\<^esub> (nat (n + m))"
    using assms 
    unfolding int_pow_def nat_pow_def 
    by auto
  then have "a [^]\<^bsub>R\<^esub> (n + m) = a [^]\<^bsub>R\<^esub> (nat n + (nat m))"
    using True assms(3) nat_add_distrib by auto
  then have "a [^]\<^bsub>R\<^esub> (n + m) = a [^]\<^bsub>R\<^esub> (nat n) \<otimes>\<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub> (nat m)"
    using assms(1) unfolding comm_monoid_def
    by (simp add: assms(1) assms(2) monoid.Units_closed monoid.nat_pow_mult)
  then show ?thesis using assms
    unfolding int_pow_def nat_pow_def 
    using True by auto
next
  case False
  then have am: "(a [^]\<^bsub>R\<^esub> m) = inv\<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> (nat (-m)))"
    unfolding int_pow_def nat_pow_def
    by auto
  then show ?thesis 
  proof(cases "(n + m) \<ge> 0")
    case T: True
    then have "a [^]\<^bsub>R\<^esub> (n + m) = a [^]\<^bsub>R\<^esub> (nat (n + m))"
      using assms 
      unfolding int_pow_def nat_pow_def 
      by auto
    then have P0: "(a [^]\<^bsub>R\<^esub> (nat (-m))) \<otimes>\<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub> (n + m) = a [^]\<^bsub>R\<^esub> ((nat (n + m)) + (nat (-m)))"
      using assms(1) unfolding comm_monoid_def
      by (simp add: add.commute assms(1) assms(2) monoid.Units_closed monoid.nat_pow_mult)
    have "(a [^]\<^bsub>R\<^esub> (nat (-m))) \<otimes>\<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub> (n + m) = a [^]\<^bsub>R\<^esub> nat n"
    proof-
      have " (nat (n + m)) + (nat (-m)) = nat n"
        using False T by linarith
      then show ?thesis using P0 
        by (simp add: \<open>nat (n + m) + nat (- m) = nat n\<close>)
    qed
    then have "(a [^]\<^bsub>R\<^esub> (nat (-m))) \<otimes>\<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub> (n + m) = a [^]\<^bsub>R\<^esub>  n"
    proof-
      have "a [^]\<^bsub>R\<^esub>  n = a [^]\<^bsub>R\<^esub>  (nat n)"
        using assms(3)
        by (metis int_nat_eq int_pow_int)
      then show ?thesis 
        by (simp add: \<open>a [^]\<^bsub>R\<^esub> nat (- m) \<otimes>\<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub> (n + m) = a [^]\<^bsub>R\<^esub> nat n\<close>)
    qed
    then have " inv\<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> (nat (-m))) \<otimes>\<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> (nat (-m))) \<otimes>\<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub> (n + m)
                   =inv\<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> (nat (-m))) \<otimes>\<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub> n"
      using assms(1) unfolding comm_monoid_def
      by (simp add: \<open>a [^]\<^bsub>R\<^esub> (n + m) = a [^]\<^bsub>R\<^esub> nat (n + m)\<close> assms(1) assms(2)
          monoid.Units_closed monoid.Units_inv_closed monoid.Units_pow_closed monoid.m_assoc)
    then have "a [^]\<^bsub>R\<^esub> (n + m)=inv\<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> (nat (-m))) \<otimes>\<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub> n"
      using assms(1) unfolding comm_monoid_def
      by (simp add: \<open>a [^]\<^bsub>R\<^esub> (n + m) = a [^]\<^bsub>R\<^esub> nat (n + m)\<close> assms(1)
          assms(2) monoid.Units_closed monoid.Units_l_inv monoid.Units_pow_closed)
    then have "a [^]\<^bsub>R\<^esub> (n + m)= a [^]\<^bsub>R\<^esub> n  \<otimes>\<^bsub>R\<^esub> inv\<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> (nat (-m))) "
      using assms comm_monoid_def[of R] Group.comm_monoid_axioms_def  
      by (metis \<open>a [^]\<^bsub>R\<^esub> nat (- m) \<otimes>\<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub> (n + m)
                 = a [^]\<^bsub>R\<^esub> n\<close> \<open>a [^]\<^bsub>R\<^esub> nat (- m) \<otimes>\<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub> (n + m) = a [^]\<^bsub>R\<^esub> nat n\<close>
          monoid.Units_closed monoid.Units_inv_closed monoid.Units_pow_closed)
    then show ?thesis 
      using am 
      by simp 
  next
    case F: False
    then show ?thesis
    proof-
      have F0: "n + m < 0"
        using F by auto 
      then have F1: "a [^]\<^bsub>R\<^esub> (n + m) = inv\<^bsub>R\<^esub>(a [^]\<^bsub>R\<^esub> (nat (-(n + m))))"
        by (simp add: int_pow_def nat_pow_def)
      have F2: "(a [^]\<^bsub>R\<^esub> (nat (-(n + m)))) \<otimes>\<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub> n =  (a [^]\<^bsub>R\<^esub> (nat (- m)))"
      proof-
        have F20: "a [^]\<^bsub>R\<^esub> n = a [^]\<^bsub>R\<^esub> (nat n)"
          by (metis assms(3) int_pow_int nat_eq_iff2)
        have F201: "(nat (-(n + m))) + nat n = (nat (- m))"
          using F0 assms(3) by linarith
        have F21: "(a [^]\<^bsub>R\<^esub> (nat (-(n + m)))) \<otimes>\<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub> nat n =  (a [^]\<^bsub>R\<^esub> (nat (- m)))"
          using F201 F Group.comm_monoid_def assms(1) assms(2) assms(3)
                monoid.Units_closed monoid.nat_pow_mult nat_add_distrib F0 assms(3) 
          by (simp add: Group.comm_monoid_def monoid.Units_closed monoid.nat_pow_mult)
        then show ?thesis
          using F1 F20 
          by simp
      qed
      have F3: "inv\<^bsub>R\<^esub>(a [^]\<^bsub>R\<^esub> (nat (-(n + m)))) \<otimes> \<^bsub>R\<^esub> ((a [^]\<^bsub>R\<^esub> (nat (-(n + m)))) \<otimes>\<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub> n) 
       =  inv\<^bsub>R\<^esub>(a [^]\<^bsub>R\<^esub> (nat (-(n + m)))) \<otimes> \<^bsub>R\<^esub>(a [^]\<^bsub>R\<^esub> (nat (- m)))"
        using F2 
        by simp

      have F4: "a [^]\<^bsub>R\<^esub> n 
       =  inv\<^bsub>R\<^esub>(a [^]\<^bsub>R\<^esub> (nat (-(n + m)))) \<otimes> \<^bsub>R\<^esub>(a [^]\<^bsub>R\<^esub> (nat (- m)))"
      proof-
        have F40: "(inv\<^bsub>R\<^esub>(a [^]\<^bsub>R\<^esub> (nat (-(n + m)))) \<otimes> \<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> (nat (-(n + m))))) \<otimes>\<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub> n
       =  inv\<^bsub>R\<^esub>(a [^]\<^bsub>R\<^esub> (nat (-(n + m)))) \<otimes> \<^bsub>R\<^esub>(a [^]\<^bsub>R\<^esub> (nat (- m)))"
        proof-
          have F400: "inv\<^bsub>R\<^esub>(a [^]\<^bsub>R\<^esub> (nat (-(n + m)))) \<in> carrier R"
            by (simp add: assms(1) assms(2) comm_monoid.is_monoid 
                monoid.Units_inv_closed monoid.Units_pow_closed)
          have F401: "(a [^]\<^bsub>R\<^esub> (nat (-(n + m)))) \<in> carrier R"
            by (simp add: assms(1) assms(2) comm_monoid.is_monoid 
                monoid.Units_closed monoid.Units_pow_closed)
          have F402: " a [^]\<^bsub>R\<^esub> n \<in> carrier R"
            using assms(1) assms(2) comm_monoid.is_monoid 
                monoid.Units_closed 
            by (metis Group.comm_monoid_def assms(3)
                int_nat_eq int_pow_int monoid.nat_pow_closed)
          then show ?thesis 
            using F3 monoid.m_assoc[of R "inv\<^bsub>R\<^esub>(a [^]\<^bsub>R\<^esub> (nat (-(n + m))))"
                                  " (a [^]\<^bsub>R\<^esub> (nat (-(n + m))))" "a [^]\<^bsub>R\<^esub> n"] 
           F400 F401 F402 
            using Group.comm_monoid_def assms(1) by auto
        qed
        have F41: "(inv\<^bsub>R\<^esub>(a [^]\<^bsub>R\<^esub> (nat (-(n + m)))) \<otimes> \<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> (nat (-(n + m))))) = \<one>\<^bsub>R\<^esub>"
          by (meson Group.comm_monoid_def assms(1) assms(2) monoid.Units_l_inv monoid.Units_pow_closed)
        have F42: "\<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub> n = inv\<^bsub>R\<^esub>(a [^]\<^bsub>R\<^esub> (nat (-(n + m)))) \<otimes>\<^bsub>R\<^esub>(a [^]\<^bsub>R\<^esub> (nat (- m)))"
          using F40 F41 
          by simp
        then show ?thesis 
          by (metis F1  assms(1) assms(2) assms(3) comm_monoid.is_monoid 
              int_nat_eq int_pow_int monoid.Units_closed monoid.Units_pow_closed monoid.l_one)
      qed
      have F5: "a [^]\<^bsub>R\<^esub> n 
       =  a [^]\<^bsub>R\<^esub> (n + m) \<otimes> \<^bsub>R\<^esub>(a [^]\<^bsub>R\<^esub> (nat (- m)))"
        by (simp add: F1 F4)
      have F6: "a [^]\<^bsub>R\<^esub> n \<otimes> \<^bsub>R\<^esub> inv \<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> (nat (- m)))
       =  a [^]\<^bsub>R\<^esub> (n + m) \<otimes> \<^bsub>R\<^esub>(a [^]\<^bsub>R\<^esub> (nat (- m))) \<otimes> \<^bsub>R\<^esub> inv \<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> (nat (- m)))"
        using F5 
        by simp
      have F7: "a [^]\<^bsub>R\<^esub> n \<otimes> \<^bsub>R\<^esub> inv \<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> (nat (- m)))
       =  a [^]\<^bsub>R\<^esub> (n + m)"
        using F6 
        by (simp add: F1 assms(1) assms(2) comm_monoid.is_monoid monoid.Units_closed
            monoid.Units_inv_closed monoid.Units_pow_closed monoid.Units_r_inv monoid.m_assoc)
      then show ?thesis 
        by (simp add: am)
    qed
  qed
qed

lemma  int_pow_unit_closed: 
  fixes n::int 
  assumes "comm_monoid R"
  assumes "a \<in> Units R"
  shows "a[^]\<^bsub>R\<^esub> n \<in> Units R"
proof(cases "n \<ge>0")
  case True
  then show ?thesis 
    by (metis assms(1) assms(2) comm_monoid.is_monoid int_nat_eq 
        int_pow_int monoid.Units_pow_closed) 
next  
  case False
  have "a[^]\<^bsub>R\<^esub> (nat (-n)) \<in> carrier R"
    by (simp add: assms(1) assms(2) comm_monoid.is_monoid monoid.Units_closed monoid.nat_pow_closed)
  then have "a[^]\<^bsub>R\<^esub> (nat (-n)) \<in> Units R"
    by (simp add: assms(1) assms(2) comm_monoid.is_monoid monoid.Units_pow_closed)
  then show ?thesis 
    using False assms 
    unfolding int_pow_def nat_pow_def 
    using comm_monoid.is_monoid monoid.Units_inv_Units 
    by fastforce
qed

lemma  nat_pow_of_inv: 
  fixes n::nat 
  assumes "comm_monoid R"
  assumes "a \<in> Units R"
  shows "inv \<^bsub>R \<^esub>a[^]\<^bsub>R\<^esub> n = inv \<^bsub>R\<^esub> (a[^]\<^bsub>R\<^esub> n)"
  by (metis (no_types, lifting) assms(1) assms(2) comm_monoid.is_monoid comm_monoid.nat_pow_distr 
      monoid.Units_inv_Units monoid.Units_inv_closed monoid.Units_inv_inv monoid.Units_l_cancel
      monoid.Units_pow_closed monoid.Units_r_inv monoid.nat_pow_one)

lemma  int_pow_of_inv_0:
  fixes n::int
  assumes "comm_monoid R"
  assumes "a \<in> Units R"
  assumes "n \<ge>0"
  shows "inv \<^bsub>R\<^esub>a[^]\<^bsub>R\<^esub> n = inv \<^bsub>R\<^esub> (a[^]\<^bsub>R\<^esub> n)"
  by (metis assms(1) assms(2) assms(3) int_nat_eq int_pow_int nat_pow_of_inv)

lemma  int_pow_of_inv:
  fixes n::int
  assumes "comm_monoid R"
  assumes "a \<in> Units R"
  shows "inv \<^bsub>R \<^esub>a[^]\<^bsub>R\<^esub> n = inv \<^bsub>R\<^esub> (a[^]\<^bsub>R\<^esub> n)"
proof(cases "n \<ge>0")
  case True
  then show ?thesis 
    by (simp add: assms(1) assms(2) int_pow_of_inv_0)
next
  case False
  then have n_neg: "n < 0"
    by auto 
  then have "a[^]\<^bsub>R\<^esub> n  = inv \<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub>(nat (- n)))"
    by (simp add: int_pow_def n_neg nat_pow_def)
  then have F0:  "inv\<^bsub>R\<^esub> (a[^]\<^bsub>R\<^esub> n)  = (a [^]\<^bsub>R\<^esub>(nat (- n)))"
    by (simp add: assms(1) assms(2) comm_monoid.is_monoid monoid.Units_inv_inv monoid.Units_pow_closed)
  have F1: "(inv\<^bsub>R\<^esub>a)[^]\<^bsub>R\<^esub> n = inv \<^bsub>R\<^esub> (inv \<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub>(nat (- n)))"
    by (simp add: int_pow_def n_neg nat_pow_def)
  have F2: "(inv \<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub>(nat (- n))) = inv \<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub>(nat (- n)))"
    by (simp add: assms(1) assms(2) nat_pow_of_inv)
  have F3: "(inv\<^bsub>R\<^esub>a)[^]\<^bsub>R\<^esub> n = inv \<^bsub>R\<^esub>  (inv \<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub>(nat (- n))))"
    by (simp add: F1 F2)
  then show ?thesis 
    by (simp add: \<open>a [^]\<^bsub>R\<^esub> n = inv\<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> nat (- n))\<close>)
qed

lemma  int_pow_inv: 
  fixes n::int 
  assumes "comm_monoid R"
  assumes "a \<in> Units R"
  shows "a[^]\<^bsub>R\<^esub> -n = inv \<^bsub>R\<^esub> a[^]\<^bsub>R\<^esub> n"
proof(cases "n >0")
  case True
  then have "-n < 0"
    by simp
  then have "a[^]\<^bsub>R\<^esub> -n = inv \<^bsub>R\<^esub> rec_nat \<one>\<^bsub>R\<^esub> (\<lambda>u b. b \<otimes>\<^bsub>R\<^esub> a) (nat (- (- n)))"
    unfolding int_pow_def  assms 
    by simp
  then have "a[^]\<^bsub>R\<^esub> -n = inv \<^bsub>R\<^esub> a[^]\<^bsub>R\<^esub> (nat (- (- n)))"
    using nat_pow_def[of R a "nat (-(-n))" ] 
    by (metis add.inverse_inverse assms(1) assms(2) comm_monoid.is_monoid group.nat_pow_inv
        monoid.Units_inv_Units monoid.Units_pow_closed monoid.units_group monoid.units_of_inv 
        monoid.units_of_pow units_of_carrier)
  then have "a[^]\<^bsub>R\<^esub> -n = inv \<^bsub>R\<^esub> a[^]\<^bsub>R\<^esub> (nat (n))"
    by simp
  then have "a[^]\<^bsub>R\<^esub> -n = inv \<^bsub>R\<^esub> a[^]\<^bsub>R\<^esub> n"
    using True  
    by (metis (full_types) int.lless_eq int_eq_iff int_pow_int)
  then show ?thesis 
    by simp
next
  case False
  then show ?thesis 
  proof(cases "n = 0")
    case True
    then show ?thesis 
      by (metis assms(1) comm_monoid.is_monoid equal_neg_zero int.minus_zero 
          int_pow_int monoid.nat_pow_0 negative_eq_positive)
  next
    case F: False
    then have n_neg: "n < 0"
      using False F 
      by auto
    then have F0: "a[^]\<^bsub>R\<^esub> n = inv \<^bsub>R\<^esub> (rec_nat \<one>\<^bsub>R\<^esub> (\<lambda>u b. b \<otimes>\<^bsub>R\<^esub> a) (nat (- n)))"
      unfolding int_pow_def  assms 
      by simp
    have F1: "a[^]\<^bsub>R\<^esub> n = inv \<^bsub>R\<^esub> (a[^]\<^bsub>R\<^esub>(nat (- n)))"
      by (simp add: int_pow_def n_neg nat_pow_def)
    have F2: "inv \<^bsub>R\<^esub> (a[^]\<^bsub>R\<^esub> n) = a[^]\<^bsub>R\<^esub>(nat (- n))"
      by (simp add: F1 assms(1) assms(2) comm_monoid.is_monoid 
          monoid.Units_inv_inv monoid.Units_pow_closed)
    have F3: "inv \<^bsub>R\<^esub> (a[^]\<^bsub>R\<^esub> n) = a[^]\<^bsub>R\<^esub>(- n)"
      by (metis F2 int_pow_int linorder_not_le n_neg nat_int neg_le_0_iff_le pos_int_cases)
    then show ?thesis 
      using assms(1) assms(2) int_pow_def nat_pow_def nat_pow_of_inv 
      by (simp add: int_pow_of_inv)
  qed
qed

lemma  int_pow_inv': 
  fixes n::int 
  assumes "comm_monoid R"
  assumes "a \<in> Units R"
  shows "a[^]\<^bsub>R\<^esub> -n = inv \<^bsub>R\<^esub> (a[^]\<^bsub>R\<^esub> n)"
  by (simp add: assms(1) assms(2) int_pow_inv int_pow_of_inv)

lemma inv_of_prod:
  assumes "comm_monoid R"
  assumes "a \<in> Units R"
  assumes "b \<in> Units R"
  shows "inv\<^bsub>R\<^esub> (a \<otimes> \<^bsub>R\<^esub> b) = (inv \<^bsub>R\<^esub> a) \<otimes>\<^bsub>R\<^esub> (inv \<^bsub>R\<^esub> b)"
  by (smt assms(1) assms(2) assms(3) comm_monoid.is_monoid comm_monoid.m_lcomm monoid.Units_closed
      monoid.Units_inv_closed monoid.Units_m_closed monoid.Units_r_inv monoid.m_closed monoid.r_one)

lemma  int_pow_add: 
  fixes n::int 
  fixes m::int
  assumes "comm_monoid R"
  assumes "a \<in> Units R"
  shows "a [^]\<^bsub>R\<^esub> (n + m) = (a [^]\<^bsub>R\<^esub> n) \<otimes>\<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> m)"
proof(cases "n \<ge>0 \<or> m \<ge> 0")
case True
  then show ?thesis 
  proof(cases "n \<ge>0")
    case True
    then show ?thesis using assms 
      by (simp add: int_pow_add_0)
  next
    case False
    then have "m \<ge>0"
      using True by blast
    then have  "a [^]\<^bsub>R\<^esub> (m + n) = (a [^]\<^bsub>R\<^esub> m) \<otimes>\<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> n)"
      using assms int_pow_add_0[of R a m n]
      by simp
    then have T0:  "a [^]\<^bsub>R\<^esub> (n + m) = (a [^]\<^bsub>R\<^esub> m) \<otimes>\<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> n)"
      by (simp add: linordered_field_class.sign_simps(2))
    show ?thesis 
    proof-
      have "(a [^]\<^bsub>R\<^esub> m) \<otimes>\<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> n) = (a [^]\<^bsub>R\<^esub> n) \<otimes>\<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> m)" 
        using int_pow_unit_closed assms 
        by (simp add: int_pow_unit_closed comm_monoid.is_monoid 
            comm_monoid.m_comm monoid.Units_closed)
      then show ?thesis 
        by (simp add: \<open>a [^]\<^bsub>R\<^esub> (m + n) = a [^]\<^bsub>R\<^esub> m \<otimes>\<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub> n\<close> 
            linordered_field_class.sign_simps(2))
    qed
  qed
next
  case False
  then have n_neg:"n < 0"
    by linarith
  then have m_neg:"m < 0"
    using False by linarith
  then have F0: "a [^]\<^bsub>R\<^esub> (-n - m) = (a [^]\<^bsub>R\<^esub> -n) \<otimes>\<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> -m)"
    by (metis (mono_tags, hide_lams) assms(1) assms(2) int.lless_eq
        int.minus_eq int_pow_add_0 n_neg neg_0_le_iff_le)
  have F1: "a [^]\<^bsub>R\<^esub> (n + m) = inv \<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> -(n+m))"
    by (metis add.inverse_inverse assms(1) assms(2) int_pow_inv')
  have F2: "a [^]\<^bsub>R\<^esub> n = inv \<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> -n)"
    using assms n_neg 
    by (metis add.inverse_inverse int_pow_inv')
  have F3: "a [^]\<^bsub>R\<^esub> m = inv \<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> -m)"
    using assms m_neg 
    by (metis add.inverse_inverse int_pow_inv')
  have F4: "inv \<^bsub>R\<^esub> ((a [^]\<^bsub>R\<^esub> -n) \<otimes>\<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> -m)) = a [^]\<^bsub>R\<^esub> n  \<otimes>\<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub> m"
  proof-
    have F40: "(a [^]\<^bsub>R\<^esub> -n) \<in> Units R"
      by (simp add: assms(1) assms(2) int_pow_unit_closed)
    have F41: "(a [^]\<^bsub>R\<^esub> -m) \<in> Units R"
      by (simp add: assms(1) assms(2) int_pow_unit_closed)
    have "inv \<^bsub>R\<^esub> ((a [^]\<^bsub>R\<^esub> -n) \<otimes>\<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> -m)) = inv \<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> -n) \<otimes>\<^bsub>R\<^esub> inv \<^bsub>R\<^esub> (a [^]\<^bsub>R\<^esub> -m)"
      using F40 F41 
      by (simp add: assms(1) inv_of_prod)
    then show ?thesis 
      by (simp add: F2 F3)
  qed
  then show ?thesis 
    by (simp add: F0 F1)
qed

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

(*
definition(in padic_integers) max_ideal :: "padic_int set"   where
"max_ideal = {x \<in> carrier Z\<^sub>p. (ord_Zp x) \<ge> (1::int) \<or> x = \<zero>}"

lemma(in padic_integers) max_ideal_is_ideal:
"ideal max_ideal Z\<^sub>p"
proof(rule idealI)
  show "ring Z\<^sub>p" 
    using cring.axioms(1) padic_int_is_cring
      Z\<^sub>p_def padic_integers_axioms prime by blast
  show "subgroup max_ideal (add_monoid Z\<^sub>p)"
  proof
    show "max_ideal \<subseteq> carrier (add_monoid Z\<^sub>p)" 
      using padic_integers.max_ideal_def padic_integers_axioms max_ideal_def by auto
    show "\<And>x y. x \<in> max_ideal \<Longrightarrow> y \<in> max_ideal \<Longrightarrow> x \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub> y \<in> max_ideal"
    proof-
      fix x y
      assume A1: "x \<in> max_ideal"
      assume A2: "y \<in> max_ideal"
      show "x \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub> y \<in> max_ideal"
      proof(cases "x = \<zero>\<^bsub>Z\<^sub>p\<^esub>")
        case True
        then show ?thesis 
          using \<open>ring Z\<^sub>p\<close> \<open>y \<in> max_ideal\<close> max_ideal_def ring.ring_simprules(8) by fastforce
      next case F1: False
        show ?thesis
        proof(cases "y = \<zero>\<^bsub>Z\<^sub>p\<^esub>") 
          case True
          then show ?thesis 
          using \<open>ring Z\<^sub>p\<close> \<open>x \<in> max_ideal \<close> max_ideal_def ring.ring_simprules(15) by fastforce 
        next case F2: False
          have Cx: "x \<in>carrier Z\<^sub>p" using A1 
            using max_ideal_def by blast
          have Cy: "y \<in>carrier Z\<^sub>p" using A2 
            using max_ideal_def by blast
          show ?thesis
          proof(cases "x \<oplus>\<^bsub>Z\<^sub>p\<^esub> y = \<zero>\<^bsub>Z\<^sub>p\<^esub>")
            case True then show ?thesis 
              by (simp add: \<open>ring Z\<^sub>p\<close> max_ideal_def ring.ring_simprules(2))
          next
            case False
            have "ord_Zp (x \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub> y) \<ge> min (ord_Zp x) (ord_Zp y)"
              using ord_Zp_def Z\<^sub>p_def False prime
                Cx Cy F1 F2 ultrametric by simp
            then have 0: "ord_Zp (x \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub> y) \<ge>1" 
              using max_ideal_def A1 A2  F1 F2 by force
            have "ring Z\<^sub>p" 
              by (simp add: \<open>ring Z\<^sub>p\<close>)
            then have 1: "x \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub> y \<in> carrier Z\<^sub>p" using Cx Cy   
              by (simp add: ring.ring_simprules(1))
            then show ?thesis using 0 1 
              using max_ideal_def by blast
          qed
        qed
      qed
    qed
    show "\<one>\<^bsub>add_monoid Z\<^sub>p\<^esub> \<in> max_ideal " 
      by (simp add: \<open>ring Z\<^sub>p\<close> max_ideal_def ring.ring_simprules(2))
    show "\<And>x. x \<in> max_ideal \<Longrightarrow> inv\<^bsub>add_monoid Z\<^sub>p\<^esub> x \<in> max_ideal"
    proof-
      fix x
      assume A: "x \<in> max_ideal"
      have 0: "x \<in>carrier Z\<^sub>p"
        using \<open>x \<in> max_ideal\<close> max_ideal_def by blast
      have 1: "inv\<^bsub>add_monoid Z\<^sub>p\<^esub> x \<in> carrier Z\<^sub>p" 
        by (metis "0" Zp_is_domain a_inv_def abelian_group.a_inv_closed cring.axioms(1) domain_def ring_def)
      have 2: "ord_Zp x = ord_Zp (inv\<^bsub>add_monoid Z\<^sub>p\<^esub> x) " 
        by (metis "0" Z\<^sub>p_def a_inv_def ord_Zp_def padic_val_add_inv prime)
      show "inv\<^bsub>add_monoid Z\<^sub>p\<^esub> x \<in> max_ideal"
        using  0 1 2 A max_ideal_def  Z\<^sub>p_def ord_Zp_def padic_val_def by auto
    qed
  qed
  show "\<And>a x. a \<in> max_ideal \<Longrightarrow> x \<in> carrier Z\<^sub>p \<Longrightarrow> x \<otimes>\<^bsub>Z\<^sub>p\<^esub> a \<in> max_ideal"
  proof
    fix a x
    assume A1: "a \<in> max_ideal"
    assume A2: "x \<in> carrier Z\<^sub>p"
    show "x \<otimes>\<^bsub>Z\<^sub>p\<^esub> a \<in> max_ideal" 
    proof(cases "x = \<zero>\<^bsub>Z\<^sub>p\<^esub>")
      case True
      then show ?thesis 
        using \<open>a \<in> max_ideal\<close> \<open>ring Z\<^sub>p\<close> \<open>x \<in> carrier Z\<^sub>p\<close> max_ideal_def
          ring.ring_simprules(24) by fastforce
      next
        case F1: False
        show ?thesis 
        proof(cases "a = \<zero>\<^bsub>Z\<^sub>p\<^esub>")
          case True then show ?thesis 
            using \<open>a \<in> max_ideal\<close> \<open>ring Z\<^sub>p\<close> \<open>x \<in> carrier Z\<^sub>p\<close>
              ring.ring_simprules(25) by fastforce
        next
          case F2: False 
          have 0: "a \<in> carrier Z\<^sub>p"
            using A1 max_ideal_def by blast
          then have 1: "x \<otimes>\<^bsub>Z\<^sub>p\<^esub> a \<in> carrier Z\<^sub>p" 
            by (simp add: A2 \<open>ring Z\<^sub>p\<close> ring.ring_simprules(5))
          have 2: "ord_Zp (x \<otimes>\<^bsub>Z\<^sub>p\<^esub> a) = (ord_Zp x) + (ord_Zp a)"
            using prime 0 A2 F1 F2 val_prod  
            by (metis monoid.simps(1) Z\<^sub>p_def  partial_object.select_convs(1)
                ring.simps(1) ord_Zp_def)
          have 3: "ord_Zp x \<ge>0" 
            using F1 Z\<^sub>p_def padic_integers_axioms padic_val_def ord_Zp_def by fastforce
          have 4: "ord_Zp a \<ge>1" 
            using A1 F2 max_ideal_def by blast
          have "ord_Zp (x \<otimes>\<^bsub>Z\<^sub>p\<^esub> a) \<ge>1" 
            using "2" "3" "4" by linarith 
          then show ?thesis 
            using "1" max_ideal_def by blast
        qed
      qed
      show "\<And>a x. a \<in> max_ideal \<Longrightarrow> x \<in> carrier Z\<^sub>p \<Longrightarrow> max_ideal \<subseteq> max_ideal" 
        by blast
    qed
    show "\<And>a x. a \<in> max_ideal \<Longrightarrow> x \<in> carrier Z\<^sub>p \<Longrightarrow> a \<otimes>\<^bsub>Z\<^sub>p\<^esub> x \<in> max_ideal " 
      by (metis (mono_tags, lifting) \<open>\<And>x a. \<lbrakk>a \<in> max_ideal ; x \<in> carrier Z\<^sub>p\<rbrakk> \<Longrightarrow> x \<otimes>\<^bsub>Z\<^sub>p\<^esub> a \<in> max_ideal \<close> 
          cring.cring_simprules(14) max_ideal_def mem_Collect_eq padic_int_is_cring
          Z\<^sub>p_def prime)
qed
*)

(*Triangle Inequality*)




lemma(in padic_integers) Zp_is_comm_monoid[simp]:
"comm_monoid Z\<^sub>p"
  using Zp_is_domain cring_def domain_def by blast

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

lemma(in padic_integers) eq_res_mod:
  assumes "f \<in> carrier Z\<^sub>p"
  assumes "g \<in> carrier Z\<^sub>p"
  assumes "f k = g k"
  obtains h where  "h \<in> carrier Z\<^sub>p \<and> f = g \<oplus> (\<p>[^]k)\<otimes>h"
proof-
  have 0: "(f \<ominus> g) k = 0"
    using assms 
    by (metis Z\<^sub>p_def Zp_is_domain a_minus_def cring.cring_simprules(17) domain.axioms(1) padic_add_def ring.simps(2) zero_vals)
  show ?thesis 
  proof(cases "f \<ominus>g = \<zero>")
    case True
    then show ?thesis 
      by (metis Zp_is_domain Zp_nat_inc_closed Zp_nat_inc_zero assms(1) assms(2)  
          cring.cring_simprules(16) cring.cring_simprules(27) cring_def domain.axioms(1)
          p_pow_rep0 ring.r_right_minus_eq that)
  next
    case False
    then have F0: "ord_Zp (f \<ominus> g) \<ge> k"
      using assms "0" Zp_is_domain cring.cring_simprules(4) domain.axioms(1) ord_Zp_geq by metis 
    then obtain m where m_def: "m = ord_Zp (f \<ominus> g) - k"
      by metis 
    then have m_prop: "m \<ge>0 \<and> (nat m) + k = ord_Zp (f \<ominus> g)"
      using F0 
      by linarith
    have F1: "(f \<ominus> g) = (ac_Zp ((f \<ominus> g))) \<otimes> \<p>[^] (ord_Zp (f \<ominus> g))"
      by (metis False Z\<^sub>p_def Zp_is_domain ac_Zp_factors_x assms(1) assms(2) cring.cring_simprules(14) 
          cring.cring_simprules(4) domain.axioms(1) int_pow_int ord_nat ord_pos 
          p_pow_car padic_integers.ac_Zp_in_Zp padic_integers_axioms)
    have F2: "\<p>[^] (ord_Zp (f \<ominus> g)) = (\<p>[^]k) \<otimes> (\<p>[^] (nat m))"
    proof-
      have F00: "\<p>[^] (ord_Zp (f \<ominus> g)) = \<p>[^] (k + (nat m))"
        using m_prop  
        by (metis add.commute int_pow_int)
      have F01: "Group.monoid Z\<^sub>p"
        using Zp_is_domain domain.nonzero_is_submonoid submonoid.axioms(1) 
        by blast
      then show ?thesis
        using  monoid.nat_pow_mult[of Z\<^sub>p "\<p>" k "nat m"] F00 F01  Zp_nat_inc_closed 
        by metis 
    qed
    have F3: "(f \<ominus> g) = (ac_Zp ((f \<ominus> g))) \<otimes>  (\<p>[^]k) \<otimes> (\<p>[^] (nat m))"
      using F1 F2 
      by (metis False Z\<^sub>p_def Zp_is_domain assms(1) assms(2) cring.cring_simprules(11) 
          cring.cring_simprules(4) domain.axioms(1) p_pow_car_nat padic_integers.ac_Zp_in_Zp padic_integers_axioms)
    have F4: "(f \<ominus> g) = (ac_Zp ((f \<ominus> g))) \<otimes>  ((\<p>[^]k) \<otimes> (\<p>[^] (nat m)))"
      using F1 F2 by metis 
    have F5: "(f \<ominus> g) = (ac_Zp ((f \<ominus> g))) \<otimes>  ((\<p>[^](nat m)) \<otimes> (\<p>[^] k))"
      using F4 Zp_is_domain 
      by (metis F2 int_pow_int m_prop p_natpow_prod)
    have F6: "(f \<ominus> g) = (((ac_Zp ((f \<ominus> g))) \<otimes>  (\<p>[^](nat m))) \<otimes> (\<p>[^] k))"
      by (metis F5 False Zp_is_domain ac_Zp_in_Zp assms(1) assms(2) 
          cring.cring_simprules(11) cring.cring_simprules(4) domain.axioms(1) p_pow_car_nat)
    have F7:  "f = (((ac_Zp ((f \<ominus> g))) \<otimes>  (\<p>[^](nat m))) \<otimes> (\<p>[^] k)) \<oplus> g"
      using F6 False Zp_is_domain ac_Zp_in_Zp assms(1) assms(2) 
          cring.cring_simprules(4) domain.axioms(1) p_pow_car_nat 
      by (metis (no_types, lifting) a_minus_def cring.cring_simprules(10) cring.cring_simprules(16) 
          cring.cring_simprules(17) cring.cring_simprules(23) cring.cring_simprules(3))
    have F8:  "f = g \<oplus>(((ac_Zp ((f \<ominus> g))) \<otimes>  (\<p>[^](nat m))) \<otimes> (\<p>[^] k))"
      using F7 False Zp_is_domain ac_Zp_in_Zp assms(1) assms(2) 
          cring.cring_simprules(4) domain.axioms(1) p_pow_car_nat 
      by (metis cring.cring_simprules(10) cring.cring_simprules(5))
    obtain h where h_def: "h = ((ac_Zp ((f \<ominus> g))) \<otimes>  (\<p>[^](nat m)))"
      by simp
    then have "f = g \<oplus> h \<otimes>(\<p>[^] k)"
      using F8 h_def 
      by blast
    then show ?thesis using h_def 
      by (metis False Z\<^sub>p_def Zp_is_domain assms(1) assms(2) cring.cring_simprules(14) 
          cring.cring_simprules(4) cring.cring_simprules(5) domain.axioms(1) 
          p_pow_car_nat padic_integers.ac_Zp_in_Zp padic_integers_axioms that)
  qed
qed

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
        angular_component_closed assms(1) local.frac_def local.inc_def
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