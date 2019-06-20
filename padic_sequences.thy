theory padic_sequences
imports padic_integers
begin

type_synonym padic_int_seq = "nat \<Rightarrow> padic_int"

type_synonym padic_int_fun = "padic_int \<Rightarrow> padic_int"

context padic_integers
begin

lemma Zp_is_cring[simp]:
"cring Z\<^sub>p" 
  by (simp add: Zp_is_domain domain.axioms(1))

lemma Zp_not_eq_diff_nonzero[simp]:
  assumes "a \<noteq>b"
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in>carrier Z\<^sub>p"
  shows "a \<ominus> b \<in> nonzero Z\<^sub>p" 
  by (meson Zp_is_domain assms(1) assms(2) assms(3) 
      cring.cring_simprules(4) cring_def domain.axioms(1) not_nonzero_Zp ring.r_right_minus_eq)

lemma Zp_minus_ominus:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  shows "a \<ominus> b = \<ominus> (b \<ominus> a)"
  by (metis (no_types, lifting) Z\<^sub>p_def Zp_is_domain a_minus_def abelian_group.minus_add
      abelian_group.minus_equality assms(1) assms(2) cring.cring_simprules(10) domain.axioms(1) 
      padic_add_inv padic_is_abelian_group prime)

lemma Zp_diff_simp:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "c \<in> carrier Z\<^sub>p"
  assumes  "X = a \<ominus> b"
  assumes "Y = c \<ominus> a"
  shows "X \<oplus> Y = c \<ominus> b"
proof-
  have "X \<oplus>Y = (a \<ominus> b) \<oplus> (c \<ominus> a)" 
    by (simp add: assms(4) assms(5))
  then have "X \<oplus>Y = (c \<ominus> a) \<oplus> (a \<ominus> b)" 
    by (simp add: Zp_is_domain assms(1) assms(2) assms(3)
        cring.cring_simprules(10) cring.cring_simprules(4) domain.axioms(1))
  then have "X \<oplus>Y = ((c \<oplus> (\<ominus> a)) \<oplus> a) \<ominus> b" 
    by (metis (no_types, lifting) Zp_is_domain a_minus_def assms(1) assms(2) 
        assms(3) cring.cring_simprules(3) cring.cring_simprules(4) cring.cring_simprules(7)
        domain.axioms(1))
  then have "X \<oplus>Y = (c \<oplus> ((\<ominus> a) \<oplus> a)) \<ominus> b" 
    by (simp add: Zp_is_domain assms(1) assms(3) cring.cring_simprules(3) cring.cring_simprules(7)
        domain.axioms(1))
  then show ?thesis 
    by (simp add: Zp_is_domain assms(1) assms(3) cring.cring_simprules(16) cring.cring_simprules(9) 
        domain.axioms(1))
qed

lemma Zp_res_eq:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "ord_Zp (a \<ominus> b) > int k"
  shows "(a k) = (b k)" 
proof-
  have "a \<ominus> b = a \<oplus> (\<ominus> b)" 
    by (simp add: a_minus_def)
  then have "(a \<ominus> b) k = (a k) \<oplus>\<^bsub>R k\<^esub> ((\<ominus> b) k)" 
    by (simp add:  Z\<^sub>p_def padic_add_def)
  then have "(a \<ominus> b) k = (a k) \<oplus>\<^bsub>R k\<^esub> (\<ominus>\<^bsub>R k\<^esub> (b k))"  
    using  Z\<^sub>p_def assms(2) padic_inv prime by auto
  have 0: "(a \<ominus> b) k = (a k) \<ominus>\<^bsub>R k\<^esub> (b k)" using assms  
    by (metis \<open>(a \<ominus> b) k = a k \<oplus>\<^bsub>R k\<^esub> \<ominus>\<^bsub>R k\<^esub> b k\<close> a_minus_def)
  have 1: "( a \<ominus> b) k = 0" using assms 
    using Zp_is_cring cring.cring_simprules(4) zero_below_ord 
    by (metis (no_types, hide_lams) dual_order.strict_trans less_irrefl not_less)
  then show ?thesis
  proof(cases "k=0")
    case True
    then show ?thesis 
      by (metis Z\<^sub>p_def assms(1) assms(2) padic_set_simp2 partial_object.select_convs(1) prime)
  next
    case False
    then have "k>0" by auto 
    then show ?thesis 
      using 0 1 R_residues R_cring 
      by (metis Z\<^sub>p_def assms(1) assms(2) cring_def padic_set_simp0 
          partial_object.select_convs(1) residues.res_zero_eq ring.r_right_minus_eq)
  qed
qed

lemma Zp_res_eq2[simp]:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "(a k) = (b k)" 
  assumes "a \<noteq>b"
  shows "ord_Zp (a \<ominus> b) \<ge> int k"
proof-
  have "a \<ominus> b = a \<oplus> (\<ominus> b)" 
    by (simp add: a_minus_def)
  then have "(a \<ominus> b) k = (a k) \<oplus>\<^bsub>R k\<^esub> ((\<ominus> b) k)" 
    by (simp add:  Z\<^sub>p_def padic_add_def)
  then have "(a \<ominus> b) k = (a k) \<oplus>\<^bsub>R k\<^esub> (\<ominus>\<^bsub>R k\<^esub> (b k))"  
    using  Z\<^sub>p_def assms(2) padic_inv prime by auto
  have 0: "(a \<ominus> b) k = (a k) \<ominus>\<^bsub>R k\<^esub> (b k)" using assms  
    by (metis \<open>(a \<ominus> b) k = a k \<oplus>\<^bsub>R k\<^esub> \<ominus>\<^bsub>R k\<^esub> b k\<close> a_minus_def)
  have 1: "( a \<ominus> b) k = 0" using assms(2) 
    by (metis  Z\<^sub>p_def Zp_is_cring \<open>(a \<ominus> b) k = a k \<oplus>\<^bsub>R k\<^esub> (\<ominus> b) k\<close> 
        assms(3) cring.cring_simprules(17) padic_add_def ring.simps(2) zero_vals)
  then show ?thesis 
    by (meson Zp_is_cring assms(1) assms(2) assms(4) cring.cring_simprules(4)
        cring_def ord_Zp_geq ring.r_right_minus_eq)
qed

(**************************************************************************************************)
(**************************************************************************************************)
(*************************************  Sequences over Zp  ****************************************)
(**************************************************************************************************)
(**************************************************************************************************)

(*Predicate for a sequence of elements in Zp*)
definition is_closed_seq :: "padic_int_seq \<Rightarrow> bool" where
"is_closed_seq s = (\<forall> n. s n \<in> carrier Z\<^sub>p)"

lemma is_closed_simp[simp]:
  assumes "is_closed_seq s"
  shows "s n \<in> carrier Z\<^sub>p"
  using assms is_closed_seq_def by blast

lemma is_closedI[simp]:
  assumes "\<And> k. s k \<in> carrier Z\<^sub>p"
  shows "is_closed_seq s"
  by (simp add: assms is_closed_seq_def)

(*The integer-valued padic (valuative) distance*)
abbreviation ord_Zp_dist :: "padic_int \<Rightarrow> padic_int \<Rightarrow> int" where
"ord_Zp_dist a b \<equiv> ord_Zp (a \<ominus> b)"

(*Distance function is symmetric*)
lemma ord_Zp_dist_sym:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in>carrier Z\<^sub>p"
  shows "ord_Zp_dist a b = ord_Zp_dist b a"
proof(cases "a = b")
  case True
  then show ?thesis 
    by blast
next
  case False
  have 0: "a \<ominus> b \<in> nonzero Z\<^sub>p" 
    using False assms(1) assms(2) Zp_not_eq_diff_nonzero 
    by blast
  have 1: "a \<ominus> b = \<ominus> (b \<ominus> a)" using assms(1) assms(2)  
    using Zp_minus_ominus by blast
  then show ?thesis 
    using ord_Zp_of_ominus  by (metis Zp_not_eq_diff_nonzero assms(1) assms(2))
qed

(*Distanc function obeys the ultrametic inequality*)
lemma ord_Zp_dist_ultrametric:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "a \<noteq> b"
  assumes "a \<noteq>c"
  assumes "b \<noteq>c"
  shows "ord_Zp_dist b c \<ge> min (ord_Zp_dist a c) (ord_Zp_dist a b)" 
proof-
  let ?X = "b \<ominus> a"
  let ?Y = "a \<ominus> c"
  let ?Z = "b \<ominus> c"
  have 0: "?Z = ?X \<oplus> ?Y" 
    by (metis (no_types, lifting) Zp_diff_simp Zp_is_cring assms(1) assms(2) assms(3) 
        cring.cring_simprules(10) cring.cring_simprules(4))
  have 1: "?X \<in> nonzero Z\<^sub>p" 
    using Zp_not_eq_diff_nonzero assms(1) assms(2) assms(4) 
    by metis
  have 2: "?Y \<in> nonzero Z\<^sub>p" 
    using Zp_not_eq_diff_nonzero assms(1) assms(3) assms(5) by blast
  have 3: "?Z \<in> nonzero Z\<^sub>p" 
    using Zp_not_eq_diff_nonzero assms(2) assms(3) assms(6) by blast
  have 4: "ord_Zp ?Z \<ge> min (ord_Zp ?X) (ord_Zp ?Y)" using 0 1 2 3 
    using Z\<^sub>p_def padic_integers.ord_Zp_ultrametric padic_integers_axioms by auto
  then show ?thesis 
    by (smt assms(1) assms(2) ord_Zp_dist_sym)
qed

(*Elements which are close have equal residues*)
lemma ord_Zp_dist_res_eq:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "ord_Zp_dist a b > int k"
  shows "(a k) = (b k)" 
  using Zp_res_eq assms(1) assms(2) assms(3) by blast

lemma ord_Zp_dist_res_eq1:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "a = b \<or> ord_Zp_dist a b > int k"
  shows "(a k) = (b k)" 
  using assms ord_Zp_dist_res_eq[of a b k] 
  by blast 

(*Elements with equal residues are close*)
lemma ord_Zp_dist_res_eq2:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "(a k) = (b k)" 
  assumes "a \<noteq>b"
  shows "ord_Zp_dist a b \<ge>int k"
  
  using Zp_res_eq2 assms(1) assms(2) assms(3) assms(4) by blast

lemma ord_Zp_dist_triangle_eqs:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "ord_Zp_dist a b > int n"
  assumes "ord_Zp_dist a c > int n"
  assumes "(k::nat) < n"
  assumes "a \<noteq> b"
  assumes "a \<noteq>c"
  assumes "b \<noteq>c"
  shows "a k = b k"
        "a k = c k"
        "b k = c k" 
proof-
  have "ord_Zp_dist b c  \<ge> min (ord_Zp_dist a c) (ord_Zp_dist a b)" 
    using assms ord_Zp_dist_ultrametric  
    by blast
  then have 0: "ord_Zp_dist b c > int n" 
    using assms(4) assms(5) by linarith
  have 1: "(a \<ominus> b) k = 0" 
    using Zp_is_cring assms(1) assms(2) assms(4) assms(6) cring.cring_simprules(4)[of Z\<^sub>p a b]
                          zero_below_ord[of "a \<ominus> b" k] 
    by linarith
  have 2: "(a \<ominus> c) k = 0" 
    using  Zp_is_cring assms(1) assms(3) assms(5) assms(6) cring.cring_simprules(4)[of Z\<^sub>p a c] 
          zero_below_ord[of "a \<ominus>c" k] 
    by linarith
  have 3: "(b \<ominus> c) k = 0"
    using "0" Zp_is_cring assms(2) assms(3) assms(6) cring.cring_simprules(4)[of Z\<^sub>p b c]
      zero_below_ord[of "b \<ominus>c" k] 
    by linarith 
  show "a k = b k" 
    using Zp_res_eq assms(1) assms(2) assms(4) assms(6) 
    by (smt less_imp_le_nat of_nat_mono)  
  show "a k = c k" 
    using Zp_res_eq assms(1) assms(3) assms(5) assms(6) sorry
  show "b k = c k" 
    using \<open>a k = b k\<close> \<open>a k = c k\<close> by auto
qed

(*Prediate for cauchy sequences*)
definition is_cauchy :: "padic_int_seq \<Rightarrow> bool" where
"is_cauchy s = ((is_closed_seq s) \<and> (\<forall> (n::int). \<exists> (N::nat). \<forall> m k::nat. (m>N \<and> k>N \<longrightarrow> (s m) = (s k) \<or> (ord_Zp_dist (s m) (s k)) > n)))"

(*Relation for a sequence which converges to a point*)
definition converges_to :: "padic_int_seq \<Rightarrow> padic_int \<Rightarrow> bool" where
"converges_to s a = ((a \<in> carrier Z\<^sub>p \<and> is_closed_seq s) 
    \<and> (\<forall>(n::int). (\<exists>(k:: nat). (\<forall>( m::nat). (m > k \<longrightarrow> (s m) = a \<or> (ord_Zp ((s m) \<ominus> a)) \<ge> n)))))"

(*Cauchy sequences eventually have constant residues*)
lemma is_cauchy_imp_eventually_const_0:
  assumes "is_cauchy s"
  fixes n::nat
  obtains N where "\<And> n0 n1. n0 > N \<and> n1 > N \<Longrightarrow> (s n0) n = (s n1) n"
proof-
  have "\<exists> (N::nat). \<forall> m k::nat. (m>N \<and> k>N \<longrightarrow> (s m) = (s k) \<or> (ord_Zp_dist (s m) (s k)) > (int n))"
    using assms is_cauchy_def by blast 
  then obtain N where P0: " \<forall> m k::nat. (m>N \<and> k>N \<longrightarrow> (s m) = (s k) \<or> (ord_Zp_dist (s m) (s k)) > (int n))"
    by blast 
  have P1: "\<And> n0 n1. n0 > N \<and> n1 > N \<Longrightarrow> (s n0) n = (s n1) n"
  proof-
    fix n0 n1
    assume A: "n0 > N \<and> n1 > N"
    have "(n0>N \<and> n1>N \<longrightarrow> (s n0) = (s n1) \<or> (ord_Zp_dist (s n0) (s n1)) > (int n))" 
      using P0 by blast
    then have C0: "(s n0) = (s n1) \<or> (ord_Zp_dist (s n0) (s n1)) > (int n)" 
      using A  by blast
    then show "(s n0) n = (s n1) n"
    proof(cases "(s n0) = (s n1)")
      case True
      then show ?thesis 
        by simp
    next
      case False
      then have A0: "(ord_Zp_dist (s n0) (s n1)) > (int n)" 
        using C0 by blast
      have A1: "s n0 \<in> carrier Z\<^sub>p" 
        using is_cauchy_def assms sorry
      have A2: "s n1 \<in> carrier Z\<^sub>p" 
        using is_cauchy_def assms sorry
      show ?thesis 
        using A0 ord_Zp_dist_res_eq  A1 A2 sorry
    qed
  qed
  then show ?thesis 
    using that by blast
qed

(*Introduction lemma for proving a sequence is cauchy*)
lemma is_cauchyI[simp]:
  assumes "is_closed_seq s"
  assumes "\<And> n.  (\<exists>N. (\<forall> n0 n1. n0 > N \<and> n1 > N \<longrightarrow> (s n0) n = (s n1) n))"
  shows "is_cauchy s"
proof-
  have "(\<forall> (n::int). \<exists> (N::nat). \<forall> m k::nat. (m>N \<and> k>N \<longrightarrow> (s m) = (s k) \<or> (ord_Zp_dist (s m) (s k)) > n))"
  proof
    fix n
    show "\<exists> (N::nat). \<forall> m k::nat. (m>N \<and> k>N \<longrightarrow> (s m) = (s k) \<or> (ord_Zp_dist (s m) (s k)) > n)"
    proof-
    have "(\<exists>N. (\<forall> n0 n1. n0 > N \<and> n1 > N \<longrightarrow> (s n0) (Suc (nat n)) = (s n1) (Suc (nat n))))" 
      using assms(2) by blast
    then obtain N where N_def: "(\<forall> n0 n1. n0 > N \<and> n1 > N \<longrightarrow> (s n0) (Suc (nat n)) = (s n1) (Suc (nat n)))"
      by blast 
    have "\<forall>m k. N < m \<and> N < k \<longrightarrow> s m = s k \<or> (nat n) < ord_Zp_dist (s m) (s k)"
    proof
      fix m
      show "\<forall>k. N < m \<and> N < k \<longrightarrow> s m = s k \<or> int (nat n) < ord_Zp_dist (s m) (s k)"
      proof
        fix k
        show "N < m \<and> N < k \<longrightarrow> s m = s k \<or> int(nat n) < ord_Zp_dist (s m) (s k)"
        proof
          assume A: "N < m \<and> N < k"
          then have E: "(s m) (Suc(nat n)) = (s k) (Suc(nat n))" 
            using N_def by blast 
          then show " s m = s k \<or> int (nat n) < ord_Zp_dist (s m) (s k)"
          proof(cases " s m = s k")
            case True
            then show ?thesis 
              sorry
          next
            case False
            have 0: "(s m) \<in> carrier Z\<^sub>p"
              by (simp add: assms(1))
            have 1: "(s k) \<in> carrier Z\<^sub>p" 
              using Z\<^sub>p_def assms(1) padic_integers.is_closed_simp padic_integers_axioms by blast
            have "int (Suc (nat n)) \<le> ord_Zp_dist (s m) (s k)" 
              using False  E 0 1 ord_Zp_dist_res_eq2[of "(s m)" "(s k)" "Suc (nat n)"] by blast
            then have "int (nat n) < ord_Zp_dist (s m) (s k)" 
              sorry 
            then show ?thesis 
              by blast
          qed
        qed
      qed
    qed
    then show ?thesis 
      using zless_nat_conj zless_nat_eq_int_zless sorry
  qed
  qed
  then show ?thesis 
    using is_cauchy_def assms  by blast
qed


lemma is_cauchy_imp_eventually_const:
  assumes "is_cauchy s"
  fixes n::nat
  obtains N r where "r \<in> carrier (R n)" and "\<And> m. m > N \<Longrightarrow> (s m) n = r"
proof-
  obtain N where A0: "\<And> n0 n1. n0 > N \<and> n1 > N \<Longrightarrow> (s n0) n = (s n1) n"
    using assms padic_integers.is_cauchy_imp_eventually_const_0 padic_integers_axioms by blast
  obtain r where A1: "s (Suc N) n = r" 
    by simp
  have 0: "r \<in> carrier (R n)" 
    using  Z\<^sub>p_def \<open>s (Suc N) n = r\<close> assms is_closed_simp 
      padic_integers.is_cauchy_def padic_integers_axioms padic_set_simp0 by auto
  have 1: "\<And> m. m > N \<Longrightarrow> (s m) n = r"
  proof-
    fix m 
    assume " m > N"
    then show "(s m) n = r" 
      using A0 A1  by blast
  qed
  then show ?thesis 
    using 0 1  that by blast
qed

(*The funciton which identifies the eventual residues of a cauchy sequence*)
definition res_lim :: "padic_int_seq \<Rightarrow> padic_int" where
"res_lim s = (\<lambda> k. (THE r. (\<exists>N.  (\<forall> m. m > N \<longrightarrow> (s m) k = r))))"

(*(res_lim s) literally is the limit of s if s is cauchy*)
lemma res_lim_cauchy_0:
  assumes "is_cauchy s"
  assumes "f = (res_lim s) k"
  shows "(\<exists>N.  (\<forall> m. (m > N \<longrightarrow> (s m) k = f)))"
        "f \<in> carrier R k"
proof-
  obtain N r where P0: "r \<in> carrier (R k)" and P1: "\<And> m. m > N \<Longrightarrow> (s m) k = r"
    by (meson assms(1) is_cauchy_imp_eventually_const)
  obtain P where  P_def: "P = (\<lambda> x. (\<exists>N.  (\<forall> m. m > N \<longrightarrow> (s m) k = x)))"
    by simp
  have 0: "P r"
    using P1 P_def by auto
  have 1: "(\<And>x. P x \<Longrightarrow> x = r)"
  proof-
    fix x
    assume A_x: "P x"
    obtain N0 where "(\<forall> m. m > N0 \<longrightarrow> (s m) k = x)" 
      using A_x P_def by blast
    let ?M = "max N0 N" 
    have C0: "s (Suc ?M) k = x" 
      by (simp add: \<open>\<forall>m>N0. s m k = x\<close>)
    have C1: "s (Suc ?M) k = r" 
      by (simp add: P1)
    show "x = r" 
      using C0 C1 by auto 
  qed
  have R: "r = (THE x. P x)" 
    using the_equality 0 1 by metis
  have "(res_lim s) k = (THE r. \<exists>N. \<forall>m>N. s m k = r)" 
    using res_lim_def by simp
  then have "f = (THE r. \<exists>N. \<forall>m>N. s m k = r)" 
    using assms by auto 
  then have "f = (THE r. P r)" 
    using P_def by auto 
  then have "r = f"
    using R by auto  
  then show "(\<exists>N.  (\<forall> m. (m > N \<longrightarrow> (s m) k = f)))" using 0 P_def 
    by blast
  show "f \<in> carrier R k" 
    using P0 \<open>r = f\<close> by auto
qed

lemma res_lim_cauchy:
  assumes "is_cauchy s"
  obtains N where "\<And> m.  (m > N \<longrightarrow> (s m) k = (res_lim s) k)"
  using res_lim_cauchy_0 assms by presburger

lemma res_lim_in_Zp:
  assumes "is_cauchy s"
  shows "res_lim s \<in> carrier Z\<^sub>p"
proof-
  have "res_lim s \<in> padic_set p"
  proof(rule padic_set_mem)
    show "\<And>m. res_lim s m \<in> carrier (residue_ring (int p ^ m))" 
      using res_lim_cauchy_0     by (simp add:  assms)
    show "\<And>m n. m < n \<Longrightarrow> res (int p ^ m) (res_lim s n) = res_lim s m"
    proof-
      fix m n
      obtain N where  N0: "\<And> l.  (l > N \<longrightarrow> (s l) m = (res_lim s) m)"
        using assms res_lim_cauchy by blast
      obtain M where M0: "\<And> l.  (l > M \<longrightarrow> (s l) n = (res_lim s) n)"
        using assms prod.simps(2) res_lim_cauchy by auto
      obtain K where K_def: "K = max M N" 
        by simp
      have Km: "\<And> l.  (l > K \<longrightarrow> (s l) m = (res_lim s) m)" 
        using K_def N0  by simp
      have Kn: "\<And> l.  (l > K \<longrightarrow> (s l) n = (res_lim s) n)" 
        using K_def M0  by simp
      assume "m < n"
      show "res (int p ^ m) (res_lim s n) = res_lim s m"
      proof-
        obtain l where l_def: "l = Suc K"
          by simp
        have ln: "(res_lim s n) = (s l) n" 
          by (simp add: Kn l_def)
        have lm: "(res_lim s m) = (s l) m"
          by (simp add: Km l_def)
        have s_car: "s l \<in> carrier Z\<^sub>p" 
          using assms is_cauchy_def is_closed_seq_def by blast
        then show ?thesis 
          using s_car lm ln \<open>m < n\<close> r_Zp by auto
      qed
    qed
  qed
  then show ?thesis 
    by (simp add: Z\<^sub>p_def)
qed

lemma is_cauchy_imp_has_limit:
  assumes "is_cauchy s"
  assumes "a = res_lim s"
  shows "converges_to s a"
proof-
  have 0: "(a \<in> carrier Z\<^sub>p \<and> is_closed_seq s)" 
    using assms(1) assms(2) is_cauchy_def res_lim_in_Zp by blast
  have 1: "(\<forall>(n::int). (\<exists>(k:: nat). (\<forall>( m::nat). 
            (m > k \<longrightarrow> (s m) = a \<or> (ord_Zp ((s m) \<ominus> a)) \<ge> n))))"
  proof
    fix n
    show "\<exists>k. \<forall>m>k. s m = a \<or> n \<le> ord_Zp_dist (s m) a"
    proof-
      obtain K where K_def: "\<And>m. (m > K \<longrightarrow> (s m) (nat n) = (res_lim s) (nat n))"
        using assms(1) res_lim_cauchy by blast
      have "\<forall>m>K. s m = a \<or> n \<le> ord_Zp_dist (s m) a"
      proof
        fix m
        show "K < m \<longrightarrow> s m = a \<or> n \<le> ord_Zp_dist (s m) a"
        proof
          assume A: "K < m"
          show "s m = a \<or> n \<le> ord_Zp_dist (s m) a"
          proof(cases "s m = a")
            case True
            then show ?thesis 
              sorry
          next
            case False
            have X: "(s m) \<in> carrier Z\<^sub>p" 
              using "0" is_closed_simp 
              by blast
            have "(s m) (nat n) = (res_lim s) (nat n)"
              using A K_def  by blast
            then have "(s m) (nat n) = a (nat n)" 
              using assms(2) by blast
            then have "int (nat n) \<le> ord_Zp_dist (s m) a"
              using False X ord_Zp_dist_res_eq2 "0" by blast
            then show ?thesis
              using int_nat_eq  by linarith
          qed
        qed
      qed
      then show ?thesis 
        by blast
    qed
  qed
  then show ?thesis 
    sorry
qed

(*Convergent sequences are cauchy*)
lemma convergent_imp_cauchy: 
  assumes "is_closed_seq s"
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "converges_to s a"
  shows "is_cauchy s"
  apply(rule is_cauchyI)
  using assms apply simp 
proof-
  fix n
  show "\<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> s n0 n = s n1 n "
  proof-
    obtain k where k_def:"\<forall>m>k. s m = a \<or> (Suc n) \<le> ord_Zp_dist (s m) a"
      using assms 
      unfolding converges_to_def 
      by blast 
    have A0:  "\<forall>n0 n1. k < n0 \<and> k < n1 \<longrightarrow> s n0 n = s n1 n "
      apply auto 
    proof-
      fix n0 n1
      assume A: " k < n0" " k < n1"
      show " s n0 n = s n1 n "
      proof-
        have 0: "(s n0) = a \<or> (Suc n) \<le> ord_Zp_dist (s n0) a"
          using k_def using  A 
          by blast  
        have 1: "(s n1) = a \<or> (Suc n) \<le> ord_Zp_dist (s n1) a"
          using k_def using  A 
          by blast
        have 2: "(s n0) n = a n"
          using assms 0 ord_Zp_dist_res_eq1[of "s n0" a n] 
          by (metis Suc_le_eq is_closed_simp nat_int nat_mono ord_Zp_def zless_nat_eq_int_zless)
        have 3: "(s n1) n = a n"
          using assms 1 ord_Zp_dist_res_eq1[of "s n1" a n] 
          by (metis Suc_le_eq is_closed_simp nat_int nat_mono ord_Zp_def zless_nat_eq_int_zless)
        show ?thesis 
          using 2 3 
          by auto 
      qed
    qed
    show ?thesis 
      using A0 
      by blast 
  qed
qed

(*A sequence converges to no more than one element*)
lemma unique_limit:
  assumes "is_closed_seq s"
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "converges_to s a"
  assumes "converges_to s b"
  shows "a = b"
proof-
  have "\<And>k. a k = b k"
  proof-
    fix k
    obtain k0 where k0_def:"\<forall>m>k0. s m = a \<or> (Suc k) \<le> ord_Zp_dist (s m) a"
      using assms unfolding converges_to_def by blast 
    obtain k1 where k1_def:"\<forall>m>k1. s m = b \<or> (Suc k) \<le> ord_Zp_dist (s m) b"
      using assms unfolding converges_to_def by blast 
    have k0_prop: "\<And>m. m> k0 \<Longrightarrow> (s m) k = a k"
      using k0_def assms is_closed_simp[of s] ord_Zp_dist_res_eq1[of _ a k]
      by (smt of_nat_Suc)
    have k1_prop: "\<And>m. m> k1 \<Longrightarrow> (s m) k = b k"
      using k1_def assms is_closed_simp[of s] ord_Zp_dist_res_eq1[of _ b k]      
      by (smt of_nat_Suc)
    have "\<And> m. m > (max k0 k1) \<Longrightarrow> a k = b k"
      using k0_prop k1_prop 
      by force
    then show "a k = b k"
      by blast
  qed
  then show ?thesis 
    by blast
qed

lemma unique_limit':
  assumes "is_closed_seq s"
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "converges_to s a"
  shows "a = res_lim s"
  using unique_limit[of s a "res_lim s"] assms 
        convergent_imp_cauchy is_cauchy_imp_has_limit res_lim_in_Zp 
  by blast

(*Elimination and introduction lemmas for convergence*)
lemma converges_toE:
  assumes "is_closed_seq s"
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "converges_to s a"
  shows "\<exists>N. \<forall>k > N. s k n = a n"
  by (metis assms(1) assms(2) assms(3) 
      convergent_imp_cauchy 
      res_lim_cauchy unique_limit')

lemma converges_toI:
  assumes "is_closed_seq s"
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "\<And>n. \<exists>N. \<forall>k > N. s k n = a n"
  shows "converges_to s a"
proof-
  have 0: "(a \<in> carrier Z\<^sub>p \<and> is_closed_seq s)" 
    using assms
    by auto 
  have 1: "(\<forall>n. \<exists>k. \<forall>m>k. s m = a \<or> n \<le> ord_Zp_dist (s m) a) "
  proof
    fix n 
    show "\<exists>k. \<forall>m>k. s m = a \<or> n \<le> ord_Zp_dist (s m) a "
    proof(cases "n \<le>0")
      case True
      have "\<forall>m>0. s m = a \<or> n \<le> ord_Zp_dist (s m) a "
      proof
        fix m ::nat
        show "0 < m \<longrightarrow> s m = a \<or> n \<le> ord_Zp_dist (s m) a"
        proof
        assume "m >0"
        show "  s m = a \<or> n \<le> ord_Zp_dist (s m) a"
          by (smt True Zp_is_cring assms(1) assms(2) 
              cring.cring_simprules(4) cring_def is_closed_simp ord_pos ring.r_right_minus_eq)
      qed
    qed
      then show ?thesis 
        by blast
    next
      case False
      then have P0: "n >0"
        by auto 
      obtain N where N_def: "\<forall>k > N. s k (nat n) = a (nat n)"
        using assms by auto 
      have "\<forall>m>N. s m = a \<or> n \<le> ord_Zp_dist (s m) a "
      proof
        fix m
        show " N < m \<longrightarrow> s m = a \<or> n \<le> ord_Zp_dist (s m) a"
        proof
          assume A: "N < m"
          then have A0: "s m (nat n) = a (nat n)"
            using N_def by auto 
          show "s m = a \<or> n \<le> ord_Zp_dist (s m) a"
            using assms A0 
            by (smt int_nat_eq is_closed_simp ord_Zp_dist_res_eq2)
        qed
      qed
      then show ?thesis 
        by blast 
    qed
  qed
  show ?thesis 
    unfolding converges_to_def 
    using 0 1 
    by blast 
qed

(*Sums and products of sequences*)
definition seq_sum:: "padic_int_seq \<Rightarrow> padic_int_seq \<Rightarrow> padic_int_seq" where
"seq_sum s1 s2 = (\<lambda> k. (s1 k) \<oplus> (s2 k))"

definition seq_prod:: "padic_int_seq \<Rightarrow> padic_int_seq \<Rightarrow> padic_int_seq" where
"seq_prod s1 s2 = (\<lambda> k. (s1 k) \<otimes> (s2 k))"

(*Sums and products of closed sequences are closed*)
lemma sum_of_closed_seq_is_closed_seq:
  assumes "is_closed_seq s"
  assumes "is_closed_seq t"
  shows "is_closed_seq (seq_sum s t)"
proof(rule is_closedI)
  fix k
  have "seq_sum s t k = (s k) \<oplus>(t k)" using seq_sum_def by auto 
  then show "seq_sum s t k \<in> carrier Z\<^sub>p" 
    using assms is_closed_simp[of "seq_sum s t"]  by (simp add:cring.cring_simprules(1))
qed

lemma prod_of_closed_seq_is_closed_seq:
  assumes "is_closed_seq s"
  assumes "is_closed_seq t"
  shows "is_closed_seq (seq_prod s t)"
proof(rule is_closedI)
  fix k
  have "seq_prod s t k = (s k) \<otimes> (t k)" using seq_prod_def by auto 
  then show "seq_prod s t k \<in> carrier Z\<^sub>p" 
    using assms is_closed_simp[of "seq_prod s t"]
    by (simp add:cring.cring_simprules(5))
qed

(*Sums and products of cauchy sequences are cauchy*)
lemma sum_of_cauchy_is_cauchy:
  assumes "is_cauchy s"
  assumes "is_cauchy t"
  shows "is_cauchy (seq_sum s t)"
proof(rule is_cauchyI)
  show "is_closed_seq (seq_sum s t)" 
    using assms is_cauchy_def sum_of_closed_seq_is_closed_seq sorry
  show "\<And>n. \<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> seq_sum s t n0 n = seq_sum s t n1 n"
  proof-
    fix n
    show "\<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> seq_sum s t n0 n = seq_sum s t n1 n"
    proof-
      obtain N1 where N1_def: "\<forall>n0 n1. N1 < n0 \<and> N1 < n1 \<longrightarrow> s n0 n = s n1 n" 
        using assms(1) padic_integers.is_cauchy_imp_eventually_const_0 padic_integers_axioms 
          by blast
      obtain N2 where N2_def: "\<forall>n0 n1. N2 < n0 \<and> N2 < n1 \<longrightarrow> t n0 n = t n1 n" 
        using assms(2) padic_integers.is_cauchy_imp_eventually_const_0 padic_integers_axioms 
          by blast
      obtain M where M_def: "M = max N1 N2"
        by simp
      have "\<forall>n0 n1. M < n0 \<and> M < n1 \<longrightarrow> seq_sum s t n0 n = seq_sum s t n1 n"
      proof
        fix n0
        show "\<forall>n1. M < n0 \<and> M < n1 \<longrightarrow> seq_sum s t n0 n = seq_sum s t n1 n"
        proof
          fix n1 
          show " M < n0 \<and> M < n1 \<longrightarrow> seq_sum s t n0 n = seq_sum s t n1 n"
          proof
            assume A: "M < n0 \<and> M < n1 "
            have Fs: " s n0 n = s n1 n" using A M_def N1_def by auto
            have Ft: " t n0 n = t n1 n" using A M_def N2_def by auto
            then show "seq_sum s t n0 n = seq_sum s t n1 n" using seq_sum_def 
              by (simp add: Fs Z\<^sub>p_def padic_add_def)
          qed
        qed
      qed
      then show ?thesis 
        by blast
    qed
  qed
qed

lemma prod_of_cauchy_is_cauchy:
  assumes "is_cauchy s"
  assumes "is_cauchy t"
  shows "is_cauchy (seq_prod s t)"
proof(rule is_cauchyI)
  show "is_closed_seq (seq_prod s t)" 
    using assms is_cauchy_def prod_of_closed_seq_is_closed_seq sorry 
  show "\<And>n. \<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> seq_prod s t n0 n = seq_prod s t n1 n"
  proof-
    fix n
    show "\<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> seq_prod s t n0 n = seq_prod s t n1 n"
    proof-
      obtain N1 where N1_def: "\<forall>n0 n1. N1 < n0 \<and> N1 < n1 \<longrightarrow> s n0 n = s n1 n" 
        using assms(1) padic_integers.is_cauchy_imp_eventually_const_0 padic_integers_axioms by blast
      obtain N2 where N2_def: "\<forall>n0 n1. N2 < n0 \<and> N2 < n1 \<longrightarrow> t n0 n = t n1 n" 
        using assms(2) padic_integers.is_cauchy_imp_eventually_const_0 padic_integers_axioms by blast
      obtain M where M_def: "M = max N1 N2"
        by simp
      have "\<forall>n0 n1. M < n0 \<and> M < n1 \<longrightarrow> seq_prod s t n0 n = seq_prod s t n1 n"
      proof
        fix n0
        show "\<forall>n1. M < n0 \<and> M < n1 \<longrightarrow> seq_prod s t n0 n = seq_prod s t n1 n"
        proof
          fix n1 
          show " M < n0 \<and> M < n1 \<longrightarrow> seq_prod s t n0 n = seq_prod s t n1 n"
          proof
            assume A: "M < n0 \<and> M < n1 "
            have Fs: " s n0 n = s n1 n" using A M_def N1_def by auto
            have Ft: " t n0 n = t n1 n" using A M_def N2_def by auto
            then show "seq_prod s t n0 n = seq_prod s t n1 n" using seq_prod_def 
              by (simp add: Fs Z\<^sub>p_def padic_mult_def)
          qed
        qed
      qed
      then show ?thesis 
        by blast
    qed
  qed
qed

(*Predicate for constant sequences*)
definition is_constant_seq :: "padic_int_seq \<Rightarrow> bool" where
"is_constant_seq s = (\<exists>x \<in> carrier Z\<^sub>p. \<forall>k. s k = x)"

(*Constant sequences are cauchy*)
lemma constant_is_cauchy:
  assumes "is_constant_seq s"
  shows "is_cauchy s"
proof(rule is_cauchyI)
  show "is_closed_seq s"
  proof(rule is_closedI)
    fix k 
    show "s k \<in> carrier Z\<^sub>p" 
      using assms is_constant_seq_def by auto
  qed
  obtain x where "\<And> k. s k = x" 
    using assms is_constant_seq_def by blast
  then show "\<And>n. \<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> s n0 n = s n1 n" 
    by simp
qed

(**************************************************************************************************)
(**************************************************************************************************)
(*******************************   SEQUENTIAL COMPACTNESS  ****************************************)
(*******************************          OF ZP            ****************************************)
(**************************************************************************************************)
(**************************************************************************************************)

(*The refinement of a sequence by a function nat \<Rightarrow> nat*)
definition take_subseq :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> 'a)" where
"take_subseq s f = (\<lambda>k. s (f k))"

(*Predicate for increasing function on the natural numbers*)
definition is_increasing :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
"is_increasing f = (\<forall> n m::nat. n>m \<longrightarrow> (f n) > (f m))"

(*Elimination and introduction lemma for increasing functions*)
lemma is_increasingI:
  assumes "\<And> n m::nat. n>m \<Longrightarrow> (f n) > (f m)"
  shows "is_increasing f"
  unfolding is_increasing_def 
  using assms 
  by blast 

lemma is_increasingE: 
  assumes "is_increasing f"
  assumes " n> m"
  shows "f n > f m"
  using assms
  unfolding is_increasing_def 
  by blast 

(*The subsequence predicate*)
definition is_subseq_of :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool" where
"is_subseq_of s s' = (\<exists>(f::nat \<Rightarrow> nat). is_increasing f \<and> s' = take_subseq s f)"

(*Subsequence introduction lemma*)
lemma is_subseqI:
  assumes "is_increasing f"
  assumes "s' = take_subseq s f"
  shows "is_subseq_of s s'"
  using assms 
  unfolding is_subseq_of_def 
  by auto 

(*Given a sequence and a predicate, returns the function nat\<Rightarrow>nat which represents the increasing
sequences of indices n on which P (s n) holds.*)

primrec filtering_function :: "(nat \<Rightarrow>'a) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat" where
"filtering_function s P (0::nat) = (LEAST k::nat. P (s k))"|
"filtering_function s P (Suc n) = (LEAST k:: nat. (P (s k)) \<and> k > (filtering_function s P n))"   

lemma filtering_func_pre_increasing:
  assumes "\<forall>n::nat. \<exists>m. m > n \<and> P (s m)"
  shows "filtering_function s P n < filtering_function s P (Suc n)" 
  apply(auto)
proof(induction n)
  case 0
  have "\<exists>k. P (s k)" using assms(1) by blast
  then have "\<exists>k::nat. (LEAST k::nat. (P (s k))) \<ge> 0" 
    by blast
  obtain k where "(LEAST k::nat. (P (s k))) = k" by simp
  have "\<exists>l. l = (LEAST l::nat. (P (s l) \<and> l > k))" 
    by simp
  thus ?case
    by (metis (no_types, lifting) LeastI assms)
next
  case (Suc n)
  then show ?case
    by (metis (no_types, lifting) LeastI assms)
qed

lemma filtering_func_increasing:
  assumes "\<forall>n::nat. \<exists>m. m > n \<and> P (s m)"
  shows "is_increasing (filtering_function s P)" 
  by (metis assms filtering_func_pre_increasing is_increasingI lift_Suc_mono_less) 


definition filtered_sequence :: "(nat \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 'a)" where
"filtered_sequence s P = take_subseq s (filtering_function s P)"

lemma filter_exist:
  assumes "is_closed_seq s"
  assumes "\<forall>n::nat. \<exists>m. m > n \<and> P (s m)"
  shows "\<And>m. n\<le>m \<Longrightarrow> P (s (filtering_function s P n))"
proof(induct n)
  case 0
  then show ?case 
    using LeastI assms(2) by force
next
  case (Suc n)
  then show ?case 
    by (smt LeastI assms(2) filtering_function.simps(2))
qed
(* In a filtered sequence, every element satisfies the given predicate *)

lemma fil_seq_pred:
  assumes "is_closed_seq s"
  assumes "s' = filtered_sequence s P"
  assumes "\<forall>n::nat. \<exists>m. m > n \<and> P (s m)"
  shows "\<And>m::nat. P (s' m)"
proof-
  have "\<exists>k. P (s k)" using assms(3) 
    by blast
  fix m
  obtain k where kdef: "k = filtering_function s P m" by auto 
  have "\<exists>k. P (s k)" 
    using assms(3) by auto
  then have "P (s k)" 
    using  kdef 
    by (metis assms(1) assms(3) le_refl padic_integers.filter_exist padic_integers_axioms)
  then have "s' m = s k"
    by (simp add: assms(2) filtered_sequence_def kdef take_subseq_def)
  hence "P (s' m)" 
    by (simp add: \<open>P (s k)\<close>)
  thus "\<And>m. P (s' m)" 
    by (metis assms(1) assms(2) assms(3) filtered_sequence_def le_refl padic_integers.filter_exist padic_integers_axioms take_subseq_def)
qed


definition kth_res_equals :: "nat \<Rightarrow> int \<Rightarrow> (padic_int  \<Rightarrow> bool)" ("Pr _  _") where
"kth_res_equals k n a = (a k = n)"

(*The characteristic function of the underlying set of a sequence*)
definition indicator:: "(nat \<Rightarrow> 'a) \<Rightarrow> ('a  \<Rightarrow> bool)" where
"indicator s a = (\<exists>n::nat. s n = a)"
  

(*Every filtering function is the indicator of the sequence that it filters
lemma filtering_function_is_indicator:
  assumes "s' = filtered_sequence s P"
  assumes "is_subseq s s'"
  shows "P = indicator s'"
  sorry*)

(*choice function for a subsequence with constant kth residue. Could be made constructive by 
choosing the LEAST n if we wanted.*)
definition equal_res_choice :: "nat \<Rightarrow> padic_int_seq \<Rightarrow> padic_int_seq" ("Cseq _ _") where
"equal_res_choice k s = (SOME s'::(padic_int_seq). (\<exists> n. is_subseq_of s s' \<and> s' 
  = (filtered_sequence s (Pr k n)) \<and> (\<forall>m. s' m k = n)))" 

(*The constant kth residue value for the sequence obtained by the previous function*)
definition equal_res_choice_res :: "nat \<Rightarrow> padic_int_seq \<Rightarrow> int" ("Cres") where
"equal_res_choice_res k s = (THE n. (\<forall> m. (Cseq k s) m k = n))" 

definition maps_to_n:: "nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> bool" where
"maps_to_n n f = (\<forall>(k::nat). f k \<in> {0..n})"

definition drop :: "nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> (nat \<Rightarrow> int)" where
"drop k f n = (if (f n)=k then 0 else f n)"
 
lemma maps_to_nE:
  assumes "maps_to_n n f"
  shows "(f k) \<in> {0..n}"
  using assms
  unfolding maps_to_n_def
  by blast
 
lemma maps_to_nI:
  assumes "\<And>n. f n \<in>{0 .. k}"
  shows "maps_to_n k f"
  using assms maps_to_n_def by auto
 
 
lemma maps_to_n_drop:
  assumes "maps_to_n (Suc n) f"
  shows "maps_to_n n (drop (Suc n) f)"
(*proof(rule maps_to_nI)*)
proof-
  fix k
  have "drop (Suc n) f k \<in> {0..n}"
  proof(cases "f k = Suc n")
    case True
    then have "drop (Suc n) f k = 0"
      unfolding drop_def by auto
    then show ?thesis 
      using assms local.drop_def maps_to_n_def by auto
  next
    case False
    then show ?thesis
      using assms atLeast0_atMost_Suc maps_to_n_def drop_def
      by auto
  qed
  then have "\<And>k. drop (Suc n) f k \<in> {0..n}" 
    using assms local.drop_def maps_to_n_def by auto
    then show "maps_to_n n (drop (Suc n) f)" using maps_to_nI
      using maps_to_n_def by blast
  qed
 
lemma drop_eq_f:
  assumes "maps_to_n (Suc n) f"
  assumes "\<not> (\<forall>m. \<exists>n. n>m \<and> (f n = (Suc k)))"
  shows "\<exists>N. \<forall>n. n>N \<longrightarrow> f n = drop (Suc k) f n"
proof-
  have "\<exists>m. \<forall>n. n \<le> m \<or> (f n) \<noteq> (Suc k)"
    using assms
    by (meson Suc_le_eq nat_le_linear)
  then have "\<exists>m. \<forall>n. n \<le> m \<or> (f n)  = drop (Suc k) f n"
    using drop_def by auto
  then show ?thesis
    by (meson less_Suc_eq_le order.asym)
qed
 
lemma maps_to_n_infinite_seq:
  shows "\<And>f. maps_to_n k f \<Longrightarrow> \<exists>l. \<forall>m. \<exists>n. n>m \<and> (f n = l)"
proof(induction k)
  case 0  
  then have "\<And>n. f n \<in> {0}"
    using maps_to_nE[of 0 f] by auto
  then show " \<exists>l. \<forall>m. \<exists>n. m < n \<and> f n = l"
    by blast
next
  case (Suc k)
  assume IH: "\<And>f. maps_to_n k f \<Longrightarrow> \<exists>l. \<forall>m. \<exists>n. m < n \<and> f n = l"
  fix f
  assume A: "maps_to_n (Suc k) f"
  show "\<exists>l. \<forall>m. \<exists>n. n>m \<and> (f n = l)"
  proof(cases " \<forall>m. \<exists>n. n>m \<and> (f n = (Suc k))")
    case True
    then show ?thesis by blast
  next
    case False
    then obtain N where N_def: "\<forall>n. n>N \<longrightarrow> f n = drop (Suc k) f n"
      using drop_eq_f drop_def
      by fastforce
    have " maps_to_n k (drop (Suc k) f) "
      by (simp add: A maps_to_n_drop)
    then have " \<exists>l. \<forall>m. \<exists>n. m < n \<and> (drop (Suc k) f) n = l"
      using IH by blast
    then obtain l where l_def: "\<forall>m. \<exists>n. m < n \<and> (drop (Suc k) f) n = l"
      by blast
    have "\<forall>m. \<exists>n. n>m \<and> (f n = l)"
      apply auto
    proof-
      fix m
      show "\<exists>n>m. f n = l"
      proof-
        obtain n where N'_def: "(max m N) < n \<and> (drop (Suc k) f) n = l"
          using l_def by blast
        have "f n =  (drop (Suc k) f) n"
          using N'_def N_def
          by simp
        then show ?thesis
          using N'_def by auto
      qed
    qed
    then show ?thesis
      by blast
  qed
qed

definition index_to_residue :: "padic_int_seq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
"index_to_residue s k m = ((s m) k)"


lemma(in padic_integers) seq_maps_to_n:
  assumes "is_closed_seq s"
  shows "\<And>m. maps_to_n ((p^k)-1) (index_to_residue s k)"
proof-
  have A1: "\<And>m. (s m) \<in> carrier Z\<^sub>p" 
    using assms is_closed_seq_def by auto
  have "\<And>m. (s m k) \<in> {0..(p^k -1)}" 
    by (metis A1 le_refl r_Zp r_range)
  have "\<And>m. index_to_residue s k m = s m k" using index_to_residue_def 
    using \<open>\<And>m. s m k \<in> {0..int (p ^ k - 1)}\<close> by auto
  thus "\<And>m. maps_to_n ((p^k)-1) (index_to_residue s k)" 
    by (metis \<open>\<And>m. s m k \<in> {0..int (p ^ k - 1)}\<close> atLeastAtMost_iff  
        padic_integers.maps_to_n_def padic_integers_axioms)
qed

lemma(in padic_integers) seq_pr_inc:
  assumes "is_closed_seq s"
  shows "\<exists>l. \<forall>m. \<exists>n > m. (Pr k l) (s n)"
proof-
  fix k l m
  have "(Pr k l) (s m) \<Longrightarrow> (s m) k = l" 
    by (simp add: kth_res_equals_def)
  have "\<And>k. s m k = index_to_residue s k m" 
    by (simp add: index_to_residue_def)
  have A1: "maps_to_n (p^k - 1) (index_to_residue s k)" using seq_maps_to_n assms by blast
  then have "\<And>m. s m k \<in> {0..(p^k - 1)}" 
    by (metis index_to_residue_def maps_to_nE)
  have "maps_to_n (p^k - 1) (index_to_residue s k) \<Longrightarrow>  \<exists>l. \<forall>m. \<exists>n. n>m \<and> (index_to_residue s k n = l)" 
    by (simp add: maps_to_n_infinite_seq)
  hence "\<exists>l. \<forall>m. \<exists>n. n > m \<and>  (index_to_residue s k n = l)" using A1 by simp
  hence "\<exists>l. \<forall>m. \<exists>n. n > m \<and>  (s n k = l)" 
    by (simp add: index_to_residue_def)
  thus "\<exists>l. \<forall>m. \<exists>n > m. (Pr k l) (s n)" 
    using kth_res_equals_def by auto
qed


lemma Pr_subseq:
  assumes "is_closed_seq s"
  shows "\<exists>n. is_subseq_of s (filtered_sequence s (Pr k n)) \<and> (\<forall>m. (filtered_sequence s (Pr k n)) m k = n)"
proof-
  obtain l where l_def: " \<forall> m. \<exists>n > m. (Pr k l) (s n)"
    using assms seq_pr_inc by blast
  have 0: "is_subseq_of s (filtered_sequence s (Pr k l))"
    unfolding filtered_sequence_def
  proof(rule is_subseqI)
    let ?f = "(filtering_function s Pr k  l)"
    show "is_increasing ?f"
      using l_def 
      by (simp add: filtering_func_increasing)
    show "take_subseq s (filtering_function s Pr k  l) = take_subseq s (filtering_function s Pr k  l)"
      by auto
  qed
  have 1: " (\<forall>m. (filtered_sequence s (Pr k l)) m k = l)"
   using l_def 
   by (meson assms kth_res_equals_def padic_integers.fil_seq_pred padic_integers_axioms)
  show ?thesis using 0 1 by blast 
qed

lemma Cseq_prop_0: 
  assumes "is_closed_seq s"
  shows "\<exists>l. (((Cseq k s) = filtered_sequence s (Pr k l)) \<and> (is_subseq_of s (Cseq k s)) \<and> (\<forall>m.(Cseq k s) m k = l))"
proof-
  have " \<exists>n. (is_subseq_of s (filtered_sequence s Pr k  n) \<and> (\<forall>m. (filtered_sequence s Pr k  n) m k = n))"
    by (simp add: Pr_subseq assms)
  then have "\<exists>s'. (\<exists>n. (is_subseq_of s s') \<and> (s' = filtered_sequence s Pr k  n) \<and> (\<forall>m. s' m k = n))"
    by blast
  then show ?thesis
  using equal_res_choice_def[of k s]   
      by (smt equal_res_choice_def someI_ex)
qed

lemma Cseq_prop_1: 
  assumes "is_closed_seq s"
  shows "(\<forall>m.(Cseq k s) m k = (Cres k s) )"
  using Cseq_prop_0[of s] equal_res_choice_res_def[of k s]
  by (smt assms equal_res_choice_def equal_res_choice_res_def the_equality)

lemma Cres_range:
  assumes "is_closed_seq s"
  assumes "k > 0"
  shows "Cres k s \<in> carrier R k"
proof-
  have 0: "is_closed_seq (Cseq k s)"
    by (metis (no_types, hide_lams) Cseq_prop_0 assms(1) 
        filtered_sequence_def is_closedI is_closed_simp take_subseq_def)
  have 1: "(Cseq k s) 0 k \<in>  carrier R k"
    using 0  padic_integers.is_closed_seq_def padic_integers_axioms padic_set_simp0 
    by auto
  then show  ?thesis
  using assms Cseq_prop_1[of s k] 
  by (simp add: \<open>is_closed_seq s\<close>)
qed

fun res_seq ::"padic_int_seq \<Rightarrow> nat \<Rightarrow>  padic_int_seq" where
"res_seq s 0 = s"|
"res_seq s (Suc k) = Cseq (Suc k) (res_seq s k)"

lemma res_seq_res:
  assumes "is_closed_seq s"
  shows "is_closed_seq (res_seq s k)"
  apply(induction k)
  apply (simp add: assms)
  by (smt is_subseq_of_def padic_integers.Cseq_prop_0 padic_integers.is_closed_seq_def 
      padic_integers_axioms res_seq.simps(2) take_subseq_def)

lemma res_seq_res':
  assumes "is_closed_seq s"
  shows "\<And>n. res_seq s (Suc k) n (Suc k) = Cres (Suc k) (res_seq s k)"
  using assms res_seq_res[of s k] Cseq_prop_1[of "(res_seq s k)" "Suc k" ] 
  by simp

lemma res_seq_subseq: 
  assumes "is_closed_seq s"
  shows "is_subseq_of (res_seq s k) (res_seq s (Suc k))"
  by (metis assms  padic_integers.Cseq_prop_0 padic_integers.res_seq_res padic_integers_axioms 
      res_seq.simps(2))


definition acc_point :: "padic_int_seq \<Rightarrow> padic_int" where
"acc_point s k = (if (k = 0) then (0::int) else ((res_seq s k) 0 k))"

lemma res_seq_res_1:
  assumes "is_closed_seq s"
  shows "res_seq s (Suc k) 0 k = res_seq s k 0 k"
proof-
  obtain n where  n_def: "res_seq s (Suc k) 0 = res_seq s k n" 
    by (metis assms is_subseq_of_def res_seq_subseq take_subseq_def)
  have "res_seq s (Suc k) 0 k = res_seq s k n k"
    using n_def by auto
  thus ?thesis 
    by (metis (no_types, hide_lams)  Cseq_prop_1 Zp_is_cring  assms cring_def  is_closed_simp 
        monoid.nat_pow_0 monoid.r_one n_def of_nat_0 of_nat_le_0_iff p_pow_factor res_seq.elims 
        res_seq_res ring_def)
qed

lemma acc_point_cres:
  assumes "is_closed_seq s"
  shows "(acc_point s (Suc k)) = (Cres (Suc k) (res_seq s k))" 
proof-
  have "Suc k > 0" by simp
  have "(res_seq s (Suc k)) = Cseq (Suc k) (res_seq s k)" (*(Cseq k s) m k = (Cres k s) )"*)
    by simp
  then have "(Cseq (Suc k) (res_seq s k)) 0 (Suc k) = Cres (Suc k)  (res_seq s k)" 
    using assms padic_integers.res_seq_res' padic_integers_axioms by auto
  have "acc_point s (Suc k) = res_seq s (Suc k) 0 (Suc k)" using acc_point_def by simp
  then have "acc_point s (Suc k) = (Cseq (Suc k) (res_seq s k)) 0 (Suc k)"
    by simp
  thus ?thesis 
    by (simp add: \<open>Cseq Suc k res_seq s k 0 (Suc k) = Cres (Suc k) (res_seq s k)\<close>)
qed

lemma acc_point_res:
  assumes "is_closed_seq s"
  shows "res (int p ^ k) (acc_point s (Suc k)) = acc_point s k"
proof(cases "k = 0")
  case True
  then show ?thesis 
    by (metis Res_0' acc_point_def of_nat_power r_range')
next
  case False
  assume "k \<noteq> 0"
  show "res (int p ^ k) (acc_point s (Suc k)) = acc_point s k" 
    by (metis False acc_point_def assms is_closed_simp lessI less_imp_le nat.distinct(1) 
        of_nat_power padic_integers.res_seq_res_1 padic_integers_axioms r_Zp res_seq_res)
qed

lemma acc_point_closed:
  assumes "is_closed_seq s"
  shows "acc_point s \<in>  carrier Z\<^sub>p" 
proof-
  have "acc_point s \<in> padic_set p"
  proof(rule padic_set_mem)
    show "\<And>m. acc_point s m \<in> carrier (residue_ring (int p ^ m))"
    proof-
      fix m
      show "acc_point s m \<in> carrier (residue_ring (int p ^ m))"
      proof(cases "m = 0")
        case True
        then show ?thesis 
          by (simp add: acc_point_def residue_ring_def)
      next
        case False
        assume "m \<noteq> 0" 
        then have "acc_point s m = res_seq s m 0 m" (*"res_seq s (Suc k) = Cseq (Suc k) (res_seq s k)"*)
          by (simp add: acc_point_def)
        (*then have "res_seq s m 0 m = Cres 0 (Cseq m (res_seq s (m-1)))" sledgehammer*)
        then show ?thesis  using Cres_range[of "(Cseq (m-1) s)" m] acc_point_def[of s m] 
          by (metis acc_point_res assms of_nat_power r_range')
      qed
    qed
    show "\<And>m n. m < n \<Longrightarrow> res (int p ^ m) (acc_point s n) = acc_point s m"
    proof-
      fix m n::nat 
      assume A: "m < n"
      show "res (int p ^ m) (acc_point s n) = acc_point s m"
      proof-
        obtain l where l_def: "l = n - m - 1"
          by simp
        have "res (int p ^ m) (acc_point s (Suc (m + l))) = acc_point s m"
        proof(induction l)
          case 0
          then show ?case 
            by (simp add: acc_point_res assms)
        next
          case (Suc l)
          then show ?case 
            by (metis acc_point_def add_Suc_right assms is_closed_simp le_add1 nat.distinct(1) 
                of_nat_power padic_integers.res_seq_res_1 padic_integers_axioms r_Zp res_seq_res)
        qed
        then show ?thesis 
          by (metis A Suc_diff_Suc Suc_eq_plus1 add_Suc_right add_diff_inverse_nat diff_diff_left 
              l_def le_less_trans less_not_refl order_less_imp_le)
      qed
    qed
  qed
  then show ?thesis 
    by (simp add: Z\<^sub>p_def)
qed

(*Choice function for a subsequence of s which converges to a, if it exists*)
fun convergent_subseq_fun :: "padic_int_seq \<Rightarrow> padic_int \<Rightarrow> (nat \<Rightarrow> nat)" where
"convergent_subseq_fun s a 0 = 0"|
"convergent_subseq_fun s a (Suc n) = (SOME k. k > (convergent_subseq_fun s a n)
                                                \<and> (s k (Suc n)) = a (Suc n))"

definition convergent_subseq :: "padic_int_seq \<Rightarrow> padic_int_seq" where
"convergent_subseq s = take_subseq s (convergent_subseq_fun s (acc_point s))"

lemma increasing_conv_subseq_fun_0:
  assumes "is_closed_seq s"
  assumes "\<exists>s'. s' = convergent_subseq s"
  assumes "a = acc_point s"
  shows "convergent_subseq_fun s a (Suc n) > convergent_subseq_fun s a n"
  apply(auto)
  sorry
proof(induction n)
  case 0
  have "convergent_subseq_fun s a 0 = 0" by simp
  have "\<exists>k. k > 0 \<and> (s k k) = a k"
  proof-
    obtain k::nat where "k > 0" by blast
    have "(s k) \<in> carrier Z\<^sub>p" 
      by (simp add: assms(1))
    have "a k = res_seq s k 0 k" using acc_point_def
      using \<open>0 < k\<close> assms(3) by auto
    have "\<And>n. res_seq s k n k = Cres k (res_seq s (k-1))" using res_seq_res' 
      by (metis One_nat_def Suc_pred \<open>0 < k\<close> assms(1))
    then have "res_seq s k 0 k = Cres k (res_seq s (k-1))" 
      by blast
    then have "s k n = a n" sledgehammer
    thus ?thesis 
      using \<open>0 < k\<close> by blast
    qed
    thus ?case 
      by (metis (mono_tags, lifting) convergent_subseq_fun.simps(1) someI2_ex)
next
  case (Suc k)
  then show ?case 
  qed

lemma increasing_conv_subseq_fun:
  assumes "is_closed_seq s"
  assumes "a = acc_point s"
  assumes "\<exists>s'. s' = convergent_subseq s"
  shows "is_increasing (convergent_subseq_fun s a)"
    by (metis assms(1) assms(2) increasing_conv_subseq_fun_0 is_increasingI lift_Suc_mono_less)

lemma convergent_subseq_is_subseq:
  assumes "is_closed_seq s"
  shows "is_subseq_of s (convergent_subseq s)" 
  using assms convergent_subseq_def increasing_conv_subseq_fun is_subseqI by blast

lemma is_closed_seq_conv_subseq:
  assumes "is_closed_seq s"
  shows "is_closed_seq (convergent_subseq s)"  
  by (simp add: assms convergent_subseq_def take_subseq_def)

lemma convergent_subsequence_is_convergent:
  assumes "is_closed_seq s"
  shows "converges_to (convergent_subseq s) (acc_point s)" (*\<And>n. \<exists>N. \<forall>k > N. s k n = a n"*)
proof(rule converges_toI)
  show "acc_point s \<in> carrier Z\<^sub>p"
    using acc_point_closed assms  by blast
  show "is_closed_seq (convergent_subseq s)" using is_closed_seq_conv_subseq assms by simp
  show "\<And>n. \<exists>N. \<forall>k>N. convergent_subseq s k n = acc_point s n" 
  proof
    have "\<exists>k. (k > (convergent_subseq_fun s (acc_point s) n) \<and> (s k (Suc n)) = (acc_point s) (Suc n))" 
    proof(induct n)
      case 0
      have "\<exists>k. (k > 0) \<and> (s k 1) = (acc_point s) 1" 
       then show ?case
    next
        case (Suc n)
        then show ?case sorry
    qed
    
    


lemma Zp_is_compact:
  assumes "is_closed_seq s"
  shows "\<exists>s'. is_subseq_of s s' \<and> (converges_to s' (acc_point s))" 
  sorry



(**************************************************************************************************)
(**************************************************************************************************)
(*******************************   CONTINUOUS FUNCTIONS    ****************************************)
(**************************************************************************************************)
(**************************************************************************************************)

definition push_forward :: "padic_int_fun \<Rightarrow> padic_int_seq \<Rightarrow> padic_int_seq" ("_\<^sub>*_") where
"push_forward f s = (\<lambda> k . f ( s k))"

definition is_closed_fun :: "padic_int_fun \<Rightarrow> bool" where
"is_closed_fun f = (\<forall> x. x \<in> carrier Z\<^sub>p \<longrightarrow> f x \<in> carrier Z\<^sub>p)"

definition fun_sum:: "padic_int_fun \<Rightarrow> padic_int_fun \<Rightarrow> padic_int_fun" where
"fun_sum f g = (\<lambda>x. (f x) \<oplus> (g x))" 

definition fun_prod:: "padic_int_fun \<Rightarrow> padic_int_fun \<Rightarrow> padic_int_fun" where
"fun_prod f g = (\<lambda>x. (f x) \<otimes> (g x))" 

definition is_constant_fun :: "padic_int_fun \<Rightarrow> bool" where
"is_constant_fun f = (\<exists>x \<in> carrier Z\<^sub>p. \<forall>y \<in> carrier Z\<^sub>p. f y = x)"

definition eq_on_Zp :: "padic_int_fun \<Rightarrow> padic_int_fun \<Rightarrow> bool" (infixl "\<doteq>" 78) where
"eq_on_Zp f g = (\<forall>x. x \<in> carrier Z\<^sub>p \<longrightarrow> f x = g x)"

lemma eq_simp:
  assumes "(f \<doteq> g)"
  assumes "x \<in> carrier Z\<^sub>p"
  shows "f x = g x" 
  using eq_on_Zp_def assms(1) assms(2) by blast


lemma push_forward_eq:
  assumes "f \<doteq> g "
  assumes "is_closed_seq s"
  shows "(f\<^sub>*s) = (g\<^sub>*s)"
proof
  fix x 
  have "s x \<in> carrier Z\<^sub>p"
    by (simp add: assms(2))
  then show "(f\<^sub>*s) x = (g\<^sub>*s) x" 
    using assms(1) eq_simp padic_integers.push_forward_def padic_integers_axioms by auto
qed


lemma is_closed_funI:
  assumes "\<And>x. x \<in> carrier Z\<^sub>p \<Longrightarrow> f x \<in> carrier Z\<^sub>p"
  shows "is_closed_fun f"
  by (simp add: assms is_closed_fun_def)

lemma is_closed_eq:
  assumes "is_closed_fun f"
  assumes "f \<doteq> g"
  shows "is_closed_fun g"
proof(rule is_closed_funI)
  show "\<And>x. x \<in> carrier Z\<^sub>p \<Longrightarrow> g x \<in> carrier Z\<^sub>p" 
    using assms eq_simp  by (simp add: is_closed_fun_def)
qed

lemma constant_is_closed:
  assumes "is_constant_fun f"
  shows "is_closed_fun f"
  using is_closed_fun_def is_constant_fun_def  assms by auto

lemma push_forward_of_constant_is_constant:
  assumes "is_constant_fun f"
  assumes "is_closed_seq s"
  shows "is_constant_seq (f\<^sub>*s)"
  using assms(1) assms(2) 
  by (metis (full_types) is_closed_simp is_constant_fun_def
      is_constant_seq_def padic_integers.push_forward_def padic_integers_axioms)

lemma is_closed_fun_simp:
  assumes "x \<in> carrier Z\<^sub>p"
  assumes "is_closed_fun f"
  shows "f x \<in> carrier Z\<^sub>p"
  using is_closed_fun_def assms  by blast  

lemma push_forward_of_closed_is_closed:
  assumes "is_closed_seq s"
  assumes "is_closed_fun f"
  shows "is_closed_seq (f\<^sub>*s)" 
  using is_closed_fun_def is_closed_seq_def assms(1) assms(2)
    padic_integers.push_forward_def padic_integers_axioms by auto

lemma push_forward_of_sum_0:
"((fun_sum f g)\<^sub>*s) k = ((f\<^sub>*s) k) \<oplus> ((g\<^sub>*s) k)"
  by (simp add: fun_sum_def push_forward_def)

lemma push_forward_of_sum:
"((fun_sum f g)\<^sub>*s) = seq_sum (f\<^sub>*s) (g\<^sub>*s)"
proof
  fix x 
  show "((fun_sum f g)\<^sub>*s) x = (seq_sum (f\<^sub>*s) (g\<^sub>*s)) x" 
    by (simp add: push_forward_of_sum_0 seq_sum_def)
qed

lemma push_forward_of_prod_0:
"((fun_prod f g)\<^sub>*s) k = ((f\<^sub>*s) k) \<otimes> ((g\<^sub>*s) k)"
  by (simp add: fun_prod_def push_forward_def)

lemma push_forward_of_prod:
"((fun_prod f g)\<^sub>*s) = seq_prod (f\<^sub>*s) (g\<^sub>*s)"
proof
  fix x 
  show "((fun_prod f g)\<^sub>*s) x = (seq_prod (f\<^sub>*s) (g\<^sub>*s)) x" 
    by (simp add: push_forward_of_prod_0 seq_prod_def)
qed

definition is_continuous ::"padic_int_fun \<Rightarrow> bool" where
"is_continuous f = (is_closed_fun f \<and>(\<forall> s. is_cauchy s \<longrightarrow> is_cauchy(f\<^sub>*s)))"

lemma continuous_is_closed:
  assumes "is_continuous f"
  shows "is_closed_fun f" 
  using assms is_continuous_def by blast

lemma is_continuousI:
  assumes "is_closed_fun f"
  assumes "\<And>s. is_cauchy s \<Longrightarrow> is_cauchy (f\<^sub>*s)"
  shows "is_continuous f"
proof-
  have "(\<forall> s. is_cauchy s \<longrightarrow> is_cauchy(f\<^sub>*s))"
  proof
    fix s
    show "is_cauchy s \<longrightarrow> is_cauchy (f\<^sub>*s) " 
      by (simp add: assms(2))
  qed
  then show ?thesis 
    using assms(1) is_continuous_def by blast
qed

lemma is_continuous_eq:
  assumes "is_continuous f"
  assumes "f \<doteq> g"
  shows "is_continuous g"
proof(rule is_continuousI)
  show "is_closed_fun g" 
    using assms(1) assms(2) continuous_is_closed is_closed_eq by blast
  show "\<And>s. is_cauchy s \<Longrightarrow> is_cauchy (g\<^sub>*s)" 
    using assms(1) assms(2) is_cauchy_def is_continuous_def push_forward_eq by auto
qed

lemma constant_is_continuous:
  assumes "is_constant_fun f"
  shows "is_continuous f"
proof(rule is_continuousI)
  show "is_closed_fun f" 
    by (simp add: assms constant_is_closed)
  show "\<And>s. is_cauchy s \<Longrightarrow> is_cauchy (f\<^sub>*s)"
  proof-
    fix s
    assume A: "is_cauchy s"
    have "is_constant_seq (f\<^sub>*s)" 
      using A is_cauchy_def by (simp add: assms push_forward_of_constant_is_constant)
    then show "is_cauchy (f\<^sub>*s)"
      using A assms  by (simp add: constant_is_cauchy)
  qed
qed

lemma sum_of_cont_is_cont:
  assumes "is_continuous f"
  assumes "is_continuous g"
  shows "is_continuous (fun_sum f g)"
proof(rule is_continuousI)
  show "is_closed_fun (fun_sum f g)" using assms 
    using Z\<^sub>p_def Zp_is_cring cring.cring_simprules(1) is_continuous_def
      padic_integers.fun_sum_def padic_integers.is_closed_fun_def padic_integers_axioms by fastforce
  show "\<And>s. is_cauchy s \<Longrightarrow> is_cauchy ((fun_sum f g)\<^sub>*s)"
  proof-
    fix s
    assume A: "is_cauchy s"
    show "is_cauchy ((fun_sum f g)\<^sub>*s)"
    proof-
      have "((fun_sum f g)\<^sub>*s) = seq_sum (f\<^sub>*s) (g\<^sub>*s)" 
        by (simp add: push_forward_of_sum)
      then show ?thesis
        using A sum_of_cauchy_is_cauchy assms(1) assms(2) is_continuous_def by auto
    qed
  qed
qed

lemma prod_of_cont_is_cont:
  assumes "is_continuous f"
  assumes "is_continuous g"
  shows "is_continuous (fun_prod f g)"
proof(rule is_continuousI)
  show "is_closed_fun (fun_prod f g)" 
    using Z\<^sub>p_def Zp_is_cring assms(1) assms(2) cring.cring_simprules(5) 
      is_continuous_def padic_integers.fun_prod_def padic_integers.is_closed_fun_def
      padic_integers_axioms by fastforce
  show "\<And>s. is_cauchy s \<Longrightarrow> is_cauchy ((fun_prod f g)\<^sub>*s)"
  proof-
    fix s
    assume A: "is_cauchy s"
    show "is_cauchy ((fun_prod f g)\<^sub>*s)"
    proof-
      have "((fun_prod f g)\<^sub>*s) = seq_prod (f\<^sub>*s) (g\<^sub>*s)"
        by (simp add: push_forward_of_prod)
      then show ?thesis 
        using A assms is_continuous_def prod_of_cauchy_is_cauchy by simp
    qed
  qed
qed

definition alt_seq where
"alt_seq s = (\<lambda>k. (if (even k) then (s k) else (res_lim s)))"

lemma alt_seq_cauchy:
  assumes "is_cauchy s"
  shows "is_cauchy (alt_seq s)"
proof(rule is_cauchyI)
  show "is_closed_seq (alt_seq s)"
    using alt_seq_def[of s] 
          assms 
    unfolding  is_cauchy_def 
    using Z\<^sub>p_def assms padic_integers.is_closedI 
          padic_integers.is_closed_simp
          padic_integers_axioms res_lim_in_Zp 
    by presburger
  fix n
  show "\<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> alt_seq s n0 n = alt_seq s n1 n "
  proof-
    obtain N where N_def: " \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> s n0 n =  s n1 n "
      using assms padic_integers.is_cauchy_imp_eventually_const_0
            padic_integers_axioms 
      by blast
    have "\<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> alt_seq s n0 n = alt_seq s n1 n "
      apply auto 
    proof-
      fix n0 n1
      assume A: "N < n0" "N < n1"
      show "alt_seq s n0 n = alt_seq s n1 n"
        using N_def 
        unfolding alt_seq_def 
        by (smt A(1) A(2) assms lessI max_less_iff_conj 
            padic_integers.res_lim_cauchy padic_integers_axioms)
    qed
    then show ?thesis 
      by blast
  qed
qed

lemma alt_seq_limit:
  assumes "is_cauchy s"
  shows "res_lim(alt_seq s) = res_lim s"
proof-
  have "\<And>k. res_lim(alt_seq s) k = res_lim s k"
  proof-
    fix k
    obtain N where N_def: "\<forall> m. m> N \<longrightarrow>  s m k = res_lim s k"
      using assms res_lim_cauchy 
      by blast
    obtain N' where N'_def: "\<forall> m. m> N' \<longrightarrow>  (alt_seq s) m k = res_lim (alt_seq s) k"
      using assms res_lim_cauchy 
            alt_seq_cauchy 
      by blast
    have "\<And>m. m > (max N N') \<Longrightarrow> s m k = res_lim (alt_seq s) k"
    proof-
      fix m 
      assume A0: "m > (max N N')"
      have A1: "s m k = res_lim s k"
        using A0 N_def 
        by simp
      have A2: "(alt_seq s) m k = res_lim (alt_seq s) k"
        using A0 N'_def 
        by simp
      have A3: "(alt_seq s) m k = res_lim s k"
        using alt_seq_def A1 A2 
        by presburger
      show "s m k = res_lim (alt_seq s) k" 
        using A1 A2 A3 
        by auto 
    qed
    then have P:"\<And>m. m > (max N N') \<Longrightarrow> (res_lim s k) = res_lim (alt_seq s) k" 
      using N_def 
      by auto
    show "res_lim(alt_seq s) k = res_lim s k" 
      using P[of "Suc (max N N')"] 
      by auto 
  qed
  then show ?thesis 
    by (simp add: ext)
qed

lemma res_lim_pushforward: 
  assumes "is_continuous f"
  assumes "is_cauchy s"
  assumes "t = alt_seq s"
  shows "res_lim (f\<^sub>*t) = f (res_lim t)"
proof-
  have 0: "converges_to (f\<^sub>*t) (res_lim (f\<^sub>*t))"
    using assms alt_seq_cauchy is_cauchy_imp_has_limit 
          is_continuous_def 
    by blast
  have  "\<And>k. res_lim (f\<^sub>*t) k = f (res_lim t) k"
  proof-
    fix k
    show "res_lim (f\<^sub>*t) k = f (res_lim t) k"
    proof-
      obtain N where N_def: "\<And>m. m> N \<Longrightarrow> (f\<^sub>*t) m k = (res_lim (f\<^sub>*t)) k"
        using 0  
        by (meson convergent_imp_cauchy converges_to_def res_lim_cauchy)
      obtain M where M_def: "M = 2*(Suc N) + 1"
        by simp
      have 0: "t M = res_lim s"
        using assms 
        unfolding alt_seq_def
        by (simp add: M_def)
      have 1: "(f\<^sub>*t) M k = (res_lim (f\<^sub>*t)) k"
        using N_def M_def 
        by auto 
      have 2: "(f\<^sub>*t) M k = f (t M) k"
        by (simp add: push_forward_def)
      have 3: "(f\<^sub>*t) M k = f (res_lim s) k"
        using 0 2 by simp
      have 4: "(f\<^sub>*t) M k = f (res_lim t) k"
        using 3 assms alt_seq_limit[of s] 
        by auto
      show ?thesis 
        using 4 1 by auto 
    qed
  qed
  then show ?thesis by(simp add: ext)
qed

lemma res_lim_pushforward': 
  assumes "is_continuous f"
  assumes "is_cauchy s"
  assumes "t = alt_seq s"
  shows "res_lim (f\<^sub>*s) = res_lim (f\<^sub>*t)"
proof-
  obtain a where a_def: "a = res_lim (f\<^sub>*s)"
    by simp
  obtain b where b_def: "b = res_lim (f\<^sub>*t)"
    by simp 
  have "\<And>k. a k = b k"
  proof-
    fix k
    obtain Na where Na_def: "\<And>m. m > Na \<Longrightarrow> (f\<^sub>*s) m k = a k"
      using a_def assms  padic_integers.is_continuous_def 
            padic_integers_axioms res_lim_cauchy
      by blast
    obtain Nb where Nb_def: "\<And>m. m > Nb \<Longrightarrow> (f\<^sub>*t) m k = b k"
      using b_def assms padic_integers.is_continuous_def 
            padic_integers_axioms res_lim_cauchy
            alt_seq_cauchy 
      by blast
    obtain M where M_def: "M = 2*(max Na Nb) + 1"
      by simp
    have M0: "odd M"
      by (simp add: M_def)
    have M1: "M > Na" 
      using M_def 
      by auto 
    have M2: "M > Nb" 
      using M_def 
      by auto 
    have M3: "t M = res_lim s"
      using assms alt_seq_def M0 
      by auto 
    have M4: "((f\<^sub>*t) M) = f (res_lim s)"
      using M3 
      unfolding push_forward_def 
      by auto 
    have M5: "((f\<^sub>*t) M) k = b k"
      using M2 Nb_def by auto 
    have M6: "f (res_lim s) = f (res_lim t)" 
      using assms alt_seq_limit[of s] 
      by auto 
    have M7: "f (res_lim t) k = b k"
      using M4 M5 M6 by auto
    have M8: "(f\<^sub>*s) M k = (f\<^sub>*s) (Suc M) k"
      using M1 Na_def by auto
    have M9: "(f\<^sub>*s) (Suc M) = (f\<^sub>*t) (Suc M)"
      using assms unfolding push_forward_def alt_seq_def
      using M_def 
      by auto 
    have M10: "(f\<^sub>*t) M k = (f\<^sub>*t) (Suc M) k"
      by (simp add: M2 Nb_def less_SucI)
    have M11: "(f\<^sub>*t) M k = (f\<^sub>*s) M k"
      by (simp add: M10 M8 M9)
    show "a k = b k" 
      using M1 M11 M5 Na_def by auto
  qed
  then show ?thesis using a_def b_def ext[of a b] by auto 
qed

lemma continuous_limit:
  assumes "is_continuous f"
  assumes "is_cauchy s"
  shows "converges_to (f\<^sub>*s) (f (res_lim s))"
proof-
  obtain t where t_def: "t = alt_seq s"
    by simp
  have 0: "converges_to (f\<^sub>*s) (res_lim (f\<^sub>*s))"
    using assms(1) assms(2) is_continuous_def 
      padic_integers.is_cauchy_imp_has_limit padic_integers_axioms by blast
  have 1: "converges_to (f\<^sub>*s) (res_lim (f\<^sub>*t))"
    using "0" assms(1) assms(2) res_lim_pushforward' t_def by auto
  have 2: "converges_to (f\<^sub>*s) (f (res_lim t))"
    using "1" assms(1) assms(2) padic_integers.res_lim_pushforward padic_integers_axioms t_def by auto
  then show  "converges_to (f\<^sub>*s) (f (res_lim s))"
    by (simp add: alt_seq_limit assms(2) t_def)
qed

definition X_Zp :: "padic_int_fun" where
"X_Zp = (\<lambda>x. x)"

lemma push_forward_X:
"(X_Zp\<^sub>*s) = s"
proof
  fix x 
  show "(X_Zp\<^sub>*s) x = s x"
  using push_forward_def by (simp add: X_Zp_def)
qed

lemma X_is_continuous:
"is_continuous X_Zp"
  using is_continuous_def push_forward_X 
  by (simp add: X_Zp_def padic_integers.is_closed_fun_def padic_integers_axioms)

definition X_pow_Zp:: "nat \<Rightarrow> padic_int_fun" where 
"X_pow_Zp n x = (if n=0 then \<one> else x[^]n)"

lemma X_pow_Zp_prod:
  shows "X_pow_Zp (Suc n) = fun_prod (X_pow_Zp n) (X_Zp)"
proof
  fix x
  show "X_pow_Zp (Suc n) x = fun_prod (X_pow_Zp n) X_Zp x"
  proof-
    have "X_pow_Zp (Suc n) x = x[^](Suc n)" 
      by (simp add: X_pow_Zp_def)
    then have "X_pow_Zp (Suc n) x = x[^]n \<otimes> x" 
      by (metis Zp_is_cring cring_def monoid.nat_pow_Suc ring_def)
    then show ?thesis using fun_prod_def X_pow_Zp_def X_Zp_def 
    proof -
      have "ring Z\<^sub>p"
        using Zp_is_cring cring_def by blast
      then show ?thesis
        by (simp add: X_Zp_def X_pow_Zp_def fun_prod_def monoid.nat_pow_0 monoid.nat_pow_Suc ring_def)
    qed
  qed
qed

lemma X_pow_Zp_is_closed:
 "is_closed_fun (X_pow_Zp n)"
proof(induction n)
  case 0
  then show ?case 
    using X_pow_Zp_def Z\<^sub>p_def Zp_one_car padic_integers.is_closed_fun_def
      padic_integers_axioms by auto
next
  case (Suc n)
  then show ?case 
    by (metis X_pow_Zp_def Zp_is_cring cring_def is_closed_fun_def
        monoid.nat_pow_closed nat.simps(3) ring_def)
qed


lemma X_pow_Zp_is_continuous:
 "is_continuous (X_pow_Zp n)"
proof(induction n)
  case 0
  have  "is_constant_fun (X_pow_Zp (0::nat))"
  proof-
    have A0: "\<forall>x \<in> carrier Z\<^sub>p. (X_pow_Zp (0::nat)) x = \<one>" 
      using X_pow_Zp_def  by simp
    have A1: "\<one>\<in> carrier Z\<^sub>p" 
      by (simp add: Zp_one_car)
    then show ?thesis 
      using is_constant_fun_def A0 A1 by blast
  qed
  then show ?case 
    by (simp add: constant_is_continuous)
next
  case (Suc n)
  fix n
  assume IH :"is_continuous (X_pow_Zp n)"
  have "X_pow_Zp (Suc n) = fun_prod (X_pow_Zp n) X_Zp"
    by (simp add: X_pow_Zp_prod)
  then show "is_continuous (X_pow_Zp (Suc n))" 
    using IH X_is_continuous prod_of_cont_is_cont by auto 
qed
 
definition scalar_mult:: "padic_int \<Rightarrow> padic_int_fun \<Rightarrow> padic_int_fun" where
"scalar_mult c f = (\<lambda>x. c \<otimes> (f x))"

lemma scalar_mult_is_closed:
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "is_closed_fun f"
  shows "is_closed_fun (scalar_mult c f)"
proof(rule is_closed_funI)
  fix x
  assume "x \<in> carrier Z\<^sub>p "
  then show " scalar_mult c f x \<in> carrier Z\<^sub>p" 
    using assms scalar_mult_def 
    by (simp add: Zp_is_cring cring.cring_simprules(5) is_closed_fun_def)
qed

definition to_const_fun:: "padic_int \<Rightarrow> padic_int_fun"  where
"to_const_fun c = (\<lambda> x. c)"

lemma to_const_fun_is_const:
  assumes "c \<in> carrier Z\<^sub>p"
  shows "is_constant_fun (to_const_fun c)" 
  using assms is_constant_fun_def to_const_fun_def by auto

lemma scalar_mult_rep:
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "is_closed_fun f"
  shows "scalar_mult c f = fun_prod (to_const_fun c) f"
proof
  fix x
  show "scalar_mult c f x = fun_prod (to_const_fun c) f x" 
    using fun_prod_def padic_integers.to_const_fun_def padic_integers_axioms scalar_mult_def by auto
qed

lemma scalar_mult_is_continuous:
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "is_continuous f"
  shows "is_continuous (scalar_mult c f)"
proof-
  have 0: "scalar_mult c f = fun_prod (to_const_fun c) f" 
    by (simp add: assms(1) assms(2) continuous_is_closed scalar_mult_rep)
  have 1: "is_continuous (to_const_fun c)" 
    using assms(1) to_const_fun_is_const constant_is_continuous by auto  
  then show ?thesis 
    using 0 1 assms prod_of_cont_is_cont by auto  
qed

definition is_monomial :: "padic_int_fun \<Rightarrow> bool" where
"is_monomial f = (\<exists>c \<in> carrier Z\<^sub>p. \<exists>n::nat. f = scalar_mult c (X_pow_Zp n))"

lemma monomial_is_closed:
  assumes "is_monomial f"
  shows "is_closed_fun f" 
proof-
  obtain c n where 0: "c \<in> carrier Z\<^sub>p" and 1: "f = scalar_mult c (X_pow_Zp n)"
    using assms is_monomial_def  by blast
  then show ?thesis 
    using 0 1 scalar_mult_is_closed X_pow_Zp_is_closed by blast
qed

lemma monomial_is_continuous:
  assumes "is_monomial f"
  shows "is_continuous f" 
proof-
  obtain c n where 0: "c \<in> carrier Z\<^sub>p" and 1: "f = scalar_mult c (X_pow_Zp n)"
    using assms is_monomial_def  by blast
  then show ?thesis 
    by (simp add: X_pow_Zp_is_continuous scalar_mult_is_continuous)
qed

definition mon:: "padic_int \<Rightarrow> nat \<Rightarrow> padic_int_fun" where
"mon c n = scalar_mult c (X_pow_Zp n)"

lemma mon_is_monomial:
  assumes "c \<in> carrier Z\<^sub>p"
  shows "is_monomial (mon c n)"
  using assms is_monomial_def mon_def by blast



end
end 