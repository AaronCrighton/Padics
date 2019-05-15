theory padic_sequences
imports padic_field
begin

type_synonym padic_int_seq = "nat \<Rightarrow> padic_int"

type_synonym padic_int_fun = "padic_int \<Rightarrow> padic_int"

context padic_integers
begin

lemma Zp_is_cring:
"cring Z\<^sub>p" 
  by (simp add: Zp_is_domain domain.axioms(1))

lemma Zp_not_eq_diff_nonzero:
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
    by (simp add: Res_def Z\<^sub>p_def padic_add_def)
  then have "(a \<ominus> b) k = (a k) \<oplus>\<^bsub>R k\<^esub> (\<ominus>\<^bsub>R k\<^esub> (b k))"  
    using Res_def Z\<^sub>p_def assms(2) padic_inv prime by auto
  have 0: "(a \<ominus> b) k = (a k) \<ominus>\<^bsub>R k\<^esub> (b k)" using assms  
    by (metis \<open>(a \<ominus> b) k = a k \<oplus>\<^bsub>R k\<^esub> \<ominus>\<^bsub>R k\<^esub> b k\<close> a_minus_def)
  have 1: "( a \<ominus> b) k = 0" using assms 
    using Zp_is_cring cring.cring_simprules(4) zero_below_ord by fastforce
  then show ?thesis
  proof(cases "k=0")
    case True
    then show ?thesis 
      by (metis Z\<^sub>p_def assms(1) assms(2) padic_set_simp2 partial_object.select_convs(1) prime)
  next
    case False
    then have "k>0" by auto 
    then show ?thesis 
      using 0 1 Res_def R_residues R_cring 
      by (metis Z\<^sub>p_def assms(1) assms(2) cring_def padic_set_simp0 
          partial_object.select_convs(1) residues.res_zero_eq ring.r_right_minus_eq)
  qed
qed

lemma Zp_res_eq2:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "(a k) = (b k)" 
  assumes "a \<noteq>b"
  shows "ord_Zp (a \<ominus> b) \<ge> int k"
proof-
  have "a \<ominus> b = a \<oplus> (\<ominus> b)" 
    by (simp add: a_minus_def)
  then have "(a \<ominus> b) k = (a k) \<oplus>\<^bsub>R k\<^esub> ((\<ominus> b) k)" 
    by (simp add: Res_def Z\<^sub>p_def padic_add_def)
  then have "(a \<ominus> b) k = (a k) \<oplus>\<^bsub>R k\<^esub> (\<ominus>\<^bsub>R k\<^esub> (b k))"  
    using Res_def Z\<^sub>p_def assms(2) padic_inv prime by auto
  have 0: "(a \<ominus> b) k = (a k) \<ominus>\<^bsub>R k\<^esub> (b k)" using assms  
    by (metis \<open>(a \<ominus> b) k = a k \<oplus>\<^bsub>R k\<^esub> \<ominus>\<^bsub>R k\<^esub> b k\<close> a_minus_def)
  have 1: "( a \<ominus> b) k = 0" using assms(2) 
    by (metis Res_def Z\<^sub>p_def Zp_is_cring \<open>(a \<ominus> b) k = a k \<oplus>\<^bsub>R k\<^esub> (\<ominus> b) k\<close> 
        assms(3) cring.cring_simprules(17) padic_add_def ring.simps(2) zero_vals)
  then show ?thesis 
    by (meson Zp_is_cring assms(1) assms(2) assms(4) cring.cring_simprules(4)
        cring_def ord_Zp_geq ring.r_right_minus_eq)
qed

(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)

definition is_closed_seq :: "padic_int_seq \<Rightarrow> bool" where
"is_closed_seq s = (\<forall> n. s n \<in> carrier Z\<^sub>p)"

lemma is_closed_simp:
  assumes "is_closed_seq s"
  shows "s n \<in> carrier Z\<^sub>p"
  using assms is_closed_seq_def by blast

lemma is_closedI:
  assumes "\<And> k. s k \<in> carrier Z\<^sub>p"
  shows "is_closed_seq s"
  by (simp add: assms is_closed_seq_def)

abbreviation ord_Zp_dist :: "padic_int \<Rightarrow> padic_int \<Rightarrow> int" where
"ord_Zp_dist a b \<equiv> ord_Zp (a \<ominus> b)"

lemma ord_Zp_dist_sym:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in>carrier Z\<^sub>p"
  shows "ord_Zp_dist a b = ord_Zp_dist b a"
proof(cases "a = b")
  case True
  then show ?thesis 
    by simp
next
  case False
  have 0: "a \<ominus> b \<in> nonzero Z\<^sub>p" 
    using False assms(1) assms(2) Zp_not_eq_diff_nonzero by auto
  have 1: "a \<ominus> b = \<ominus> (b \<ominus> a)" using assms(1) assms(2)  
    using Zp_minus_ominus by blast
  then show ?thesis 
    using ord_Zp_of_ominus  by (metis Zp_not_eq_diff_nonzero assms(1) assms(2))
qed

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
    using Zp_not_eq_diff_nonzero assms(1) assms(2) assms(4) by auto
  have 2: "?Y \<in> nonzero Z\<^sub>p" 
    using Zp_not_eq_diff_nonzero assms(1) assms(3) assms(5) by blast
  have 3: "?Z \<in> nonzero Z\<^sub>p" 
    using Zp_not_eq_diff_nonzero assms(2) assms(3) assms(6) by blast
  have 4: "ord_Zp ?Z \<ge> min (ord_Zp ?X) (ord_Zp ?Y)" using 0 1 2 3 
    using Z\<^sub>p_def padic_integers.ord_Zp_ultrametric padic_integers_axioms by auto
  then show ?thesis 
    by (simp add: assms(1) assms(2) ord_Zp_dist_sym)
qed

lemma ord_Zp_dist_res_eq:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "ord_Zp_dist a b > int k"
  shows "(a k) = (b k)" 
  by (simp add: Zp_res_eq assms(1) assms(2) assms(3))

lemma ord_Zp_dist_res_eq2:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "(a k) = (b k)" 
  assumes "a \<noteq>b"
  shows "ord_Zp_dist a b \<ge>int k"
  by (simp add: Zp_res_eq2 assms(1) assms(2) assms(3) assms(4))

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
    using assms ord_Zp_dist_ultrametric  by simp
  then have 0: "ord_Zp_dist b c > int n" 
    using assms(4) assms(5) by linarith
  have 1: "(a \<ominus> b) k = 0" 
    using Zp_is_domain assms(1) assms(2) assms(4) assms(6) cring.cring_simprules(4)
      domain.axioms(1) zero_below_ord by fastforce
  have 2: "(a \<ominus> c) k = 0" 
    using Zp_is_domain assms(1) assms(3) assms(5) assms(6) cring.cring_simprules(4) 
      domain.axioms(1) zero_below_ord by fastforce
  have 3: "(b \<ominus> c) k = 0"
    using "0" Zp_is_cring assms(2) assms(3) assms(6) cring.cring_simprules(4) zero_below_ord by fastforce
  show "a k = b k" 
    using Zp_res_eq assms(1) assms(2) assms(4) assms(6) by auto
  show "a k = c k" 
    using Zp_res_eq assms(1) assms(3) assms(5) assms(6) by auto
  show "b k = c k" 
    using \<open>a k = b k\<close> \<open>a k = c k\<close> by auto
qed

definition is_cauchy :: "padic_int_seq \<Rightarrow> bool" where
"is_cauchy s = ((is_closed_seq s) \<and> (\<forall> (n::int). \<exists> (N::nat). \<forall> m k::nat. (m>N \<and> k>N \<longrightarrow> (s m) = (s k) \<or> (ord_Zp_dist (s m) (s k)) > n)))"

definition converges_to :: "padic_int_seq \<Rightarrow> padic_int \<Rightarrow> bool" where
"converges_to s a = ((a \<in> carrier Z\<^sub>p \<and> is_closed_seq s) 
    \<and> (\<forall>(n::int). (\<exists>(k:: nat). (\<forall>( m::nat). (m > k \<longrightarrow> (s m) = a \<or> (ord_Zp ((s m) \<ominus> a)) \<ge> n)))))"

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
        using is_cauchy_def assms by (simp add: is_closed_simp)
      have A2: "s n1 \<in> carrier Z\<^sub>p" 
        using is_cauchy_def assms by (simp add: is_closed_simp)
      show ?thesis 
        using A0 ord_Zp_dist_res_eq  A1 A2 by auto
    qed
  qed
  then show ?thesis 
    using that by blast
qed

lemma is_cauchyI:
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
              by simp
          next
            case False
            have 0: "(s m) \<in> carrier Z\<^sub>p"
              by (simp add: assms(1) is_closed_simp)
            have 1: "(s k) \<in> carrier Z\<^sub>p" 
              using Z\<^sub>p_def assms(1) padic_integers.is_closed_simp padic_integers_axioms by blast
            have "int (Suc (nat n)) \<le> ord_Zp_dist (s m) (s k)" 
              using False  E 0 1 ord_Zp_dist_res_eq2[of "(s m)" "(s k)" "Suc (nat n)"] by blast
            then have "int (nat n) < ord_Zp_dist (s m) (s k)" 
              by auto 
            then show ?thesis 
              by blast
          qed
        qed
      qed
    qed
    then show ?thesis 
      using zless_nat_conj zless_nat_eq_int_zless by auto
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
    using Res_def Z\<^sub>p_def \<open>s (Suc N) n = r\<close> assms is_closed_simp 
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

definition res_lim :: "padic_int_seq \<Rightarrow> padic_int" where
"res_lim s = (\<lambda> k. (THE r. (\<exists>N.  (\<forall> m. m > N \<longrightarrow> (s m) k = r))))"

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
      using res_lim_cauchy_0     by (simp add: Res_def assms)
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
              by auto
          next
            case False
            have X: "(s m) \<in> carrier Z\<^sub>p" 
              using "0" is_closed_simp by auto
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
    by (simp add: "0" converges_to_def)
qed

definition seq_sum:: "padic_int_seq \<Rightarrow> padic_int_seq \<Rightarrow> padic_int_seq" where
"seq_sum s1 s2 = (\<lambda> k. (s1 k) \<oplus> (s2 k))"

definition seq_prod:: "padic_int_seq \<Rightarrow> padic_int_seq \<Rightarrow> padic_int_seq" where
"seq_prod s1 s2 = (\<lambda> k. (s1 k) \<otimes> (s2 k))"

lemma sum_of_closed_seq_is_closed_seq:
  assumes "is_closed_seq s"
  assumes "is_closed_seq t"
  shows "is_closed_seq (seq_sum s t)"
proof(rule is_closedI)
  fix k
  have "seq_sum s t k = (s k) \<oplus>(t k)" using seq_sum_def by auto 
  then show "seq_sum s t k \<in> carrier Z\<^sub>p" 
    using assms is_closed_simp  by (simp add: Zp_is_cring cring.cring_simprules(1))
qed

lemma prod_of_closed_seq_is_closed_seq:
  assumes "is_closed_seq s"
  assumes "is_closed_seq t"
  shows "is_closed_seq (seq_prod s t)"
proof(rule is_closedI)
  fix k
  have "seq_prod s t k = (s k) \<otimes> (t k)" using seq_prod_def by auto 
  then show "seq_prod s t k \<in> carrier Z\<^sub>p" 
    using assms is_closed_simp  by (simp add: Zp_is_cring cring.cring_simprules(5))
qed

lemma sum_of_cauchy_is_cauchy:
  assumes "is_cauchy s"
  assumes "is_cauchy t"
  shows "is_cauchy (seq_sum s t)"
proof(rule is_cauchyI)
  show "is_closed_seq (seq_sum s t)" 
    using assms is_cauchy_def sum_of_closed_seq_is_closed_seq by auto  
  show "\<And>n. \<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> seq_sum s t n0 n = seq_sum s t n1 n"
  proof-
    fix n
    show "\<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> seq_sum s t n0 n = seq_sum s t n1 n"
    proof-
      obtain N1 where N1_def: "\<forall>n0 n1. N1 < n0 \<and> N1 < n1 \<longrightarrow> s n0 n = s n1 n" 
        using assms(1) padic_integers.is_cauchy_imp_eventually_const_0 padic_integers_axioms by blast
      obtain N2 where N2_def: "\<forall>n0 n1. N2 < n0 \<and> N2 < n1 \<longrightarrow> t n0 n = t n1 n" 
        using assms(2) padic_integers.is_cauchy_imp_eventually_const_0 padic_integers_axioms by blast
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
    using assms is_cauchy_def prod_of_closed_seq_is_closed_seq by auto  
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

definition is_constant_seq :: "padic_int_seq \<Rightarrow> bool" where
"is_constant_seq s = (\<exists>x \<in> carrier Z\<^sub>p. \<forall>k. s k = x)"

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
(*******************************   CONTINUOUS FUNCTIONS    ****************************************)
(**************************************************************************************************)
(**************************************************************************************************)

definition push_forward :: "padic_int_fun \<Rightarrow> padic_int_seq \<Rightarrow> padic_int_seq" ("_\<^sub>*_") where
"push_forward f s = (\<lambda> k. f ( s k))"

definition is_closed_fun :: "padic_int_fun \<Rightarrow> bool" where
"is_closed_fun f = (\<forall> x. x \<in> carrier Z\<^sub>p \<longrightarrow> f x \<in> carrier Z\<^sub>p)"

definition fun_sum:: "padic_int_fun \<Rightarrow> padic_int_fun \<Rightarrow> padic_int_fun" where
"fun_sum f g = (\<lambda>x. (f x) \<oplus> (g x))" 

definition fun_prod:: "padic_int_fun \<Rightarrow> padic_int_fun \<Rightarrow> padic_int_fun" where
"fun_prod f g = (\<lambda>x. (f x) \<otimes> (g x))" 

definition is_constant_fun :: "padic_int_fun \<Rightarrow> bool" where
"is_constant_fun f = (\<exists>x \<in> carrier Z\<^sub>p. \<forall>y \<in> carrier Z\<^sub>p. f y = x)"

lemma is_closed_funI:
  assumes "\<And>x. x \<in> carrier Z\<^sub>p \<Longrightarrow> f x \<in> carrier Z\<^sub>p"
  shows "is_closed_fun f"
  by (simp add: assms is_closed_fun_def)

lemma constant_is_closed:
  assumes "is_constant_fun f"
  shows "is_closed_fun f"
  using is_closed_fun_def is_constant_fun_def  assms by auto

lemma push_forward_of_constant_is_constant:
  assumes "is_constant_fun f"
  assumes "is_closed_seq s"
  shows "is_constant_seq (f\<^sub>*s)"
  using assms(1) assms(2) is_closed_simp is_constant_fun_def is_constant_seq_def
    padic_integers.push_forward_def padic_integers_axioms by auto

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
end