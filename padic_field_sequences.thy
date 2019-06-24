theory padic_field_sequences
imports padic_field_topology padic_int_topology
begin

type_synonym padic_num_seq = "nat \<Rightarrow> padic_number"

type_synonym padic_num_fun = "padic_number \<Rightarrow> padic_number"

locale padic_num_poly = padic_integers

context padic_num_poly
begin 

lemma PP[simp]: 
"padic_int_polynomial p"
  by (simp add: padic_int_polynomial.intro padic_integers_axioms)

lemma Qp_is_cring[simp]:
"cring Q\<^sub>p" 
  by (simp add: domain.axioms(1))

lemma Qp_not_eq_diff_nonzero[simp]:
  assumes "a \<noteq>b"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in>carrier Q\<^sub>p"
  shows "a \<ominus>\<^bsub>Q\<^sub>p\<^esub> b \<in> nonzero Q\<^sub>p" 
  by (meson Qp_is_domain assms(1) assms(2) assms(3) 
      cring.cring_simprules(4) cring_def domain.axioms(1) not_nonzero_Qp ring.r_right_minus_eq)

lemma Qp_minus_ominus:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  shows "a \<ominus>\<^bsub>Q\<^sub>p\<^esub> b = \<ominus>\<^bsub>Q\<^sub>p\<^esub> (b \<ominus>\<^bsub>Q\<^sub>p\<^esub> a)"
  by (metis Qp_is_cring a_minus_def assms(1) assms(2) cring.cring_simprules(10)
      cring.cring_simprules(20) cring.cring_simprules(21) cring.cring_simprules(3))

lemma Qp_diff_simp:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes  "X = a \<ominus>\<^bsub>Q\<^sub>p\<^esub> b"
  assumes "Y = c \<ominus>\<^bsub>Q\<^sub>p\<^esub> a"
  shows "X \<oplus>\<^bsub>Q\<^sub>p\<^esub> Y = c \<ominus>\<^bsub>Q\<^sub>p\<^esub> b"
proof-
  have "X \<oplus>\<^bsub>Q\<^sub>p\<^esub>Y = (a \<ominus>\<^bsub>Q\<^sub>p\<^esub> b) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (c \<ominus>\<^bsub>Q\<^sub>p\<^esub> a)" 
    by (simp add: assms(4) assms(5))
  then have "X \<oplus>\<^bsub>Q\<^sub>p\<^esub>Y = (c \<ominus>\<^bsub>Q\<^sub>p\<^esub> a) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (a \<ominus>\<^bsub>Q\<^sub>p\<^esub> b)" 
    by (metis (no_types, lifting) Qp_is_cring assms(1) assms(2) assms(3) 
        cring.cring_simprules(10) cring.cring_simprules(4))
  then have "X \<oplus>\<^bsub>Q\<^sub>p\<^esub>Y = ((c \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<ominus>\<^bsub>Q\<^sub>p\<^esub> a)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> a) \<ominus>\<^bsub>Q\<^sub>p\<^esub> b" 
    by (metis (no_types, lifting) Qp_is_domain a_minus_def assms(1) assms(2) 
        assms(3) cring.cring_simprules(3) cring.cring_simprules(4) cring.cring_simprules(7)
        domain.axioms(1))
  then have "X \<oplus>\<^bsub>Q\<^sub>p\<^esub>Y = (c \<oplus>\<^bsub>Q\<^sub>p\<^esub> ((\<ominus>\<^bsub>Q\<^sub>p\<^esub> a) \<oplus>\<^bsub>Q\<^sub>p\<^esub> a)) \<ominus>\<^bsub>Q\<^sub>p\<^esub> b" 
    by (metis (no_types, lifting) Qp_is_cring assms(1) assms(3) cring.cring_simprules(3) 
        cring.cring_simprules(7))
  then show ?thesis 
    by (simp add:  assms(1) assms(3) cring.cring_simprules(16) cring.cring_simprules(9) 
        domain.axioms(1))
qed

lemma(in cring) prod_diff:
  assumes "a0 \<in> carrier R"
  assumes "a1 \<in> carrier R"
  assumes "b0 \<in> carrier R"
  assumes "b1 \<in> carrier R"
  shows "(a0 \<otimes> b0) \<ominus> (a1 \<otimes> b1) = (b0 \<otimes> (a0 \<ominus> a1)) \<oplus>  (a1 \<otimes> (b0 \<ominus>b1))"
proof-
  have "(b0 \<otimes> (a0 \<ominus> a1)) \<oplus>  (a1 \<otimes> (b0 \<ominus>b1)) = ((b0 \<otimes> a0) \<ominus> (b0 \<otimes> a1))\<oplus>  (a1 \<otimes> (b0 \<ominus>b1))"
    using assms ring.ring_simprules[of R] 
    by (smt a_inv_def a_minus_def add.inv_closed add.inv_solve_left add.inv_solve_right 
        add.l_inv_ex add.m_comm add.r_inv_ex local.minus_unique local.minus_zero local.ring_axioms
        minus_closed minus_equality monoid.simps(2) r_minus r_zero ring.ring_simprules(23)
        ring.ring_simprules(4) zero_closed)
  then have "(b0 \<otimes> (a0 \<ominus> a1)) \<oplus>  (a1 \<otimes> (b0 \<ominus>b1)) = ((b0 \<otimes> a0) \<ominus> (b0 \<otimes> a1))\<oplus>  ((a1 \<otimes> b0) \<ominus> (a1 \<otimes> b1))"
    using assms ring.ring_simprules[of R] 
    by (smt a_inv_def a_minus_def add.inv_closed add.inv_solve_right add.l_cancel_one' add.l_inv_ex
        cring.cring_simprules(1) is_cring local.minus_unique local.minus_zero local.ring_axioms
        r_distr r_minus zero_closed)
  then have "(b0 \<otimes> (a0 \<ominus> a1)) \<oplus>  (a1 \<otimes> (b0 \<ominus>b1)) = (a0 \<otimes> b0) \<oplus> (\<ominus> (a1 \<otimes> b0)) \<oplus>  ((a1 \<otimes> b0) \<oplus>  \<ominus>(a1 \<otimes> b1))"
    unfolding  a_minus_def[of R]
    using m_comm cring.cring_simprules[of R]
     by (simp add: assms(1) assms(2) assms(3))
   then have "(b0 \<otimes> (a0 \<ominus> a1)) \<oplus>  (a1 \<otimes> (b0 \<ominus>b1)) = (a0 \<otimes> b0) \<oplus> ((\<ominus> (a1 \<otimes> b0)) \<oplus>  ((a1 \<otimes> b0)) \<oplus>  \<ominus>(a1 \<otimes> b1))"
     by (simp add: assms(1) assms(2) assms(3) assms(4) cring.cring_simprules(7) is_cring)
   then show ?thesis 
     by (simp add: add.m_assoc assms(2) assms(3) assms(4) cring.cring_simprules(19) is_cring minus_eq)
 qed

(**************************************************************************************************)
(**************************************************************************************************)
(*************************************  Sequences over Qp  ****************************************)
(**************************************************************************************************)
(**************************************************************************************************)

(*Predicate for a sequence of elements in Qp*)
definition is_closed_seq :: "padic_num_seq \<Rightarrow> bool" where
"is_closed_seq s = (\<forall> n. s n \<in> carrier Q\<^sub>p)"

lemma is_closed_simp[simp]:
  assumes "is_closed_seq s"
  shows "s n \<in> carrier Q\<^sub>p"
  using assms is_closed_seq_def by blast

lemma is_closedI[simp]:
  assumes "\<And> k. s k \<in> carrier Q\<^sub>p"
  shows "is_closed_seq s"
  by (simp add: assms is_closed_seq_def)

(*The integer-valued padic (valuative) distance*)
abbreviation ord_dist :: "padic_number \<Rightarrow> padic_number \<Rightarrow> int" where
"ord_dist a b \<equiv> ord (a \<ominus>\<^bsub>Q\<^sub>p\<^esub> b)"

(*Distance function is symmetric*)
lemma ord_dist_sym:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in>carrier Q\<^sub>p"
  shows "ord_dist a b = ord_dist b a"
proof(cases "a = b")
  case True
  then show ?thesis 
    by metis 
next
  case False
  have 0: "a \<ominus>\<^bsub>Q\<^sub>p\<^esub> b \<in> nonzero Q\<^sub>p" 
    using False assms(1) assms(2) Qp_not_eq_diff_nonzero by metis 
  have 1: "a \<ominus>\<^bsub>Q\<^sub>p\<^esub> b = \<ominus>\<^bsub>Q\<^sub>p\<^esub> (b \<ominus>\<^bsub>Q\<^sub>p\<^esub> a)" using assms(1) assms(2)  
    using Qp_minus_ominus by blast
  then show ?thesis 
    using False Qp_not_eq_diff_nonzero assms(1) assms(2) ord_minus by presburger
qed

(*Distanc function obeys the ultrametic inequality*)
lemma ord_dist_ultrametric:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "a \<noteq> b"
  assumes "a \<noteq>c"
  assumes "b \<noteq>c"
  shows "ord_dist b c \<ge> min (ord_dist a c) (ord_dist a b)" 
proof-
  let ?X = "b \<ominus>\<^bsub>Q\<^sub>p\<^esub> a"
  let ?Y = "a \<ominus>\<^bsub>Q\<^sub>p\<^esub> c"
  let ?Z = "b \<ominus>\<^bsub>Q\<^sub>p\<^esub> c"
  have 0: "?Z = ?X \<oplus>\<^bsub>Q\<^sub>p\<^esub> ?Y" 
    by (metis (no_types, lifting) Qp_diff_simp Qp_is_cring assms(1) assms(2) assms(3) 
        cring.cring_simprules(10) cring.cring_simprules(4))
  have 1: "?X \<in> nonzero Q\<^sub>p" 
    using Qp_not_eq_diff_nonzero assms(1) assms(2) assms(4) by metis 
  have 2: "?Y \<in> nonzero Q\<^sub>p" 
    using Qp_not_eq_diff_nonzero assms(1) assms(3) assms(5) by blast
  have 3: "?Z \<in> nonzero Q\<^sub>p" 
    using Qp_not_eq_diff_nonzero assms(2) assms(3) assms(6) by blast
  have 4: "ord ?Z \<ge> min (ord ?X) (ord ?Y)" using 0 1 2 3 
    using Q\<^sub>p_def ord_ultrametric padic_integers_axioms by auto
  then show ?thesis 
    by (metis assms(1) assms(2) min.commute ord_dist_sym)
qed

(*The integer-valued padic (valuative) distance*)
abbreviation val_dist :: "padic_number \<Rightarrow> padic_number \<Rightarrow> int option" where
"val_dist a b \<equiv> val (a \<ominus>\<^bsub>Q\<^sub>p\<^esub> b)"

(*Distance function is symmetric*)
lemma val_dist_sym:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in>carrier Q\<^sub>p"
  shows "val_dist a b = val_dist b a"
proof(cases "a = b")
  case True
  then show ?thesis 
    by metis 
next
  case False
  have 0: "a \<ominus>\<^bsub>Q\<^sub>p\<^esub> b \<in> nonzero Q\<^sub>p" 
    using False assms(1) assms(2) Qp_not_eq_diff_nonzero by metis 
  have 1: "a \<ominus>\<^bsub>Q\<^sub>p\<^esub> b = \<ominus>\<^bsub>Q\<^sub>p\<^esub> (b \<ominus>\<^bsub>Q\<^sub>p\<^esub> a)" using assms(1) assms(2)  
    using Qp_minus_ominus by blast
  then show ?thesis 
    by (metis Qp_is_cring assms(1) assms(2) cring.cring_simprules(4) val_minus)
qed

(*Distanc function obeys the ultrametic inequality*)
lemma val_dist_ultrametric:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  shows "val_dist b c \<succeq>\<^bsub>G\<^esub>  Min\<^bsub>G\<^esub> (val_dist a c) (val_dist a b)" 
proof-
  let ?X = "b \<ominus>\<^bsub>Q\<^sub>p\<^esub> a"
  let ?Y = "a \<ominus>\<^bsub>Q\<^sub>p\<^esub> c"
  let ?Z = "b \<ominus>\<^bsub>Q\<^sub>p\<^esub> c"
  have 0: "?Z = ?X \<oplus>\<^bsub>Q\<^sub>p\<^esub> ?Y" 
    by (metis (no_types, lifting) Qp_diff_simp Qp_is_cring assms(1) assms(2) assms(3) 
        cring.cring_simprules(10) cring.cring_simprules(4))
  have 4: " val ?Z \<succeq>\<^bsub>G\<^esub>  Min\<^bsub>G\<^esub>  (val ?X) (val ?Y)" 
    using 0 Q\<^sub>p_def ord_ultrametric padic_integers_axioms 
    by (metis Qp_is_cring assms(1) assms(2) assms(3) cring.cring_simprules(4) val_ultrametric)
  then show ?thesis 
    by (metis (no_types, lifting) "0" Qp_is_cring Qp_minus_ominus a_minus_def
        assms(1) assms(2) assms(3) cring.cring_simprules(10) cring.cring_simprules(4) val_ultrametric')
qed

(*Predicate for cauchy sequences*)
definition is_cauchy :: "padic_num_seq \<Rightarrow> bool" where
"is_cauchy s = ((is_closed_seq s) \<and>
           (\<forall> (n::int). \<exists> (N::nat). \<forall> m k::nat. (m>N \<and> k>N \<longrightarrow> (val_dist (s m) (s k)) \<succeq>\<^bsub>G\<^esub>  *n*)))"

lemma is_cauchyI: 
  assumes "is_closed_seq s"
  assumes "\<And>k. \<exists>N. \<forall>k0 k1. k0 > N \<and> k1 > N \<longrightarrow> val_dist (s k0) (s k1) \<succeq>\<^bsub>G\<^esub> *k*"
  shows "is_cauchy s"
  using assms unfolding is_cauchy_def 
  by blast

(*Relation for a sequence which converges to a point*)
definition converges_to :: "padic_num_seq \<Rightarrow> padic_number \<Rightarrow> bool" where
"converges_to s a = ((a \<in> carrier Q\<^sub>p \<and> is_closed_seq s) 
    \<and> (\<forall>(n::int). (\<exists>(k:: nat). (\<forall>( m::nat). (m > k \<longrightarrow> (val_dist (s m) a) \<succeq>\<^bsub>G\<^esub> *n*)))))"

(*Bounded sequences over Q\<^sub>p*)
definition is_bounded_pred:: "(int \<Rightarrow> bool) \<Rightarrow> bool" where
"is_bounded_pred P = (\<exists>n. \<forall> k >n. \<not> (P k))"

definition is_bounded_pred_below:: "(int \<Rightarrow> bool) \<Rightarrow> bool" where
"is_bounded_pred_below P = (\<exists>n. \<forall> k \<le> n. \<not> (P k))"

definition sup :: "(int \<Rightarrow> bool) \<Rightarrow> int option" where
"sup P = (if (is_bounded_pred P) then *(GREATEST x. P x)* else None)"

definition mirror:: "(int \<Rightarrow> bool) \<Rightarrow> (int \<Rightarrow> bool)" where
"mirror P = (\<lambda>x. P (-x))"

definition inf :: "(int \<Rightarrow> bool) \<Rightarrow> int option" where
"inf P = *-fromSome (sup (mirror P))*"

lemma mirror_involutive[simp]: 
"mirror (mirror P) = P"
  using mirror_def[of P] mirror_def[ of "mirror P"]
  by auto 

lemma supI[simp]:
  assumes "is_bounded_pred P"
  assumes  "s = sup P"
  assumes "\<exists>m. P m"
  shows "s \<noteq> \<infinity>\<^bsub>G\<^esub>"
        "P (fromSome s)"
        "\<And>n. P n \<Longrightarrow> *n* \<preceq>\<^bsub>G\<^esub>  s"
proof-
  have "s = *(GREATEST x. P x)*"
    by (simp add: assms(1) assms(2) local.sup_def)
  then show "s \<noteq> \<infinity>\<^bsub>G\<^esub>"
    by (simp add: G_def)
  obtain M where M_def: "P M"
    using assms by blast 
  obtain n where n_def: "n = (GREATEST x. P x)"
    by simp 
  obtain N where N_def: "\<forall> k >N. \<not> (P k)"
    using assms is_bounded_pred_def by blast
  have "\<exists>n. P n \<and> (\<forall>m. P m \<longrightarrow> m \<le>n)"
  proof(rule ccontr)
    assume C: "\<not> (\<exists>n. (P n \<and> (\<forall>m. P m \<longrightarrow> m \<le> n)))"
    then have C0: "\<forall>n. \<not> P n \<or> \<not>  (\<forall>m. P m \<longrightarrow> m \<le> n)"
      by blast 
    have C1: "\<forall> k::nat. \<exists> m. m> M + int k \<and> P m"
    proof
      fix k
      show "\<exists> m. m> M + int k \<and> P m"
      proof(induction k)
        case 0
        then show ?case 
          using C M_def eq_iff int_ops(1) by fastforce
      next
        case (Suc k)
        assume IH: "\<exists>m>M + int k. P m"
        show "\<exists>m>M + int (Suc k). P m"
        proof-
          obtain a where a_def: "a > M + int k \<and> P a"
            using IH by blast
          have "\<not>  (\<forall>m. P m \<longrightarrow> m \<le> a)"
            using C0 a_def by blast 
          then have "\<exists>m. P m \<and>  m > a"
            by auto
          then show ?thesis using a_def 
            by force
        qed  
      qed
    qed
    have M_leq_N: "M \<le> N"
      using M_def N_def  not_le 
      by blast
    obtain l where l_def: " l> M + int (nat (N - M)) \<and> P l"
      using C1 
      by blast
    then have "l > N \<and> P l"
      using M_leq_N 
      by simp
    then show False 
      using N_def 
      by blast
  qed
  then obtain n' where n'_def: "P n' \<and> (\<forall>m. P m \<longrightarrow> m \<le>n')"
    by blast 
  have "n' = n"
    using n_def n'_def Greatest_equality 
    by blast
  then show " P (fromSome s)"
    using \<open>s = Some (GREATEST x. P x)\<close> n'_def n_def by auto
  show "\<And>n. P n \<Longrightarrow> s \<succeq>\<^bsub>G\<^esub> Some n"
    using G_ord(2) \<open>n' = n\<close> \<open>s = Some (GREATEST x. P x)\<close> n'_def n_def by blast
qed

lemma bounded_mirror:
  assumes "is_bounded_pred P"
  assumes "\<exists>m. P m"
  shows "is_bounded_pred_below (mirror P)"
  using assms
  unfolding is_bounded_pred_def is_bounded_pred_below_def mirror_def
  by (metis lt_ex minus_equation_iff neg_less_iff_less order.strict_trans1)

lemma sup_inf: 
  assumes "is_bounded_pred P"
  assumes "\<exists>m. P m"
  shows "sup P = *-fromSome (inf (mirror P))*"
  using assms 
  unfolding is_bounded_def inf_def using mirror_involutive[of P]
  by (simp add: local.sup_def)

lemma bounded_mirror':
  assumes "is_bounded_pred_below P"
  assumes "\<exists>m. P m"
  shows "is_bounded_pred (mirror P)"
  by (metis (mono_tags, hide_lams) assms(1) dual_order.order_iff_strict 
      is_bounded_pred_def minus_le_iff padic_num_poly.is_bounded_pred_below_def 
      padic_num_poly.mirror_def padic_num_poly_axioms)

lemma infI:
  assumes "is_bounded_pred_below P"
  assumes  "s = inf P"
  assumes "\<exists>m. P m"
  shows "s \<noteq> \<infinity>\<^bsub>G\<^esub>"
        "P (fromSome s)"
        "\<And>n. P n \<Longrightarrow> *n* \<succeq>\<^bsub>G\<^esub>   s"
proof-
  have 0: "s = *- fromSome (sup (mirror P))*"
    by (simp add: assms(2) local.inf_def)
  have 00: "(sup (mirror P)) = *- (fromSome s)*"
    using 0 
    by (simp add: assms(1) assms(3) bounded_mirror' local.sup_def)
  have 1: "\<exists>m. (mirror P) m"
    using assms mirror_def 
    by (metis mirror_involutive)
  have 2: " (sup (mirror P)) \<noteq> \<infinity>\<^bsub>G\<^esub>"
    using "1" assms(1) assms(3) bounded_mirror' supI(1)
    by blast
  show 3: "s \<noteq> \<infinity>\<^bsub>G\<^esub>" 
    by (simp add: "0" G_def)
  show 4: "P (fromSome s)"
    using 0 1 supI(2)[of "mirror P" s] bounded_mirror'[of P] assms(1) assms(3) 
    by (metis (full_types)  fromSome.simps  mirror_def supI(2))
  have "\<And>n. (mirror P) (-n) \<Longrightarrow> *-n* \<preceq>\<^bsub>G\<^esub> (sup (mirror P))" 
    using 00 1 supI(3)[of "mirror P" ] "4" assms(1) bounded_mirror' 
    by blast
  then have "\<And>n. P n \<Longrightarrow> *-n* \<preceq>\<^bsub>G\<^esub> (sup (mirror P))" 
    by (metis mirror_def mirror_involutive)
  then show "\<And>n. P n \<Longrightarrow> Some n \<succeq>\<^bsub>G\<^esub> s"
    by (metis (full_types) "0" "00" G_ord(2) add.inverse_inverse 
        fromSome.simps local.sup_def neg_le_iff_le not_None_eq option.simps(3))
qed

definition is_bounded_seq :: "padic_num_seq \<Rightarrow> bool" where
"is_bounded_seq s \<equiv> (is_closed_seq s) \<and> (\<exists> (n ::int).( \<forall> (k:: nat). (val (s k) \<succeq>\<^bsub>G\<^esub> *n*)))"

definition seq_rad :: "padic_num_seq \<Rightarrow> int option" where
"seq_rad s = inf (\<lambda>n. (\<exists>k. val (s k) = *n*))"

lemma bounded_seq_bounded_pred: 
  assumes "is_bounded_seq s"
  shows   "is_bounded_pred_below (\<lambda>n. (\<exists>k. val (s k) = *n*))"
proof-
  obtain n where n_def: "( \<forall> (k:: nat). (val (s k) \<succeq>\<^bsub>G\<^esub> *n*))"
    using assms is_bounded_seq_def
    by blast
  then show ?thesis unfolding is_bounded_pred_below_def  
    by (metis G_ord(2) diff_ge_0_iff_ge le_add_same_cancel1 min.coboundedI2 min_def rel_simps(28))
qed

lemma seq_rad_const:
  assumes "s 0 \<in> carrier Q\<^sub>p"
  assumes "\<And>k.  s k = s 0"
  shows "is_bounded_seq s"
        "is_bounded_pred_below (\<lambda>n. (\<exists>k. val (s k) = *n*))"
proof-
  show "is_bounded_seq s"
    unfolding is_bounded_seq_def 
    by (metis G_eq G_ord(1) G_ord_trans assms(1) assms(2)
        is_closedI local.val_zero val_def )
  then  show "is_bounded_pred_below (\<lambda>n. (\<exists>k. val (s k) = *n*))"
    using bounded_seq_bounded_pred[of s]
    by blast 
qed

lemma seq_radI: 
  assumes "is_bounded_seq s"
  assumes "seq_rad s = n"
  shows "val (s k) \<succeq>\<^bsub>G\<^esub> n"
  using assms bounded_seq_bounded_pred[of s] 
  unfolding seq_rad_def 
  using infI[of "(\<lambda>n. \<exists>k. val (s k) = Some n)"]
  by (metis G_ord(1) val_def)

lemma bounded_finite_segment: 
  assumes "is_closed_seq s"
  shows "\<exists>k. \<forall>n \<le>N. (val (s n) \<succeq>\<^bsub>G\<^esub> *k*)"
proof(induction N)
  case 0
  then show ?case 
    by (metis G_eq G_ord(1) eq_iff less_eq_nat.simps(1) local.val_zero  val_def )
next
  case (Suc N)
  assume IH : "\<exists>k. \<forall>n\<le>N. val (s n) \<succeq>\<^bsub>G\<^esub> Some k"
  show "\<exists>k. \<forall>n\<le>Suc N. val (s n) \<succeq>\<^bsub>G\<^esub> Some k "
  proof-
    obtain k where k_def: "\<forall>n\<le>N. val (s n) \<succeq>\<^bsub>G\<^esub> Some k"
      using IH by blast 
    obtain k' where k'_def: " *k'* = Min\<^bsub>G\<^esub> (val (s (Suc N))) *k*"
      by (metis assms is_closed_simp val_nonzero val_ord)
    have " \<forall>n\<le>Suc N. val (s n) \<succeq>\<^bsub>G\<^esub> Some k' "
    proof
      fix n 
      show "n \<le> Suc N \<longrightarrow> val (s n) \<succeq>\<^bsub>G\<^esub> Some k'"
      proof
        assume A: "n \<le> Suc N"
        show "val (s n) \<succeq>\<^bsub>G\<^esub> Some k'"
          apply(cases "n \<le>N")
          using k'_def k_def apply (metis G_ord_trans)
          by (metis A  G_eq G_ord(1) G_ord(2)  k'_def le_Suc_eq le_cases val_def)
      qed
    qed
    then show "\<exists>k. \<forall>n\<le>Suc N. val (s n) \<succeq>\<^bsub>G\<^esub> Some k"
      by blast 
  qed
qed

lemma unbounded_imp_tail_unbounded:
  assumes "is_closed_seq s"
  assumes "\<not> (is_bounded_seq s)"
  shows "\<exists>k. k > N \<and> (val (s k) \<preceq>\<^bsub>G\<^esub> *M*)"
proof-
  obtain k where k_def: "\<forall>n \<le>N. (val (s n) \<succeq>\<^bsub>G\<^esub> *k*)"
    using assms(1) bounded_finite_segment by blast
  obtain K where K_def: "K < min M k"
    using lt_ex by blast
  then have N_def': "*K* \<prec>\<^bsub>G\<^esub> Min\<^bsub>G\<^esub> *M* *k*"
    by (smt G_ord(2))
  have " (\<forall> n. \<exists> k. \<not> ( val (s k) \<succeq>\<^bsub>G\<^esub> Some n))"
    using assms
    unfolding is_bounded_seq_def 
    by blast
  then have " (\<forall> n. \<exists> k.  ( val (s k) \<prec>\<^bsub>G\<^esub> Some n))"
    by (metis G_eq order_fact')
  then obtain k' where k'_def: "val (s k') \<prec>\<^bsub>G\<^esub> Some K"
    by blast 
  then have k'_bound: "k' > N"
    by (smt G_ord(2) G_ord_trans K_def k_def not_less)
  then show ?thesis
    using k'_def 
    by (meson G_ord(2) G_ord_trans K_def min_less_iff_conj order.strict_implies_order)
qed

(*Cauchy sequences are bounded*)
lemma cauchy_imp_bounded[simp]: 
  assumes "is_cauchy s"
  shows "is_bounded_seq s"
proof-
  obtain N where N_def: "\<forall>m k. N < m \<and> N < k \<longrightarrow> val_dist (s m) (s k) \<succeq>\<^bsub>G\<^esub> Some 0"
    using is_cauchy_def assms by blast 
  show "is_bounded_seq s" 
  proof(rule ccontr)
    assume A: "\<not> is_bounded_seq s"
    then obtain k where k_def: "k > N \<and> \<not> (val (s k) \<succeq>\<^bsub>G\<^esub> Some 0)"
      using assms unbounded_imp_tail_unbounded[of s] 
      unfolding is_cauchy_def
      by (metis (no_types, hide_lams) G_ord(1) G_ord_trans is_bounded_seq_def val_def)
    obtain n where n_def: "val (s k) = *n*"
      using k_def 
      by (metis G_ord(1) val_def)
    have n_ineq: "n < 0"
      using k_def n_def 
      by (simp add: n_def G_ord(2))
    obtain k' where k'_def: "k' > N \<and> \<not> (val (s k') \<succeq>\<^bsub>G\<^esub> Some n)"
      using assms A unbounded_imp_tail_unbounded[of s] 
      unfolding is_cauchy_def 
      by (metis (no_types, hide_lams) G_ord(1) G_ord_trans is_bounded_seq_def val_def)
    obtain n' where n'_def: "val (s k') = *n'*"
      by (metis G_ord(1) k'_def val_def)
    have "n' < n"
      by (metis G_eq G_ord(2) int.lless_eq k'_def less_linear n'_def)
    show False 
      by (smt G_ord_trans N_def assms is_cauchy_def is_closed_simp k'_def k_def 
          less_not_geq n_def val_ultrametric_noteq')
  qed
qed

(*Sequences with radius \<ge>0 are in \<O>\<^sub>p*)
lemma val_ring_seq:
  assumes "is_bounded_seq s"
  assumes "seq_rad s \<succeq>\<^bsub>G\<^esub> *0*"
  shows "s k \<in> \<O>\<^sub>p"
proof-
  have "val (s k) \<succeq>\<^bsub>G\<^esub> *0*"
    using assms seq_radI[of s]  G_ord_trans 
    by blast
  then show ?thesis 
    by (metis Zp_val_criterion assms(1) gzero_id is_bounded_seq_def is_closed_simp)
qed

definition to_Zp_seq :: "padic_num_seq \<Rightarrow> padic_int_seq" where
"to_Zp_seq s = (\<lambda>n. to_Zp (s n))"

definition to_Qp_seq :: "padic_int_seq \<Rightarrow> padic_num_seq" where
"to_Qp_seq s n = \<iota> (s n)"

lemma val_ring_map_to:
  assumes "is_closed_seq s"
  shows "padic_int_polynomial.is_closed_seq p (to_Zp_seq s)"
proof-
  have " (\<And>k. to_Zp_seq s k \<in> carrier (padic_int p))"
  proof-
    fix k
    show "to_Zp_seq s k \<in> carrier (padic_int p)"
      using Z\<^sub>p_def assms is_closed_simp to_Zp_closed to_Zp_seq_def by presburger
  qed
  then show ?thesis 
    using padic_int_polynomial.is_closedI[of p "(to_Zp_seq s)"] PP 
    by blast
qed

lemma to_Zp_to_Qp[simp]:
  assumes "padic_int_polynomial.is_closed_seq p  s"
  shows "to_Zp_seq (to_Qp_seq s) = s"
proof
  fix x
  have 0: "(s x) \<in> carrier Z\<^sub>p" 
    using assms PP padic_int_polynomial.is_closed_seq_def[of p s] Z\<^sub>p_def 
    by blast
  have "to_Zp_seq (to_Qp_seq s) x = to_Zp ((to_Qp_seq s) x )"
    by (simp add: to_Zp_seq_def)
  then have "to_Zp_seq (to_Qp_seq s) x = to_Zp (\<iota> (s x) )"
    by (simp add: to_Qp_seq_def)
  then show "to_Zp_seq (to_Qp_seq s) x = s x" 
    using 0 
    by (simp add: inc_to_Zp)
qed

lemma to_Qp_to_Zp[simp]:
  assumes "is_closed_seq  s"
  assumes "\<And>k. s k \<in> \<O>\<^sub>p"
  shows "to_Qp_seq (to_Zp_seq s) = s"
proof
  fix x
  have "to_Qp_seq (to_Zp_seq s) x = \<iota> (to_Zp (s x))"
    using assms 
    by (simp add: assms(1) assms(2) to_Qp_seq_def to_Zp_seq_def)
  then show "to_Qp_seq (to_Zp_seq s) x = s x"
    by (simp add: assms(2) to_Zp_inc)
qed

definition normalize_seq :: "padic_num_seq \<Rightarrow> padic_num_seq" where
"normalize_seq s n = (if (\<forall>k. s k \<in> \<O>\<^sub>p) then (s n) else  (s n) \<otimes>\<^bsub>Q\<^sub>p\<^esub>  (\<pp> e (- fromSome (seq_rad s))))"

lemma normalize_in_val_ring:
  assumes "is_bounded_seq s"
  shows "\<And>n. normalize_seq s n \<in> \<O>\<^sub>p"
proof-
  obtain n where n_def: "n = (seq_rad s) "
    by simp 
  have n_def':"n \<noteq>\<infinity>\<^bsub>G\<^esub>"
      by (metis (no_types, lifting) G_def extended_ordered_monoid.simps(1) local.inf_def 
          n_def option.simps(3) padic_num_poly.seq_rad_def padic_num_poly_axioms)
  show "\<And>n. normalize_seq s n \<in> \<O>\<^sub>p"
  proof-
    fix m
    show "normalize_seq s m \<in> \<O>\<^sub>p"
    proof(cases "(\<forall>k. s k \<in> \<O>\<^sub>p)")
      case True
      then show ?thesis 
        by (simp add: True normalize_seq_def)
    next
      case False
      then have F0: "normalize_seq s m =  (s m) \<otimes>\<^bsub>Q\<^sub>p\<^esub>  (\<pp> e (- fromSome (seq_rad s)))"
        by (meson normalize_seq_def)
      obtain k where k_def: "(seq_rad s) = *k*"
        by (metis local.inf_def n_def seq_rad_def)
      have F1: " (- fromSome (seq_rad s)) = -k"
        using k_def 
        by simp
      have F2: "normalize_seq s m =  (s m) \<otimes>\<^bsub>Q\<^sub>p\<^esub>  (\<pp> e (- k))"
        using F1 F0 
        by simp
      have F3: "val (normalize_seq s m) = val (s m) \<ominus>\<^bsub>G\<^esub> *k*"
        by (metis F2 assms g_uminus_minus is_bounded_seq_def is_closed_simp 
            ord_p_pow_int p_intpow_closed(1) p_intpow_closed(2) val_mult val_ord)
      have F4: "val (s m) \<succeq>\<^bsub>G\<^esub>  *k*"
        using assms k_def seq_radI by blast
      have F5: "val (normalize_seq s m) \<succeq>\<^bsub>G\<^esub> *0*"
      proof(cases "val (s m) = \<infinity>\<^bsub>G\<^esub>")
        case True
        then show ?thesis 
          by (simp add: True F3 G_ord(1))
      next
        case False
        obtain M where M_def: "*M* = val (s m)"
          by (metis False val_def)
        have "val (normalize_seq s m) = *M - k*"
          by (metis F3 M_def gminus_minus)
        show ?thesis using M_def F3 F4 
          by (metis (full_types) G_ord(2) \<open>val (normalize_seq s m) = Some (M - k)\<close>
              diff_ge_0_iff_ge)
      qed
      have F6: "(normalize_seq s m) \<in> carrier Q\<^sub>p"
      proof-
        have "(s m) \<in> carrier Q\<^sub>p"
          using assms is_bounded_seq_def is_closed_seq_def by blast
        then show ?thesis using F2 
          by (metis Qp_is_cring cring.cring_simprules(5) p_intpow_closed(1))
      qed
      show ?thesis using F5 F6
        using Zp_val_criterion gzero_id 
        by presburger
    qed
  qed
qed

lemma normalize_is_closed:
  assumes "is_bounded_seq s"
  shows "is_closed_seq (normalize_seq s)"
  using normalize_in_val_ring  assms is_bounded_seq_def 
  by (metis Q\<^sub>p_def Qp_is_cring Z\<^sub>p_def cring.cring_simprules(5) p_intpow_closed(1) 
      padic_num_poly.is_closed_seq_def padic_num_poly.normalize_seq_def padic_num_poly_axioms)

definition scalar_mult :: "padic_number \<Rightarrow> padic_num_seq \<Rightarrow> padic_num_seq" where 
"scalar_mult c s = (\<lambda>n. c \<otimes>\<^bsub>Q\<^sub>p\<^esub> (s n))"

lemma scalar_mult_is_closed:
  assumes "is_closed_seq s"
  assumes "c \<in> carrier Q\<^sub>p"
  shows "is_closed_seq (scalar_mult c s)"
  using assms 
  unfolding is_closed_seq_def scalar_mult_def 
  by (meson Qp_is_cring cring.cring_simprules(5))

lemma scalar_mult_is_cauchy:
  assumes "is_cauchy s"
  assumes "c \<in> carrier Q\<^sub>p"
  shows "is_cauchy (scalar_mult c s)"
proof(rule is_cauchyI)
  show "is_closed_seq (scalar_mult c s)"
    using assms(1) assms(2) is_cauchy_def scalar_mult_is_closed by blast
  show "\<And>k. \<exists>N. \<forall>k0 k1. N < k0 \<and> N < k1 \<longrightarrow> val_dist (scalar_mult c s k0) (scalar_mult c s k1) \<succeq>\<^bsub>G\<^esub> Some k"
  proof-
    fix k
    show " \<exists>N. \<forall>k0 k1. N < k0 \<and> N < k1 \<longrightarrow> val_dist (scalar_mult c s k0) (scalar_mult c s k1) \<succeq>\<^bsub>G\<^esub> Some k"
    proof(cases "c = \<zero>\<^bsub>Q\<^sub>p\<^esub>")
      case True
      have " \<forall>k0 k1. 0 < k0 \<and> 0 < k1 \<longrightarrow> val_dist (scalar_mult c s k0) (scalar_mult c s k1) \<succeq>\<^bsub>G\<^esub> Some k"
        unfolding scalar_mult_def 
        using assms  
        by (metis G_ord(1) Qp_is_cring True a_minus_def cring.cring_simprules(16) 
            cring.cring_simprules(22) cring.cring_simprules(26) is_cauchy_def 
            is_closed_simp local.val_zero)
      then show ?thesis 
        by blast 
    next
      case False
      obtain N1 where N1_def: "*N1* = val c"
        using False 
        by (simp add: val_def)
      obtain N0 where 
        N0_def: "\<forall>k0 k1. N0 < k0 \<and> N0 < k1 \<longrightarrow> val_dist (s k0) (s k1) \<succeq>\<^bsub>G\<^esub> *k - N1*"
        using assms is_cauchy_def by blast
      have "\<And> k0 k1. N0 < k0 \<and> N0 < k1 \<longrightarrow> val_dist (scalar_mult c s k0) (scalar_mult c s k1) \<succeq>\<^bsub>G\<^esub> Some k"
      proof
        fix k0 k1
        assume A: "N0 < k0 \<and> N0 < k1"
        have 0: "val_dist (scalar_mult c s k0) (scalar_mult c s k1) = *N1* \<oplus>\<^bsub>G\<^esub> val_dist (s k0) (s k1)"
        proof-
          have "val_dist (scalar_mult c s k0) (scalar_mult c s k1) = 
                val (c \<otimes>\<^bsub>Q\<^sub>p\<^esub> ((s k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (s k1)))"
            using assms 
            unfolding is_cauchy_def is_closed_seq_def  
            by (smt Qp_is_cring a_minus_def cring.cring_simprules(17) cring.cring_simprules(27)
                cring.cring_simprules(4) cring.cring_simprules(5) cring.cring_simprules(8)
                cring.prod_diff scalar_mult_def)
          then show ?thesis 
            by (metis N1_def Qp_is_cring assms(1) assms(2) cring.cring_simprules(4)
                is_cauchy_def is_closed_simp val_mult)
        qed
        have "val_dist (s k0) (s k1) \<succeq>\<^bsub>G\<^esub> *k - N1*"
          using A N0_def 
          by blast
        then have 1: " val_dist (scalar_mult c s k0) (scalar_mult c s k1) \<succeq>\<^bsub>G\<^esub> *N1* \<oplus>\<^bsub>G\<^esub> *k - N1*"
          using 0 gord_plus' by presburger
        have 2: "*N1* \<oplus>\<^bsub>G\<^esub> *k - N1* = *k*"
          by simp
        show "val_dist (scalar_mult c s k0) (scalar_mult c s k1) \<succeq>\<^bsub>G\<^esub> Some k"
          using 1 2 G_eq G_ord_trans 
          by blast
      qed
      then have "\<forall>k0 k1. N0 < k0 \<and> N0 < k1 \<longrightarrow> val_dist (scalar_mult c s k0) (scalar_mult c s k1) \<succeq>\<^bsub>G\<^esub> Some k"
        by blast
      then show ?thesis 
        by blast 
    qed
  qed
qed

lemma scalar_mult_scalar_mult:
  assumes "is_closed_seq s"
  assumes "c0 \<in> carrier Q\<^sub>p"
  assumes "c1 \<in> carrier Q\<^sub>p"
  shows "scalar_mult c1 (scalar_mult c0 s) = scalar_mult (c1 \<otimes>\<^bsub>Q\<^sub>p\<^esub> c0) s"
  using assms unfolding scalar_mult_def
  by (metis Qp_is_cring cring.cring_simprules(11) is_closed_seq_def)

lemma scalar_mult_one[simp]:
  assumes "is_closed_seq s"
  shows "scalar_mult \<one>\<^bsub>Q\<^sub>p\<^esub> s = s"
  using assms ext[of "scalar_mult \<one>\<^bsub>Q\<^sub>p\<^esub> s " s]  unfolding scalar_mult_def
  by (meson Qp_is_cring cring.cring_simprules(12) is_closed_simp)

lemma scalar_mult_zero[simp]:
  assumes "is_closed_seq s"
  shows "scalar_mult \<zero>\<^bsub>Q\<^sub>p\<^esub> s = (\<lambda>n. \<zero>\<^bsub>Q\<^sub>p\<^esub>)"
  using assms ext[of "scalar_mult \<zero>\<^bsub>Q\<^sub>p\<^esub> s " s]  unfolding scalar_mult_def
  by (meson Qp_is_cring cring.cring_simprules(26) is_closed_simp)

lemma normalize_seq_def':
  assumes "is_closed_seq s"
  shows "normalize_seq s = (if (\<forall>k. (s k) \<in> \<O>\<^sub>p) then s else  (scalar_mult (\<pp> e (- fromSome (seq_rad s))) s))"
proof(cases "(\<forall>k. (s k) \<in> \<O>\<^sub>p)")
  case True
  then show ?thesis 
    by (simp add: True ext normalize_seq_def)
next
  case False
  have "\<And>n. normalize_seq s n = (scalar_mult (\<pp> e (- fromSome (seq_rad s))) s) n"
  proof-
    fix n
    have "normalize_seq s n =  s n \<otimes>\<^bsub>Q\<^sub>p\<^esub> (\<pp> e - fromSome (seq_rad s))"
      by (meson False normalize_seq_def)
    then show "normalize_seq s n = (scalar_mult (\<pp> e (- fromSome (seq_rad s))) s) n"
      unfolding scalar_mult_def  
      by (metis Qp_is_cring assms cring.cring_simprules(14) is_closed_simp p_intpow_closed(1))
  qed
  then show ?thesis 
    using False ext[of "normalize_seq s" "(scalar_mult (\<pp> e (- fromSome (seq_rad s))) s)" ] 
    by presburger
qed

lemma normalize_seq_def'':
  assumes "is_closed_seq s"
  shows "s = (if (\<forall>k. (s k) \<in> \<O>\<^sub>p) then normalize_seq s else  
                (scalar_mult (\<pp> e ( fromSome (seq_rad s))) (normalize_seq s)))"
proof(cases "(\<forall>k. (s k) \<in> \<O>\<^sub>p)")
  case True
  then show ?thesis 
    by (simp add: True assms normalize_seq_def')
next
  case False
  have  0:    " (\<pp> e - fromSome (seq_rad s)) \<in> carrier Q\<^sub>p" 
    using p_intpow_closed(1) by blast
  have 1: " (\<pp> e fromSome (seq_rad s)) \<in> carrier Q\<^sub>p"
      by simp
  have 2: "normalize_seq s = (scalar_mult (\<pp> e (- fromSome (seq_rad s))) s)"
    by (meson False assms normalize_seq_def')
  then have 3: "(scalar_mult (\<pp> e ( fromSome (seq_rad s))) (normalize_seq s)) = 
          (scalar_mult ((\<pp> e ( fromSome (seq_rad s))) \<otimes>\<^bsub>Q\<^sub>p\<^esub> (\<pp> e (- fromSome (seq_rad s)))) s)"
    using 0 1 assms scalar_mult_scalar_mult[of s "\<pp> e ( -fromSome (seq_rad s))" "\<pp> e (fromSome (seq_rad s))"] 
    by metis  
  then have "(scalar_mult (\<pp> e ( fromSome (seq_rad s))) (normalize_seq s)) = s"
    using 3 scalar_mult_one[of s] 
    by (simp add: assms p_intpow_inv)
  then show ?thesis 
    by (metis assms normalize_seq_def')
qed

lemma cauchy_imp_normalize_cauchy:
  assumes "is_closed_seq s"
  shows "is_cauchy (normalize_seq s) \<longleftrightarrow> is_cauchy s"
proof
  show "is_cauchy (normalize_seq s) \<Longrightarrow> is_cauchy s"
  proof-
    assume "is_cauchy (normalize_seq s)"
    then show "is_cauchy s"
      using normalize_seq_def''[of s] assms
            scalar_mult_is_cauchy[of "(normalize_seq s)" " (\<pp> e fromSome (seq_rad s))"]
      by (metis p_intpow_closed(1))
  qed
  show "is_cauchy s \<Longrightarrow> is_cauchy (normalize_seq s)"
  proof-
    assume "is_cauchy s"
    then show "is_cauchy (normalize_seq s)"
      using assms normalize_seq_def' p_intpow_closed(1) scalar_mult_is_cauchy 
      by presburger
  qed
qed

(*Sums and products of sequences*)

definition seq_sum:: "padic_num_seq \<Rightarrow> padic_num_seq \<Rightarrow> padic_num_seq" where
"seq_sum s1 s2 = (\<lambda> k. (s1 k) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (s2 k))"

definition seq_prod:: "padic_num_seq \<Rightarrow> padic_num_seq \<Rightarrow> padic_num_seq" where
"seq_prod s1 s2 = (\<lambda> k. (s1 k) \<otimes>\<^bsub>Q\<^sub>p\<^esub>  (s2 k))"

(*Sums and products of closed sequences are closed*)
lemma sum_of_closed_seq_is_closed_seq:
  assumes "is_closed_seq s"
  assumes "is_closed_seq t"
  shows "is_closed_seq (seq_sum s t)"
proof(rule is_closedI)
  fix k
  have "seq_sum s t k = (s k) \<oplus>\<^bsub>Q\<^sub>p\<^esub>(t k)" using seq_sum_def by auto 
  then show "seq_sum s t k \<in> carrier Q\<^sub>p" 
    using assms is_closed_simp[of "seq_sum s t"] 
    by (metis Qp_is_cring cring.cring_simprules(1) is_closed_simp)
qed

lemma prod_of_closed_seq_is_closed_seq:
  assumes "is_closed_seq s"
  assumes "is_closed_seq t"
  shows "is_closed_seq (seq_prod s t)"
proof(rule is_closedI)
  fix k
  have "seq_prod s t k = (s k) \<otimes>\<^bsub>Q\<^sub>p\<^esub>  (t k)" using seq_prod_def by auto 
  then show "seq_prod s t k \<in> carrier Q\<^sub>p" 
    using assms is_closed_simp[of "seq_prod s t"]
    by (metis Qp_is_cring cring.cring_simprules(5) is_closed_simp)
qed

(*Sums and products of cauchy sequences are cauchy*)
lemma sum_of_cauchy_is_cauchy:
  assumes "is_cauchy s"
  assumes "is_cauchy t"
  shows "is_cauchy (seq_sum s t)"
proof(rule is_cauchyI)
  show "is_closed_seq (seq_sum s t)" 
    using assms is_cauchy_def sum_of_closed_seq_is_closed_seq by metis   
  show "\<And>k. \<exists>N. \<forall>k0 k1. N < k0 \<and> N < k1 \<longrightarrow> val_dist (seq_sum s t k0) (seq_sum s t k1) \<succeq>\<^bsub>G\<^esub> Some k"
  proof-
    fix k
    show "\<exists>N. \<forall>k0 k1. N < k0 \<and> N < k1 \<longrightarrow> val_dist (seq_sum s t k0) (seq_sum s t k1) \<succeq>\<^bsub>G\<^esub> Some k"
      unfolding seq_sum_def
    proof-
      obtain N0 where N0_def: "\<forall>k0 k1. N0 < k0 \<and> N0 < k1 \<longrightarrow> val_dist (t k0) (t k1) \<succeq>\<^bsub>G\<^esub> Some k"
        using assms  is_cauchy_def
        by blast
      obtain N1 where N1_def: "\<forall>k0 k1. N1 < k0 \<and> N1 < k1 \<longrightarrow> val_dist (s k0) (s k1) \<succeq>\<^bsub>G\<^esub> Some k"
        using assms  is_cauchy_def
        by blast
      obtain N where N_def: "N = max N0 N1"
        by simp
      have "\<forall>k0 k1. N < k0 \<and> N < k1 \<longrightarrow> val_dist (s k0 \<oplus>\<^bsub>Q\<^sub>p\<^esub> t k0) (s k1 \<oplus>\<^bsub>Q\<^sub>p\<^esub> t k1) \<succeq>\<^bsub>G\<^esub> Some k"
      proof-
        have "\<And>k0 k1.  N < k0 \<and> N < k1 \<longrightarrow> val_dist (s k0 \<oplus>\<^bsub>Q\<^sub>p\<^esub> t k0) (s k1 \<oplus>\<^bsub>Q\<^sub>p\<^esub> t k1) \<succeq>\<^bsub>G\<^esub> Some k "
        proof
          fix k0 k1
          assume A: " N < k0 \<and> N < k1"
          show "val_dist (s k0 \<oplus>\<^bsub>Q\<^sub>p\<^esub> t k0) (s k1 \<oplus>\<^bsub>Q\<^sub>p\<^esub> t k1) \<succeq>\<^bsub>G\<^esub> Some k "
          proof-
            have C0: "s k0 \<in> carrier Q\<^sub>p"
              using assms(1) is_closed_simp padic_num_poly.is_cauchy_def padic_num_poly_axioms
              by blast
            have C1: "s k1 \<in> carrier Q\<^sub>p"
              using assms(1) is_cauchy_def is_closed_seq_def  
              by blast
            have C2: "t k0 \<in> carrier Q\<^sub>p"
              using assms(2) is_cauchy_def is_closed_seq_def 
              by blast
            have C3: "t k1 \<in> carrier Q\<^sub>p"
              using assms(2) is_cauchy_def is_closed_seq_def 
              by blast
            have C4: "(s k0) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (t k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> ((s k1) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (t k1)) = 
                                    ((s k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (s k1)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> ((t k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (t k1))"
              using C1 C2 C3 C0 
              by (smt Qp_is_cring a_minus_def cring.cring_simprules(1) cring.cring_simprules(20)
                  cring.cring_simprules(23) cring.cring_simprules(3) cring.cring_simprules(7))
            have "val_dist (s k0 \<oplus>\<^bsub>Q\<^sub>p\<^esub> t k0) (s k1 \<oplus>\<^bsub>Q\<^sub>p\<^esub> t k1) = 
                        val ((s k0) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (t k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> ((s k1) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (t k1)))"
              by blast
            then have "val_dist (s k0 \<oplus>\<^bsub>Q\<^sub>p\<^esub> t k0) (s k1 \<oplus>\<^bsub>Q\<^sub>p\<^esub> t k1) = 
                        val (((s k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (s k1)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> ((t k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (t k1)))"
              using C4 by presburger
            then have C5: "val_dist (s k0 \<oplus>\<^bsub>Q\<^sub>p\<^esub> t k0) (s k1 \<oplus>\<^bsub>Q\<^sub>p\<^esub> t k1) \<succeq>\<^bsub>G\<^esub> 
                      Min\<^bsub>G\<^esub> (val ((s k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (s k1))) (val ((t k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (t k1)))"
              by (metis C0 C1 C2 C3 Qp_is_cring cring.cring_simprules(4) val_ultrametric)
            have C6: "(val_dist (s k0) (s k1)) \<succeq>\<^bsub>G\<^esub> *k*"
              by (metis A N1_def N_def max.strict_boundedE)
            have C7: "(val_dist (t k0) (t k1)) \<succeq>\<^bsub>G\<^esub> *k*"
              by (metis A N0_def N_def max.strict_boundedE)
            then show ?thesis using C5 C6 C7 A N_def 
              by (smt  G_ord_trans )
          qed
        qed
        then show ?thesis 
          by blast 
      qed
      then show "\<exists>N. \<forall>k0 k1. N < k0 \<and> N < k1 
                \<longrightarrow> val_dist (s k0 \<oplus>\<^bsub>Q\<^sub>p\<^esub> t k0) (s k1 \<oplus>\<^bsub>Q\<^sub>p\<^esub> t k1) \<succeq>\<^bsub>G\<^esub> Some k"
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
    using assms is_cauchy_def prod_of_closed_seq_is_closed_seq by metis   
  show "\<And>k. \<exists>N. \<forall>k0 k1. N < k0 \<and> N < k1 \<longrightarrow> val_dist (seq_prod s t k0) (seq_prod s t k1) \<succeq>\<^bsub>G\<^esub> Some k"
  proof-
    fix k
    obtain R0 where R0_def: "R0 = seq_rad s"
      by simp
    obtain R1 where R1_def: "R1 = seq_rad t"
      by simp
    obtain n0 where n0_def: "*n0* = R0"
      by (metis R0_def local.inf_def padic_num_poly.seq_rad_def padic_num_poly_axioms)
    obtain n1 where n1_def: "*n1* = R1"
      by (metis R1_def local.inf_def padic_num_poly.seq_rad_def padic_num_poly_axioms)
    obtain N0 where N0_def: "\<forall>k0 k1. N0 < k0 \<and> N0 < k1 \<longrightarrow> val_dist (s k0) (s k1) \<succeq>\<^bsub>G\<^esub> Some (k - n1)"
      using assms  is_cauchy_def
      by blast
    obtain N1 where N1_def: "\<forall>k0 k1. N1 < k0 \<and> N1 < k1 \<longrightarrow> val_dist (t k0) (t k1) \<succeq>\<^bsub>G\<^esub> Some (k - n0)"
      using assms  is_cauchy_def
      by blast
    obtain N where N_def: "N = max N0 N1"
      by simp 
    have "\<And> k0 k1. N < k0 \<and> N < k1 \<longrightarrow> val_dist (seq_prod s t k0) (seq_prod s t k1) \<succeq>\<^bsub>G\<^esub> Some k"
    proof-
      fix k0 k1
      show "N < k0 \<and> N < k1 \<longrightarrow> val_dist (seq_prod s t k0) (seq_prod s t k1) \<succeq>\<^bsub>G\<^esub> Some k"
      proof
        assume A: "N < k0 \<and> N < k1"
        show "val_dist (seq_prod s t k0) (seq_prod s t k1) \<succeq>\<^bsub>G\<^esub> Some k"
          unfolding seq_prod_def
        proof-
          have C0: "s k0 \<in> carrier Q\<^sub>p"
            using assms(1) is_closed_simp padic_num_poly.is_cauchy_def padic_num_poly_axioms
            by blast
          have C1: "s k1 \<in> carrier Q\<^sub>p"
            using assms(1) is_cauchy_def is_closed_seq_def  
            by blast
          have C2: "t k0 \<in> carrier Q\<^sub>p"
            using assms(2) is_cauchy_def is_closed_seq_def 
            by blast
          have C3: "t k1 \<in> carrier Q\<^sub>p"
            using assms(2) is_cauchy_def is_closed_seq_def 
            by blast
          have C4: "(s k0 \<otimes>\<^bsub>Q\<^sub>p\<^esub> t k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (s k1 \<otimes>\<^bsub>Q\<^sub>p\<^esub> t k1) = 
                   (t k0)\<otimes>\<^bsub>Q\<^sub>p\<^esub>((s k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (s k1)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (s k1)\<otimes>\<^bsub>Q\<^sub>p\<^esub>((t k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (t k1))"
            using  cring.prod_diff[of Q\<^sub>p "s k0" "s k1" "t k0" "t k1"] 
            by (simp add: C0 C1 C2 C3)
          then have "val_dist (s k0 \<otimes>\<^bsub>Q\<^sub>p\<^esub> t k0) (s k1 \<otimes>\<^bsub>Q\<^sub>p\<^esub> t k1) \<succeq>\<^bsub>G\<^esub>  Min\<^bsub>G\<^esub>  (val ((t k0)\<otimes>\<^bsub>Q\<^sub>p\<^esub>((s k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (s k1))))
                                                                              (val ((s k1)\<otimes>\<^bsub>Q\<^sub>p\<^esub>((t k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (t k1))))"
            by (metis C0 C1 C2 C3 Qp_is_cring cring.cring_simprules(4) cring.cring_simprules(5) val_ultrametric)
          then have C5: "val_dist (s k0 \<otimes>\<^bsub>Q\<^sub>p\<^esub> t k0) (s k1 \<otimes>\<^bsub>Q\<^sub>p\<^esub> t k1) \<succeq>\<^bsub>G\<^esub>  Min\<^bsub>G\<^esub>  ((val (t k0)) \<oplus>\<^bsub>G\<^esub> (val ((s k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (s k1))))
                                                                              ((val (s k1)) \<oplus>\<^bsub>G\<^esub> (val ((t k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (t k1))))"
            by (metis (no_types, lifting) C0 C1 C2 C3 Qp_is_cring cring.cring_simprules(4) val_mult)
          have C6: "val_dist (s k0) (s k1) \<succeq>\<^bsub>G\<^esub> Some (k - n1)"
            using A N0_def n1_def 
            by (metis N_def max.strict_boundedE)
          have C7: "val_dist (t k0) (t k1) \<succeq>\<^bsub>G\<^esub> Some (k - n0)"
            using A N1_def n0_def 
            by (metis N_def max.strict_boundedE)
          have C8: "(val (t k0)) \<succeq>\<^bsub>G\<^esub> *n1*"
            using R1_def assms(2) local.cauchy_imp_bounded n1_def seq_radI 
            by presburger
          have C9: "(val (s k1)) \<succeq>\<^bsub>G\<^esub> *n0*"
            using R0_def assms(1) local.cauchy_imp_bounded n0_def seq_radI
            by presburger 
          have C10: " ((val (t k0)) \<oplus>\<^bsub>G\<^esub> (val ((s k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (s k1)))) \<succeq>\<^bsub>G\<^esub> *n1* \<oplus>\<^bsub>G\<^esub> *k - n1*"
            using C8 C6 
             by (metis G_ord_trans gord_plus gplus_comm)
          have C11: " ((val (s k1)) \<oplus>\<^bsub>G\<^esub> (val ((t k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (t k1)))) \<succeq>\<^bsub>G\<^esub> *n0* \<oplus>\<^bsub>G\<^esub> *k - n0*"
             using C9 C5         
             by (metis C7 G_ord_trans gord_plus gplus_comm)
           have C12: " ((val (t k0)) \<oplus>\<^bsub>G\<^esub> (val ((s k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (s k1)))) \<succeq>\<^bsub>G\<^esub> *k*"
           proof-
             have " *n1* \<oplus>\<^bsub>G\<^esub> *k - n1* = *k*"
               by auto
             then show ?thesis 
               using C10 
             by presburger
           qed
           have C13: " ((val (s k1)) \<oplus>\<^bsub>G\<^esub> (val ((t k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (t k1)))) \<succeq>\<^bsub>G\<^esub> *k*"
           proof-
             have " *n0* \<oplus>\<^bsub>G\<^esub> *k - n0* = *k*"
               by auto
             then show ?thesis 
               using C11 
               by presburger
           qed
           show "val_dist (s k0 \<otimes>\<^bsub>Q\<^sub>p\<^esub> t k0) (s k1 \<otimes>\<^bsub>Q\<^sub>p\<^esub> t k1) \<succeq>\<^bsub>G\<^esub> Some k"
             using C5 C12 C13 
             by (smt G_ord_trans)
         qed
       qed
    qed
    then have "\<forall>k0 k1. N < k0 \<and> N < k1 \<longrightarrow> val_dist (seq_prod s t k0) (seq_prod s t k1) \<succeq>\<^bsub>G\<^esub> Some k"
      by blast
    then show "\<exists>N. \<forall>k0 k1. N < k0 \<and> N < k1 \<longrightarrow> val_dist (seq_prod s t k0) (seq_prod s t k1) \<succeq>\<^bsub>G\<^esub> Some k"
      by blast 
  qed
qed


(*Predicate for constant sequences*)
definition is_constant_seq :: "padic_num_seq \<Rightarrow> bool" where
"is_constant_seq s = (\<exists>x \<in> carrier Q\<^sub>p. \<forall>k. s k = x)"

(*Constant sequences are cauchy*)
lemma constant_is_cauchy:
  assumes "is_constant_seq s"
  shows "is_cauchy s"
  apply(rule is_cauchyI)
  using assms 
  unfolding is_constant_seq_def
  apply (metis is_closedI)
    by (metis G_ord(1) Qp_is_cring a_minus_def assms cring.cring_simprules(17) 
      is_constant_seq_def local.val_zero)

(*Convergent sequences are cauchy*)

lemma convergent_imp_cauchy: 
  assumes "is_closed_seq s"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "converges_to s a"
  shows "is_cauchy s"
proof(rule is_cauchyI)
  show "is_closed_seq s" 
    by (simp add: assms(1))
  show "\<And>k. \<exists>N. \<forall>k0 k1. N < k0 \<and> N < k1 \<longrightarrow> val_dist (s k0) (s k1) \<succeq>\<^bsub>G\<^esub> Some k"
  proof-
    fix k
    show "\<exists>N. \<forall>k0 k1. N < k0 \<and> N < k1 \<longrightarrow> val_dist (s k0) (s k1) \<succeq>\<^bsub>G\<^esub> Some k"
    proof-
      obtain N where N_def: "\<And>n. n > N \<longrightarrow> val_dist (s n) a \<succeq>\<^bsub>G\<^esub> *k*"
        using assms 
        unfolding converges_to_def 
        by blast
      have "\<And> k0 k1. N < k0 \<and> N < k1 \<longrightarrow> val_dist (s k0) (s k1) \<succeq>\<^bsub>G\<^esub> Some k"
      proof
        fix k0 k1
        assume A: "N < k0 \<and> N < k1"
        have A0: "val_dist (s k0) a \<succeq>\<^bsub>G\<^esub> *k*"
          using A N_def 
          by blast
        have A1: "val_dist (s k1) a \<succeq>\<^bsub>G\<^esub> *k*"
          using A N_def 
          by blast
        show "val_dist (s k0) (s k1) \<succeq>\<^bsub>G\<^esub> Some k"
          using A0 A1 Qp_isosceles assms(1) assms(2) is_closed_simp
          by blast
      qed
      then show ?thesis by blast 
    qed
  qed
qed

(*A sequence converges to no more than one element*)
lemma unique_limit:
  assumes "is_closed_seq s"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "converges_to s a"
  assumes "converges_to s b"
  shows "a = b"
proof-
  have A: "\<And>k. val_dist a b \<succeq>\<^bsub>G\<^esub> *k*"
  proof-
    fix k
    obtain N0 where N0_def: "\<And>n. n > N0 \<longrightarrow> val_dist (s n) a \<succeq>\<^bsub>G\<^esub> *k*"
      using assms 
      unfolding converges_to_def 
      by blast
    obtain N1 where N1_def: "\<And>n. n > N1 \<longrightarrow> val_dist (s n) b \<succeq>\<^bsub>G\<^esub> *k*"
      using assms 
      unfolding converges_to_def 
      by blast
    obtain n where n_def: "n = max (Suc N1) (Suc N0)"
      by simp
    have 0:"val_dist (s n) a \<succeq>\<^bsub>G\<^esub> *k*"
      by (metis N0_def lessI max.strict_boundedE n_def not_less_eq)
    have 1:"val_dist (s n) b \<succeq>\<^bsub>G\<^esub> *k*"
      by (metis N1_def lessI max.strict_boundedE n_def not_less_eq)
    show " val_dist a b \<succeq>\<^bsub>G\<^esub> *k*"
      using 0 1 assms 
      by (metis Qp_isosceles is_closed_simp val_dist_sym)
  qed
  have "val_dist a b = \<infinity>\<^bsub>G\<^esub>"
  proof(rule ccontr)
    assume C: "val_dist a b \<noteq> \<infinity>\<^bsub>G\<^esub>"
    then obtain k where k_def: "val_dist a b = *k*"
      by (metis val_def)
    have "val_dist a b \<succeq>\<^bsub>G\<^esub> *k + 1*"
      using A 
      by blast
    then show False 
      using k_def  
      by (simp add: \<open>val_dist a b = Some k\<close> G_ord(2)) 
  qed
  then show ?thesis 
    by (metis G_def Qp_not_eq_diff_nonzero assms(2) assms(3)
        extended_ordered_monoid.simps(1) option.simps(3) val_ord)
qed

definition limit :: "padic_num_seq \<Rightarrow> padic_number" where
"limit s = (THE a. converges_to s a)"

lemma limit_def': 
  assumes "is_closed_seq s"
  assumes "converges_to s a"
  shows "a = limit s"
  using assms unique_limit unfolding limit_def
  by (metis converges_to_def the_equality)

lemma converges_toI:
  assumes "is_closed_seq s"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "\<And>n. \<exists>N. \<forall>k > N. val_dist (s k) a \<succeq>\<^bsub>G\<^esub> *n*"
  shows "converges_to s a"
  using assms(1) assms(2) assms(3) converges_to_def by blast

(**************************************************************************************************)
(**************************************************************************************************)
(*******************************   CONTINUOUS FUNCTIONS    ****************************************)
(**************************************************************************************************)
(**************************************************************************************************)

definition push_forward :: "padic_num_fun \<Rightarrow> padic_num_seq \<Rightarrow> padic_num_seq" ("_\<^sub>*_") where
"push_forward f s = (\<lambda> k . f ( s k))"

definition is_closed_fun :: "padic_num_fun \<Rightarrow> bool" where
"is_closed_fun f = (\<forall> x. x \<in> carrier Q\<^sub>p \<longrightarrow> f x \<in> carrier Q\<^sub>p)"

definition fun_sum:: "padic_num_fun \<Rightarrow> padic_num_fun \<Rightarrow> padic_num_fun" where
"fun_sum f g = (\<lambda>x. (f x) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (g x))" 

definition fun_prod:: "padic_num_fun \<Rightarrow> padic_num_fun \<Rightarrow> padic_num_fun" where
"fun_prod f g = (\<lambda>x. (f x) \<otimes>\<^bsub>Q\<^sub>p\<^esub>  (g x))" 

definition is_constant_fun :: "padic_num_fun \<Rightarrow> bool" where
"is_constant_fun f = (\<exists>x \<in> carrier Q\<^sub>p. \<forall>y \<in> carrier Q\<^sub>p. f y = x)"

definition eq_on_Qp :: "padic_num_fun \<Rightarrow> padic_num_fun \<Rightarrow> bool" (infixl "\<doteq>" 78) where
"eq_on_Qp f g = (\<forall>x. x \<in> carrier Q\<^sub>p \<longrightarrow> f x = g x)"

lemma eq_simp:
  assumes "(f \<doteq> g)"
  assumes "x \<in> carrier Q\<^sub>p"
  shows "f x = g x" 
  using eq_on_Qp_def assms(1) assms(2) by blast

lemma push_forward_eq:
  assumes "f \<doteq> g "
  assumes "is_closed_seq s"
  shows "(f\<^sub>*s) = (g\<^sub>*s)"
proof
  fix x 
  have "s x \<in> carrier Q\<^sub>p"
    using assms(2) is_closed_simp by blast
  then show "(f\<^sub>*s) x = (g\<^sub>*s) x" 
    using assms(1) eq_simp push_forward_def 
    by (simp add: \<open>f \<doteq> g\<close> \<open>s x \<in> carrier Q\<^sub>p\<close>)
qed

lemma is_closed_funI:
  assumes "\<And>x. x \<in> carrier Q\<^sub>p \<Longrightarrow> f x \<in> carrier Q\<^sub>p"
  shows "is_closed_fun f"
  using assms is_closed_fun_def 
  by blast

lemma is_closed_eq:
  assumes "is_closed_fun f"
  assumes "f \<doteq> g"
  shows "is_closed_fun g"
proof(rule is_closed_funI)
  show "\<And>x. x \<in> carrier Q\<^sub>p \<Longrightarrow> g x \<in> carrier Q\<^sub>p" 
    using assms eq_simp  
    by (metis is_closed_fun_def)
qed

lemma constant_is_closed:
  assumes "is_constant_fun f"
  shows "is_closed_fun f"
  using is_closed_fun_def is_constant_fun_def assms 
  by metis

lemma push_forward_of_constant_is_constant:
  assumes "is_constant_fun f"
  assumes "is_closed_seq s"
  shows "is_constant_seq (f\<^sub>*s)"
  using assms(1) assms(2) 
  by (metis (full_types) is_closed_seq_def is_constant_fun_def
      is_constant_seq_def push_forward_def)

lemma is_closed_fun_simp:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "is_closed_fun f"
  shows "f x \<in> carrier Q\<^sub>p"
  using is_closed_fun_def assms  
  by blast  

lemma push_forward_of_closed_is_closed:
  assumes "is_closed_seq s"
  assumes "is_closed_fun f"
  shows "is_closed_seq (f\<^sub>*s)" 
  using is_closed_fun_def is_closed_seq_def assms(1) assms(2)
        push_forward_def 
  by presburger

lemma push_forward_of_sum_0:
"((fun_sum f g)\<^sub>*s) k = ((f\<^sub>*s) k) \<oplus>\<^bsub>Q\<^sub>p\<^esub> ((g\<^sub>*s) k)"
  by (simp add: fun_sum_def push_forward_def)

lemma push_forward_of_sum:
"((fun_sum f g)\<^sub>*s) = seq_sum (f\<^sub>*s) (g\<^sub>*s)"
proof
  fix x 
  show "((fun_sum f g)\<^sub>*s) x = (seq_sum (f\<^sub>*s) (g\<^sub>*s)) x" 
    by (simp add: push_forward_of_sum_0 seq_sum_def)
qed

lemma push_forward_of_prod_0:
"((fun_prod f g)\<^sub>*s) k = ((f\<^sub>*s) k) \<otimes>\<^bsub>Q\<^sub>p\<^esub>  ((g\<^sub>*s) k)"
  by (simp add: fun_prod_def push_forward_def)

lemma push_forward_of_prod:
"((fun_prod f g)\<^sub>*s) = seq_prod (f\<^sub>*s) (g\<^sub>*s)"
proof
  fix x 
  show "((fun_prod f g)\<^sub>*s) x = (seq_prod (f\<^sub>*s) (g\<^sub>*s)) x" 
    by (simp add: push_forward_of_prod_0 seq_prod_def)
qed

definition is_continuous ::"padic_num_fun \<Rightarrow> bool" where
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
    using assms(1) assms(2) is_cauchy_def is_continuous_def push_forward_eq by metis 
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
      using A is_cauchy_def assms push_forward_of_constant_is_constant 
      by blast
    then show "is_cauchy (f\<^sub>*s)"
      using A assms  constant_is_cauchy 
      by blast
  qed
qed

lemma sum_of_cont_is_cont:
  assumes "is_continuous f"
  assumes "is_continuous g"
  shows "is_continuous (fun_sum f g)"
proof(rule is_continuousI)
  show "is_closed_fun (fun_sum f g)" using assms
    using Q\<^sub>p_def Qp_is_cring cring.cring_simprules(1) is_continuous_def
      fun_sum_def is_closed_fun_def 
    by (simp add: cring.cring_simprules(1))
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
    using Q\<^sub>p_def Qp_is_cring assms(1) assms(2) cring.cring_simprules(5) 
      is_continuous_def fun_prod_def is_closed_fun_def
    by (simp add: cring.cring_simprules(5))
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

(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)
(*****************************     Completeness of Qp     *****************************************)
(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)
lemma val_dist_to_Zp:
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  shows "val_Zp (to_Zp (a \<ominus>\<^bsub>Q\<^sub>p\<^esub> b)) = val_dist a b"
proof-
  have "(a \<ominus>\<^bsub>Q\<^sub>p\<^esub> b) \<in> \<O>\<^sub>p"
    by (simp add: Zp_is_subring a_minus_def assms(1) assms(2) subringE(5) subringE(7))
  then show ?thesis 
    using assms to_Zp_val[of "(a \<ominus>\<^bsub>Q\<^sub>p\<^esub> b)"] 
    by linarith
qed

lemma val_dist_to_Zp':
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  shows "val_Zp ((to_Zp a) \<ominus> (to_Zp b)) = val_dist a b"
  using assms(1) assms(2) to_Zp_minus val_dist_to_Zp 
  by presburger

lemma val_ring_seq_cauchy:
  assumes "\<And>k. s k \<in> \<O>\<^sub>p"
  assumes "is_closed_seq s"
  shows "is_cauchy s \<longleftrightarrow> padic_int_polynomial.is_cauchy p (to_Zp_seq s)"
proof
  show "is_cauchy s \<Longrightarrow> padic_int_polynomial.is_cauchy p (to_Zp_seq s)"
  proof-
    assume "is_cauchy s"
    show "padic_int_polynomial.is_cauchy p (to_Zp_seq s)"
    proof(rule padic_int_polynomial.is_cauchyI)
      show "padic_int_polynomial p" by simp 
      show "padic_int_polynomial.is_closed_seq p (to_Zp_seq s)"
        using \<open>is_cauchy s\<close> is_cauchy_def padic_num_poly.val_ring_map_to padic_num_poly_axioms 
        by blast
      show "\<And>n. \<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> to_Zp_seq s n0 n = to_Zp_seq s n1 n"
      proof-
        fix n
        show "\<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> to_Zp_seq s n0 n = to_Zp_seq s n1 n "
        proof-
          obtain N where N_def:  "\<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> val_dist (s n0) (s n1) \<succeq>\<^bsub>G\<^esub> *n + 1*"
            using assms  \<open>is_cauchy s\<close> is_cauchy_def 
            by blast
          have "\<And> n0 n1. N < n0 \<and> N < n1 \<longrightarrow> to_Zp_seq s n0 n = to_Zp_seq s n1 n "
          proof
            fix n0 n1 
            assume A: "N < n0 \<and> N < n1"
            show "to_Zp_seq s n0 n = to_Zp_seq s n1 n"
              unfolding to_Zp_seq_def
            proof-
              have "val_dist (s n0) (s n1) \<succeq>\<^bsub>G\<^esub> *n + 1*"
                using N_def A by blast
              then have "val_Zp (to_Zp ((s n0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (s n1)))  \<succeq>\<^bsub>G\<^esub> *n + 1*"
                using to_Zp_val[of "((s n0) \<ominus>\<^bsub>Q\<^sub>p\<^esub> (s n1))"]
                by (metis (no_types, lifting) G_ord(1) to_Zp_def val_Zp_def)
              then have "val_Zp ((to_Zp (s n0)) \<ominus> (to_Zp (s n1)))  \<succeq>\<^bsub>G\<^esub> *n + 1*"
                by (metis assms to_Zp_minus)
              then have 0:"ord_Zp ((to_Zp (s n0)) \<ominus> (to_Zp (s n1))) \<ge> n + 1 \<or> ((to_Zp (s n0)) = (to_Zp (s n1)))"
              proof(cases "(to_Zp (s n0)) \<ominus> (to_Zp (s n1)) = \<zero>")
                case True
                then show ?thesis 
                  by (metis (no_types, lifting) G_def Qp_is_cring assms  cring_def 
                      extended_ordered_monoid.simps(1) is_closed_simp option.simps(3)
                      ring.r_right_minus_eq to_Zp_minus val_Zp_def val_def val_dist_to_Zp)
              next
                case False
                then have "val_Zp ((to_Zp (s n0)) \<ominus> (to_Zp (s n1))) 
                                = *ord_Zp ((to_Zp (s n0)) \<ominus> (to_Zp (s n1)))*"
                  by (metis Zp_is_domain \<open>is_cauchy s\<close> cring.cring_simprules(4) 
                      domain.axioms(1) is_closed_simp padic_num_poly.is_cauchy_def 
                      padic_num_poly_axioms to_Zp_closed val_ord_Zp)
                then show ?thesis 
                  using G_ord(2) \<open>val_Zp (to_Zp (s n0) \<ominus> to_Zp (s n1)) \<succeq>\<^bsub>G\<^esub> Some (int (n + 1))\<close> 
                  by presburger
              qed
              show "to_Zp (s n0) n = to_Zp (s n1) n"
                apply(cases "to_Zp (s n0) = to_Zp (s n1)")
                 apply presburger
              proof-
                assume A: "to_Zp (s n0) \<noteq> to_Zp (s n1)"
                then have "ord_Zp ((to_Zp (s n0)) \<ominus> (to_Zp (s n1))) \<ge> n + 1"
                  using 0 
                  by blast
                then have A0: "ord_Zp ((to_Zp (s n0)) \<ominus> (to_Zp (s n1))) > n"
                  by linarith
                then have A1: "((to_Zp (s n0)) \<ominus> (to_Zp (s n1))) n = 0"
                  by (meson Zp_is_domain \<open>is_cauchy s\<close> cring.cring_simprules(4) domain.axioms(1)
                      int.lless_eq is_closed_simp padic_num_poly.is_cauchy_def
                      padic_num_poly_axioms to_Zp_closed zero_below_ord)
                have A2: "to_Zp (s n1) \<in> padic_set p"
                  by (metis Z\<^sub>p_def \<open>is_cauchy s\<close> is_closed_simp padic_num_poly.is_cauchy_def
                      padic_num_poly_axioms partial_object.select_convs(1) to_Zp_closed)
                have A3: "to_Zp (s n1) \<in> padic_set p"
                  using A2 by auto
                have A4: "to_Zp (s n0) n \<in> carrier R n"
                  by (metis Z\<^sub>p_def \<open>is_cauchy s\<close> is_closed_simp padic_num_poly.is_cauchy_def 
                      padic_num_poly_axioms padic_set_simp0 partial_object.select_convs(1)
                      to_Zp_closed)
                have A5: "to_Zp (s n1) n \<in> carrier R n"
                  using A3 padic_set_simp0 by blast
                then have "to_Zp (s n0) n \<ominus>\<^bsub>R n\<^esub> to_Zp (s n1) n = \<zero>\<^bsub>R n\<^esub>"
                  using A1 A2 A3 
                  by (smt R_residues Z\<^sub>p_def Zp_one_car Zp_one_notzero a_minus_def nat_int 
                      of_nat_0 of_nat_0_less_iff of_nat_le_0_iff ord_Zp_def ord_Zp_one 
                      padic_add_def padic_inv padic_set_simp2 partial_object.select_convs(1) 
                      prime residues.res_zero_eq ring.simps(1) ring.simps(2) val_of_nonzero(2))
                then show "to_Zp (s n0) n =  to_Zp (s n1) n "
                  using A4 A5 R_cring[of n] 
                  by (metis Res_0' cring_def neq0_conv ring.r_right_minus_eq)
              qed
            qed
          qed
          then show ?thesis 
            by blast
        qed
      qed
    qed
  qed
  show "padic_int_polynomial.is_cauchy p (to_Zp_seq s) \<Longrightarrow> is_cauchy s"
  proof(rule is_cauchyI)
    show "padic_int_polynomial.is_cauchy p (to_Zp_seq s) \<Longrightarrow> is_closed_seq s"
    proof-
      assume "padic_int_polynomial.is_cauchy p (to_Zp_seq s)"
      then have "padic_int_polynomial.is_closed_seq p (to_Zp_seq s)"
        using padic_int_polynomial.is_cauchy_def[of p "(to_Zp_seq s)"]  PP 
        by blast
      then show "is_closed_seq s"
        by (simp add: assms(2))
    qed
    fix k
    assume A: "padic_int_polynomial.is_cauchy p (to_Zp_seq s)" 
    show "\<exists>N. \<forall>k0 k1. N < k0 \<and> N < k1 \<longrightarrow> val_dist (s k0) (s k1) \<succeq>\<^bsub>G\<^esub> Some k"
    proof-
      have " (\<forall>n. \<exists>N. \<forall>m k. N < m \<and> N < k \<longrightarrow> to_Zp_seq s m = to_Zp_seq s k \<or> n < ord_Zp (to_Zp_seq s m \<ominus>\<^bsub>padic_int p\<^esub> to_Zp_seq s k))"
        using A padic_int_polynomial.is_cauchy_def[of p "(to_Zp_seq s)"]
        unfolding to_Zp_seq_def 
        using PP by blast
      then  obtain N where
        N_def: "\<forall>k0 k1. N < k0 \<and> N < k1 \<longrightarrow> (to_Zp (s k0)) = (to_Zp (s k1)) 
                        \<or> padic_int_polynomial.ord_Zp_dist Z\<^sub>p p (to_Zp (s k0)) (to_Zp (s k1)) \<ge> k"
          by (metis Z\<^sub>p_def int.lless_eq ord_Zp_def to_Zp_seq_def)
      have "\<And>k0 k1. N < k0 \<and> N < k1 \<longrightarrow> val_dist (s k0) (s k1) \<succeq>\<^bsub>G\<^esub> *k*"
      proof
          fix k0 k1 
          assume "N < k0 \<and> N < k1"
          then have P0: " (to_Zp (s k0)) = (to_Zp (s k1)) 
                        \<or> padic_int_polynomial.ord_Zp_dist Z\<^sub>p p (to_Zp (s k0)) (to_Zp (s k1)) \<ge> k"
            using N_def by blast  
          show "val_dist (s k0) (s k1) \<succeq>\<^bsub>G\<^esub> *k*"
          proof(cases "(to_Zp (s k0)) = (to_Zp (s k1)) ")
            case True
            then have "s k0 = s k1"
              using assms(1)[of k0] assms(1)[of k1]  
              by (metis to_Zp_inc)
            then show ?thesis
              by (metis G_ord(1) Qp_is_cring assms(2) cring_def is_closed_simp 
                  local.val_zero ring.r_right_minus_eq)
          next
            case False
            then have "padic_int_polynomial.ord_Zp_dist Z\<^sub>p p (to_Zp (s k0)) (to_Zp (s k1)) \<ge> k"
              using P0 by blast
            then have "ord (\<iota> ((to_Zp (s k0) \<ominus> to_Zp (s k1))))\<ge> k"
              by (metis (no_types, lifting) False Zp_is_domain assms(2) cring.cring_simprules(4) 
                  cring_def domain.axioms(1) is_closed_simp ord_of_inc ord_of_nonzero(2)
                  ord_pos ring.r_right_minus_eq to_Zp_closed)
            then have "ord ((s k0) \<ominus>\<^bsub>Q\<^sub>p\<^esub>(s k1))\<ge> k"
              by (metis assms(1) assms(2) inc_of_diff is_closed_simp to_Zp_closed to_Zp_inc)
            then show "val_dist (s k0) (s k1) \<succeq>\<^bsub>G\<^esub> Some k" 
              using False  
              by (metis (no_types, lifting) G_def Zp_is_domain assms(1) assms(2) cring_def 
                  domain.axioms(1) extended_order.elims(3) is_closed_simp option.inject 
                  option.simps(3) ordered_monoid.simps(1) ring.r_right_minus_eq to_Zp_closed 
                  to_Zp_minus to_Zp_zero val_def)
          qed
      qed
      then show ?thesis 
        by blast  
    qed
  qed
qed

lemma val_ring_seq_converges:
  assumes "\<And>k. s k \<in> \<O>\<^sub>p"
  assumes "is_closed_seq s"
  assumes "a \<in> carrier Z\<^sub>p"
  assumes  "padic_int_polynomial.converges_to p (to_Zp_seq s) a" 
  shows "converges_to s (\<iota> a)"
  apply(rule converges_toI)
    apply (simp add: assms(2))
proof-
  show "\<iota> a \<in> carrier Q\<^sub>p" 
    using assms 
    by (metis (full_types, hide_lams) Qp_nonzero_def(1)  Zp_one_nonzero 
        \<open>a \<in> carrier Z\<^sub>p\<close> frac_closed inc_of_nonzero local.inc_def 
        nonzero_fraction_imp_nonzero_numer )
  show "\<And>n. \<exists>N. \<forall>k>N. val_dist (s k) (\<iota> a) \<succeq>\<^bsub>G\<^esub> Some n"
  proof-
    fix n
    obtain N where "\<forall>k>N. to_Zp (s k) = a \<or> padic_int_polynomial.ord_Zp_dist Z\<^sub>p p (to_Zp (s k)) a \<ge>n"
      using assms(4)  padic_int_polynomial.converges_to_def[of p "(to_Zp_seq s)" a] 
            PP Z\<^sub>p_def to_Zp_seq_def 
      by fastforce 
    then have "\<And>k. k > N \<Longrightarrow> val_dist (s k) (\<iota> a) \<succeq>\<^bsub>G\<^esub> Some n"
    proof-
           fix k
           assume k_def: "k > N"
           show " val_dist (s k) (\<iota> a) \<succeq>\<^bsub>G\<^esub> Some n"
           proof(cases "to_Zp (s k) = a")
             case True
             then show ?thesis 
               by (metis G_ord(1) Qp_is_cring \<open>\<iota> a \<in> carrier Q\<^sub>p\<close> a_minus_def assms(1)
              cring.cring_simprules(17) local.val_zero to_Zp_inc)
           next
             case False
             then have "padic_int_polynomial.ord_Zp_dist Z\<^sub>p p (to_Zp (s k)) a \<ge>n"
               using \<open>\<forall>k>N. to_Zp (s k) = a \<or> n \<le> ord_Zp (to_Zp (s k) \<ominus> a)\<close> k_def 
               by blast
             then show ?thesis 
               by (metis (no_types, lifting) G_ord(1) G_ord(2) Zp_is_domain Zp_one_nonzero 
              assms(1) assms(2) assms(3) cring.cring_simprules(4) domain.axioms(1) 
              inc_of_diff is_closed_simp local.inc_def nonzero_fraction_imp_numer_not_zero
              ord_of_inc ord_of_nonzero(2) ord_pos to_Zp_closed to_Zp_inc val_def)
           qed
    qed
    then show "\<exists>N. \<forall>k>N. val_dist (s k) (\<iota> a) \<succeq>\<^bsub>G\<^esub> Some n"
      by blast 
  qed
qed

lemma scalar_mult_converges:
  assumes "is_closed_seq s"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "converges_to s a"
  assumes "c \<in> carrier Q\<^sub>p"
  shows "converges_to (scalar_mult c s) (c \<otimes>\<^bsub>Q\<^sub>p\<^esub> a)"
  apply(rule converges_toI)
  using assms(1) assms(4) scalar_mult_is_closed
  apply blast
   apply (meson Qp_is_cring assms(2) assms(4) cring.cring_simprules(5))
proof-
  show "\<And>n. \<exists>N. \<forall>k>N. val_dist (scalar_mult c s k) (c \<otimes>\<^bsub>Q\<^sub>p\<^esub> a) \<succeq>\<^bsub>G\<^esub> Some n"
  proof- fix n
    show " \<exists>N. \<forall>k>N. val_dist (scalar_mult c s k) (c \<otimes>\<^bsub>Q\<^sub>p\<^esub> a) \<succeq>\<^bsub>G\<^esub> Some n"
    proof(cases "c = \<zero>\<^bsub>Q\<^sub>p\<^esub>")
      case True
      then have T0: "(c \<otimes>\<^bsub>Q\<^sub>p\<^esub> a) = \<zero>\<^bsub>Q\<^sub>p\<^esub>"
        by (simp add: assms(2) cring.cring_simprules(26))
      have T1: "\<And>k. k> 0 \<Longrightarrow> (scalar_mult c s k) = \<zero>\<^bsub>Q\<^sub>p\<^esub>"
        using True 
        by (simp add: assms(1))
      have " \<forall>k>0. val_dist (scalar_mult c s k) (c \<otimes>\<^bsub>Q\<^sub>p\<^esub> a) \<succeq>\<^bsub>G\<^esub> Some n" 
        using True T0 T1 
        by (metis G_ord(1) Qp_is_cring a_minus_def assms(4)
            cring.cring_simprules(17) local.val_zero)
      then show ?thesis 
        by blast
    next
      case False
      fix n
      obtain N where
      N_def: "\<forall>k>N. val_dist (s k) a \<succeq>\<^bsub>G\<^esub>( Some n \<ominus>\<^bsub>G\<^esub> *ord c*)"
        using False 
        by (metis assms(3) converges_to_def gminus_minus)
      have "\<forall>k>N. val_dist (scalar_mult c s k) (c \<otimes>\<^bsub>Q\<^sub>p\<^esub> a) \<succeq>\<^bsub>G\<^esub> Some n"
      proof
        fix k
        show "N < k \<longrightarrow> val_dist (scalar_mult c s k) (c \<otimes>\<^bsub>Q\<^sub>p\<^esub> a) \<succeq>\<^bsub>G\<^esub> Some n"
        proof
          assume A: "N < k"
          have "val_dist (scalar_mult c s k) (c \<otimes>\<^bsub>Q\<^sub>p\<^esub> a) = 
                  val (c \<otimes>\<^bsub>Q\<^sub>p\<^esub> (s k) \<ominus>\<^bsub>Q\<^sub>p\<^esub>(c \<otimes>\<^bsub>Q\<^sub>p\<^esub> a))"
            using scalar_mult_def by presburger
          then have "val_dist (scalar_mult c s k) (c \<otimes>\<^bsub>Q\<^sub>p\<^esub> a) = 
                  val (c \<otimes>\<^bsub>Q\<^sub>p\<^esub> ((s k) \<ominus>\<^bsub>Q\<^sub>p\<^esub> a))"
            by (smt Qp_is_cring assms(1) assms(2) assms(4) cring.cring_simprules(27) 
                cring.cring_simprules(4) cring.cring_simprules(5) cring.cring_simprules(8)
                cring.prod_diff cring_def is_closed_simp ring.r_right_minus_eq)
          then have "val_dist (scalar_mult c s k) (c \<otimes>\<^bsub>Q\<^sub>p\<^esub> a) = 
                  val c \<oplus>\<^bsub>G\<^esub> (val ((s k) \<ominus>\<^bsub>Q\<^sub>p\<^esub> a))"
            by (metis (no_types, lifting) Qp_is_cring assms(1) assms(2) assms(4) cring.cring_simprules(4) is_closed_simp val_mult)
          then have "val_dist (scalar_mult c s k) (c \<otimes>\<^bsub>Q\<^sub>p\<^esub> a) \<succeq>\<^bsub>G\<^esub> 
                  val c \<oplus>\<^bsub>G\<^esub> ( Some n \<ominus>\<^bsub>G\<^esub> *ord c*)"
            using A N_def gord_plus' 
            by presburger
          then have "val_dist (scalar_mult c s k) (c \<otimes>\<^bsub>Q\<^sub>p\<^esub> a) \<succeq>\<^bsub>G\<^esub> 
                  *ord c* \<oplus>\<^bsub>G\<^esub> ( Some n \<ominus>\<^bsub>G\<^esub> *ord c*)"
            by (metis False val_def)
          then have "val_dist (scalar_mult c s k) (c \<otimes>\<^bsub>Q\<^sub>p\<^esub> a) \<succeq>\<^bsub>G\<^esub> 
                   *ord c + n - (ord c)*"
            by (metis (mono_tags) 
                \<open>val_dist (scalar_mult c s k) (c \<otimes>\<^bsub>Q\<^sub>p\<^esub> a) = val (c \<otimes>\<^bsub>Q\<^sub>p\<^esub> (s k \<ominus>\<^bsub>Q\<^sub>p\<^esub> a))\<close> 
                add_diff_cancel_left' add_diff_eq  gminus_minus gplus_plus )
          then show "val_dist (scalar_mult c s k) (c \<otimes>\<^bsub>Q\<^sub>p\<^esub> a) \<succeq>\<^bsub>G\<^esub> Some n"
            by (metis (full_types) add_diff_cancel_left')
        qed
      qed
      then show "\<exists>N. \<forall>k>N. val_dist (scalar_mult c s k) (c \<otimes>\<^bsub>Q\<^sub>p\<^esub> a) \<succeq>\<^bsub>G\<^esub> Some n"
        by blast 
    qed
  qed
qed

lemma normalize_converges_imp_converges:
  assumes "\<not> (\<forall>k. (s k) \<in> \<O>\<^sub>p)"
  assumes "is_closed_seq s"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "converges_to (normalize_seq s) a"
  shows "converges_to s ((\<pp> e ( fromSome (seq_rad s))) \<otimes>\<^bsub>Q\<^sub>p\<^esub> a)"
proof-
  have "s = (scalar_mult (\<pp> e ( fromSome (seq_rad s))) (normalize_seq s))"
    using normalize_seq_def''[of s] assms(1) assms(2) 
    by presburger
  then show ?thesis 
    using assms scalar_mult_converges[of "(normalize_seq s)" a 
                                    "(\<pp> e ( fromSome (seq_rad s))) \<otimes>\<^bsub>Q\<^sub>p\<^esub> a"] 
    by (metis converges_to_def p_intpow_closed(1) scalar_mult_converges)
qed

lemma normalize_converges_imp_converges':
  assumes "(\<forall>k. (s k) \<in> \<O>\<^sub>p)"
  assumes "is_closed_seq s"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "converges_to (normalize_seq s) a"
  shows "converges_to s a"
  using assms 
  by (metis normalize_seq_def'')

lemma normalize_converges_imp_converges'':
  assumes "is_closed_seq s"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "converges_to (normalize_seq s) a"
  shows "\<exists>b \<in> carrier Q\<^sub>p. converges_to s b"
  apply(cases "(\<forall>k. (s k) \<in> \<O>\<^sub>p)")
  using assms  normalize_converges_imp_converges' 
  apply blast
    using assms normalize_converges_imp_converges  converges_to_def 
    by blast

lemma Qp_complete:
  assumes "is_cauchy s"
  shows "\<exists>a. converges_to s a"
proof-
  have Nc: "is_cauchy (normalize_seq s)"
    using assms cauchy_imp_normalize_cauchy is_cauchy_def by blast
  have 0: "padic_int_polynomial.is_cauchy p (to_Zp_seq (normalize_seq s))"
    using Nc 
    by (meson assms local.cauchy_imp_bounded normalize_in_val_ring
        normalize_is_closed val_ring_seq_cauchy)
  then obtain a0 where a0_def: "a0 = padic_int_polynomial.res_lim (to_Zp_seq (normalize_seq s))"
    by simp 
  have a0_car: "a0 \<in> carrier Z\<^sub>p"
    using a0_def 0 padic_int_polynomial.res_lim_in_Zp[of p "(to_Zp_seq (normalize_seq s))"]  
          PP Z\<^sub>p_def by blast
  then have "padic_int_polynomial.converges_to p (to_Zp_seq (normalize_seq s)) a0"
    using a0_def padic_int_polynomial.is_cauchy_imp_has_limit[of p "(to_Zp_seq (normalize_seq s))" a0] 
          PP \<open>padic_int_polynomial.is_cauchy p (to_Zp_seq (normalize_seq s))\<close> by blast
  then have "converges_to (normalize_seq s) (\<iota> a0)"
    using a0_car val_ring_seq_converges[of "(normalize_seq s)" a0]  
    using assms normalize_in_val_ring padic_num_poly.cauchy_imp_bounded 
      padic_num_poly.normalize_is_closed padic_num_poly_axioms 
    by blast
  then show ?thesis 
    by (meson assms converges_to_def normalize_converges_imp_converges''
        padic_num_poly.is_cauchy_def padic_num_poly_axioms)
qed

lemma Qp_complete':
  assumes "is_cauchy s"
  shows "(limit s) \<in> carrier Q\<^sub>p \<and> converges_to s (limit s)"
  using Qp_complete assms converges_to_def limit_def' 
  by blast


definition alt_seq where
"alt_seq s = (\<lambda>k. (if (even k) then (s k) else (limit s)))"

lemma alt_seq_cauchy:
  assumes "is_cauchy s"
  shows "is_cauchy (alt_seq s)"
proof(rule is_cauchyI)
  show "is_closed_seq (alt_seq s)"
    using alt_seq_def[of s] 
          assms 
    unfolding  is_cauchy_def[of s] 
    using assms is_closedI[of s] 
          is_closed_simp[of s]  Qp_complete' is_closedI
    by presburger
  show  "\<And>k. \<exists>N. \<forall>k0 k1. N < k0 \<and> N < k1 \<longrightarrow> val_dist (alt_seq s k0) (alt_seq s k1) \<succeq>\<^bsub>G\<^esub> Some k"
  proof-
    fix k
    show "\<exists>N. \<forall>k0 k1. N < k0 \<and> N < k1 \<longrightarrow> val_dist (alt_seq s k0) (alt_seq s k1) \<succeq>\<^bsub>G\<^esub> Some k"
    proof-
      obtain N0 where N0_def: "\<forall>k0 k1. N0 < k0 \<and> N0< k1 \<longrightarrow> val_dist (s k0) ( s k1) \<succeq>\<^bsub>G\<^esub> Some k"
        using assms unfolding is_cauchy_def  
        by blast
      obtain N1 where N1_def: "\<forall>k0. N1 < k0 \<longrightarrow> val_dist (s k0) (limit s) \<succeq>\<^bsub>G\<^esub> Some k"
        using assms Qp_complete'[of s] 
        unfolding converges_to_def  
        by blast
      obtain N where N_def: "N = max N1 N0"
        by simp 
      have "\<And> k0 k1. N < k0 \<and> N < k1 \<longrightarrow> val_dist (alt_seq s k0) (alt_seq s k1) \<succeq>\<^bsub>G\<^esub> Some k"
      proof
        fix k0 k1
        assume A: "N < k0 \<and>N < k1"
        show " val_dist (alt_seq s k0) (alt_seq s k1) \<succeq>\<^bsub>G\<^esub> Some k"
        proof(cases "even k0")
          case T: True
          then show ?thesis 
          proof(cases "even k1")
            case True
            show ?thesis 
              using T True 
              unfolding alt_seq_def
              by (smt A N0_def N_def max.strict_boundedE)
          next
            case False
            then show ?thesis 
              using T  
              unfolding alt_seq_def 
              by (smt A N1_def N_def max.strict_boundedE)
          qed
        next
          case F: False
          then show ?thesis 
          proof(cases "even k1")
            case True
            then show ?thesis 
              using F True 
              unfolding alt_seq_def
              by (smt A N1_def N_def Qp_complete' assms is_closed_simp 
                  max.strict_boundedE padic_num_poly.is_cauchy_def padic_num_poly_axioms
                  val_dist_sym)
          next
            case False
            then show ?thesis
              using F False
              unfolding alt_seq_def 
              by (smt G_ord(1) Qp_complete' Qp_is_cring assms cring_def 
                  local.val_zero ring.r_right_minus_eq)
          qed
        qed
      qed
      then show ?thesis by blast 
    qed
  qed
qed

lemma alt_seq_limit:
  assumes "is_cauchy s"
  shows "limit (alt_seq s) = limit s"
proof-
  have ac: "is_cauchy (alt_seq s)"
    by (simp add: alt_seq_cauchy assms)
  obtain l0 where l0_def: "l0 = limit s"
    by simp
  obtain l1 where l1_def: "l1 = limit (alt_seq s)"
    by simp 
  have C0: "converges_to s l0"
    by (simp add: Qp_complete' assms l0_def)
  have C1: "converges_to (alt_seq s) l1"
    by (simp add: ac l1_def padic_num_poly.Qp_complete' padic_num_poly_axioms)
  have C2: "converges_to (alt_seq s) l0 "
    apply(rule converges_toI)
    using C1 converges_to_def apply blast
      using C0 converges_to_def apply blast
    proof-
    show "\<And>n. \<exists>N. \<forall>k>N. val_dist (alt_seq s k) l0 \<succeq>\<^bsub>G\<^esub> Some n"
      proof-
        fix n
        obtain N where N_def: "\<forall>k>N. val_dist (s k) l0 \<succeq>\<^bsub>G\<^esub> Some n"
          using C0 unfolding converges_to_def 
          by blast   
        have "\<forall>k>N. val_dist (alt_seq s k) l0 \<succeq>\<^bsub>G\<^esub> Some n"
        proof
          fix k
          show "N < k \<longrightarrow> val_dist (alt_seq s k) l0 \<succeq>\<^bsub>G\<^esub> Some n"
          proof
            assume A: "N < k"
            show "val_dist (alt_seq s k) l0 \<succeq>\<^bsub>G\<^esub> Some n"
            proof(cases "even k")
              case True
              then show ?thesis
                using A N_def alt_seq_def 
                by presburger
            next
              case False
              then show ?thesis 
                by (metis C0 G_ord(1) Qp_is_cring alt_seq_def converges_to_def 
                    cring_def l0_def local.val_zero ring.r_right_minus_eq)
            qed
          qed
        qed
        then show " \<exists>N. \<forall>k>N. val_dist (alt_seq s k) l0 \<succeq>\<^bsub>G\<^esub> Some n"
          by blast 
    qed
  qed
  then show ?thesis 
    using ac l0_def padic_num_poly.is_cauchy_def padic_num_poly.limit_def' padic_num_poly_axioms 
    by blast
qed

lemma res_lim_pushforward: 
  assumes "is_continuous f"
  assumes "is_cauchy s"
  assumes "t = alt_seq s"
  shows "limit (f\<^sub>*t) = f (limit t)"
proof-
  obtain fl where fl_def: "fl = limit (f\<^sub>*t)"
    by simp 
  obtain l where l_def: "l = limit t"
    by simp
  have C0: "converges_to (f\<^sub>*t) fl "
    using assms 
    by (simp add: fl_def is_continuous_def padic_num_poly.Qp_complete' 
        padic_num_poly.alt_seq_cauchy padic_num_poly_axioms)
  have C1: "converges_to t l"
    by (simp add: Qp_complete' assms(2) assms(3) l_def 
        padic_num_poly.alt_seq_cauchy padic_num_poly_axioms)
  have C2: "converges_to (f\<^sub>*t) (f l)"
    apply(rule converges_toI)
    using C0 converges_to_def apply blast
    using C1 assms(1) continuous_is_closed converges_to_def is_closed_fun_simp apply blast
  proof-
    show "\<And>n. \<exists>N. \<forall>k>N. val_dist ((f\<^sub>*t) k) (f l) \<succeq>\<^bsub>G\<^esub> Some n"
    proof-
      fix n
      show " \<exists>N. \<forall>k>N. val_dist ((f\<^sub>*t) k) (f l) \<succeq>\<^bsub>G\<^esub> Some n"
      proof-
        obtain N0 where N0_def: " \<forall>k>N0. val_dist ((f\<^sub>*t) k) fl \<succeq>\<^bsub>G\<^esub> Some n"
          using C0 unfolding converges_to_def
          by blast  
        have C3: "is_cauchy (f\<^sub>*t)"
          using C0 convergent_imp_cauchy converges_to_def 
          by blast
        obtain N1 where N1_def: "\<And>k0 k1. k0>N1 \<and> k1> N1 \<Longrightarrow> val_dist ((f\<^sub>*t) k0) ((f\<^sub>*t) k1)  \<succeq>\<^bsub>G\<^esub> Some n"
          using C3 
          unfolding is_cauchy_def 
          by blast  
        obtain N where N_def: "N = max N0 N1"
          by simp
        have "\<forall>k>N. val_dist ((f\<^sub>*t) k) (f l) \<succeq>\<^bsub>G\<^esub> Some n"
        proof
          fix k
          show " N < k \<longrightarrow> val_dist ((f\<^sub>*t) k) (f l) \<succeq>\<^bsub>G\<^esub> Some n "
          proof
            assume A: "N < k"
            show "val_dist ((f\<^sub>*t) k) (f l) \<succeq>\<^bsub>G\<^esub> Some n"
            proof(cases "odd k")
              case True
              then have "((f\<^sub>*t) k)  = f l"
                using l_def assms 
                unfolding alt_seq_def push_forward_def l_def
                using alt_seq_limit assms(3) by force
              then show "val_dist ((f\<^sub>*t) k) (f l) \<succeq>\<^bsub>G\<^esub> Some n"
                by (metis C0 G_ord(1) Qp_is_cring converges_to_def cring_def 
                    is_closed_simp local.val_zero ring.r_right_minus_eq)
            next
              case False
              then have F0: "((f\<^sub>*t) k)  = f (t k)"
                using l_def assms 
                unfolding alt_seq_def push_forward_def l_def
                using alt_seq_limit assms(3) by force 
              then have F1: "((f\<^sub>*t) (Suc k))  = f l "
                using l_def assms 
                unfolding alt_seq_def push_forward_def l_def
                using alt_seq_limit assms(3)  False 
                by force
              have F2: "val_dist ((f\<^sub>*t) k) ((f\<^sub>*t) (Suc k)) \<succeq>\<^bsub>G\<^esub> *n*"
                using A N_def N1_def[of k "Suc k"]  
                by linarith
              then show "val_dist ((f\<^sub>*t) k) (f l) \<succeq>\<^bsub>G\<^esub> *n*"
                by (metis F1 push_forward_def)
            qed
          qed
        qed
        then show ?thesis 
          by blast 
      qed
    qed
  qed
  then show ?thesis 
    using converges_to_def l_def limit_def' 
    by blast
qed

lemma alt_seq_pushforward: 
  assumes "is_continuous f"
  assumes "is_cauchy s"
  assumes "t = alt_seq s"
  shows "limit (f\<^sub>*s) = limit (f\<^sub>*t)"
proof(rule ccontr)
  assume C: "limit (f\<^sub>*s) \<noteq> limit (f\<^sub>*t)"
  have C0: "\<not> converges_to (f\<^sub>*s)  (limit (f\<^sub>*t))"
    using C converges_to_def limit_def' 
    by blast
  have C1: "\<exists>n. \<forall>N. \<exists>k. k > N \<and> \<not> val_dist ((f\<^sub>*s) k) (limit (f\<^sub>*t)) \<succeq>\<^bsub>G\<^esub>  *n*"
    using C0 
    unfolding converges_to_def 
    by (metis Qp_complete' assms(1) assms(2) assms(3) continuous_is_closed is_closed_fun_simp 
        padic_num_poly.alt_seq_limit padic_num_poly.is_cauchy_def padic_num_poly_axioms
        push_forward_of_closed_is_closed res_lim_pushforward)
  have C2: "\<exists>n. \<forall>N. \<exists>k. k > N \<and>  val_dist ((f\<^sub>*s) k) (limit (f\<^sub>*t)) \<prec>\<^bsub>G\<^esub>  *n*"
    using C1 
    by (metis G_eq order_fact')
  then obtain n where n_def: "\<forall>N. \<exists>k. k > N \<and>  val_dist ((f\<^sub>*s) k) (limit (f\<^sub>*t)) \<prec>\<^bsub>G\<^esub>  *n*"
    by blast 
  have C3: "(limit (f\<^sub>*t)) = f (limit s)"
    using assms padic_num_poly.alt_seq_limit padic_num_poly_axioms res_lim_pushforward 
    by auto
  have C4: "is_cauchy (f\<^sub>*t)"
    using assms(1) assms(2) assms(3) is_continuous_def 
          padic_num_poly.alt_seq_cauchy padic_num_poly_axioms 
          by blast
  then obtain N0 where N0_def: "\<And>k.  k > N0 \<Longrightarrow> val_dist ((f\<^sub>*t) k) (limit (f\<^sub>*t)) \<succeq>\<^bsub>G\<^esub> *n*"
    using assms Qp_complete'[of "(f\<^sub>*t)"] converges_to_def 
    by blast
  obtain N1 where N1_def: "\<And>k0 k1.  k0 > N1 \<and> k1 > N1 \<Longrightarrow> val_dist ((f\<^sub>*t) k0) ((f\<^sub>*t) k1) \<succeq>\<^bsub>G\<^esub> *n*"
    using C4 is_cauchy_def 
    by blast
  have C5: "is_cauchy (f\<^sub>*s)"
    using assms(1) assms(2) is_continuous_def 
    by blast
  obtain N2 where N2_def: "\<And>k0 k1.  k0 > N2 \<and> k1 > N2 \<Longrightarrow> val_dist ((f\<^sub>*s) k0) ((f\<^sub>*s) k1) \<succeq>\<^bsub>G\<^esub> *n*"
    using C5 is_cauchy_def
    by blast 
  obtain N3 where N3_def: "N3 > N0 \<and> N3 > N1 \<and> N3 > N2"
    by (metis Suc_le_eq Suc_lessD dual_order.strict_trans le_SucI less_SucI less_Suc_eq 
        less_Suc_eq_le not_less_eq )
  obtain N where N_def: "N > N3 \<and> val_dist ((f\<^sub>*s) N) (limit (f\<^sub>*t)) \<prec>\<^bsub>G\<^esub>  *n*"
    using n_def 
    by blast   
  show False
  proof(cases "even N")
    case True
    then have T0: "(f\<^sub>*t) N = (f\<^sub>*s) N"
      using assms unfolding alt_seq_def push_forward_def 
      by simp
    have T1: "(f\<^sub>*t) (Suc N) = f (limit s)"
      using assms unfolding alt_seq_def push_forward_def
      by (simp add: True)
    have T4: "val_dist ((f\<^sub>*t) N) (limit (f\<^sub>*t)) \<succeq>\<^bsub>G\<^esub> *n*"
      using N_def N3_def N0_def Suc_lessD less_trans_Suc by blast
    show False 
      using T4 N_def T0 
      by (metis order_fact)
  next
    case False
    then have F0: "(f\<^sub>*t) (Suc N) = (f\<^sub>*s) (Suc N)"
      by (simp add: alt_seq_def assms(3) push_forward_def)
    have F1: "(f\<^sub>*t) (N) = f (limit s)"
      using assms unfolding alt_seq_def push_forward_def
      by (simp add: False)
    have F2: " val_dist ((f\<^sub>*s) N) ((f\<^sub>*s) (Suc N)) \<succeq>\<^bsub>G\<^esub> *n*"
      using N_def N3_def N2_def 
      by (meson Suc_lessD less_Suc_eq less_trans_Suc)
    have F3: "val_dist ((f\<^sub>*t) N) ((f\<^sub>*t) (Suc N)) \<succeq>\<^bsub>G\<^esub> *n*"
      using N_def N3_def N1_def 
      by (meson Suc_lessD lessI less_trans_Suc)
    have F4: "val_dist ((f\<^sub>*t) N) (limit (f\<^sub>*t)) \<succeq>\<^bsub>G\<^esub> *n*"
      using N_def N3_def N0_def C3 
      by (metis C4 F1 G_ord(1) Qp_complete' Qp_is_cring cring_def local.val_zero ring.r_right_minus_eq)
    have F5: "val_dist ((f\<^sub>*t) N) (limit (f\<^sub>*t)) \<succeq>\<^bsub>G\<^esub> *n*" 
      using F4 by blast
    have F6: "val_dist ((f\<^sub>*t) N) ((f\<^sub>*s) (Suc N)) \<succeq>\<^bsub>G\<^esub> *n*"
      using F0 F3 by presburger
    have F7: "val_dist ((f\<^sub>*s) (Suc N)) (limit (f\<^sub>*t)) \<succeq>\<^bsub>G\<^esub> *n*" 
      by (metis C3 C4 F0 F1 F3 is_closed_simp padic_num_poly.is_cauchy_def padic_num_poly_axioms val_dist_sym)
    have F8: "val_dist ((f\<^sub>*s) N) (limit (f\<^sub>*t)) \<succeq>\<^bsub>G\<^esub> *n*" 
      by (metis (no_types, lifting) C3 C4 C5 F1 F2 F6 Qp_isosceles is_closed_simp padic_num_poly.is_cauchy_def padic_num_poly_axioms)
    then show False using N_def 
      using less_not_geq by blast
  qed
qed



lemma continuous_limit:
  assumes "is_continuous f"
  assumes "is_cauchy s"
  shows "converges_to (f\<^sub>*s) (f (limit s))"
proof-
  obtain t where t_def: "t = alt_seq s"
    by simp
  have 0: "converges_to (f\<^sub>*s) (limit (f\<^sub>*s))"
    using assms(1) assms(2) is_continuous_def padic_num_poly.Qp_complete' padic_num_poly_axioms 
    by blast
  have 1: "converges_to (f\<^sub>*s) (limit (f\<^sub>*t))"
    using "0" alt_seq_pushforward assms(1) assms(2) t_def 
    by auto
  have 2: "converges_to (f\<^sub>*s) (f (limit t))"
    using "1" assms(1) assms(2) res_lim_pushforward t_def 
    by auto
  then show  "converges_to (f\<^sub>*s) (f (limit s))"
    by (simp add: alt_seq_limit assms(2) t_def)
qed

lemma continuous_limit':
  assumes "is_continuous f"
  assumes "is_cauchy s"
  shows "limit (f\<^sub>*s) = (f (limit s))"
  using assms continuous_limit[of f s]  converges_to_def limit_def' 
  by blast

definition X_Qp :: "padic_num_fun"  where
"X_Qp  = (\<lambda>x. x)"

lemma push_forward_X_Qp:
"(X_Qp\<^sub>*s) = s"
proof
  fix x 
  show "(X_Qp\<^sub>*s) x = s x"
  using push_forward_def by (simp add: X_Qp_def)
qed

lemma X_Qp_is_continuous:
"is_continuous X_Qp"
  using is_continuous_def push_forward_X_Qp 
  by (simp add: X_Qp_def padic_num_poly.is_closed_fun_def padic_num_poly_axioms)

definition X_Qp_pow :: "nat \<Rightarrow> padic_num_fun"  where 
"X_Qp_pow n x = (if n=0 then \<one>\<^bsub>Q\<^sub>p\<^esub> else x e n)"

lemma X_Qp_pow_Qp_prod:
  shows "X_Qp_pow (Suc n) = fun_prod (X_Qp_pow n) (X_Qp)"
proof
  fix x
  show "X_Qp_pow (Suc n) x = fun_prod (X_Qp_pow n) X_Qp x"
  proof-
    have "X_Qp_pow (Suc n) x = x [^]\<^bsub>Q\<^sub>p\<^esub> (Suc n)" 
      by (simp add: X_Qp_pow_def)
    then have "X_Qp_pow (Suc n) x = x[^]\<^bsub>Q\<^sub>p\<^esub>n \<otimes>\<^bsub>Q\<^sub>p\<^esub>  x" 
      by (metis Qp_is_cring cring_def monoid.nat_pow_Suc ring_def)
    then show ?thesis using fun_prod_def X_Qp_pow_def X_Qp_def 
    proof -
      have "ring Q\<^sub>p"
        using Qp_is_cring cring_def by blast
      then show ?thesis
        by (metis (no_types, lifting) X_Qp_pow_def \<open>X_Qp_pow (Suc n) x = (x e n) \<otimes>\<^bsub>Q\<^sub>p\<^esub> x\<close> 
            fun_prod_def monoid.nat_pow_0 padic_num_poly.X_Qp_def padic_num_poly_axioms ring_def)
    qed
  qed
qed

lemma X_pow_Qp_is_closed:
 "is_closed_fun (X_Qp_pow n)"
proof(induction n)
  case 0
  then show ?case 
    using X_Qp_pow_def Q\<^sub>p_def Qp_one_car is_closed_fun_def
    by simp
next
  case (Suc n)
  then show ?case 
    by (metis X_Qp_pow_def Qp_is_cring cring_def is_closed_fun_def
        monoid.nat_pow_closed nat.simps(3) ring_def)
qed


lemma X_Qp_pow_Qp_is_continuous:
 "is_continuous (X_Qp_pow n)"
proof(induction n)
  case 0
  have  "is_constant_fun (X_Qp_pow (0::nat))"
  proof-
    have A0: "\<forall>x \<in> carrier Q\<^sub>p. (X_Qp_pow (0::nat)) x = \<one>\<^bsub>Q\<^sub>p\<^esub>" 
      using X_Qp_pow_def  by simp
    have A1: "\<one>\<^bsub>Q\<^sub>p\<^esub>\<in> carrier Q\<^sub>p" 
      by (simp add: Qp_one_car)
    then show ?thesis 
      using is_constant_fun_def A0 A1 by blast
  qed
  then show ?case 
    by (simp add: constant_is_continuous)
next
  case (Suc n)
  fix n
  assume IH :"is_continuous (X_Qp_pow n)"
  have "X_Qp_pow (Suc n) = fun_prod (X_Qp_pow n) X_Qp"
    by (simp add: X_Qp_pow_Qp_prod)
  then show "is_continuous (X_Qp_pow (Suc n))" 
    using IH X_Qp_is_continuous prod_of_cont_is_cont by auto 
qed
 
definition fun_scalar_mult:: "padic_number \<Rightarrow> padic_num_fun \<Rightarrow> padic_num_fun" where
"fun_scalar_mult c f = (\<lambda>x. c \<otimes>\<^bsub>Q\<^sub>p\<^esub>  (f x))"

lemma fun_scalar_mult_is_closed:
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "is_closed_fun f"
  shows "is_closed_fun (fun_scalar_mult c f)"
proof(rule is_closed_funI)
  fix x
  assume "x \<in> carrier Q\<^sub>p "
  then show " fun_scalar_mult c f x \<in> carrier Q\<^sub>p" 
    using assms fun_scalar_mult_def 
    by (metis Qp_is_cring cring.cring_simprules(5) is_closed_fun_def) 
qed

definition to_const_fun:: "padic_number \<Rightarrow> padic_num_fun"  where
"to_const_fun c = (\<lambda> x. c)"

lemma to_const_fun_is_const:
  assumes "c \<in> carrier Q\<^sub>p"
  shows "is_constant_fun (to_const_fun c)" 
  using assms is_constant_fun_def to_const_fun_def by auto

lemma fun_scalar_mult_rep:
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "is_closed_fun f"
  shows "fun_scalar_mult c f = fun_prod (to_const_fun c) f"
proof
  fix x
  show "fun_scalar_mult c f x = fun_prod (to_const_fun c) f x" 
    using fun_prod_def to_const_fun_def 
    by (simp add: fun_scalar_mult_def)
qed

lemma fun_scalar_mult_is_continuous:
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "is_continuous f"
  shows "is_continuous (fun_scalar_mult c f)"
proof-
  have 0: "fun_scalar_mult c f = fun_prod (to_const_fun c) f" 
    by (simp add: assms(1) assms(2) continuous_is_closed fun_scalar_mult_rep)
  have 1: "is_continuous (to_const_fun c)" 
    using assms(1) to_const_fun_is_const constant_is_continuous by auto  
  then show ?thesis 
    using 0 1 assms prod_of_cont_is_cont by auto  
qed

definition is_monomial :: "padic_num_fun \<Rightarrow> bool" where
"is_monomial f = (\<exists>c \<in> carrier Q\<^sub>p. \<exists>n::nat. f = fun_scalar_mult c (X_Qp_pow n))"

lemma monomial_is_closed:
  assumes "is_monomial f"
  shows "is_closed_fun f" 
proof-
  obtain c n where 0: "c \<in> carrier Q\<^sub>p" and 1: "f = fun_scalar_mult c (X_Qp_pow n)"
    using assms is_monomial_def  by blast
  then show ?thesis 
    using 0 1 fun_scalar_mult_is_closed  X_pow_Qp_is_closed 
    by blast
qed

lemma monomial_is_continuous:
  assumes "is_monomial f"
  shows "is_continuous f" 
proof-
  obtain c n where 0: "c \<in> carrier Q\<^sub>p" and 1: "f = fun_scalar_mult c (X_Qp_pow n)"
    using assms is_monomial_def  by blast
  then show ?thesis 
    by (simp add: X_Qp_pow_Qp_is_continuous fun_scalar_mult_is_continuous)
qed

definition mon:: "padic_number \<Rightarrow> nat \<Rightarrow> padic_num_fun" where
"mon c n = fun_scalar_mult c (X_Qp_pow n)"

lemma mon_is_monomial:
  assumes "c \<in> carrier Q\<^sub>p"
  shows "is_monomial (mon c n)"
  using assms is_monomial_def mon_def by blast

end
end 