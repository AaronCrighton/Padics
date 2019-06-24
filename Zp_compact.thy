theory Zp_compact
imports padic_int_topology
begin

(**************************************************************************************************)
(**************************************************************************************************)
(*******************************   SEQUENTIAL COMPACTNESS  ****************************************)
(*******************************          OF ZP            ****************************************)
(**************************************************************************************************)
(**************************************************************************************************)

context padic_int_poly
begin

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
  shows "\<And>m::nat. P (s' m)" sorry
(*proof-
  have "\<exists>k. P (s k)" using assms(3) 
    by blast
  fix m
  obtain k where kdef: "k = filtering_function s P m" by auto 
  have "\<exists>k. P (s k)" 
    using assms(3) by auto
  then have "P (s k)" 
    sledgehammer
  then have "s' m = s k"
    by (simp add: assms(2) filtered_sequence_def kdef take_subseq_def)
  hence "P (s' m)" 
    by (simp add: \<open>P (s k)\<close>)
  thus "\<And>m. P (s' m)" using  assms(2) assms(3) dual_order.strict_trans filter_exist filtered_sequence_def
      lessI less_Suc_eq_le take_subseq_def sledgehammer
    
qed*)


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


lemma seq_maps_to_n:
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
        maps_to_n_def)
qed

lemma seq_pr_inc:
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
   by (meson assms kth_res_equals_def fil_seq_pred padic_integers_axioms)
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
    using 0  is_closed_seq_def padic_integers_axioms padic_set_simp0 
    using padic_int_poly.is_closed_simp padic_int_poly_axioms by auto

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
  by (smt is_subseq_of_def Cseq_prop_0 is_closed_seq_def 
      padic_integers_axioms res_seq.simps(2) take_subseq_def)

lemma res_seq_res':
  assumes "is_closed_seq s"
  shows "\<And>n. res_seq s (Suc k) n (Suc k) = Cres (Suc k) (res_seq s k)"
  using assms res_seq_res[of s k] Cseq_prop_1[of "(res_seq s k)" "Suc k" ] 
  by simp

lemma res_seq_subseq: 
  assumes "is_closed_seq s"
  shows "is_subseq_of (res_seq s k) (res_seq s (Suc k))"
  by (metis assms  Cseq_prop_0 res_seq_res  
      res_seq.simps(2))

(**)
lemma is_increasing_id[simp]:
"is_increasing (\<lambda> n. n)"
  by (simp add: is_increasingI)

lemma is_increasing_comp:
  assumes "is_increasing f"
  assumes "is_increasing g"
  shows "is_increasing (f \<circ> g)"
  using assms(1) assms(2) is_increasing_def 
  by auto

lemma is_increasing_imp_geq_id[simp]:
  assumes  "is_increasing f"
  shows "f n \<ge>n"
  apply(induction n)
  apply simp
  by (metis (mono_tags, lifting) assms is_increasing_def
      leD lessI not_less_eq_eq order_less_le_subst2)

lemma is_subseq_ofE:
  assumes "is_closed_seq s"
  assumes "is_subseq_of s s'"
  shows "\<exists>k. k \<ge> n \<and> s' n = s k"
proof-
  obtain f where "is_increasing f \<and> s' = take_subseq s f"
    using assms(2) is_subseq_of_def by blast
  then have  " f n \<ge> n \<and> s' n = s (f n)"
    unfolding take_subseq_def 
    by simp
  then show ?thesis by blast 
qed


lemma is_subseq_of_id:
  assumes "is_closed_seq s"
  shows "is_subseq_of s s"
proof-
  have "s = take_subseq s (\<lambda>n. n)"
    unfolding take_subseq_def 
    by auto 
  then show ?thesis using is_increasing_id
    using is_subseqI 
    by blast
qed

lemma is_subseq_of_trans:
  assumes "is_closed_seq s"
  assumes "is_subseq_of s s'"
  assumes "is_subseq_of s' s''"
  shows "is_subseq_of s s''"
proof-
  obtain f where f_def: "is_increasing f \<and> s' = take_subseq s f"
    using assms(2) is_subseq_of_def 
    by blast
  obtain g where g_def: "is_increasing g \<and> s'' = take_subseq s' g"
    using assms(3) is_subseq_of_def 
    by blast
  have "s'' = take_subseq s (f \<circ> g)"
  proof
    fix x
    show "s'' x = take_subseq s (f \<circ> g) x"
      using f_def g_def unfolding take_subseq_def
      by auto
  qed
  then show ?thesis 
    using f_def g_def is_increasing_comp is_subseq_of_def 
    by blast
qed

lemma res_seq_subseq':
  assumes "is_closed_seq s"
  shows "is_subseq_of s (res_seq s k)"
proof(induction k)
  case 0
  then show ?case using is_subseq_of_id 
    by (simp add: assms)
next
  case (Suc k)
  fix k
  assume "is_subseq_of s (res_seq s k)"
  then show "is_subseq_of s (res_seq s (Suc k)) "
    using assms is_subseq_of_trans res_seq_subseq 
    by blast
qed

lemma res_seq_subseq'':
  assumes "is_closed_seq s"
  shows "is_subseq_of (res_seq s n) (res_seq s (n + k))"
  apply(induction k)
  apply (simp add: assms is_subseq_of_id res_seq_res)
  using add_Suc_right assms is_subseq_of_trans res_seq_res res_seq_subseq by presburger
(**)

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
    using assms res_seq_res' padic_integers_axioms by auto
  have "acc_point s (Suc k) = res_seq s (Suc k) 0 (Suc k)" using acc_point_def by simp
  then have "acc_point s (Suc k) = (Cseq (Suc k) (res_seq s k)) 0 (Suc k)"
    by simp
  thus ?thesis 
    by (simp add: \<open>(Cseq (Suc k) (res_seq s k)) 0 (Suc k) = Cres (Suc k) (res_seq s k)\<close>)
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
  assume "k \<noteq> 0"  show "res (int p ^ k) (acc_point s (Suc k)) = acc_point s k" 
    by (metis False acc_point_def assms is_closed_simp lessI less_imp_le nat.distinct(1) 
        of_nat_power res_seq_res_1  r_Zp res_seq_res)
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
                of_nat_power res_seq_res_1  r_Zp res_seq_res)
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

lemma increasing_conv_induction_0_pre:
  assumes "is_closed_seq s"
  assumes "a = acc_point s"
  shows "\<exists>k > convergent_subseq_fun s a n. (s k (Suc n)) = a (Suc n)"
proof-
  obtain l::nat where "l > 0 " by blast
  have "is_subseq_of s (res_seq s (Suc n))" 
    using assms(1) res_seq_subseq' by blast
  then obtain m where "s m = res_seq s (Suc n) l \<and> m \<ge> l" 
    by (metis is_increasing_imp_geq_id is_subseq_of_def take_subseq_def )
    
  have "a (Suc n) = res_seq s (Suc n) 0 (Suc n)" 
    by (simp add: acc_point_def assms(2))
  have "s m (Suc n) = a (Suc n)" 
    by (metis \<open>a (Suc n) = res_seq s (Suc n) 0 (Suc n)\<close> \<open>s m = res_seq s (Suc n) l \<and> l \<le> m\<close> assms(1) res_seq_res')
  
  thus ?thesis 
    using \<open>0 < l\<close> \<open>s m = res_seq s (Suc n) l \<and> l \<le> m\<close> less_le_trans  \<open>s m (Suc n) = a (Suc n)\<close> 
    by (metis \<open>a (Suc n) = res_seq s (Suc n) 0 (Suc n)\<close> \<open>is_subseq_of s (res_seq s (Suc n))\<close>
        assms(1) lessI is_subseq_ofE res_seq_res' )
qed

  

lemma increasing_conv_subseq_fun_0:
  assumes "is_closed_seq s"
  assumes "\<exists>s'. s' = convergent_subseq s"
  assumes "a = acc_point s"
  shows "convergent_subseq_fun s a (Suc n) > convergent_subseq_fun s a n"
  apply(auto) 
proof(induction n)
  case 0
  have "convergent_subseq_fun s a 0 = 0" by simp
  then show ?case 
    by (smt assms(1) assms(3) less_Suc_eq less_Suc_eq_0_disj increasing_conv_induction_0_pre padic_integers_axioms someI_ex)
next
  case (Suc k)
  then show ?case 
    by (metis (mono_tags, lifting) assms(1) assms(3) increasing_conv_induction_0_pre someI_ex) 
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

lemma convergent_sequence_res:
  assumes "is_closed_seq s"
  assumes "a = acc_point s"
  shows "convergent_subseq s l l = res (p ^ l) (acc_point s l)"
proof-
  have "\<exists>k. convergent_subseq s l =  s k \<and> s k l = a l" 
  proof-
    have "convergent_subseq s l = s (convergent_subseq_fun s a l)" 
      by (simp add: assms(2) convergent_subseq_def take_subseq_def)
    obtain k where kdef: "(convergent_subseq_fun s a l) = k" 
      by simp
    have "convergent_subseq s l = s k" 
      by (simp add: \<open>convergent_subseq s l = s (convergent_subseq_fun s a l)\<close> kdef)
    have "s k l = a l"
    proof(cases "l = 0")
      case True
      then show ?thesis 
        by (metis acc_point_def assms(1) assms(2) is_closed_simp of_nat_0 ord_pos zero_below_ord zero_vals)
    next
      case False
      have "0 < l"
        using False by blast
      then have "k > convergent_subseq_fun s a (l-1)" 
        by (metis One_nat_def Suc_pred assms(1) assms(2) increasing_conv_subseq_fun_0 kdef)
      then have "s k l = a l" using kdef 
        assms(1) assms(2) convergent_subseq_fun.simps(2) increasing_conv_induction_0_pre 
        padic_integers_axioms someI_ex One_nat_def  \<open>0 < l\<close> increasing_conv_induction_0_pre 
        by (smt Suc_diff_1)
   
      then show ?thesis
        by simp
    qed
    then have "convergent_subseq s l =  s k \<and> s k l = a l" 
      using \<open>convergent_subseq s l = s k\<close> by blast
    thus ?thesis 
      by blast
  qed
  thus ?thesis 
    using acc_point_closed assms(1) assms(2) r_Zp by auto
qed

lemma convergent_subsequence_is_convergent:
  assumes "is_closed_seq s"
  assumes "a = acc_point s"
  shows "converges_to (convergent_subseq s) (acc_point s)" (*\<And>n. \<exists>N. \<forall>k > N. s k n = a n"*) 
proof(rule converges_toI)
  show "acc_point s \<in> carrier Z\<^sub>p"
    using acc_point_closed assms  by blast
  show "is_closed_seq (convergent_subseq s)" using is_closed_seq_conv_subseq assms by simp
  show "\<And>n. \<exists>N. \<forall>k>N. convergent_subseq s k n = acc_point s n" 
  proof-
    fix n
    show "\<exists>N. \<forall>k>N. convergent_subseq s k n = acc_point s n"
    proof(induction n)
      case 0
      then show ?case  by (metis (mono_tags, hide_lams) acc_point_def assms convergent_subseq_def is_closed_seq_def of_nat_0 ord_pos take_subseq_def zero_below_ord zero_vals)
    next
      case (Suc n)
      have "acc_point s (Suc n) = res_seq s (Suc n) 0 (Suc n)"
        by (simp add: acc_point_def)
      obtain k where kdef: "convergent_subseq_fun s a (Suc n) = k" by simp
      have "Suc n > 0" by simp
      then have "k > (convergent_subseq_fun s a n)" 
        using assms(1) assms(2) increasing_conv_subseq_fun_0 kdef by blast 
      then have " k > (convergent_subseq_fun s a n) \<and> (s k (Suc n)) = a (Suc n)" using kdef 
        by (metis (mono_tags, lifting) assms(1) assms(2) convergent_subseq_fun.simps(2) increasing_conv_induction_0_pre someI_ex)
      have "s k (Suc n) = a (Suc n)" 
        using \<open>convergent_subseq_fun s a n < k \<and> s k (Suc n) = a (Suc n)\<close> by blast
      then have "convergent_subseq s (Suc n) (Suc n) = a (Suc n)" 
        by (metis assms(2) convergent_subseq_def kdef take_subseq_def)
      then have "\<forall>l > n.  convergent_subseq s l (Suc n) = a (Suc n)" 
        by (metis Suc_leI \<open>is_closed_seq (convergent_subseq s)\<close> acc_point_closed assms(1) assms(2) convergent_sequence_res is_closed_simp le_refl r_Zp)
      then show ?case 
        using assms(2) by blast
    qed
  qed
qed
    


theorem Zp_is_compact:
  assumes "is_closed_seq s"
  shows "\<exists>s'. is_subseq_of s s' \<and> (converges_to s' (acc_point s))" 
  using assms convergent_subseq_is_subseq convergent_subsequence_is_convergent by blast

end
end