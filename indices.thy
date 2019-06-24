theory indices
imports Main
begin

(*Projection function from a list to which picks out the value at given index*)
definition project_at_index :: " nat \<Rightarrow> 'a list  \<Rightarrow> 'a" ("\<pi>\<^bsub>=_\<^esub>") where 
"project_at_index k as \<equiv> as ! k"

lemma project_at_index_simp[simp]:
"project_at_index k as \<equiv> as ! k"
  by (simp add: project_at_index_def)

(****************Canonical Map from finite sets of natural numbers to lists ***********************)

fun remove_smallest :: "nat set \<Rightarrow> nat \<Rightarrow> nat set" where 
"remove_smallest A 0 = A"|
"remove_smallest A (Suc n) = (remove_smallest A n) - {(LEAST s. s \<in> (remove_smallest A n))}"

lemma remove_smallest_subset[simp]: 
"remove_smallest A (Suc n) \<subseteq> (remove_smallest A n)"
  by auto

lemma remove_smallest_subset'[simp]: 
"remove_smallest A (Suc n) \<subseteq> A"
  by (metis less_imp_le lift_Suc_antimono_le remove_smallest.simps(1) 
      remove_smallest_subset zero_less_Suc)

lemma remove_smallest_card_infinite[simp]:
"\<And>A. infinite A \<Longrightarrow> infinite (remove_smallest A n)"
  apply(induction n)
  apply simp
  by simp

lemma remove_smallest_shrink[simp]:
  assumes "finite (A:: nat set) \<and> card A \<ge>1"
  shows "(LEAST s. s \<in> A) \<in> A"
  by (metis Inf_nat_def1 LeastI assms card_empty le_numeral_extra(2))

lemma remove_smallest_card_finite[simp]:
  assumes "finite A "
  shows "card (remove_smallest A 1) = (card A) - 1"
proof(cases "card A \<ge>1")
  case True
  then show ?thesis 
    by (simp add: assms)
next
  case False
  then show ?thesis 
    by (metis One_nat_def Suc_leI assms card_0_eq diff_le_self gr_zeroI 
        le_zero_eq remove_smallest.simps(1) remove_smallest_subset subset_empty)
qed

lemma remove_smallest_card_finite'[simp]:
"\<And>A. finite A  \<Longrightarrow> card (remove_smallest A n) = (card A) - n"
  apply(induction n)
   apply simp
proof-
  fix n A
  assume IH: "\<And>A. (finite A  \<Longrightarrow> card (remove_smallest A n) = card A - n)"
  show "finite A  \<Longrightarrow> card (remove_smallest A (Suc n)) = card A - Suc n"
  proof-
    assume A: "finite A"
    then have A0: "finite (remove_smallest A n) \<and> card (remove_smallest A n) = card A - n"
      using IH  Suc_leD 
      by (metis finite_subset remove_smallest.elims remove_smallest_subset')
    then have A1: " card (remove_smallest (remove_smallest A n) 1) = card (remove_smallest A n) - 1"
      using remove_smallest_card_finite[of "(remove_smallest A n)"] by auto 
    have "remove_smallest A (Suc n) = (remove_smallest (remove_smallest A n) 1)"
    proof-
      have 0: "remove_smallest A (Suc n) = (remove_smallest A n) - {(LEAST s. s \<in> (remove_smallest A n))}"
        by simp 
      have "(remove_smallest (remove_smallest A n) 1) =  (remove_smallest A n) - {(LEAST s. s \<in> (remove_smallest A n))}"
        by simp 
      then show ?thesis using 0 by auto 
    qed
    then show ?thesis 
      using A0 A1 
      by presburger
  qed
qed

lemma remove_smallest_subset'': 
"k \<le> n \<Longrightarrow> remove_smallest A n \<subseteq> remove_smallest A k"
  apply(induction n)
  apply blast
  using lift_Suc_antimono_le remove_smallest_subset 
  by blast

definition enumerate_by_order :: "nat set \<Rightarrow> nat \<Rightarrow> nat" ("enum") where
"enumerate_by_order A n =  (LEAST s. s \<in> (remove_smallest A n))"

lemma enumerate_in_A_0: 
  assumes "A \<noteq> {}"
  shows "enum A 0 \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> a \<ge> (enum A 0))"
 unfolding enumerate_by_order_def  
  by (metis (full_types) Inf_nat_def1 LeastI Least_le assms remove_smallest.simps(1))

lemma enumerate_step: 
  assumes "\<not> finite A \<or> (finite A \<and> (card A > (Suc  n)))"
  assumes "A' = A - {(enum A 0)}"
  shows "\<not> finite A' \<or> (finite A' \<and> (card A' > n))"
  using assms enumerate_in_A_0[of A]
  by force

lemma enumerate_in_set[simp]: 
"\<And>(A::nat set). \<not> finite A \<or> (finite A \<and> (card A > n)) \<Longrightarrow> (enum A n) \<in> A"
proof(induction n)
  case 0
  show ?case 
    by (metis "0.prems" card_empty enumerate_in_A_0 finite.intros(1) less_numeral_extra(3))
next
  case (Suc n)
  then show ?case 
    using enumerate_step[of "(remove_smallest A n)"] 
    by (metis card_empty enumerate_by_order_def enumerate_in_A_0 finite.emptyI not_gr0
        remove_smallest_card_finite' remove_smallest_card_infinite remove_smallest_subset'
        subsetCE wellorder_Least_lemma(1) zero_less_diff)
qed

lemma enum_remove_enum: 
"enum A n = enum (remove_smallest A n) 0" 
proof-
  have " enum (remove_smallest A n) 0 = (LEAST s. s \<in> (remove_smallest A n))"
    using enumerate_by_order_def[of "(remove_smallest A n)" 0]  
    by simp 
  then show ?thesis 
    using enumerate_by_order_def[of A n] by simp 
qed


lemma remove_smallest_enum: 
"remove_smallest A (Suc n) = A - (enum A ` {0..n})"
  apply(induction n)
  apply (simp add: enumerate_by_order_def)
proof-
  fix n
  assume IH: "remove_smallest A (Suc n) = A - enum A ` {0..n}"
  show "remove_smallest A (Suc (Suc n)) = A - enum A ` {0..Suc n}"
    using IH atLeast0_atMost_Suc enumerate_by_order_def
    by auto
qed

lemma remove_smallest_prop:
"(remove_smallest A (Suc k)) = (remove_smallest (A - {enum A 0}) k)"
  apply(induction k)
  apply (simp add: enumerate_by_order_def)
  by auto 


lemma enumerate_order_step: 
"enum A (Suc k) = enum (A - {enum A 0}) k"
proof-
  have 0:"enum A (Suc k) = enum (remove_smallest A (Suc k)) 0"
    using enum_remove_enum 
    by blast
  have 1: " enum (A - {enum A 0}) k = enum (remove_smallest (A - {enum A 0}) k) 0"
    using enum_remove_enum by blast
  show ?thesis 
    using 0 1  remove_smallest_prop 
    by auto
qed


lemma enumerate_order[simp]:
"\<And>A. \<not> finite A \<or> (finite A \<and> (card A > Suc k)) \<Longrightarrow> enum A k < enum A (Suc k)"
  apply(induction k)
   apply (metis Diff_iff empty_iff enum_remove_enum enumerate_by_order_def 
      enumerate_in_A_0 enumerate_in_set enumerate_step le_neq_trans remove_smallest.simps(1) 
      remove_smallest.simps(2) singletonI)
    using enumerate_order_step enumerate_step 
    by auto


lemma enumerate_order'[simp]: 
  assumes " \<not> finite A \<or> (finite A \<and> (card A > n))"
  assumes "n > k"
  shows "enum A n > enum A k"
proof-
  have "\<And>m A. \<not> finite A \<or> (finite A \<and> (card A > k + (Suc m))) \<Longrightarrow> enum A  (k + (Suc m)) > enum A k"
  proof-
    fix m
    show  "\<And>A. \<not> finite A \<or> (finite A \<and> (card A > k + (Suc m))) \<Longrightarrow> enum A  (k + (Suc m)) > enum A k"
      apply(induction m)
       apply (simp)
      by (metis add_Suc_right enumerate_order less_Suc_eq  less_trans)
  qed
  then show ?thesis using assms 
    by (metis gr0_implies_Suc less_imp_add_positive)
qed

lemma enumerate_by_order_eq:
  shows "enum A (Suc n)= (LEAST a. a \<in>  (A - (enum A ` {0..n})))"
proof-
  have "enum A (Suc n)=  (LEAST s. s \<in> remove_smallest A (Suc n))"
    unfolding  enumerate_by_order_def by auto 
  then show ?thesis using remove_smallest_enum[of A n]
    by metis  
qed

(*Given an input nat n, returns  the index list [0,...,n-1]*)
definition index_list :: "nat \<Rightarrow> nat list" where
"index_list n = map nat [0..(int n) -1]"

definition index_set :: "nat \<Rightarrow> nat set" where
"index_set n = set (index_list n)"

lemma index_list_length[simp]:
"length (index_list n) = n"
  unfolding index_list_def 
  by simp

lemma index_set_memI[simp]:
  assumes "(i::nat) < n"
  shows "i \<in> index_set n"
proof-
  have "i = index_list n ! i"
    by (simp add: assms index_list_def)
  then show ?thesis 
    by (metis assms index_list_length index_set_def nth_mem)
qed


lemma index_set_notmemI[simp]:
  assumes "(i::nat) \<ge> n"
  shows "i \<notin> index_set n"
  using assms index_list_def index_set_def 
  by auto

lemma index_set_induct:
"index_set (Suc n) = (index_set n) \<union> {n}"
  apply(induction n)
proof
  show "index_set (Suc 0) \<subseteq> index_set 0 \<union> {0}"
  by (metis One_nat_def Suc_inject Suc_le_D Suc_le_mono atMost_0 
      index_set_notmemI inf_sup_aci(5) insert_subset le0 le_SucE le_supI1 lessThan_Suc_atMost 
      lessThan_Suc_eq_insert_0 not_less_eq_eq order_refl subsetI)
  show "index_set 0 \<union> {0} \<subseteq> index_set (Suc 0)"
    using index_set_memI index_set_notmemI by blast
  fix n
  assume IH: "index_set (Suc n) = index_set n \<union> {n}"
  show "index_set (Suc (Suc n)) = index_set (Suc n) \<union> {Suc n}"
  proof
    show "index_set (Suc (Suc n)) \<subseteq> index_set (Suc n) \<union> {Suc n}"
      using IH 
      by (metis UnCI index_set_memI index_set_notmemI insertCI less_Suc_eq linorder_not_le subsetI)
    show "index_set (Suc n) \<union> {Suc n} \<subseteq> index_set (Suc (Suc n))"
      by (meson empty_subsetI index_set_memI index_set_notmemI insert_subset le_supI 
          less_Suc_eq linorder_not_le subsetI)
  qed
qed

(*Function from sets of nat to lists of nat*)

lemma index_list_hd[simp]:
"hd (index_list (Suc n)) = 0"
unfolding index_list_def 
  using upto.simps
  by auto

lemma index_list_index:
  assumes "k < n"
  shows "index_list n ! k = k"
  using assms 
  unfolding index_list_def 
  by simp


definition set_to_list :: "nat set \<Rightarrow> nat list" where
"set_to_list A = map (enum A) (index_list (card A))"

lemma set_to_list_hd:
  assumes "finite A"
  assumes "card A > 0"
  shows "hd (set_to_list A) = enum A 0"
  using assms unfolding set_to_list_def 
  by (metis Suc_pred card_0_eq card_gt_0_iff index_list_hd index_list_length 
      list.map_sel(1) list.size(3))

lemma set_to_list_ind[simp]:
  assumes "finite A"
  assumes "card A > n"
  shows "(set_to_list A) ! n = (enum A n)"
  unfolding set_to_list_def 
  by (simp add: assms(2) index_list_index)

lemma set_to_list_remove_smallest:
  assumes "finite A"
  assumes "card A \<ge> Suc (Suc n)"
  shows "(set_to_list A) ! (Suc n) = set_to_list (remove_smallest A 1) ! n"
  by (metis One_nat_def assms(1) assms(2) enum_remove_enum enumerate_step finite_subset lessI
      less_le_trans remove_smallest.simps(1) remove_smallest_prop remove_smallest_subset 
      set_to_list_ind)

lemma tl_id:
  assumes "length as = Suc n"
  assumes "length bs = n"
  assumes "\<And>k. k < n \<Longrightarrow> as ! (Suc k) = bs ! k"
  shows "tl as = bs"
  using assms 
  by (metis (mono_tags, lifting) Nitpick.size_list_simp(2) 
      Suc_inject nat.simps(3) nth_equalityI nth_tl)

lemma set_to_list_tail:
  assumes "finite A"
  assumes "card A > 0"
  shows "tl (set_to_list A) = set_to_list (remove_smallest A 1)"
proof-
  obtain n where n_def: "Suc n = card A"
    by (metis Suc_pred' assms(2))
  show ?thesis using tl_id[of "(set_to_list A)" n "set_to_list (remove_smallest A 1)"]
    by (metis Suc_lessI Suc_less_eq add_diff_cancel_left' assms(1) index_list_length le_less 
        length_map n_def plus_1_eq_Suc remove_smallest_card_finite set_to_list_def 
        set_to_list_remove_smallest)
qed

lemma set_to_list_size:
  assumes "finite A"
  shows "length (set_to_list A) = card A"
  using set_to_list_def by auto

lemma set_to_list_to_set: 
  shows "finite A \<Longrightarrow> set (set_to_list A) = A"
proof-
  have 0:"\<And>n A. finite A \<Longrightarrow> n = card A \<Longrightarrow> set (set_to_list A) = A"
  proof-
    fix n
    show "\<And> A. finite A \<Longrightarrow> n = card A \<Longrightarrow> set (set_to_list A) = A"
      apply(induction n)
      using set_to_list_size apply force
    proof-
      fix n
      fix A:: "nat set"
      assume IH: "(\<And>A. finite A \<Longrightarrow> n = card A \<Longrightarrow> set (set_to_list A) = A)"
      assume A0: "finite A"
      assume A1: "Suc n = card A"
      show "set (set_to_list A) = A"
      proof
        show "set (set_to_list A) \<subseteq> A"
          using set_to_list_ind[of A n]
          by (metis A0 enumerate_in_set in_set_conv_nth set_to_list_ind set_to_list_size subsetI)
        show "A \<subseteq> set (set_to_list A)"
        proof
          have "set (set_to_list A) = insert (hd (set_to_list A)) (set (tl (set_to_list A)))"
            by (metis A1 card_0_eq card_gt_0_iff list.exhaust_sel list.set(2) list.size(3) set_to_list_size zero_less_Suc)
          then have A2: "set (set_to_list A) = insert (hd (set_to_list A)) (set (set_to_list (remove_smallest A 1)))"
            using A0 A1 set_to_list_tail by auto
          fix x
          assume A3: "x \<in> A"
          show " x \<in> set (set_to_list A) "
          proof(cases "x = enum A 0")
            case True
            then show ?thesis 
              using A0 A1 in_set_conv_nth set_to_list_size 
              by fastforce
          next
            case False
            then have "x \<in> (remove_smallest A 1)"
              by (metis A3 DiffI One_nat_def atLeastAtMost_singleton empty_iff image_empty image_insert insertE remove_smallest_enum)
            then have "x \<in> (set (set_to_list (remove_smallest A 1)))"
              by (metis A0 A1 IH One_nat_def add_diff_cancel_left' finite_subset plus_1_eq_Suc remove_smallest.simps(1) remove_smallest_card_finite remove_smallest_subset)
            then show ?thesis 
              using A2 by blast
          qed
        qed
      qed
    qed
  qed
  assume "finite A"
  then show "set (set_to_list A) = A"
    using 0[of A "card A"]
    by auto 
qed

lemma set_to_list_inc[simp]:
  assumes "finite S"
  assumes "card S = n"
  assumes "j < n"
  assumes "i < j"
  shows "set_to_list S ! i < set_to_list S ! j"
  using assms(1) assms(2) assms(3) assms(4) 
  by auto

definition rank :: "nat set \<Rightarrow> nat \<Rightarrow> nat" where
"rank A s = (THE j. j < card A \<and> s = enum A j)"

lemma rank_enum:
  assumes "finite A"
  assumes "card A = n"
  shows "j < n \<Longrightarrow> rank A (enum A j) = j"
proof-
  assume A: "j < n"
  have "\<And>k. k < n \<Longrightarrow> (enum A j) = (enum A k) \<Longrightarrow> k = j"
    by (metis \<open>j < n\<close> assms(1) assms(2) enumerate_order' less_irrefl less_linear less_not_refl2)
  then show "rank A (enum A j) = j"
    using A  the_equality[of "(\<lambda>k. k < card A \<and> enum A j = enum A k)" j] 
    unfolding rank_def
    using assms(2) 
    by blast
qed

lemma enum_rank:
  assumes "finite A"
  assumes "card A = n"
  assumes "t \<in> A"
  shows "enum A (rank A t) = t"
  by (metis assms(1) assms(3) in_set_conv_nth rank_enum set_to_list_ind set_to_list_size set_to_list_to_set)

lemma rank_bound[simp]:
  assumes "finite A"
  assumes "card A = n"
  assumes "a \<in> A"
  shows  "rank A a < n"
  by (metis assms(1) assms(2) assms(3) in_set_conv_nth rank_enum set_to_list_ind 
      set_to_list_size set_to_list_to_set)

lemma set_to_list_induct:
  assumes "finite S"
  assumes "\<And>x. x \<in>S \<Longrightarrow> s > x"
  shows "j < card S \<Longrightarrow> enum S j = enum (insert s S) j"
proof(induction j)
  case 0
  then show ?case 
    by (metis assms(2) card_gt_0_iff empty_not_insert enumerate_in_A_0 insert_iff le_neq_implies_less linorder_not_le)
next
  case (Suc j)
  fix j
  assume IH: "(j < card S \<Longrightarrow> enum S j = enum (insert s S) j)"
  assume A: "Suc j < card S"
  show " enum S (Suc j) = enum (insert s S) (Suc j)"
  proof-
    have A0: "enum S j = enum (insert s S) j"
      using IH A Suc_lessD
      by blast
    have A1: "enum (insert s S) (Suc j) > enum S j"
      by (metis A Suc_lessD Suc_mono \<open>enum S j = enum (insert s S) j\<close> assms(1) 
          card_insert_disjoint enumerate_order insert_absorb)
    have A2: "enum (insert s S) (Suc j) \<in> S"
      by (metis A Suc_lessD Suc_mono assms(1) assms(2) card_insert_disjoint 
          enumerate_in_set enumerate_order insertE less_asym')
    obtain k where k_def: "k = rank S  (enum (insert s S) (Suc j))"
      by simp
    have k_j:"k > j"
      using k_def A1 
      by (metis A A2 Suc_lessD assms(1) enumerate_order' in_set_conv_nth not_less_iff_gr_or_eq 
        rank_enum set_to_list_ind set_to_list_size set_to_list_to_set)
    have k_bound:"k < card S"
      using A2 assms(1) k_def rank_bound by blast
    have enum_k: "enum S k = (enum (insert s S) (Suc j))"
      by (metis A2 assms(1) in_set_conv_nth k_def rank_enum set_to_list_ind 
            set_to_list_size set_to_list_to_set)
    have "k = Suc j"
    proof(rule ccontr)
      assume B: "k \<noteq>Suc j"
      then have B0: "k > Suc j"
        using Suc_lessI k_j 
        by blast
      then have "enum S k > enum S (Suc j)"
        by (simp add: k_bound)
      then have "enum (insert s S) (Suc j) > enum S (Suc j)"
        by (simp add: enum_k)
      obtain t where t_def: "t = enum S (Suc j)"
        by simp
      obtain i where i_def: "i = rank (insert s S) t"
        by simp
      have "i > j"
      proof(rule ccontr)
        assume "\<not> j < i"
        then have "enum (insert s S) i \<le> enum (insert s S) j"
          by (metis A assms(1) card_insert_disjoint enumerate_order' insert_absorb 
              less_SucI less_or_eq_imp_le not_less_iff_gr_or_eq)
        then have "enum (insert s S) i \<le> enum S j"
          using A0 by auto 
        then have "t \<le> enum S j"
          using enum_rank i_def 
          by (simp add: A assms(1) t_def)
        then show False 
          using A enumerate_order leD t_def by blast
      qed
      then show False 
        by (metis A Suc_lessI \<open>enum S (Suc j) < enum S k\<close> assms(1) enum_k enum_rank 
            enumerate_in_set enumerate_order' finite.insertI i_def insert_iff less_asym'
            rank_bound t_def)
    qed
    then show ?thesis 
      using enum_k by blast
  qed
qed
     
lemma set_to_list_induct':
  assumes "finite S"
  assumes "\<And>x. x \<in> S \<Longrightarrow>  s > x"
  shows "set_to_list (insert s S) = (set_to_list S) @ [s]"
proof-     
  obtain n where n_def[simp]: "card S = n"
    by simp 
  have 0: "take n (set_to_list (insert s S)) = take n (set_to_list S)"
  proof-
    have "\<And>j. j < n \<Longrightarrow> (set_to_list (insert s S))!j = (set_to_list S)!j"
      by (metis assms(1) assms(2) card_insert_disjoint finite.insertI insert_absorb 
          less_SucI n_def set_to_list_ind set_to_list_induct)      
    then show ?thesis 
      by (metis (no_types, lifting) assms(1) card_insert_le finite.insertI length_take
          lessI less_Suc_eq_le min.absorb2 n_def nth_equalityI nth_take set_to_list_size)
  qed
  have 1: "set_to_list (insert s S)  = (take n (set_to_list (insert s S)))@[set_to_list (insert s S)!n]"
  by (metis Suc_leI assms(1) assms(2) card_insert_disjoint finite.insertI hd_drop_conv_nth 
      infinite_growing insert_absorb insert_not_empty lessI n_def set_to_list_size take_all
      take_hd_drop)
  have 2: "s = set_to_list (insert s S)!n"
  by (smt "0" "1" assms(1) butlast_snoc card_insert_if finite.insertI in_set_conv_nth insertI1 
      length_append_singleton lessI less_Suc_eq_le n_def nat_less_le nth_butlast set_to_list_size
      set_to_list_to_set take_all)
  then show ?thesis 
    using "0" "1" assms(1) set_to_list_size by auto
qed

lemma set_to_list_one:
"set_to_list {0} = [0]"
  by (metis card_empty card_insert_disjoint enumerate_in_set finite.insertI hd_Cons_tl 
      insert_absorb insert_not_empty lessI list.size(3) set_to_list_hd 
      set_to_list_size singletonD tl_id)

lemma set_to_list_empty[simp]:
"set_to_list {} = []"
  using set_to_list_size by force

lemma index_set_zero[simp]:
"index_set 0 = {}"
  using index_set_notmemI by blast

lemma index_set_one[simp]: 
"index_set 1 = {0}"
  using index_set_induct by auto

lemma index_set_to_list_induct:
"set_to_list (index_set (Suc n)) = (set_to_list (index_set n))@[n]"
  apply(induction n)
  using index_set_one set_to_list_one apply auto[1]
proof-
  fix n
  assume IH: "set_to_list (index_set (Suc n)) = set_to_list (index_set n) @ [n]"
  show "set_to_list (index_set (Suc (Suc n))) = set_to_list (index_set (Suc n)) @ [Suc n]"
  proof-
    have "index_set (Suc (Suc n)) = (index_set (Suc n)) \<union> {Suc n}"
      by (simp add: index_set_induct)
    then show ?thesis
      using set_to_list_induct' 
      by (metis IH Nil_is_append_conv Un_insert_right card_infinite index_list_length
          index_set_notmemI length_0_conv length_map linorder_not_le not_Cons_self2 
          set_to_list_def sup_bot.right_neutral)
  qed
qed
    
lemma index_set_to_list:
  shows "set_to_list (index_set n) = index_list n"
  apply(induction n)
  using index_list_length apply fastforce
proof-
  fix n
  assume IH: "set_to_list (index_set n) = index_list n "
  show "set_to_list (index_set (Suc n)) = index_list (Suc n)"
  proof-
    have 0: "set_to_list (index_set (Suc n)) = (index_list n) @ [n]"
      using IH index_set_to_list_induct[of n]
      by auto
    have 1: "index_list (Suc n) = (index_list n) @ [n]"
    proof-
      have 10: "\<And>j. j < Suc n \<Longrightarrow>  index_list (Suc n) ! j= ((index_list n) @ [n]) ! j"
      proof-
        fix j
        assume A: "j < Suc n"
        show "index_list (Suc n) ! j= ((index_list n) @ [n]) ! j"
          apply(cases "j < n")
           apply (simp add: index_list_index nth_append)
          by (metis A index_list_index index_list_length less_SucE nth_append_length)
      qed
      have 11: "length (index_list (Suc n)) = Suc n"
        by simp
      have 12: "length ((index_list n) @ [n]) = Suc n"
        by simp
      then show ?thesis
        by (metis "10" "11" nth_equalityI)
    qed
    then show ?thesis 
      by (simp add: "0")
  qed
qed
    
(*Insert a in list as at index n*)
abbreviation initial_segment :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"initial_segment n as \<equiv> take n as"

abbreviation final_segment :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"final_segment n as \<equiv> drop n as"

lemma final_intitial_seg:
"as = (initial_segment n as) @ (final_segment n as)"
  by simp 

definition insert_at_ind :: " 'a list \<Rightarrow>'a \<Rightarrow> nat \<Rightarrow> 'a list" where
"insert_at_ind as a n= (initial_segment n as) @ (a#(final_segment n as))"

lemma insert_at_ind_length:
  assumes "n \<le> length as"
  shows "length (insert_at_ind as a n) = length as + 1"
  by (simp add: insert_at_ind_def)

lemma insert_at_ind_eq[simp]:
  assumes "n \<le> length as"
  shows "(insert_at_ind as a n)!n = a"
  unfolding insert_at_ind_def
  using assms 
  by (metis length_take min.absorb2 nth_append_length)

lemma insert_at_ind_eq'[simp]:
  assumes "n \<le> length as"
  assumes "k < n"
  shows "(insert_at_ind as a n)!k = as ! k"
  using assms 
  unfolding insert_at_ind_def
  by (simp add: nth_append)

lemma insert_at_ind_eq''[simp]:
  assumes "n < length as"
  assumes "k \<le> n"
  shows "(insert_at_ind as a k)!(Suc n) = as ! n"
  using assms 
  unfolding insert_at_ind_def
proof(cases "k < n")
  case T: True
  have "(insert_at_ind as a k)!n = (final_segment k as)! (n - (Suc k))"
    by (smt T Suc_diff_Suc assms(1) assms(2) diff_is_0_eq' insert_at_ind_def 
        length_take less_imp_le_nat less_numeral_extra(3) less_trans min.absorb2
        nth_Cons_Suc nth_append zero_less_diff)
  then show "(initial_segment k as @ a # final_segment k as) ! Suc n = as ! n"
    using assms unfolding project_at_index_def 
    by (smt T Cons_nth_drop_Suc Suc_diff_Suc add_diff_cancel_left' diff_Suc_Suc id_take_nth_drop 
        length_take less_Suc_eq less_imp_le_nat less_trans min.absorb2 nth_Cons_pos nth_append 
        order_less_irrefl plus_1_eq_Suc zero_less_diff)
next
  case False
  then show "(initial_segment k as @ a # final_segment k as) ! Suc n = as ! n"
    by (smt Cons_nth_drop_Suc Groups.add_ac(2) One_nat_def Suc_lessD add_diff_cancel_left'
        assms(1) assms(2) le_neq_implies_less length_take less_imp_le_nat min.absorb2 nth_Cons_0
        nth_Cons_Suc nth_append plus_1_eq_Suc)
qed


(*Given a set of indices, projects the input list to the sublist of elements  with those indices*)
fun proj_at_index_list :: "nat list \<Rightarrow> 'a list \<Rightarrow> 'a list"  where 
"proj_at_index_list [] as = []"|
"proj_at_index_list (x#xs) as = (as!x)#(proj_at_index_list xs as)"

definition proj_at_indices where
"proj_at_indices S as = proj_at_index_list (set_to_list S) as"

text\<open>Correctness of proj_at_indices\<close>

definition indices_of :: "'a list \<Rightarrow> nat set" where
"indices_of as = index_set (length as)"

lemma proj_at_index_listE:
  assumes "set L \<subseteq> indices_of as"
  shows "\<And>i. i < length L \<Longrightarrow> proj_at_index_list L as ! i = as ! (L ! i)"
  apply(induction L)
   apply simp
proof-
  fix a L
  fix i
  assume IH: " (\<And>i. i < length L \<Longrightarrow> proj_at_index_list L as ! i = as ! (L ! i))"
  assume "i < length (a # L)"
  show "proj_at_index_list (a # L) as ! i = as ! ((a # L) ! i)"
  proof(cases "i = 0")
    case True
    then show ?thesis 
      by simp 
  next
    case False
    then obtain k where k_def: "i = Suc k"
      by (meson lessI less_Suc_eq_0_disj)
    have 0: "proj_at_index_list (a # L) as = (as! a)# (proj_at_index_list L as)"
      by simp
    then have 1: "proj_at_index_list (a # L) as ! i =  (proj_at_index_list L as) ! k"
      by (simp add: k_def)
    then have 2: "proj_at_index_list (a # L) as ! i =  as ! (L ! k)"
      using IH \<open>i < length (a # L)\<close> k_def by auto
    then show ?thesis 
      by (simp add: k_def)
  qed
qed

lemma proj_at_indicesE: 
  assumes "S \<subseteq> indices_of as"
  assumes "i < card S"
  shows " proj_at_indices S as ! i = as ! (enum S i)"
proof-
  have 0: "(enum S i) = (set_to_list S)!i"
    by (metis assms(2) card_infinite not_less0 set_to_list_ind)    
  have 1: "proj_at_index_list (set_to_list S) as ! i = as ! ((set_to_list S) ! i)"  
    using proj_at_index_listE 
    by (metis assms(1) assms(2) card_infinite not_less_zero set_to_list_size set_to_list_to_set)   
  then show ?thesis 
    by (simp add: "0" proj_at_indices_def)
qed

lemma proj_at_index_list_length[simp]:
  assumes "set L \<subseteq> indices_of as"
  shows "length (proj_at_index_list L as) = length L"
  apply(induction L)
  apply simp
    by simp

lemma proj_at_indices_length:
  assumes "S \<subseteq> indices_of as"
  shows "length (proj_at_indices S as) = card S"
  using assms 
  unfolding proj_at_indices_def
  by (metis card_infinite empty_subsetI length_0_conv length_map list.set(1)
      proj_at_index_list_length set_to_list_def set_to_list_empty set_to_list_size 
      set_to_list_to_set)

(*Projects a list to the sublist of values not at the given index*)
definition proj_away_from_index :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" ("\<pi>\<^bsub>\<noteq>_\<^esub>")where
"proj_away_from_index n as = (initial_segment n as)@(final_segment (Suc n) as)"

text\<open>proj_away_from_index is an inverse to insert_at_ind\<close>

lemma insert_at_ind_project_away[simp]:
  assumes "k < length as"
  assumes "bs = (insert_at_ind as a k)"
  shows "\<pi>\<^bsub>\<noteq> k\<^esub> bs = as"
  by (smt Cons_nth_drop_Suc One_nat_def add.right_neutral add_Suc_right append_eq_conv_conj
      assms(1) assms(2)  insert_at_ind_def insert_at_ind_length length_take less_Suc_eq 
      less_imp_le_nat less_trans list.inject min.absorb2 proj_away_from_index_def)


definition fibred_cell :: "'a list set \<Rightarrow> ('a list \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list set" where 
"fibred_cell C P = {as . \<exists>x t. as = (t#x) \<and> x \<in> C \<and> (P x t)}"

definition fibred_cell_at_ind :: "nat \<Rightarrow> 'a list set \<Rightarrow> ('a list \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list set" where
"fibred_cell_at_ind n C P = {as . \<exists>x t. as = (insert_at_ind x t n) \<and> x \<in> C \<and> (P x t)}"

lemma fibred_cell_lengths:
  assumes "\<And>k. k \<in> C \<Longrightarrow> length k = n"
  shows "k \<in> (fibred_cell C P) \<Longrightarrow> length k = Suc n"
proof-
  assume "k \<in> (fibred_cell C P)"
  obtain x t where "k = (t#x) \<and> x \<in> C \<and> P x t"
  proof -
    assume a1: "\<And>t x. k = t # x \<and> x \<in> C \<and> P x t \<Longrightarrow> thesis"
    have "\<exists>as a. k = a # as \<and> as \<in> C \<and> P as a"
      using \<open>k \<in> fibred_cell C P\<close> fibred_cell_def by blast
    then show ?thesis
      using a1 by blast
  qed
  then show ?thesis 
    by (simp add: assms)
qed

lemma fibred_cell_at_ind_lengths:
  assumes "\<And>k. k \<in> C \<Longrightarrow> length k = n"
  assumes "k \<le> n"
  shows "c \<in> (fibred_cell_at_ind k C P) \<Longrightarrow> length c = Suc n"
proof-
  assume "c \<in> (fibred_cell_at_ind k C P)"
  then obtain x t where "c = (insert_at_ind x t k) \<and> x \<in> C \<and> (P x t)"
    using assms
    unfolding fibred_cell_at_ind_def 
    by blast
  then show ?thesis 
    by (simp add: assms(1) assms(2) insert_at_ind_length)
qed

lemma project_fibred_cell[simp]:
  assumes "\<And>k. k \<in> C \<Longrightarrow> length k = n"
  assumes "k < n"
  assumes "\<forall>x \<in> C. \<exists>t. P x t"
  shows "\<pi>\<^bsub>\<noteq> k\<^esub> ` (fibred_cell_at_ind k C P) = C"
proof
  show "\<pi>\<^bsub>\<noteq>k\<^esub> ` fibred_cell_at_ind k C P \<subseteq> C"
  proof
    fix x
    assume x_def: "x \<in> \<pi>\<^bsub>\<noteq>k\<^esub> ` fibred_cell_at_ind k C P"
    then obtain c where c_def: "x = \<pi>\<^bsub>\<noteq>k\<^esub> c \<and> c \<in>  fibred_cell_at_ind k C P"
      by blast
    then obtain y t where yt_def: "c = (insert_at_ind y t k) \<and> y \<in> C \<and> (P y t)"
      using assms
      unfolding fibred_cell_at_ind_def 
      by blast
    have 0: "x =\<pi>\<^bsub>\<noteq>k\<^esub> c"
      by (simp add: c_def)
    have 1: "y =\<pi>\<^bsub>\<noteq>k\<^esub> c"
      using yt_def  assms(1) assms(2)
      by fastforce
    have 2: "x = y" using 0 1 by auto 
    then show "x \<in> C"
      by (simp add: yt_def)
  qed
  show "C \<subseteq> \<pi>\<^bsub>\<noteq>k\<^esub> ` fibred_cell_at_ind k C P"
  proof fix x
    assume A: "x \<in> C"
    obtain t where t_def: "P x t"
      using assms A by auto 
    then show "x \<in> \<pi>\<^bsub>\<noteq>k\<^esub> ` fibred_cell_at_ind k C P"
    proof -
      have f1: "\<forall>a n A as. initial_segment n as @ (a::'a) # final_segment n as \<notin> A \<or> as \<in> \<pi>\<^bsub>\<noteq>n\<^esub> ` A \<or> \<not> n < length as"
        by (metis (no_types) imageI insert_at_ind_def insert_at_ind_project_away)
      have "\<forall>n. \<exists>as a. initial_segment n x @ t # final_segment n x = insert_at_ind as a n \<and> as \<in> C \<and> P as a"
        by (metis (full_types) A insert_at_ind_def t_def)
      then have "\<forall>n. initial_segment n x @ t # final_segment n x \<in> {insert_at_ind as a n |as a. as \<in> C \<and> P as a}"
        by blast
      then have "x \<in> \<pi>\<^bsub>\<noteq>k\<^esub> ` {insert_at_ind as a k |as a. as \<in> C \<and> P as a}"
        using f1 by (metis (lifting) A assms(1) assms(2))
      then show ?thesis
        by (simp add: fibred_cell_at_ind_def)
    qed
  qed
qed


end
