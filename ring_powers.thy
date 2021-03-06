theory ring_powers
  imports "HOL-Algebra.Chinese_Remainder" "HOL-Library.Permutations" function_ring indices
"HOL-Algebra.Generated_Rings"
begin

text\<open>Powers of a ring\<close>

text\<open>(R_list n R) produces the list [R, ... , R] of length n\<close>

fun R_list :: "nat \<Rightarrow> 'a ring \<Rightarrow> ('a ring) list" where
"R_list 0 R = []"|
"R_list (Suc n) R = R#(R_list n R)"

text\<open>Cartesian powers of a ring\<close>

definition cartesian_power :: "'a ring \<Rightarrow> nat \<Rightarrow> ('a list) ring" ("Pow _ _") where
"cartesian_power R n \<equiv> RDirProd_list (R_list n R)"

lemma R_list_project[simp]:
  assumes "i < n"
  shows "(\<pi>\<^bsub>=i\<^esub> (R_list n R)) = R"
proof-
  have "\<And>i. i < n \<Longrightarrow> (\<pi>\<^bsub>=i\<^esub> (R_list n R)) = R"
  apply(induction n)
  apply blast
  proof-
    show "\<And>n i. (\<And>i. i < n \<Longrightarrow> \<pi>\<^bsub>=i\<^esub> (R_list n R) = R) \<Longrightarrow> i < Suc n \<Longrightarrow> \<pi>\<^bsub>=i\<^esub> (R_list (Suc n) R) = R"
    proof-
      fix n
      fix i
      assume IH: "\<And>i. (i < n \<Longrightarrow> \<pi>\<^bsub>=i\<^esub> (R_list n R) = R)"
      assume A: "i < Suc n"
      show "\<pi>\<^bsub>=i\<^esub> (R_list (Suc n) R) = R "
      proof(cases "i = 0")
        case True
        then show ?thesis by simp 
      next
        case False   
        then have "\<pi>\<^bsub>=i\<^esub> (R_list (Suc n) R) =  \<pi>\<^bsub>=(i-1)\<^esub> (R_list n R) "
          by auto
        then show ?thesis using A IH 
          using False by auto
      qed
    qed
  qed
  then show ?thesis using assms 
    by blast
qed 

lemma R_list_length: 
"length (R_list n R) = n"
  apply(induction n) by auto 

lemma cartesian_power_car_memI[simp]:
  assumes "length as = n" 
  assumes "set as \<subseteq> carrier R" 
  shows "as \<in> carrier (Pow R n)"
proof-
  have "(\<And>i. i < length (R_list n R) \<Longrightarrow>  as ! i \<in> carrier (\<pi>\<^bsub>=i\<^esub> (R_list n R)))"
  proof-
    fix i assume A: "i < length (R_list n R)"
    then have "i < n"
      by (simp add: R_list_length)
    then have "as ! i \<in> carrier R"
      using assms nth_mem by blast
    then show "as ! i \<in> carrier (\<pi>\<^bsub>=i\<^esub> (R_list n R))"
      by (metis R_list_project \<open>i < n\<close>)
  qed
  then show ?thesis 
    using RDirProd_list_carrier_memI[of as "(R_list n R)"] 
    by (simp add: R_list_length assms(1) cartesian_power_def)
qed

lemma cartesian_power_car_memI'[simp]:
  assumes "length as = n"
  assumes "(\<And>i. i < length (R_list n R) \<Longrightarrow>  as ! i \<in> carrier (\<pi>\<^bsub>=i\<^esub> (R_list n R)))"
  shows "as \<in> carrier (Pow R n)"
  using assms   RDirProd_list_carrier_memI[of as "(R_list n R)"] 
  by (simp add: R_list_length cartesian_power_def)

lemma cartesian_power_car_memI''[simp]:
  assumes "length as = n"
  assumes "\<And>i. i < length (R_list n R) \<Longrightarrow>  as ! i \<in> carrier R"
  shows "as \<in> carrier (Pow R n)"
  by (metis R_list_length R_list_project assms(1) assms(2) cartesian_power_car_memI')

lemma cartesian_power_car_memE[simp]:
  assumes "as \<in> carrier (Pow R n)"
  shows "length as = n"
  using RDirProd_list_carrier_mem(1) 
  by (metis R_list_length assms cartesian_power_def)
  
lemma cartesian_power_car_memE'[simp]:
  assumes "as \<in> carrier (Pow R n)"
  assumes "i < n"
  shows " as ! i \<in> carrier R"
  using assms  RDirProd_list_carrier_mem(2) 
  by (metis R_list_length R_list_project cartesian_power_def project_at_index_simp)
    
lemma insert_at_ind_pow_car[simp]:
  assumes "length as = n"
  assumes "as \<in> carrier (Pow R n)"
  assumes "a \<in> carrier R"
  assumes "k \<le> n"
  shows "(insert_at_ind as a k) \<in> carrier (Pow R (Suc n))"
  apply(rule cartesian_power_car_memI')
  apply (metis Groups.add_ac(2) assms(1) assms(4) insert_at_ind_length plus_1_eq_Suc)
proof-
  fix i
  assume A: "i < length (R_list (Suc n) R)"
  have P0: "carrier (\<pi>\<^bsub>=i\<^esub> (R_list (Suc n) R)) = carrier R"
    by (metis A R_list_length R_list_project)
  have P1: "i \<le> n" 
    by (metis A R_list_length less_Suc_eq_le)
  have "insert_at_ind as a k ! i \<in> carrier R "
    apply(cases "i = k")
    apply (simp add: assms(1) assms(3) assms(4))
  proof(cases "i < k")
    case True
    then show ?thesis 
    by (metis assms(1) assms(2) assms(4) cartesian_power_car_memE' insert_at_ind_eq' less_le_trans)
  next
    case False
    then show ?thesis 
      using insert_at_ind_eq''[of "i-1" as k] 
      by (smt P1 add_diff_inverse_nat assms(1) assms(2) assms(3) cartesian_power_car_memE' diff_less
          insert_at_ind_eq le_neq_implies_less less_Suc_eq_le less_imp_diff_less less_one 
          linorder_neqE_nat plus_1_eq_Suc)
  qed
  then show "insert_at_ind as a k ! i \<in> carrier (\<pi>\<^bsub>=i\<^esub> (R_list (Suc n) R))"
    using P0 
    by blast
qed

lemma insert_at_ind_pow_not_car[simp]:
  assumes "k \<le>n"
  assumes "length x = n"
  assumes "(insert_at_ind x a k) \<in> carrier (Pow R (Suc n))" 
  shows "x \<in> carrier Pow R n"
apply(rule cartesian_power_car_memI')
  using assms 
  apply blast
    using assms 
    by (metis R_list_length R_list_project Suc_mono cartesian_power_car_memE' insert_at_ind_eq'
      insert_at_ind_eq'' le_eq_less_or_eq less_SucI not_less_iff_gr_or_eq)

lemma insert_at_ind_pow_not_car'[simp]:
  assumes "k \<le>n"
  assumes "length x = n"
  assumes "x \<notin> carrier Pow R n"
  shows "(insert_at_ind x a n) \<notin> carrier (Pow R (Suc n))"
  by (metis assms(2) assms(3) insert_at_ind_pow_not_car lessI less_Suc_eq_le)

text\<open>Cartesian products of subsets\<close>

abbreviation cartesian_product :: "('a list) set \<Rightarrow> ('a list) set \<Rightarrow> ('a list) set" where
"cartesian_product A B \<equiv> {xs. \<exists>as \<in> A. \<exists>bs \<in> B. xs = as@bs}"

lemma cartesian_product_closed[simp]:
  assumes "A \<subseteq> carrier (Pow R n)"
  assumes "B \<subseteq> carrier (Pow R m)"
  shows "cartesian_product A B \<subseteq> carrier (Pow R (n + m))"
proof
  fix x 
  assume "x \<in> cartesian_product A B "
  then obtain as bs where as_bs_def: "x = as@bs \<and> as \<in> A \<and> bs \<in> B"
    by blast
  show "x \<in> carrier Pow R (n + m) "
    apply(rule cartesian_power_car_memI'')
     apply (metis as_bs_def assms cartesian_power_car_memE length_append subsetD)
       by (metis R_list_length as_bs_def  add_diff_inverse_nat assms
           cartesian_power_car_memE cartesian_power_car_memE' nat_add_left_cancel_less nth_append
           subset_iff)
qed

lemma cartesian_product_carrier: 
"cartesian_product (carrier (Pow R n)) (carrier (Pow R m)) =  carrier (Pow R (n + m))"
proof
  show "cartesian_product (carrier Pow R n) (carrier Pow R m) \<subseteq> carrier Pow R (n + m)"
    using cartesian_product_closed[of "(carrier Pow R n)" R n "(carrier Pow R m) " m] 
    by blast
  show "carrier (Pow R (n + m)) \<subseteq> cartesian_product (carrier Pow R n) (carrier Pow R m)"
  proof
    fix x
    assume A: "x \<in> carrier (Pow R (n + m))"
    
      
    have 0: "take n x \<in> carrier (Pow R n)"
      apply(rule cartesian_power_car_memI'')  
       apply (metis A cartesian_power_car_memE le_add1 length_take min.absorb2)
         by (metis A R_list_length add.commute cartesian_power_car_memE' 
            nth_take trans_less_add2) 
    have 1: "drop n x \<in> carrier (Pow R m)"
      apply(rule cartesian_power_car_memI'')  
        apply (metis A add_diff_cancel_left' cartesian_power_car_memE length_drop)
          by (metis A R_list_length cartesian_power_car_memE cartesian_power_car_memE' le_add1 nat_add_left_cancel_less nth_drop)
    show "x \<in> cartesian_product (carrier Pow R n) (carrier Pow R m)"
      using 0 1 
      by (metis (mono_tags, lifting) append_take_drop_id mem_Collect_eq)
qed    





text\<open>Higher function rings\<close>
qed

abbreviation ring_pow_function_ring ("Fun\<^bsub>_\<^esub> _") where
"ring_pow_function_ring n R \<equiv> function_ring (carrier (Pow R n)) R"

definition substitute :: "'a ring \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>  ('a list \<Rightarrow> 'a) \<Rightarrow> 'a  \<Rightarrow> ('a list \<Rightarrow> 'a) " ("sub\<^bsub>_\<^esub> _ _") where
"substitute R m n f c = restrict (\<lambda> as. f (insert_at_ind as c n)) (carrier (Pow R m))"

lemma sub_domain:
  assumes "f \<in> carrier (Fun\<^bsub>Suc k\<^esub> R)"
  assumes "a \<in> carrier R"
  assumes "n \<le>k"
  shows "(substitute R k n f a)  \<in> carrier (Fun\<^bsub>k\<^esub> R)"
  apply(rule function_ring_car_memI)
proof-
  show "\<And>x. x \<in> carrier Pow R k \<Longrightarrow> (substitute R k n f a)  x \<in> (carrier R)"  
  proof-
    fix x
    assume A: "x \<in> carrier Pow R k"
    show "(substitute R k n f a)  x \<in> (carrier R)"
    proof(cases "n = k")
      case True
      then have "(substitute R k n f a)  x = f (insert_at_ind x a n)"
        by (metis (no_types, lifting) A restrict_apply' substitute_def)
        
      then show "(substitute R k n f a) x \<in> carrier R"
        by (metis A True assms(1) assms(2) cartesian_power_car_memE
            function_ring_car_simp insert_at_ind_pow_car order_refl)
    next
      case False
      then have F0: "(substitute R k n f a)  x = f (insert_at_ind x a n)"
        unfolding substitute_def 
        using assms   
        by (meson A restrict_apply')  
      have "(insert_at_ind x a n) \<in> carrier (Pow R (Suc k))"
        using A assms insert_at_ind_pow_car[of x k R a n]  
        by (simp add: cartesian_power_def)
      then show "(substitute R k n f a) x \<in> carrier R"
        by (metis F0 assms(1) function_ring_car_simp)
    qed
  qed
  show "\<And>x. x \<notin> carrier Pow R k \<Longrightarrow> (substitute R k n f a)  x = undefined"
  proof-
    fix x
    assume "x \<notin> carrier Pow R k"
    show "(substitute R k n f a) x = undefined"
      unfolding substitute_def 
      by (meson \<open>x \<notin> carrier Pow R k\<close> restrict_apply)
  qed
qed

text\<open>Pullbacks preserve ring power functions\<close>

lemma fun_struct_maps:
"struct_maps (Pow R n) R = carrier (Fun\<^bsub>n\<^esub> R)"
proof
  show "struct_maps (Pow R n) R \<subseteq> carrier Fun\<^bsub>n\<^esub> R"
    by (smt function_ring_car_memI struct_mapsE(1) struct_mapsE(2) subsetI)
  show "carrier (Fun\<^bsub>n\<^esub> R) \<subseteq> struct_maps (Pow R n) R"
    by (smt function_ring_car_simp function_ring_not_car_simp struct_mapsI subsetI)
qed

lemma pullback_fun_closed:
  assumes "f \<in> struct_maps (Pow R n) (Pow R m)"
  assumes "g \<in> carrier (Fun\<^bsub>m\<^esub> R)"
  shows "pullback (Pow R n) f g \<in> carrier (Fun\<^bsub>n\<^esub> R)"
  using assms(1) assms(2) fun_struct_maps pullback_closed by blast

text\<open>Projections of ring powers on each other\<close>

definition pow_proj ::  "'a ring \<Rightarrow> (nat set) \<Rightarrow> nat  \<Rightarrow> ('a list)  \<Rightarrow> ('a list) " where
"pow_proj R S n = restrict (proj_at_indices S) (carrier (Pow R n))"

lemma pow_proj_is_map[simp]:
  assumes "S \<subseteq> (index_set n)"
  shows "pow_proj R S n \<in> struct_maps (Pow R n) (Pow R (card S))"
proof(rule struct_mapsI)
  show "\<And>x. x \<in> carrier (Pow R n) \<Longrightarrow> pow_proj R S n x \<in> carrier (Pow R (card S))"
  proof-
    fix x
    assume A: "x \<in> carrier (Pow R n)" 
    show "pow_proj R S n x \<in> carrier (Pow R (card S))"
      apply(rule cartesian_power_car_memI'')
       apply (metis A assms cartesian_power_car_memE indices_of_def pow_proj_def 
          proj_at_indices_length restrict_apply')
    proof-
      fix i
      assume B: "i < length (R_list (card S) R)"
      have C: "x ! enum S i \<in> carrier R"
        by (metis A B R_list_length assms cartesian_power_car_memE'   
            enumerate_in_set index_set_notmemI not_le subsetD)
      show "pow_proj R S n x ! i \<in> carrier R "
        using proj_at_indicesE[of S x i]
        unfolding pow_proj_def 
        by (metis A B C R_list_length assms cartesian_power_car_memE indices_of_def restrict_apply)
    qed
  qed
  show "\<And>x. x \<notin> carrier Pow R n \<Longrightarrow> pow_proj R S n x = undefined"
    by (simp add: cartesian_power_def pow_proj_def)
qed

text\<open>inclusion of function rings into one another\<close>

text\<open>Includes R^|S| into R^n by pulling back along the projection R^n => R^|S| at indices S \<close>

definition ring_pow_inc :: "'a ring \<Rightarrow> (nat set) \<Rightarrow> nat  \<Rightarrow> ('a list  \<Rightarrow> 'a) => ('a list  \<Rightarrow> 'a)  " where
"ring_pow_inc R S n f = pullback (Pow R n) (pow_proj R S n) f"

lemma ring_pow_inc_is_fun:
  assumes "S \<subseteq> (index_set n)"
  assumes "f \<in> carrier (Fun\<^bsub>card S\<^esub> R)"
  shows "ring_pow_inc R S n f \<in> carrier (Fun\<^bsub>n\<^esub> R)"
  by (metis assms(1) assms(2) pow_proj_is_map pullback_fun_closed ring_pow_inc_def)

text\<open>The "standard" inclusion of powers of function rings into one another\<close>

abbreviation std_proj:: "'a ring \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list) \<Rightarrow> ('a list)" where 
"std_proj R n m \<equiv> pow_proj R (index_set m) n"


lemma std_proj_id[simp]: 
  assumes "m \<le> n"
  assumes "as \<in> carrier (Pow R n)"
  assumes "i < m"
  shows "std_proj R n m as ! i = as ! i"
  unfolding pow_proj_def using assms proj_at_indicesE[of "(index_set m)" as i] 
  by (metis cartesian_power_car_memE dual_order.strict_trans in_set_conv_nth index_list_index 
      index_list_length index_set_def index_set_to_list indices_of_def le_eq_less_or_eq
      proj_at_index_listE proj_at_indices_def restrict_apply subsetI)



abbreviation std_inc:: "'a ring \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list  \<Rightarrow> 'a)  => ('a list  \<Rightarrow> 'a)" where
"std_inc R n m f \<equiv> ring_pow_inc R (index_set m) n f"

lemma std_proj_is_map[simp]:
  assumes "m \<le> n"
  shows "std_proj R n m \<in> struct_maps (Pow R n) (Pow R m)"
  by (metis (mono_tags, hide_lams) assms index_list_length index_set_memI index_set_notmemI 
      index_set_to_list length_map  not_le  not_less_iff_gr_or_eq order_refl order_trans 
      pow_proj_is_map set_to_list_def subsetD subsetI)

text\<open>Polynomial rings\<close>

definition var :: "'a ring \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list \<Rightarrow> 'a)" where
"var R n i = restrict (\<lambda>x.  x!i) (carrier (Pow R n))"

lemma var_in_car:
  assumes "i < n"
  shows "var R n i \<in> carrier (Fun\<^bsub>n\<^esub> R)"
  apply(rule function_ring_car_memI)
  apply (simp add: assms cartesian_power_def var_def)
  by (simp add: cartesian_power_def var_def)

lemma varE[simp]: 
  assumes "i < n"
  assumes "x \<in> carrier (Pow R n)"
  shows "var R n i x = x ! i"
  unfolding var_def project_at_index_def
  using  assms(2) 
  by (meson restrict_apply')
 

lemma std_inc_of_var:
  assumes "i < n"
  assumes "n \<le>m"
  shows "std_inc R m n (var R n i) =  (var R m i)"
  apply(rule ext)
proof-
  fix x
  show "std_inc R m n (var R n i) x = var R m i x"
    apply(cases "x \<in> carrier (Pow R m )")
  proof-
    show "x \<in> carrier Pow R m \<Longrightarrow> std_inc R m n (var R n i) x = var R m i x"
    proof-
      assume A: "x \<in> carrier Pow R m"
      have "(restrict (proj_at_indices (index_set n)) (carrier Pow R m)) x =  ((proj_at_indices (index_set n)) x)"
        by (meson A restrict_apply')
      then have B: "std_inc R m n (var R n i) x = (var R n i) ((proj_at_indices (index_set n)) x)"
        unfolding ring_pow_inc_def pow_proj_def pullback_def s_comp_def
        by (metis A comp_apply restrict_apply)
      have C: "var R m i x = x ! i"
        using assms A varE[of i m x R]   
        by linarith        
      have D: "enum (index_set m) i = i"
        using assms 
        by (metis index_list_index index_list_length index_set_to_list 
            length_map less_le_trans nth_map set_to_list_def)
      have E: "(\<lambda>as\<in>carrier Pow R m. as ! i) (proj_at_indices (index_set m) x) = (var R m i) ((proj_at_indices (index_set m)) x)"
        by (metis project_at_index_simp restrict_apply var_def)
      have F: "index_set m \<subseteq> index_set (length x)"
        using A cartesian_power_car_memE 
        by blast
      have G: "(var R m i) ((proj_at_indices (index_set m)) x) = x !enum (index_set m) i"

        unfolding var_def project_at_index_def 
        using F proj_at_indicesE[of "(index_set m)" x i]   
        by (smt A C D E card.infinite cartesian_power_car_memE index_list_index index_list_length 
            index_set_def index_set_to_list indices_of_def not_less_zero nth_equalityI
            proj_at_index_list_length proj_at_indicesE proj_at_indices_def proj_at_indices_length
            set_to_list_ind)
      then show "std_inc R m n (var R n i) x = var R m i x" 
        by (metis A B C \<open>restrict (proj_at_indices (index_set n)) (carrier Pow R m) x =
               proj_at_indices (index_set n) x\<close> assms(1) assms(2) pow_proj_def std_proj_id 
              std_proj_is_map struct_mapsE(1) varE)
    qed
    show "x \<notin> carrier Pow R m \<Longrightarrow> std_inc R m n (var R n i) x = var R m i x"
      by (metis pullback_def restrict_apply ring_pow_inc_def s_comp_def var_def)
  qed
qed
      
text\<open>defintion of polynomial ring\<close>

definition var_set :: "'a ring \<Rightarrow> nat \<Rightarrow> ('a list \<Rightarrow> 'a) set" where
"var_set R n = var R n ` {0..n-1}"

lemma var_setE:
  assumes "f \<in> var_set R n"
  obtains i where "f = var R n i \<and> i \<in> {0 .. n-1}"
  by (metis assms imageE that var_set_def)

lemma var_setI:
  assumes "i \<in> {0..n-1}"
  assumes  "f = var R n i"
  shows "f \<in> var_set R n"
  using assms(1) assms(2) var_set_def by fastforce

definition constant_ring where
"constant_ring R n = (constant_function (carrier (Pow R n)) ` (carrier R)) "

lemma constant_ring_subring:
  assumes "cring R"
  shows "subring (constant_ring R n) (Fun\<^bsub>n\<^esub> R)"
  apply(rule ring.subringI)
  using assms cring_imp_Fun_is_cring 
  using cring.axioms(1)
  apply blast
    unfolding constant_ring_def 
    apply (simp add: image_subset_iff)
  proof-
    show "\<one>\<^bsub>Fun\<^bsub>n\<^esub> R\<^esub> \<in> constant_function (carrier Pow R n) ` carrier R"
      unfolding constant_function_def 
      using function_ring_def 
      by (smt assms cring.axioms(1) cring.cring_simprules(6) cring_imp_Fun_is_cring fun_struct_maps 
      image_iff mem_Collect_eq restrict_ext ring.function_oneE struct_maps_def)
    show "\<And>h. h \<in> constant_function (carrier Pow R n) ` carrier R \<Longrightarrow> \<ominus>\<^bsub>Fun\<^bsub>n\<^esub> R\<^esub> h \<in> constant_function (carrier Pow R n) ` carrier R"
      using assms constant_function_minus cring.cring_simprules(3) by fastforce
    show "\<And>h1 h2.
       h1 \<in> constant_function (carrier Pow R n) ` carrier R \<Longrightarrow>
       h2 \<in> constant_function (carrier Pow R n) ` carrier R \<Longrightarrow> h1 \<otimes>\<^bsub>Fun\<^bsub>n\<^esub> R\<^esub> h2 \<in> constant_function (carrier Pow R n) ` carrier R"
      by (smt assms constant_function_mult cring.cring_simprules(5) image_iff)
    show " \<And>h1 h2.
       h1 \<in> constant_function (carrier Pow R n) ` carrier R \<Longrightarrow>
       h2 \<in> constant_function (carrier Pow R n) ` carrier R \<Longrightarrow> h1 \<oplus>\<^bsub>Fun\<^bsub>n\<^esub> R\<^esub> h2 \<in> constant_function (carrier Pow R n) ` carrier R"
      by (smt assms constant_function_add cring.cring_simprules(1) image_iff)
  qed
      
definition polynomial_functions where
"polynomial_functions R n = generate_ring (Fun\<^bsub>n\<^esub> R) ((var_set R n) \<union> (constant_ring R n)) "


end