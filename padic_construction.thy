theory padic_construction
imports Main "HOL-Number_Theory.Residues" "HOL-Algebra.RingHom" "HOL-Algebra.IntRing"
begin

type_synonym padic_int = "nat \<Rightarrow> int"

(*Inverse Limit construction of p-adics*)

definition res :: "int \<Rightarrow> int \<Rightarrow> int" where 
"res n m = m mod n"

lemma res_hom_0:
  assumes "n > 1"
  shows "res n \<in> ring_hom \<Z> (residue_ring n)"
proof(rule ring_hom_memI)
  have R: "residues n" 
    by (simp add: assms residues_def) 
  show "\<And>x. x \<in> carrier \<Z> \<Longrightarrow> res n x \<in> carrier (residue_ring n)"
    using assms res_def residues.mod_in_carrier residues_def by auto 
  show " \<And>x y. x \<in> carrier \<Z> \<Longrightarrow> y \<in> carrier \<Z> \<Longrightarrow>
   res n (x \<otimes>\<^bsub>\<Z>\<^esub> y) = res n x \<otimes>\<^bsub>residue_ring n\<^esub> res n y"
    by (simp add: R res_def residues.mult_cong) 
  show "\<And>x y. x \<in> carrier \<Z> \<Longrightarrow>
               y \<in> carrier \<Z> \<Longrightarrow>
         res n (x \<oplus>\<^bsub>\<Z>\<^esub> y) = res n x \<oplus>\<^bsub>residue_ring n\<^esub> res n y"
    by (simp add: R res_def residues.res_to_cong_simps(1)) 
  show "res n \<one>\<^bsub>\<Z>\<^esub> = \<one>\<^bsub>residue_ring n\<^esub>" 
    by (simp add: R res_def residues.res_to_cong_simps(4)) 
qed

lemma res_hom_1:
  assumes "n > 1"
  assumes "m > 1"
  assumes "n dvd m"
  shows "res n \<in> ring_hom (residue_ring m) (residue_ring n)"
proof(rule ring_hom_memI)
  have 0: "residues n" 
    by (simp add: assms(1) residues_def) 
  have 1: "residues m" 
    by (simp add: assms(2) residues_def) 
  show "\<And>x. x \<in> carrier (residue_ring m) \<Longrightarrow> res n x \<in> carrier (residue_ring n)" 
    using assms(1) res_def residue_ring_def by auto 
  show "\<And>x y. x \<in> carrier (residue_ring m) \<Longrightarrow>
               y \<in> carrier (residue_ring m) \<Longrightarrow> 
          res n (x \<otimes>\<^bsub>residue_ring m\<^esub> y) = res n x \<otimes>\<^bsub>residue_ring n\<^esub> res n y"
    using 0 1 assms by (metis mod_mod_cancel res_def residues.mult_cong residues.res_mult_eq) 
  show "\<And>x y. x \<in> carrier (residue_ring m) 
        \<Longrightarrow> y \<in> carrier (residue_ring m) 
        \<Longrightarrow> res n (x \<oplus>\<^bsub>residue_ring m\<^esub> y) = res n x \<oplus>\<^bsub>residue_ring n\<^esub> res n y"
    using 0 1 assms by (metis mod_mod_cancel res_def residues.add_cong residues.res_add_eq) 
  show "res n \<one>\<^bsub>residue_ring m\<^esub> = \<one>\<^bsub>residue_ring n\<^esub>" 
    by (simp add: assms(1) res_def residue_ring_def) 
qed

lemma res_id:
  assumes "x \<in> carrier (residue_ring n)"
  assumes "n \<ge>0"
  shows "res n x = x"
proof(cases "n=0")
  case True
  then show ?thesis 
    by (simp add: res_def) 
next
  case False 
  have 0: "x \<ge>0"  
    using assms(1)  by (simp add: residue_ring_def)
  have 1: "x < n" 
    using assms(1) residue_ring_def by auto 
  have "x mod n = x" 
    using 0 1 by simp 
  then show ?thesis 
    using res_def by auto
qed

lemma res_hom_p:
  assumes "(n::nat) \<ge> m"
  assumes "m >0"
  assumes "prime p"
  shows "res (p^m) \<in> ring_hom (residue_ring (p^n)) (residue_ring (p^m))"
proof(rule res_hom_1)
  show " 1 < p^n" using assms  
    using prime_gt_1_int by auto
  show "1 < p^m" 
    by (simp add: assms(2) assms(3) prime_gt_1_int)
  show "p ^ m dvd p ^ n" using assms(1) 
    by (simp add: dvd_power_le) 
qed


definition padic_set :: "nat \<Rightarrow> padic_int set" where
"padic_set p = {(f::padic_int) .(\<forall>(m::nat). (f m) \<in> (carrier (residue_ring (p^m))))
                                    \<and>(\<forall>(n::nat) (m::nat). (n > m \<longrightarrow> (res (p^m) (f n) = (f m)))) }"



lemma padic_set_simp0:
  assumes "f \<in> padic_set p"
  shows "(f m) \<in> (carrier (residue_ring (p^m)))" 
  using assms padic_set_def by auto  


lemma padic_set_simp1:
  assumes "f \<in> padic_set p"
  assumes "n \<ge> m"
  assumes "prime p"
  shows "res (p^m) (f n) = (f m)"
proof(cases "n=m")
  case True
  have "(f m) \<in> carrier (residue_ring (p^m))" 
    using assms padic_set_simp0 by blast 
  then have "res (p^m) (f m) = (f m)" 
    by (simp add: res_def residue_ring_def) 
  then show ?thesis 
    using True by blast 
next
  case False
  then show ?thesis
    using assms(1) assms(2) padic_set_def by auto 
qed

lemma padic_set_simp2:
  assumes "prime p"
  assumes "f \<in> (padic_set p)"
  shows "f 0 = 0"
proof-
  have "f 0 \<in> carrier (residue_ring 1)" 
    using assms(1) padic_set_simp0 
    by (metis assms(2) of_nat_1 power_0) 
  then show ?thesis 
    using residue_ring_def  by simp 
qed

lemma padic_set_mem:
  fixes f :: "padic_int"
  assumes "\<And>m. (f m) \<in> (carrier (residue_ring (p^m)))"
  assumes "(\<And>(m::nat) n. (n > m \<Longrightarrow> (res (p^m) (f n) = (f m))))"
  shows "f \<in> padic_set p"
  by (simp add: assms(1) assms(2) padic_set_def) 



definition padic_add :: "nat \<Rightarrow> padic_int \<Rightarrow> padic_int \<Rightarrow> padic_int " 
  where "padic_add p f g \<equiv> (\<lambda> n. (f n) \<oplus>\<^bsub>(residue_ring (p^n))\<^esub> (g n))"

lemma padic_add_simp:
"(padic_add p f g) n = (f n) \<oplus>\<^bsub>(residue_ring (p^n))\<^esub> (g n)"
  by (simp add: padic_add_def) 


definition padic_mult :: "nat \<Rightarrow> padic_int \<Rightarrow> padic_int \<Rightarrow> padic_int" 
  where "padic_mult p f g \<equiv> (\<lambda> n. (f n) \<otimes>\<^bsub>(residue_ring (p^n))\<^esub> (g n))"

lemma padic_mult_simp: 
"(padic_mult p f g) n = (f n) \<otimes>\<^bsub>(residue_ring (p^n))\<^esub> (g n)"
  by (simp add: padic_mult_def) 


(*padic multiplicative unit*)

definition padic_one :: "nat \<Rightarrow> padic_int" where
"padic_one p \<equiv> (\<lambda>n.(if n=0 then 0 else 1))"

lemma padic_one_simp:
  assumes "n >0"
  shows "padic_one p n =  \<one>\<^bsub>residue_ring (p^n)\<^esub>"
  by (simp add: assms padic_one_def residue_ring_def) 

(*padic additive unit*)

definition padic_zero :: "nat \<Rightarrow> padic_int" where
"padic_zero p \<equiv> (\<lambda>n. 0)"

lemma padic_zero_simp:
"padic_zero p n = \<zero>\<^bsub>residue_ring (p^n)\<^esub>" 
  by (simp add: padic_zero_def residue_ring_def) 



(*padic unary minus*)

definition padic_uminus :: "nat \<Rightarrow>  padic_int \<Rightarrow>  padic_int" where
"padic_uminus p f \<equiv> \<lambda> n. \<ominus>\<^bsub>residue_ring (p^n)\<^esub> (f n)"

lemma padic_uminus_simp:
"padic_uminus p f n\<equiv> \<ominus>\<^bsub>residue_ring (p^n)\<^esub> (f n)"
   by (simp add: padic_uminus_def) 

(*padic simp rules bundled together*)

lemma padic_simps:
"padic_zero p n = \<zero>\<^bsub>residue_ring (p^n)\<^esub>" 
"padic_uminus p f n \<equiv> \<ominus>\<^bsub>residue_ring (p^n)\<^esub> (f n)"
"(padic_mult p f g) n = (f n) \<otimes>\<^bsub>(residue_ring (p^n))\<^esub> (g n)"
"(padic_add p f g) n = (f n) \<oplus>\<^bsub>(residue_ring (p^n))\<^esub> (g n)"
"n>0 \<Longrightarrow>padic_one p n =  \<one>\<^bsub>residue_ring (p^n)\<^esub>"
  apply (simp add: padic_zero_simp) 
  apply (simp add: padic_uminus_simp)
  apply (simp add: padic_mult_def)
  apply (simp add: padic_add_simp)  
  using padic_one_simp by auto

(*padic_one is an element of the padics:*)

lemma padic_one_mem:
  assumes "prime p"
  shows "padic_one p \<in> padic_set p"
proof(rule padic_set_mem)
  show "\<And>m. padic_one p m \<in> carrier (residue_ring (int p ^ m))"
  proof-
    fix m::nat
    show "padic_one p m \<in> carrier (residue_ring (int p ^ m)) " 
      by (simp add: assms padic_one_def prime_gt_1_int residue_ring_def)
  qed
  show "\<And>m n. m < n \<Longrightarrow> res (int p ^ m) (padic_one p n) = padic_one p m"
  proof- 
    fix m n::nat
    assume "m <n"
    show "res (int p ^ m) (padic_one p n) = padic_one p m"
    proof(cases "m = 0")
      case True
      then have 0:"padic_one p m = 0" 
        by (simp add: padic_one_def)
      have 1: "padic_one p n = 1" 
        using \<open>m < n\<close> padic_one_def by auto
      then show ?thesis using res_def 0 1 
        by (simp add: True)
    next
      case False 
      then have 0: "padic_one p m = 1"
        by (simp add: padic_one_def)
      have 1: "padic_one p n = 1"
        using \<open>m < n\<close> padic_one_def by auto
      show ?thesis using res_def 0 1 
        by (metis \<open>\<And>m. padic_one p m \<in> carrier (residue_ring (int p ^ m))\<close>
            of_nat_0_le_iff res_id zero_le_power)
    qed
  qed
qed
(*padic_zero is an element of the padics *)

lemma padic_zero_mem:
  assumes "p \<noteq>0"
  shows "padic_zero p \<in> padic_set p" 
      proof (rule padic_set_mem)
        show "\<And>m. padic_zero p m \<in> carrier (residue_ring (int p ^ m))" 
          using assms padic_zero_def residue_ring_def by auto 
        show "\<And>m n. m < n \<Longrightarrow> res (int p ^ m) (padic_zero p n) = padic_zero p m"         
          using \<open>\<And>m. padic_zero p m \<in> carrier (residue_ring (int p ^ m))\<close>
            padic_zero_def res_id by auto 
      qed
(*padic uminus maps to residue_ring*)

lemma res_1_prop:
"\<ominus>\<^bsub>residue_ring 1\<^esub> \<zero>\<^bsub>residue_ring 1\<^esub> =  \<zero>\<^bsub>residue_ring 1\<^esub>"
proof-
  let ?x = "\<zero>\<^bsub>residue_ring 1\<^esub>"
  let ?y = "\<ominus>\<^bsub>residue_ring 1\<^esub> \<zero>\<^bsub>residue_ring 1\<^esub>"
  let ?G = "add_monoid (residue_ring 1)"
  have P0:" ?x \<oplus>\<^bsub>residue_ring 1\<^esub> ?x =  ?x" 
    by (simp add: residue_ring_def) 
  have P1: "?x \<in> carrier (residue_ring 1)" 
    by (simp add: residue_ring_def) 
  have "?x \<in> carrier ?G \<and> ?x \<otimes>\<^bsub>?G\<^esub> ?x = \<one>\<^bsub>?G\<^esub> \<and> ?x \<otimes>\<^bsub>?G\<^esub> ?x = \<one>\<^bsub>?G\<^esub>"
    using P0 P1  by auto 
  then show ?thesis 
    by (simp add: m_inv_def a_inv_def residue_ring_def) 
qed

lemma res_1_zero:
  "res 1 n = 0" 
  by (simp add: res_def) 

lemma padic_uminus_closed:
  assumes "f \<in> padic_set p"
  assumes "prime p"
  shows "(padic_uminus p f) \<in> padic_set p"
proof(rule padic_set_mem)
  show "\<And>m. padic_uminus p f m \<in> carrier (residue_ring (int p ^ m))"
  proof-
    fix m
    show "padic_uminus p f m \<in> carrier (residue_ring (int p ^ m))"
    proof-
      have P0: "padic_uminus p f m = \<ominus>\<^bsub>residue_ring (p^m)\<^esub> (f m)" 
        using padic_uminus_def by simp 
      then show ?thesis 
      proof(cases "m=0")
        case True
        then have 0:"f m \<in> carrier (residue_ring (p^m))" 
          using assms(1) padic_set_simp0 by blast   
        have 1:"carrier (residue_ring (p^m)) = {0}" 
          using True residue_ring_def by simp 
        have "f m = 0" 
          using 0 1  by blast 
        then have "padic_uminus p f m = \<ominus>\<^bsub>residue_ring (p^m)\<^esub> 0"
          using P0  by auto 
        then have "padic_uminus p f m = 0"
          using res_1_prop by (simp add: True residue_ring_def) 
        then show ?thesis 
          using "0" \<open>f m = 0\<close> by auto 
      next
        case False
        then have 0:"f m \<in> carrier (residue_ring (p^m))"  
          using assms(1) padic_set_simp0 by blast
        have 1: "residues (p^m)" 
          using False assms(2) less_irrefl prime_gt_1_int residues.intro by auto
        then show ?thesis 
          using P0 by (simp add: residues.mod_in_carrier residues.res_neg_eq) 
      qed
    qed
  qed
  show "\<And>m n. m < n \<Longrightarrow> res (int p ^ m) (padic_uminus p f n) = padic_uminus p f m" 
  proof-
    fix m n::nat
    assume "m < n"
    show "res (int p ^ m) (padic_uminus p f n) = padic_uminus p f m" 
    proof(cases "m=0")
      case True
      then have 0: "res (int p ^ m) (padic_uminus p f n) = 0" using res_1_zero 
        by simp
      have "f m = 0" 
        using assms True padic_set_def residue_ring_def 
        by (metis (mono_tags, hide_lams) infinite_descent linorder_neqE_nat 
            linorder_not_le not_less_zero  padic_set_simp1 power_0 
            prime_gt_1_nat res_1_zero semiring_char_0_class.of_nat_eq_1_iff) 
      then have 1: "padic_uminus p f m = 0" using res_1_prop assms
        by (simp add: True padic_uminus_def residue_ring_def) 
      then show ?thesis using 0 1
        by simp 
      next
        case False
        have 0: "f n \<in> carrier (residue_ring (p^n)) "
          using assms(1) padic_set_simp0 by auto
        have 1: "padic_uminus p f n = \<ominus>\<^bsub>residue_ring (p^n)\<^esub> (f n)" using padic_uminus_def
          by simp 
        have 2: "padic_uminus p f m = \<ominus>\<^bsub>residue_ring (p^m)\<^esub> (f m)" using  False padic_uminus_def
          by simp 
        have 3: "res (p ^ m) \<in> ring_hom (residue_ring (p ^ n)) (residue_ring (p ^ m))" 
          using res_hom_p False \<open>m < n\<close> assms(2) by auto 
        have 4: " cring (residue_ring (p ^ n))" 
          using \<open>m < n\<close> assms(2) prime_gt_1_int residues.cring residues.intro by auto 
        have 5: " cring (residue_ring (p ^ m))" 
          using False assms(2) prime_gt_1_int residues.cring residues.intro by auto
        have  "ring_hom_cring (residue_ring (p ^ n))  (residue_ring (p ^ m)) (res (p ^ m))"
          using 3 4 5 UnivPoly.ring_hom_cringI by blast  
        then show ?thesis using 0  1 2 ring_hom_cring.hom_a_inv 
          by (metis \<open>m < n\<close> assms(1) assms(2) less_imp_le of_nat_power padic_set_simp1) 
      qed
    qed
  qed

(*padic set is closed under multiplication*)

lemma res_1_mult:
  assumes "x \<in> carrier (residue_ring 1)"
  assumes "y \<in> carrier (residue_ring 1)"
  shows "x \<otimes>\<^bsub>residue_ring 1\<^esub> y = 0"
  by (simp add: residue_ring_def)

lemma padic_mult_closed:
  assumes "f \<in> (padic_set p)"
  assumes "g \<in> (padic_set p)"
  assumes "prime p"
  shows "(padic_mult p f g)\<in> (padic_set p)"
proof(rule padic_set_mem)
  show "\<And>m. padic_mult p f g m \<in> carrier (residue_ring (int p ^ m))"
  proof-
    fix m
    show "padic_mult p f g m \<in> carrier (residue_ring (int p ^ m))"
    proof(cases "m=0")
      case True 
      have "padic_mult p f g m = 0" using padic_set_simp0 res_1_mult assms  
        by (metis True of_nat_1 padic_mult_simp power_0) 
      then show ?thesis 
        by (simp add: True residue_ring_def) 
    next
      case False show ?thesis 
        by (simp add: assms(3) padic_mult_def prime_gt_0_nat residue_ring_def) 
    qed
  qed
  show "\<And>m n. m < n \<Longrightarrow> res (int p ^ m) (padic_mult p f g n) = padic_mult p f g m"
  proof-
      fix m n::nat
      assume A: "m < n"
      then show "res (int p ^ m) (padic_mult p f g n) = padic_mult p f g m"
      proof(cases "m=0")
        case True
        then have 0: "padic_mult p f g m = 0"
        proof -
          have "padic_mult p f g m \<in> {0..0}"
            by (metis (no_types) True \<open>\<And>m. padic_mult p f g m \<in> carrier (residue_ring (int p ^ m))\<close>
                cancel_comm_monoid_add_class.diff_cancel partial_object.select_convs(1) 
                residue_ring_def semiring_normalization_rules(32))
          then show ?thesis
            by simp
        qed 
        have 1: "res (int p ^ m) (padic_mult p f g n) = 0"
          using True by (simp add: res_def) 
        then show ?thesis 
          using 0 1 by simp
      next
        case False
        have 0:"res (p ^ m) \<in> ring_hom (residue_ring (int (p ^ n))) (residue_ring (int (p ^ m)))"
          using A res_hom_p assms  False by auto  
        have 1:"f n \<in> carrier (residue_ring (p^n))" 
          using assms(1) padic_set_simp0 by auto 
        have 2:"g n \<in> carrier (residue_ring (p^n))" 
          using assms(2) padic_set_simp0 by auto 
        have 3: "res (int p ^ m) (f n \<otimes>\<^bsub>residue_ring (int (p ^ n))\<^esub> g n) 
                    = f m \<otimes>\<^bsub>residue_ring (int (p ^ m))\<^esub> g m" 
          using  "0" "1" "2" A assms(1) assms(2) assms(3) less_imp_le of_nat_power padic_set_simp1 
            by (simp add: assms(2) ring_hom_mult)
        then show ?thesis
            using ring_hom_mult padic_simps[simp] by auto 
        qed
    qed
qed


(*padic valuation. Maps 0 to -1 for now, otherwise is correct*)

definition padic_val :: "nat \<Rightarrow>  padic_int \<Rightarrow> int"  where
"padic_val p f \<equiv> if (f = padic_zero p) then -1 else int (LEAST k::nat. (f (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc k))\<^esub>)"

(*characterization of padic_val on nonzero elements*)

lemma val_of_nonzero:
  assumes "f \<in> padic_set p"
  assumes "f \<noteq> padic_zero p"
  assumes "prime p"
  shows "f (nat (padic_val p f) + 1) \<noteq>  \<zero>\<^bsub>residue_ring (p^((nat (padic_val p f) + 1)))\<^esub>"
        "f (nat (padic_val p f)) =  \<zero>\<^bsub>residue_ring (p^((nat (padic_val p f))))\<^esub>"
proof-
  let ?vf = "padic_val p f"
  have 0: "?vf =int (LEAST k::nat. (f (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc k))\<^esub>)"
    using assms(2) padic_val_def by auto    
  have 1: "(\<exists> k::nat. (f (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc k))\<^esub>)"
    proof-
      obtain k where 1: "(f k) \<noteq> (padic_zero p k)"
        using assms(2) by (meson ext) 
      have 2: "k \<noteq> 0" 
      proof
        assume "k=0"
        then have "f k = 0"
          using assms padic_set_simp2 by blast 
        then show False 
          using padic_zero_def 1 by simp 
      qed
        then obtain m where "k = Suc m"
      by (meson lessI less_Suc_eq_0_disj)
    then have "(f (Suc m)) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc m))\<^esub>" 
      using "1" padic_zero_simp by simp    
    then show ?thesis 
      by auto
  qed
  then have "(f (Suc (nat ?vf))) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc (nat ?vf)))\<^esub>" 
    using 0 by (metis (mono_tags, lifting) LeastI_ex nat_int) 
  then show "f (nat (padic_val p f) + 1) \<noteq>  \<zero>\<^bsub>residue_ring (p^((nat (padic_val p f) + 1)))\<^esub>" 
    using 0 1 by simp
  show "f (nat (padic_val p f)) =  \<zero>\<^bsub>residue_ring (p^((nat (padic_val p f))))\<^esub>"
  proof(cases "(padic_val p f) = 0")
    case True
    then show ?thesis 
      using assms(1) assms(3) padic_set_simp2 residue_ring_def by auto 
  next
    case False 
    have "\<not> f (nat (padic_val p f)) \<noteq> \<zero>\<^bsub>residue_ring (int (p ^ nat (padic_val p f)))\<^esub>"
    proof
      assume "f (nat (padic_val p f)) \<noteq> \<zero>\<^bsub>residue_ring (int (p ^ nat (padic_val p f)))\<^esub>"
      obtain k where " (Suc k) = (nat (padic_val p f))" using False 
        using "0" gr0_conv_Suc by auto
      then have "?vf  \<noteq> int (LEAST k::nat. (f (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc k))\<^esub>)"
        using False by (metis (mono_tags, lifting) Least_le 
          \<open>f (nat (padic_val p f)) \<noteq> \<zero>\<^bsub>residue_ring (int (p ^ nat (padic_val p f)))\<^esub>\<close>
            add_le_same_cancel2 nat_int not_one_le_zero plus_1_eq_Suc)
      then show False  using "0" by blast
    qed    
    then show "f (nat (padic_val p f)) = \<zero>\<^bsub>residue_ring (int (p ^ nat (padic_val p f)))\<^esub>" by auto
  qed
qed

lemma below_val_zero:
  assumes "prime p"
  assumes "x \<in> (padic_set p)"
  assumes "x (Suc n) \<noteq>  \<zero>\<^bsub>residue_ring (p^(Suc n))\<^esub>"
  shows  "of_nat n \<ge> (padic_val p x )"
proof(cases "x = padic_zero p")
  case True
  then show  ?thesis  
    using assms(3) padic_zero_simp by blast 
next
  case False
  then have "padic_val p x = int (LEAST k::nat. x (Suc k) \<noteq> \<zero>\<^bsub>residue_ring (p ^ Suc k)\<^esub>)"
    using padic_val_def by auto  
  then show "of_nat n \<ge> (padic_val p x )"
    by (metis (mono_tags, lifting) Least_le assms(3) nat_int nat_le_iff)
qed

lemma  zero_below_val:
  assumes "prime p"
  assumes "x \<in> padic_set p"
  assumes "n \<le> padic_val p x"
  shows  "x n =  \<zero>\<^bsub>residue_ring (p^n)\<^esub>"
proof(cases "n=0")
  case True
  then have  "x 0 \<in>carrier (residue_ring (p^0))" 
    using assms(2) padic_set_simp0  by blast
  then show ?thesis 
    by (simp add: True residue_ring_def) 
  next
    case False 
    show ?thesis 
    proof(cases "x = padic_zero p")
      case True 
      then show ?thesis 
        by (simp add: padic_zero_simp)
      next
        case F: False
        then have A: "padic_val p x = int (LEAST k::nat. (x (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc k))\<^esub>)" 
          using padic_val_def by auto
        have "\<not> (x n) \<noteq> \<zero>\<^bsub>residue_ring (p^n)\<^esub>"
        proof
          assume "(x n) \<noteq> \<zero>\<^bsub>residue_ring (p^n)\<^esub>"
          obtain k where "n = Suc k" 
            using False old.nat.exhaust by auto
          then have "k \<ge> padic_val p x" using A 
            by (metis (mono_tags, lifting) Least_le
                \<open>x n \<noteq> \<zero>\<^bsub>residue_ring (int (p ^ n))\<^esub>\<close> int_eq_iff 
                nat_le_iff)
          then have "n > padic_val p x" 
            using \<open>n = Suc k\<close> by linarith
          then show False using assms(3) 
            by linarith
        qed
        then show ?thesis 
          by simp
      qed
qed
(*zero is the only element with valuation equal to -1*)

lemma val_zero:
 assumes P: "f \<in> (padic_set p)"   
 shows "padic_val p f = -1 \<longleftrightarrow>  (f = (padic_zero p))"
proof
  show "padic_val p f = -1 \<Longrightarrow>  (f = (padic_zero p))"
  proof
    assume A:"padic_val p f = -1" 
    fix k
    show "f k = padic_zero p k" 
    proof-
      have  "f k \<noteq> padic_zero p k \<Longrightarrow> False"
      proof-
        assume A0: " f k \<noteq> padic_zero p k"
        have False
        proof-
          have "f 0 \<in> carrier (residue_ring 1)" using P padic_set_def 
            by (metis (no_types, lifting) mem_Collect_eq of_nat_1 power_0) 
          then have "f 0 = \<zero>\<^bsub>residue_ring (p^0)\<^esub>"  
            by (simp add: residue_ring_def) 
          then have "k>0" 
            using A0 gr0I padic_zero_def 
            by (metis padic_zero_simp)    
          then have "(LEAST k. 0 < k \<and> f (Suc k) \<noteq> padic_zero p (Suc k)) \<ge>0 " 
            by simp
          then have "padic_val p f \<ge>0" 
            using A0 padic_val_def by auto 
          then show ?thesis  using A0 by (simp add: A)  
        qed
        then show ?thesis by blast
      qed
      then show ?thesis 
        by blast
    qed
  qed
  assume B: "f = padic_zero p"
  then show "padic_val p f = -1" 
  using padic_val_def by simp 
qed

(*val turns multiplication into integer addition on nonzero elements*)

lemma val_prod:
  assumes  "prime p"
  assumes "f \<in> (padic_set p)" 
  assumes "g \<in> (padic_set p)"
  assumes "f \<noteq> padic_zero p"
  assumes "g \<noteq> padic_zero p"
  shows "padic_val p (padic_mult p f g) = padic_val p f + padic_val p  g"
proof-
  let ?vp = "padic_val p (padic_mult p f g)"
  let ?vf = "padic_val p f"
  let ?vg = "padic_val p g"
  have 0: "f (nat ?vf + 1) \<noteq>  \<zero>\<^bsub>residue_ring (p^(nat ?vf + 1))\<^esub>" 
    using assms(2) assms(4) val_of_nonzero  assms(1) by blast 
  have 1: "g (nat ?vg + 1) \<noteq>  \<zero>\<^bsub>residue_ring (p^(nat ?vg + 1))\<^esub>" 
    using assms(3) assms(5) val_of_nonzero assms(1) by blast 
  have 2: "f (nat ?vf) =  \<zero>\<^bsub>residue_ring (p^(nat ?vf))\<^esub>" 
    using assms(1) assms(2) assms(4) val_of_nonzero(2) by blast 
  have 3: "g (nat ?vg) =  \<zero>\<^bsub>residue_ring (p^(nat ?vg))\<^esub>" 
    using assms(1) assms(3) assms(5) val_of_nonzero(2) by blast
  let ?nm = "((padic_mult p f g) (Suc (nat (?vf + ?vg))))"    
  let ?n = "(f (Suc (nat (?vf + ?vg))))"    
  let ?m = "(g (Suc (nat (?vf + ?vg))))"  
  have A: "?nm = ?n \<otimes>\<^bsub>residue_ring (p^((Suc (nat (?vf + ?vg))))) \<^esub> ?m" 
    using padic_mult_def  by simp 
  have 5: "f (nat ?vf + 1) = res (p^(nat ?vf + 1)) ?n" 
  proof-
    have "(Suc (nat (?vf + ?vg))) \<ge> (nat ?vf + 1)" 
      by (simp add: assms(5) padic_val_def)
    then have "f (nat ?vf + 1) =  res (p^(nat ?vf + 1)) (f (Suc (nat (?vf + ?vg))))" 
      using assms(1) assms(2) padic_set_simp1 by presburger
    then show ?thesis by auto 
  qed
  have 6: "f (nat ?vf) = res (p^(nat ?vf)) ?n" 
   using add.commute assms(1) assms(2) assms(5) int_nat_eq nat_int 
        nat_le_iff not_less_eq_eq padic_set_simp1 padic_val_def plus_1_eq_Suc  by auto 
  have 7: "g (nat ?vg + 1) = res (p^(nat ?vg + 1)) ?m"  
  proof-
    have "(Suc (nat (?vf + ?vg))) \<ge> (nat ?vg + 1)" 
      by (simp add: assms(4) padic_val_def)
    then have "g (nat ?vg + 1) =  res (p^(nat ?vg + 1)) (g (Suc (nat (?vf + ?vg))))" 
      using assms(1) assms(3) padic_set_simp1 by presburger
    then show ?thesis by auto 
  qed
  have 8: "g (nat ?vg) = res (p^(nat ?vg)) ?m"
  proof-
    have "(Suc (nat (?vf + ?vg))) \<ge> (nat ?vg)" 
      by (simp add: assms(4) padic_val_def)
    then have "g (nat ?vg) =  res (p^(nat ?vg)) (g (Suc (nat (?vf + ?vg))))" 
      using assms(1) assms(3) padic_set_simp1 by presburger
    then show ?thesis by auto 
  qed 
  have 9: "f (nat ?vf) = 0" 
    by (simp add: "2" residue_ring_def) 
  have 10: "g (nat ?vg) = 0" 
    by (simp add: "3" residue_ring_def) 
  have 11: "f (nat ?vf + 1) \<noteq> 0" 
    using "0" residue_ring_def by auto 
  have 12: "g (nat ?vg + 1) \<noteq>0" 
    using "1" residue_ring_def by auto 
  have 13:"\<exists>i. ?n = i*p^(nat ?vf) \<and> \<not> p dvd (nat i)" 
  proof-
    have  "res (p^(nat ?vf)) (?n) = f (nat ?vf)" 
      by (simp add: "6") 
    then have P0: "res (p^(nat ?vf)) (?n) = 0" 
      using "9" by linarith 
    have "res (p^(nat ?vf + 1)) (?n) = f (nat ?vf + 1)" 
      using "5" by linarith 
    then have P1: "res (p^(nat ?vf + 1)) (?n) \<noteq> 0"
      using "11" by linarith 
    have P2: "?n mod (p^(nat ?vf)) = 0" 
      using P0 res_def by auto 
    have P3: "?n mod (p^(nat ?vf + 1)) \<noteq>  0" 
      using P1 res_def by auto 
    have "p^(nat ?vf) dvd ?n" 
      using P2 by auto 
    then obtain i where A0:"?n = i*(int p^(nat ?vf))" 
      by fastforce 
    have "?n \<in> carrier (residue_ring (p^(Suc (nat (?vf + ?vg)))))" 
      using assms(2) padic_set_simp0 by blast 
    then have "?n \<ge>0" 
      by (simp add: residue_ring_def) 
    then have NN:"i \<ge> 0" 
    proof-
      have S0:"?n \<ge>0" 
        using \<open>0 \<le> f (Suc (nat (padic_val p f + padic_val p g)))\<close> by blast
      have S1:"(int p^(nat ?vf)) > 0" 
        using assms(1) by auto
      have "\<not> i<0"
      proof
        assume "i < 0"
        then have "?n < 0" 
          using S1 A0 by (metis mult.commute times_int_code(1) zmult_zless_mono2)
        then show False 
          using S0  by linarith
      qed
      then show ?thesis by auto 
    qed
    have A1: "\<not> p dvd (nat i)"
    proof
      assume "p dvd nat i"
      then obtain j where "nat i = j*p" 
        by fastforce 
      then have "?n = j*p*(p^(nat ?vf))" using A0 NN 
        by (metis int_nat_eq of_nat_mult of_nat_power) 
      then show False 
        using P3 by auto 
    qed
    then show ?thesis 
      by (metis (no_types, lifting) A0 NN int_nat_eq of_nat_mult of_nat_power) 
  qed
  have 14:"\<exists> i. ?m = i*p^(nat ?vg) \<and> \<not> p dvd (nat i)"
  proof-
    have  "res (p^(nat ?vg)) (?m) = g (nat ?vg)" 
      by (simp add: "8") 
    then have P0: "res (p^(nat ?vg)) (?m) = 0" 
      using "10" by linarith 
    have "res (p^(nat ?vg + 1)) (?m) = g (nat ?vg + 1)" 
      using "7" by auto 
    then have P1: "res (p^(nat ?vg + 1)) (?m) \<noteq> 0"
      using "12" by linarith 
    have P2: "?m mod (p^(nat ?vg)) = 0"
      using P0 res_def by auto 
    have P3: "?m mod (p^(nat ?vg + 1)) \<noteq>  0" 
      using P1 res_def by auto 
    have "p^(nat ?vg) dvd ?m" 
      using P2 by auto 
    then obtain i where A0:"?m = i*(int p^(nat ?vg))" 
      by fastforce 
    have "?m \<in> carrier (residue_ring (p^(Suc (nat (?vf + ?vg)))))" 
      using assms(3) padic_set_simp0 by blast 
    then have S0: "?m \<ge>0" 
      by (simp add: residue_ring_def) 
    then have NN:"i \<ge> 0" 
    proof-
      have S1:"(int p^(nat ?vg)) > 0" 
        using assms(1) by auto
      have "\<not> i<0"
      proof
        assume "i < 0"
        then have "?m < 0" 
          using S1 A0 by (metis mult.commute times_int_code(1) zmult_zless_mono2)
        then show False 
          using S0  by linarith
      qed
      then show ?thesis by auto 
    qed    
    have A1: "\<not> p dvd (nat i)"
    proof
      assume "p dvd nat i"
      then obtain j where "nat i = j*p" 
        by fastforce 
      then have "?m = j*p*(p^(nat ?vg))" using A0 NN 
        by (metis int_nat_eq of_nat_mult of_nat_power) 
      then show False 
        using P3 by auto 
    qed
    then show ?thesis 
      by (metis (no_types, lifting) A0 NN int_nat_eq of_nat_mult of_nat_power) 
  qed
  obtain i where I:"?n = i*p^(nat ?vf) \<and> \<not> p dvd (nat i)" 
    using "13" by blast 
  obtain j where J:"?m = j*p^(nat ?vg) \<and> \<not> p dvd (nat j)"
    using "14" by blast 
  let ?i = "(p^(Suc (nat (?vf + ?vg))))"
  have P:"?nm mod ?i = ?n*?m mod ?i"
  proof-
    have P1:"?nm = (?n \<otimes>\<^bsub>residue_ring ?i \<^esub> ?m)"
      using A by simp
    have P2:"(?n \<otimes>\<^bsub>residue_ring ?i \<^esub> ?m) = (res ?i (?n)) \<otimes>\<^bsub>residue_ring ?i\<^esub>   (res ?i (?m))" 
      by (metis assms(2) assms(3) of_nat_0_le_iff padic_set_simp0 res_id) 
    then have P3:"(?n \<otimes>\<^bsub>residue_ring ?i \<^esub> ?m) = (res ?i (?n*?m))" 
      by (metis monoid.simps(1) res_def residue_ring_def) 
    then show ?thesis 
      by (simp add: P1 res_def) 
  qed
  then have 15: "?nm mod ?i =  i*j*p^((nat ?vf) +(nat ?vg)) mod ?i"
    by (metis I J mult.assoc mult.left_commute of_nat_mult power_add zmod_int)
  have 16: "\<not> p dvd (i*j)" using 13 14
    using I J assms(1) prime_dvd_mult_iff by auto 
  have 17: "((nat ?vf) +(nat ?vg)) < (Suc (nat (?vf + ?vg)))" 
    by (simp add: assms(4) assms(5) nat_add_distrib padic_val_def) 
  have 18:"?nm mod ?i \<noteq>0"
  proof-
    have A0:"\<not>  p^((Suc (nat (?vf + ?vg)))) dvd p^((nat ?vf) +(nat ?vg)) " 
      using 17 by (metis One_nat_def assms(1) linorder_not_less power_dvd_imp_le prime_gt_Suc_0_nat)
    then have A1: "p^((nat ?vf) +(nat ?vg)) mod ?i \<noteq> 0" 
      using dvd_eq_mod_eq_0 by blast
    have "\<not>  p^((Suc (nat (?vf + ?vg)))) dvd i*j*p^((nat ?vf) +(nat ?vg)) "
      using 16 A0 assms(1) 
      by (metis (no_types, lifting) "17" A1 One_nat_def assms(4) assms(5)
          dvd_times_right_cancel_iff mod_less nat_int nat_plus_as_int padic_val_def
          power_Suc power_strict_increasing_iff prime_gt_Suc_0_nat)
    then show ?thesis 
      using "15" by force
  qed
  have 19: "(?nm mod ?i ) mod (p^(nat ?vf + nat ?vg)) = i*j*p^((nat ?vf) +(nat ?vg)) mod (p^(nat ?vf + nat ?vg))"
    using 15 by (simp add: assms(4) assms(5) nat_add_distrib padic_val_def)
  then have 20: "?nm mod (p^(nat ?vf + nat ?vg)) = 0" 
    by (metis (mono_tags, lifting) A P dvd_imp_mod_0 
        dvd_triv_right monoid.simps(1) of_nat_eq_0_iff residue_ring_def)
  have 21: "(padic_mult p f g) \<noteq> padic_zero p"
  proof
    assume "(padic_mult p f g) =  padic_zero p"
    then have "(padic_mult p f g) (Suc (nat (padic_val p f + padic_val p g))) =  padic_zero p (Suc (nat (padic_val p f + padic_val p g)))"
      by simp
    then have "?nm  = (padic_zero p (Suc (nat (padic_val p f + padic_val p g))))"
      by blast 
    then have "?nm = 0"  
      by (simp add: padic_zero_def)  
    then show False
      using "18" by auto
  qed
  have 22: "(padic_mult p f g)\<in> (padic_set p)" 
    using assms(1) assms(2) assms(3) padic_mult_closed by blast 
  have 23: "\<And> j. j < Suc (nat (padic_val p f + padic_val p g)) \<Longrightarrow> (padic_mult p f g) j = \<zero>\<^bsub>residue_ring (p^j)\<^esub>"
  proof-
    fix k
    let ?j = "Suc (nat (padic_val p f + padic_val p g))"
    assume P: "k < ?j"
    show "(padic_mult p f g) k = \<zero>\<^bsub>residue_ring (p^k)\<^esub>" 
      proof-
      have P0: "(padic_mult p f g) (nat ?vf + nat ?vg) = \<zero>\<^bsub>residue_ring (p^(nat ?vf + nat ?vg))\<^esub>"
        proof-
          let ?k = "(nat ?vf + nat ?vg)"
          have "((padic_mult p f g) ?k) = res (p^?k) ((padic_mult p f g) ?k) " 
            using P 22 padic_set_simp1 by (simp add: assms(1) prime_gt_0_nat)
          then have "((padic_mult p f g) ?k) = res (p^?k) ?nm" 
            using "17" "22" assms(1) padic_set_simp1 by fastforce 
          then have "((padic_mult p f g) ?k) = res (p^?k) ?nm" 
            by (simp add: res_def)
          then have "((padic_mult p f g) ?k) = res (p^?k) 0"  
            using "20" res_def by auto 
          then show ?thesis 
            by (simp add: res_def residue_ring_def) 
        qed
      then show ?thesis 
      proof(cases "k = (nat ?vf + nat ?vg)")
      case True then show ?thesis  
        using P0 by blast
    next
      case B: False
      then show ?thesis 
      proof(cases "k=0")
        case True
        then show ?thesis 
          using "22" assms(1) padic_set_simp2 residue_ring_def by auto 
      next
        case C: False 
        then have "((padic_mult p f g) k) = res (p^k) ((padic_mult p f g) (nat ?vf + nat ?vg)) " 
          using B P 22 padic_set_simp1 by (simp add: assms(1) assms(4) assms(5) padic_val_def prime_gt_0_nat) 
        then have S: "((padic_mult p f g) k) = res (p^k) \<zero>\<^bsub>residue_ring (p^((nat ?vf + nat ?vg)))\<^esub>" 
          by (simp add: P0)
        have "res (p^k) \<in> ring_hom (residue_ring (p^((nat ?vf + nat ?vg)))) (residue_ring (p^k))"
          using B P C res_hom_p 
          using assms(1) assms(4) assms(5) less_Suc0 nat_int not_less_eq of_nat_power padic_val_def prime_nat_int_transfer by auto 
        then show ?thesis using S 
          using P0 padic_zero_def padic_zero_simp res_def by auto 
      qed
    qed
  qed
qed
  have 24: "(padic_mult p f g) (Suc (nat ?vf + nat ?vg)) \<noteq> \<zero>\<^bsub>residue_ring (int (p ^ Suc (nat (padic_val p f + padic_val p g))))\<^esub>" 
    by (metis (no_types, lifting) "18" A P assms(4) assms(5) monoid.simps(1) nat_int nat_int_add padic_val_def residue_ring_def ring.simps(1)) 
  have 25: "padic_val p (padic_mult p f g) = int (LEAST k::nat. ((padic_mult p f g) (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (int p^(Suc k))\<^esub>)"
    using padic_val_def 21 by auto 
  have 26:"(nat (padic_val p f + padic_val p g)) \<in> {k::nat. ((padic_mult p f g) (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (int p^(Suc k))\<^esub>}" using 24 
    using "18" assms(1) prime_gt_0_nat 
    by (metis (mono_tags, lifting) mem_Collect_eq mod_0 residue_ring_def ring.simps(1))
  have 27: "\<And> j. j < (nat (padic_val p f + padic_val p g)) \<Longrightarrow>
     j \<notin> {k::nat. ((padic_mult p f g) (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (int p^(Suc k))\<^esub>}" 
    by (simp add: "23") 
  have "(nat (padic_val p f + padic_val p g)) = (LEAST k::nat. ((padic_mult p f g) (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (int p^(Suc k))\<^esub>) "
  proof-
    obtain P where C0: "P= (\<lambda> k. ((padic_mult p f g) (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (int p^(Suc k))\<^esub>)" 
      by simp
    obtain x where C1: "x = (nat (padic_val p f + padic_val p g))" 
      by blast
    have C2: "P x" 
      using "26" C0 C1  by blast
    have C3:"\<And> j. j< x \<Longrightarrow> \<not> P j" 
      using C0 C1 by (simp add: "23")
    have C4: "\<And> j. P j \<Longrightarrow> x \<le>j" 
      using C3 le_less_linear by blast
    have "x = (LEAST k. P k)" 
      using C2 C4 Least_equality by auto 
    then show ?thesis using C0 C1 by auto
  qed
  then have "padic_val p (padic_mult p f g) = (nat (padic_val p f + padic_val p g))" 
    using "25" by linarith
  then show ?thesis 
    by (simp add: assms(4) assms(5) padic_val_def)

qed

(*abbreviation for the ring of p_adic integers*)

abbreviation padic_int :: "nat \<Rightarrow> padic_int ring"
  where "padic_int (p::nat) \<equiv> \<lparr>carrier = (padic_set p),
         Group.monoid.mult = (padic_mult p), one = (padic_one p), 
          zero = (padic_zero p), add = (padic_add p)\<rparr>"

(*padic multiplication is associative*)

lemma residues_n:
  assumes "n \<noteq> 0"
  assumes "prime p"
  shows "residues (int p^n)" 
proof
  have "p > 1" using assms(2) 
    using prime_gt_1_nat by auto
  then show " 1 < int p ^ n "  
    using assms(1) by auto
qed

lemma padic_mult_assoc:
assumes "prime p"
shows  "\<And>x y z.
       x \<in> carrier (padic_int p) \<Longrightarrow>
       y \<in> carrier (padic_int p) \<Longrightarrow> 
       z \<in> carrier (padic_int p) \<Longrightarrow>
       x \<otimes>\<^bsub>padic_int p\<^esub> y \<otimes>\<^bsub>padic_int p\<^esub> z = x \<otimes>\<^bsub>padic_int p\<^esub> (y \<otimes>\<^bsub>padic_int p\<^esub> z)"
proof-
  fix x y z
  assume Ax: " x \<in> carrier (padic_int p)"
  assume Ay: " y \<in> carrier (padic_int p)"
  assume Az: " z \<in> carrier (padic_int p)"
  show "x \<otimes>\<^bsub>padic_int p\<^esub> y \<otimes>\<^bsub>padic_int p\<^esub> z = x \<otimes>\<^bsub>padic_int p\<^esub> (y \<otimes>\<^bsub>padic_int p\<^esub> z)"
  proof
    fix n
    show "((x \<otimes>\<^bsub>padic_int p\<^esub> y) \<otimes>\<^bsub>padic_int p\<^esub> z) n = (x \<otimes>\<^bsub>padic_int p\<^esub> (y \<otimes>\<^bsub>padic_int p\<^esub> z)) n"
    proof(cases "n=0") 
      case True
      then show ?thesis 
        by (metis Ax Ay Az assms monoid.select_convs(1) 
            padic_mult_closed padic_set_simp2 partial_object.select_convs(1)) 
    next
      case False
      then have "residues (int p^n)" 
        by (simp add: assms residues_n)
      then show ?thesis 
        using residues.cring padic_set_simp0 padic_mult_closed Ax Ay Az padic_mult_simp
        by (simp add: cring.cring_simprules(11))
    qed
  qed
qed


(*The padics are closed under addition*)

lemma padic_add_closed:
  assumes "prime p"
  shows  "\<And>x y. x \<in> carrier (padic_int p) \<Longrightarrow> y \<in> carrier (padic_int p) \<Longrightarrow> x \<oplus>\<^bsub>(padic_int p)\<^esub> y \<in> carrier (padic_int p)"
 proof
      fix x::"padic_int"
      fix y::"padic_int"
      assume Px: "x \<in>carrier (padic_int p) "
      assume Py: "y \<in>carrier (padic_int p)"
      show "x \<oplus>\<^bsub>(padic_int p)\<^esub> y \<in> carrier (padic_int p)"
      proof-
        let ?f = "x \<oplus>\<^bsub>(padic_int p)\<^esub> y"
        have 0: "(\<forall>(m::nat). (?f m) \<in> (carrier (residue_ring (p^m))))"
        proof fix m
          have A1 : "?f m = (x m) \<oplus>\<^bsub>(residue_ring (p^m))\<^esub> (y m)"
             by (simp add: padic_add_def)  
          have A2: "(x m) \<in>(carrier (residue_ring (p^m)))" 
            using Px by (simp add: padic_set_def) 
          have A3: "(y m) \<in>(carrier (residue_ring (p^m)))" 
            using Py by (simp add: padic_set_def) 
          then show "(?f m) \<in> (carrier (residue_ring (p^m)))" 
            using A1 assms of_nat_0_less_iff prime_gt_0_nat residue_ring_def by force  
        qed
        have 1: "(\<forall>(n::nat) (m::nat). (n > m \<longrightarrow> (res (p^m) (?f n) = (?f m))))" 
        proof 
          fix n::nat
          show "(\<forall>(m::nat). (n > m \<longrightarrow> (res (p^m) (?f n) = (?f m))))" 
          proof
            fix m::nat
            show "(n > m \<longrightarrow> (res (p^m) (?f n) = (?f m)))"
              proof
                assume A: "m < n"
                show "(res (p^m) (?f n) = (?f m))"
                proof(cases "m = 0")
                  case True 
                  then have A0: "(res (p^m) (?f n)) = 0" 
                    by (simp add: res_1_zero) 
                  have A1: "?f m = 0" using True 
                    by (metis (mono_tags, lifting) "0" atLeastAtMost_singleton
                        cancel_comm_monoid_add_class.diff_cancel empty_iff 
                        insert_iff of_nat_1 partial_object.select_convs(1) 
                        power.simps(1) residue_ring_def ring_record_simps(12)) 
                  then show ?thesis 
                    using A0 by linarith 
             
                next
                  case False
                  then have  "m \<noteq>0" using A by linarith
                  have D: "p^n mod p^m = 0" using A 
                    using assms divides_primepow_nat dvd_imp_mod_0 less_imp_le by blast 
                  let ?LHS = "res (p ^ m) ((x \<oplus>\<^bsub>padic_int p\<^esub> y) n)"
                  have A0: "?LHS = res (p ^ m) ((x n)\<oplus>\<^bsub>residue_ring (p^n)\<^esub>( y n))" 
                    by (simp add: padic_add_def)  
                  have "res (p^m) \<in> ring_hom (residue_ring (int (p^n))) (residue_ring (int (p^m)))"
                    using A False assms res_hom_p by auto 
                  then have "res (p ^ m) ((x n)\<oplus>\<^bsub>residue_ring (p^n)\<^esub>( y n)) = (res (p ^ m) (x n))\<oplus>\<^bsub>residue_ring (p^m)\<^esub>((res (p ^ m) (y n)))"  
                    by (metis (no_types, lifting) Px Py mem_Collect_eq padic_set_def partial_object.select_convs(1) ring_hom_add) 
                  then have "?LHS =(res (p ^ m) (x n))\<oplus>\<^bsub>residue_ring (p^m)\<^esub>((res (p ^ m) (y n)))" 
                    using A0 by force 
                  then show ?thesis
                    using A Px Py padic_set_def by (simp add: padic_add_def) 
                qed
              qed
            qed
          qed
          then show ?thesis
            using "0" padic_set_mem by auto 
        qed
        then have "  x \<oplus>\<^bsub>padic_int p\<^esub> y \<in> (padic_set p)" 
        by simp
      then show "carrier (padic_int p) \<subseteq> carrier (padic_int p)" 
        by blast  
    qed

(*padic addition is associative*)

lemma padic_add_assoc:
assumes "prime p"
shows  " \<And>x y z.
       x \<in> carrier (padic_int p) \<Longrightarrow>
       y \<in> carrier (padic_int p) \<Longrightarrow> z \<in> carrier (padic_int p)
       \<Longrightarrow> x \<oplus>\<^bsub>padic_int p\<^esub> y \<oplus>\<^bsub>padic_int p\<^esub> z = x \<oplus>\<^bsub>padic_int p\<^esub> (y \<oplus>\<^bsub>padic_int p\<^esub> z)"
proof-
  fix x y z
  assume Ax: "x \<in> carrier (padic_int p)"
  assume Ay: "y \<in> carrier (padic_int p)"
  assume Az: "z \<in> carrier (padic_int p)"
  show " (x \<oplus>\<^bsub>padic_int p\<^esub> y) \<oplus>\<^bsub>padic_int p\<^esub> z = x \<oplus>\<^bsub>padic_int p\<^esub> (y \<oplus>\<^bsub>padic_int p\<^esub> z)"
    proof
      fix n
      show "((x \<oplus>\<^bsub>padic_int p\<^esub> y) \<oplus>\<^bsub>padic_int p\<^esub> z) n = (x \<oplus>\<^bsub>padic_int p\<^esub> (y \<oplus>\<^bsub>padic_int p\<^esub> z)) n "
      proof-
        have Ex: "(x n) \<in> carrier (residue_ring (p^n))" 
          using Ax padic_set_def by auto 
        have Ey: "(y n) \<in> carrier (residue_ring (p^n))" 
          using Ay padic_set_def by auto 
        have Ez: "(z n) \<in> carrier (residue_ring (p^n))" 
          using Az padic_set_def by auto 
        let ?x = "(x n)"
        let ?y = "(y n)"
        let ?z = "(z n)"
        have P1: "(?x \<oplus>\<^bsub>residue_ring (p^n)\<^esub> ?y) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> ?z = (x n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> ((y \<oplus>\<^bsub>padic_int p\<^esub> z) n)"
        proof(cases "n = 0")
          case True
          then show ?thesis 
            by (simp add: residue_ring_def)
        next
          case False
          then have "residues (int p^n)" 
            by (simp add: assms residues_n)
          then show ?thesis 
            using Ex Ey Ez cring.cring_simprules(7) padic_add_simp residues.cring by fastforce
        qed
        have " ((y n)) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> z n =((y \<oplus>\<^bsub>padic_int p\<^esub> z) n)"
          using padic_add_def by simp 
        then have P0: "(x n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> ((y \<oplus>\<^bsub>padic_int p\<^esub> z) n) = ((x n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> ((y n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> z n))"
          using padic_add_def by simp 
        have "((x \<oplus>\<^bsub>padic_int p\<^esub> y) \<oplus>\<^bsub>padic_int p\<^esub> z) n = ((x  \<oplus>\<^bsub>padic_int p\<^esub> y) n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> z n"
          using padic_add_def  by simp
        then have  "((x \<oplus>\<^bsub>padic_int p\<^esub> y) \<oplus>\<^bsub>padic_int p\<^esub> z) n =((x n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> (y n)) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> z n"
          using padic_add_def  by simp 
        then have  "((x \<oplus>\<^bsub>padic_int p\<^esub> y) \<oplus>\<^bsub>padic_int p\<^esub> z) n =((x n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> ((y n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> z n))"
          using Ex Ey Ez P1 P0   by linarith 
        then have  "((x \<oplus>\<^bsub>padic_int p\<^esub> y) \<oplus>\<^bsub>padic_int p\<^esub> z) n = (x n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> ((y \<oplus>\<^bsub>padic_int p\<^esub> z) n)"
          using P0 by linarith 
        then show ?thesis by (simp add: padic_add_def) 
      qed
    qed
   qed

(*padic addition is commutative*)
lemma padic_add_comm:
  assumes "prime p"
  shows " \<And>x y. x \<in> carrier (padic_int p) \<Longrightarrow> y \<in> carrier (padic_int p) \<Longrightarrow> x \<oplus>\<^bsub>padic_int p\<^esub> y = y \<oplus>\<^bsub>padic_int p\<^esub> x"
    proof-
      fix x y
      assume Ax: "x \<in> carrier (padic_int p)" assume Ay:"y \<in> carrier (padic_int p)"
      show "x \<oplus>\<^bsub>padic_int p\<^esub> y = y \<oplus>\<^bsub>padic_int p\<^esub> x"
      proof fix n
        show "(x \<oplus>\<^bsub>padic_int p\<^esub> y) n = (y \<oplus>\<^bsub>padic_int p\<^esub> x) n " 
        proof(cases "n=0")
          case True
          then show ?thesis 
            by (metis Ax Ay assms padic_add_def padic_set_simp2   
                partial_object.select_convs(1) ring_record_simps(12)) 
        next
          case False
          have LHS0: "(x \<oplus>\<^bsub>padic_int p\<^esub> y) n = (x n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> (y n)" 
            by (simp add: padic_add_simp) 
          have RHS0: "(y \<oplus>\<^bsub>padic_int p\<^esub> x) n = (y n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> (x n)" 
            by (simp add: padic_add_simp) 
          have Ex: "(x n) \<in> carrier (residue_ring (p^n))" 
            using Ax padic_set_simp0 by auto 
          have Ey: "(y n) \<in> carrier (residue_ring (p^n))" 
            using Ay padic_set_simp0 by auto 
          have LHS1: "(x \<oplus>\<^bsub>padic_int p\<^esub> y) n = ((x n) +(y n)) mod (p^n)"
            using LHS0 residue_ring_def by simp
          have RHS1: "(y \<oplus>\<^bsub>padic_int p\<^esub> x) n = ((y n) +(x n)) mod (p^n)"
            using RHS0 residue_ring_def by simp
          then show ?thesis using LHS1 RHS1 by presburger 
        qed
      qed
    qed

(*padic_zero is an additive identity*)
lemma padic_add_zero:
assumes "prime p"
shows "\<And>x. x \<in> carrier (padic_int p) \<Longrightarrow> \<zero>\<^bsub>padic_int p\<^esub> \<oplus>\<^bsub>padic_int p\<^esub> x = x"
proof-
  fix x
  assume Ax: "x \<in> carrier (padic_int p)"
  show " \<zero>\<^bsub>padic_int p\<^esub> \<oplus>\<^bsub>padic_int p\<^esub> x = x " 
  proof fix n
    have A: "(padic_zero p) n = 0" 
      by (simp add: padic_zero_def) 
    have "((padic_zero p) \<oplus>\<^bsub>padic_int p\<^esub> x) n = x n" 
      apply(simp add:padic_add_simp)
      apply(simp add:residue_ring_def)
      apply(simp add: A)
    proof-
      have "x \<in>padic_set p" using Ax by auto 
      then have "x n \<in> {0..p^n - 1}" 
        using Ax padic_set_simp0 residue_ring_def assms int_ops(6) by auto
      then have "x n \<le> (int p^n) - 1" 
        using atLeastAtMost_iff 
        by (metis assms of_nat_1 of_nat_diff of_nat_power one_le_power prime_ge_1_nat)
      then have R: "x n < p^n" 
        by simp
      have "x n \<ge>0 " 
        using \<open>x n \<in> {0..int (p ^ n - 1)}\<close> atLeastAtMost_iff by blast
      then show "x n mod int p ^ n = x n" using R 
        by simp
    qed
    then show "(\<zero>\<^bsub>padic_int p\<^esub> \<oplus>\<^bsub>padic_int p\<^esub> x) n = x n" 
      by simp
  qed
qed

(*padic_zero is closed under additive inverses*)
lemma padic_add_inv:
  assumes "prime p"
  shows "\<And>x. x \<in> carrier (padic_int p) \<Longrightarrow> \<exists>y\<in>carrier (padic_int p). y \<oplus>\<^bsub>padic_int p\<^esub> x = \<zero>\<^bsub>padic_int p\<^esub>"
proof-
  fix x
  assume Ax: " x \<in> carrier (padic_int p)"
  show "\<exists>y\<in>carrier (padic_int p). y \<oplus>\<^bsub>padic_int p\<^esub> x = \<zero>\<^bsub>padic_int p\<^esub>"
    proof
      let ?y = "(padic_uminus p) x"
      show "?y \<oplus>\<^bsub>padic_int p\<^esub> x = \<zero>\<^bsub>padic_int p\<^esub>"
      proof 
        fix n
        show  "(?y \<oplus>\<^bsub>padic_int p\<^esub> x) n = \<zero>\<^bsub>padic_int p\<^esub> n" 
        proof(cases "n=0")
          case True
          then show ?thesis 
            using Ax assms padic_add_closed padic_set_simp2 padic_uminus_closed padic_zero_def by auto 
        next
          case False 
          have C: "(x n) \<in> carrier (residue_ring (p^n))" 
            using Ax padic_set_simp0 by auto
          have R: "residues (int p^n)" 
            using False  by (simp add: assms residues_n)
          have "(?y \<oplus>\<^bsub>padic_int p\<^esub> x) n = (?y n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> x n" 
            by (simp add: padic_add_simp)
          then have "(?y \<oplus>\<^bsub>padic_int p\<^esub> x) n = 0"
            using C R residue_ring_def[simp] residues.cring 
            by (metis cring.cring_simprules(9) of_nat_power padic_uminus_simp residues.res_zero_eq)
          then show ?thesis 
            by (simp add: padic_zero_def)
        qed
    qed
    then show "padic_uminus p x \<in> carrier (padic_int p)" 
      using padic_uminus_closed
        Ax assms prime_gt_0_nat by auto 
  qed
qed

(*The ring of padic integers forms an abelian group under addition*)

lemma padic_is_abelian_group:
assumes "prime p"
shows "abelian_group (padic_int p)"
  proof (rule abelian_groupI)
    show "\<And>x y. x \<in> carrier (padic_int p) \<Longrightarrow> y \<in> carrier (padic_int p) \<Longrightarrow> x \<oplus>\<^bsub>(padic_int p)\<^esub> y \<in> carrier (padic_int p)"
      using padic_add_closed  by (simp add: assms)
    show zero: "\<zero>\<^bsub>padic_int p\<^esub> \<in> carrier (padic_int p)" 
      by (metis assms not_prime_0 padic_zero_mem
          partial_object.select_convs(1) ring_record_simps(11))
    show add_assoc: " \<And>x y z.
       x \<in> carrier (padic_int p) \<Longrightarrow>
       y \<in> carrier (padic_int p) \<Longrightarrow> z \<in> carrier (padic_int p)
       \<Longrightarrow> x \<oplus>\<^bsub>padic_int p\<^esub> y \<oplus>\<^bsub>padic_int p\<^esub> z = x \<oplus>\<^bsub>padic_int p\<^esub> (y \<oplus>\<^bsub>padic_int p\<^esub> z)"
      using assms padic_add_assoc by auto
    show comm: " \<And>x y. x \<in> carrier (padic_int p) \<Longrightarrow> y \<in> carrier (padic_int p) \<Longrightarrow> x \<oplus>\<^bsub>padic_int p\<^esub> y = y \<oplus>\<^bsub>padic_int p\<^esub> x"
      using assms padic_add_comm by blast
    show "\<And>x. x \<in> carrier (padic_int p) \<Longrightarrow> \<zero>\<^bsub>padic_int p\<^esub> \<oplus>\<^bsub>padic_int p\<^esub> x = x"
      using assms padic_add_zero by blast
    show "\<And>x. x \<in> carrier (padic_int p) \<Longrightarrow> \<exists>y\<in>carrier (padic_int p). y \<oplus>\<^bsub>padic_int p\<^esub> x = \<zero>\<^bsub>padic_int p\<^esub>"
      using assms padic_add_inv by blast
  qed

(*padic_one is a multiplicative identity*)

lemma padic_one_id:
assumes "prime p"
assumes "x \<in> carrier (padic_int p)"
shows  "\<one>\<^bsub>padic_int p\<^esub> \<otimes>\<^bsub>padic_int p\<^esub> x = x"
proof
  fix n
  show "(\<one>\<^bsub>padic_int p\<^esub> \<otimes>\<^bsub>padic_int p\<^esub> x) n = x n "
  proof(cases "n=0")
    case True
    then show ?thesis 
      by (metis assms(1) assms(2) monoid.select_convs(1) monoid.select_convs(2)
          padic_mult_closed padic_one_mem padic_set_simp2 partial_object.select_convs(1)) 
  next
    case False
    then have "residues (p^n)" 
      by (simp add: assms(1) residues_n)
    then show ?thesis 
      using False assms(2) cring.cring_simprules(12) 
        padic_mult_simp padic_one_simp padic_set_simp0 residues.cring by fastforce
  qed
qed

(*padic multiplication is commutative*)

lemma padic_mult_comm:
assumes "prime p"
assumes "x \<in> carrier (padic_int p)"
assumes "y \<in> carrier (padic_int p)"
shows "x \<otimes>\<^bsub>padic_int p\<^esub> y = y \<otimes>\<^bsub>padic_int p\<^esub> x"
proof
  fix n
  have Ax: "(x n) \<in> carrier (residue_ring (p^n))" 
    using padic_set_def assms(2) by auto
  have Ay: "(y n) \<in>carrier (residue_ring (p^n))"
    using padic_set_def assms(3) padic_set_simp0 by auto
  show "(x \<otimes>\<^bsub>padic_int p\<^esub> y) n = (y \<otimes>\<^bsub>padic_int p\<^esub> x) n"
     proof(cases "n=0")
          case True
          then show ?thesis 
            by (metis assms(1) assms(2) assms(3) monoid.select_convs(1) padic_set_simp2 padic_simps(3) partial_object.select_convs(1)) 
        next
          case False
          have LHS0: "(x \<otimes>\<^bsub>padic_int p\<^esub> y) n = (x n) \<otimes>\<^bsub>residue_ring (p^n)\<^esub> (y n)" 
            by (simp add: padic_mult_simp)       
          have RHS0: "(y \<otimes>\<^bsub>padic_int p\<^esub> x) n = (y n) \<otimes>\<^bsub>residue_ring (p^n)\<^esub> (x n)" 
            by (simp add: padic_mult_simp) 
          have Ex: "(x n) \<in> carrier (residue_ring (p^n))" 
            using Ax padic_set_simp0 by auto 
          have Ey: "(y n) \<in> carrier (residue_ring (p^n))" 
            using Ay padic_set_simp0 by auto 
          have LHS1: "(x \<otimes>\<^bsub>padic_int p\<^esub> y) n = ((x n) *(y n)) mod (p^n)"
            using LHS0 
            by (simp add: residue_ring_def) 
          have RHS1: "(y \<otimes>\<^bsub>padic_int p\<^esub> x) n = ((y n) *(x n)) mod (p^n)"
            using RHS0 
            by (simp add: residue_ring_def) 
          then show ?thesis using LHS1 RHS1 
            by (simp add: mult.commute) 
        qed
      qed

lemma padic_is_comm_monoid:
assumes "prime p"
shows "Group.comm_monoid (padic_int p)"
proof(rule comm_monoidI)
  show  "\<And>x y. x \<in> carrier (padic_int p) \<Longrightarrow> y \<in> carrier (padic_int p) \<Longrightarrow> x \<otimes>\<^bsub>padic_int p\<^esub> y \<in> carrier (padic_int p)"
    by (simp add: assms padic_mult_closed) 
  show "\<one>\<^bsub>padic_int p\<^esub> \<in> carrier (padic_int p)" 
    by (metis assms monoid.select_convs(2) 
        padic_one_mem partial_object.select_convs(1))
  show "\<And>x y z. x \<in> carrier (padic_int p) \<Longrightarrow>
                y \<in> carrier (padic_int p) \<Longrightarrow> 
                z \<in> carrier (padic_int p) \<Longrightarrow>
                x \<otimes>\<^bsub>padic_int p\<^esub> y \<otimes>\<^bsub>padic_int p\<^esub> z = x \<otimes>\<^bsub>padic_int p\<^esub> (y \<otimes>\<^bsub>padic_int p\<^esub> z)"
    using assms padic_mult_assoc by auto
  show "\<And>x. x \<in> carrier (padic_int p) \<Longrightarrow> \<one>\<^bsub>padic_int p\<^esub> \<otimes>\<^bsub>padic_int p\<^esub> x = x"
    using assms  padic_one_id by blast 

  show "\<And>x y. x \<in> carrier (padic_int p) \<Longrightarrow>
              y \<in> carrier (padic_int p) \<Longrightarrow>
              x \<otimes>\<^bsub>padic_int p\<^esub> y = y \<otimes>\<^bsub>padic_int p\<^esub> x"
    using padic_mult_comm  by (simp add: assms)
qed

(*The padic integers form a commutative ring when p is prime*)

lemma padic_int_is_cring:
  assumes "prime (p::nat)"
  shows "cring (padic_int p)"
proof (rule cringI)
  show "abelian_group (padic_int p)"
    by (simp add: assms padic_is_abelian_group)
  show "Group.comm_monoid (padic_int p)"
    by (simp add: assms padic_is_comm_monoid)
  show "\<And>x y z.
       x \<in> carrier (padic_int p) \<Longrightarrow>
       y \<in> carrier (padic_int p) \<Longrightarrow>
       z \<in> carrier (padic_int p) \<Longrightarrow>
       (x \<oplus>\<^bsub>padic_int p\<^esub> y) \<otimes>\<^bsub>padic_int p\<^esub> z = x \<otimes>\<^bsub>padic_int p\<^esub> z \<oplus>\<^bsub>padic_int p\<^esub> y \<otimes>\<^bsub>padic_int p\<^esub> z "
  proof-
    fix x y z
    assume Ax: " x \<in> carrier (padic_int p)"
    assume Ay: " y \<in> carrier (padic_int p)"
    assume Az: " z \<in> carrier (padic_int p)"
    show "(x \<oplus>\<^bsub>padic_int p\<^esub> y) \<otimes>\<^bsub>padic_int p\<^esub> z = x \<otimes>\<^bsub>padic_int p\<^esub> z \<oplus>\<^bsub>padic_int p\<^esub> y \<otimes>\<^bsub>padic_int p\<^esub> z"
    proof
      fix n
      have Ex: " (x n) \<in> carrier (residue_ring (p^n))" 
        using Ax padic_set_def by auto
      have Ey: " (y n) \<in> carrier (residue_ring (p^n))" 
        using Ay padic_set_def by auto
      have Ez: " (z n) \<in> carrier (residue_ring (p^n))" 
        using Az padic_set_def by auto
      show "( (x \<oplus>\<^bsub>padic_int p\<^esub> y) \<otimes>\<^bsub>padic_int p\<^esub> z) n = (x \<otimes>\<^bsub>padic_int p\<^esub> z \<oplus>\<^bsub>padic_int p\<^esub> y \<otimes>\<^bsub>padic_int p\<^esub> z) n "
      proof(cases "n=0")
        case True
        then show ?thesis 
          by (metis Ax Ay Az \<open>Group.comm_monoid (padic_int p)\<close> assms comm_monoid.is_monoid
              monoid.m_closed padic_add_closed padic_set_simp2 partial_object.select_convs(1)) 
      next
        case False 
        then have "residues (p^n)" 
          by (simp add: assms residues_n)
        then show ?thesis 
          using Ex Ey Ez cring.cring_simprules(13) padic_add_simp 
            padic_mult_simp residues.cring by fastforce 
      qed
    qed
  qed
qed

(*The padic ring has no nontrivial zero divisors*)

lemma padic_no_zero_divisors:
assumes "prime p"
assumes "a \<in> carrier (padic_int p)"
assumes "b \<in>carrier (padic_int p)"
assumes "a \<noteq>\<zero>\<^bsub>padic_int p\<^esub> "
assumes "b \<noteq>\<zero>\<^bsub>padic_int p\<^esub> "
shows "a \<otimes>\<^bsub>padic_int p\<^esub> b \<noteq> \<zero>\<^bsub>padic_int p\<^esub> "
proof
  assume C: "a \<otimes>\<^bsub>padic_int p\<^esub> b = \<zero>\<^bsub>padic_int p\<^esub>"
  show False
  proof-
    have 0: "a = \<zero>\<^bsub>padic_int p\<^esub> \<or> b = \<zero>\<^bsub>padic_int p\<^esub>"
    proof(cases "a = \<zero>\<^bsub>padic_int p\<^esub>")
      case True
      then show ?thesis by auto
    next
      case False
      have "\<not> b  \<noteq>\<zero>\<^bsub>padic_int p\<^esub>"
      proof
        assume "b \<noteq> \<zero>\<^bsub>padic_int p\<^esub>"
        have "padic_val p (a \<otimes>\<^bsub>padic_int p\<^esub> b) = (padic_val p a) + (padic_val p b)" 
          using False assms(1) assms(2) assms(3) assms(5) val_prod by auto
          then have "padic_val p (a \<otimes>\<^bsub>padic_int p\<^esub> b) \<noteq> -1" 
          using False \<open>b \<noteq> \<zero>\<^bsub>padic_int p\<^esub>\<close> padic_val_def by auto
        then show False 
          using C padic_val_def by auto      
        qed
      then show ?thesis 
        by blast
    qed
    show ?thesis 
      using "0" assms(4) assms(5) by blast
  qed
qed

(*padic integers form an integral domain*)

lemma padic_int_is_domain:
  assumes "prime (p::nat)"
  shows "domain (padic_int p)"
proof(rule domainI)
  show "cring (padic_int p)" 
    using padic_int_is_cring assms(1) by auto
  show "\<one>\<^bsub>padic_int p\<^esub> \<noteq> \<zero>\<^bsub>padic_int p\<^esub>"
  proof
    assume "\<one>\<^bsub>padic_int p\<^esub> = \<zero>\<^bsub>padic_int p\<^esub> "
    then have "(\<one>\<^bsub>padic_int p\<^esub>) (1::nat) = \<zero>\<^bsub>padic_int p\<^esub> 1" by auto
    show False using assms(1) padic_simps[simp] 
      by (metis (mono_tags, hide_lams) \<open>\<one>\<^bsub>padic_int p\<^esub> = \<zero>\<^bsub>padic_int p\<^esub>\<close>  monoid.simps(2) 
          of_nat_0_eq_iff of_nat_1 padic_one_def  padic_zero_def ring_record_simps(11)  zero_neq_one)
  qed
  show "\<And>a b. a \<otimes>\<^bsub>padic_int p\<^esub> b = \<zero>\<^bsub>padic_int p\<^esub> \<Longrightarrow> a \<in> carrier (padic_int p) \<Longrightarrow> b \<in> carrier (padic_int p)  \<Longrightarrow> a = \<zero>\<^bsub>padic_int p\<^esub> \<or> b = \<zero>\<^bsub>padic_int p\<^esub>"
    using assms padic_no_zero_divisors by blast
qed     

lemma ultrametric:
  assumes "prime p"
  assumes "a \<in> carrier (padic_int p) "
  assumes "b \<in> carrier (padic_int p) "
  assumes "a \<noteq> \<zero>\<^bsub>(padic_int p)\<^esub>"
  assumes "b \<noteq> \<zero>\<^bsub>(padic_int p)\<^esub>"
  assumes  "a \<oplus>\<^bsub>(padic_int p)\<^esub> b \<noteq> \<zero>\<^bsub>(padic_int p)\<^esub>"
  shows "padic_val p (a \<oplus>\<^bsub>(padic_int p)\<^esub> b) \<ge> min (padic_val p a) (padic_val p b)"
proof-
  let ?va = " nat (padic_val p a)"
  let ?vb = "nat (padic_val p b)"
  let ?vab = "nat (padic_val p (a \<oplus>\<^bsub>(padic_int p)\<^esub> b))"
  have P:" \<not> ?vab < min ?va ?vb"
  proof
    assume P0: "?vab < min ?va ?vb"
    then have "Suc ?vab \<le> min ?va ?vb"
      using Suc_leI by blast
    have "(a \<oplus>\<^bsub>(padic_int p)\<^esub> b) \<in> carrier (padic_int p) " 
      using assms(1) assms(2) assms(3)  padic_add_closed by simp
    then have C: "(a \<oplus>\<^bsub>(padic_int p)\<^esub> b) (?vab + 1) \<noteq>  \<zero>\<^bsub>residue_ring (p^(?vab + 1))\<^esub>" 
      using val_of_nonzero(1) assms(6)
      by (simp add: val_of_nonzero(1) assms(1)) 
    have S: "(a \<oplus>\<^bsub>(padic_int p)\<^esub> b) (?vab + 1) = (a (?vab + 1)) \<oplus>\<^bsub>residue_ring (p^((?vab + 1)))\<^esub> (b ((?vab + 1)))"  
      by (simp add: padic_add_def)
    have "int (?vab + 1) \<le> padic_val p a" 
      using P0  using Suc_le_eq by auto
    then have A: "(a (?vab + 1)) = \<zero>\<^bsub>residue_ring (int p^((?vab + 1)))\<^esub> " 
      using assms(1) assms(2) zero_below_val 
      by (metis partial_object.select_convs(1)) 
    have "int (?vab + 1) \<le> padic_val p b" 
      using P0  using Suc_le_eq by auto
    then have B: "(b (?vab + 1)) = \<zero>\<^bsub>residue_ring (int p^((?vab + 1)))\<^esub> " 
      using assms(1) assms(3) zero_below_val 
      by (metis partial_object.select_convs(1)) 
    have "p^(?vab + 1) > 1" 
      using assms(1) by (metis add.commute plus_1_eq_Suc power_gt1 prime_gt_1_nat)
    then have "residues (p^(?vab + 1))" 
      using less_imp_of_nat_less residues.intro by fastforce 
    then have "(a \<oplus>\<^bsub>(padic_int p)\<^esub> b) (?vab + 1) = \<zero>\<^bsub>residue_ring (int p^((?vab + 1)))\<^esub> "
      using A B by (metis (no_types, lifting) S cring.cring_simprules(2)
          cring.cring_simprules(8) of_nat_power residues.cring) 
    then show False using C by auto
  qed
  have A0: "(padic_val p a) \<ge> 0" 
    using assms(4) padic_val_def by auto
  have A1: "(padic_val p b) \<ge> 0" 
    using assms(5) padic_val_def by auto
  have A2: "padic_val p (a \<oplus>\<^bsub>(padic_int p)\<^esub> b) \<ge> 0" 
    using assms(6) padic_val_def by auto
  show ?thesis using P A0 A1 A2 
    by linarith 
qed

lemma padic_inv:
  assumes "prime p"
  assumes "a \<in> carrier (padic_int p)"
  shows "\<ominus>\<^bsub>padic_int p\<^esub> a = (\<lambda> n. \<ominus>\<^bsub>residue_ring (p^n)\<^esub> (a n))"

proof
  fix n
  show "(\<ominus>\<^bsub>padic_int p\<^esub> a) n = \<ominus>\<^bsub>residue_ring (int (p ^ n))\<^esub> a n" 
  proof(cases "n=0")
    case True
    then show ?thesis 
      by (metis (no_types, lifting) assms(1) assms(2) cring.sum_zero_eq_neg of_nat_1 padic_add_inv 
        padic_int_is_cring padic_set_simp2 partial_object.select_convs(1) power_0 res_1_prop residue_ring_def ring_record_simps(11)) 
  next
    case False
    then have R: "residues (p^n)" 
      by (simp add: assms(1) residues_n)
    have "(\<ominus>\<^bsub>padic_int p\<^esub> a) \<oplus>\<^bsub>padic_int p\<^esub> a = \<zero>\<^bsub>padic_int p\<^esub>" 
      by (meson assms(1) assms(2) cring.cring_simprules(9) padic_int_is_cring)
    then have P: "(\<ominus>\<^bsub>padic_int p\<^esub> a) n \<oplus>\<^bsub>residue_ring (p^n)\<^esub> a n = 0"
      by (metis padic_add_def padic_zero_def ring_record_simps(11) ring_record_simps(12))
    have Q: "(a n) \<in> carrier (residue_ring (p^n))" 
      using assms(2) padic_set_simp0 by auto
    show ?thesis using R Q residues.cring  
      by (metis P abelian_group.minus_equality assms(1) assms(2)
          cring.cring_simprules(3) padic_int_is_cring padic_set_simp0
          partial_object.select_convs(1) residues.abelian_group residues.res_zero_eq)
  qed
qed

lemma padic_val_add_inv:
  assumes "prime p"
  assumes "a \<in> carrier (padic_int p)"
  shows "padic_val p a = padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a)"
proof(cases "a = \<zero>\<^bsub>padic_int p\<^esub>")
  case True
  then show ?thesis 
    by (metis assms(1) cring.cring_simprules(22) padic_int_is_cring) 
next
  case False
  have 0: "\<And> n. (a n) = \<zero>\<^bsub>residue_ring (p^n)\<^esub> \<Longrightarrow> (\<ominus>\<^bsub>padic_int p\<^esub> a) n = \<zero>\<^bsub>residue_ring (p^n)\<^esub>"
    using padic_inv 
    by (metis (no_types, lifting) One_nat_def assms(1) assms(2) cring.cring_simprules(22)
        nat_power_eq_Suc_0_iff of_nat_1 of_nat_power res_1_prop residues.cring residues_n)
  have 1: "\<And> n. (a n) \<noteq> \<zero>\<^bsub>residue_ring (p^n)\<^esub> \<Longrightarrow> (\<ominus>\<^bsub>padic_int p\<^esub> a) n \<noteq> \<zero>\<^bsub>residue_ring (p^n)\<^esub>"
    using padic_inv 
    by (metis (no_types, lifting) assms(1) assms(2) cring.cring_simprules(21)
        cring.cring_simprules(22) cring.cring_simprules(3) of_nat_power
        padic_int_is_cring padic_set_simp2 partial_object.select_convs(1) 
        residues.cring residues_n)
  have A:"padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a) \<ge> (padic_val p a)" 
  proof-
    have "\<not> padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a) < (padic_val p a)" 
    proof 
      assume "padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a) < padic_val p a"
      let ?n = "padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a)"
      let ?m = " padic_val p a"
      have "(\<ominus>\<^bsub>padic_int p\<^esub> a)  \<noteq> (padic_zero p)" 
        by (metis False assms(1) assms(2) cring.cring_simprules(9) padic_add_zero padic_int_is_cring ring_record_simps(11))
      then have P0: "?n \<ge>0" 
        by (simp add: padic_val_def)
      have P1: "?m \<ge>0" using False 
        using \<open>0 \<le> padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a)\<close> 
          \<open>padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a) < padic_val p a\<close> by linarith
      have "(Suc (nat ?n)) < Suc (nat (padic_val p a))"
        using P0 P1  \<open>padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a) < padic_val p a\<close> by linarith
      then have "int (Suc (nat ?n)) \<le> (padic_val p a)" 
        using of_nat_less_iff by linarith
      then have "a (Suc (nat ?n)) =  \<zero>\<^bsub>residue_ring (int p ^ ((Suc (nat ?n))))\<^esub>" 
        using assms(1) assms(2) zero_below_val residue_ring_def by auto 
      then have "(\<ominus>\<^bsub>padic_int p\<^esub> a) (Suc (nat ?n)) =  \<zero>\<^bsub>residue_ring (int p ^ ((Suc (nat ?n))))\<^esub>" 
        using 0 by simp
      then show False using below_val_zero assms 
        by (metis (no_types, lifting) Suc_eq_plus1 \<open>\<ominus>\<^bsub>padic_int p\<^esub> a \<noteq> padic_zero p\<close> 
            cring.cring_simprules(3) of_nat_power padic_int_is_cring 
            partial_object.select_convs(1) val_of_nonzero(1))
    qed
    then show ?thesis 
      by linarith
  qed
  have B: "padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a) \<le> (padic_val p a)" 
  proof-
   let ?n = "nat (padic_val p a)"
    have "a (Suc ?n) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc ?n))\<^esub> " 
      using False assms(2) val_of_nonzero(1) 
      by (metis Suc_eq_plus1 assms(1) partial_object.select_convs(1) ring_record_simps(11)) 
    then have "(\<ominus>\<^bsub>padic_int p\<^esub> a) (Suc ?n) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc ?n))\<^esub> "
      using 1  by blast 
    then have  "padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a) \<le> int ?n"  using assms(1) assms(2) below_val_zero  
      by (metis abelian_group.a_inv_closed padic_is_abelian_group partial_object.select_convs(1)) 
    then show ?thesis 
      using False padic_val_def by auto 
  qed
  then show ?thesis using A B by auto
qed

end