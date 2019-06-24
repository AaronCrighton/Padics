theory fraction_field
  imports "HOL-Algebra.Ring" 
          "HOL-Algebra.UnivPoly"
          Localization
          "HOL-Algebra.Subrings"
begin

definition nonzero :: "('a, 'b) ring_scheme \<Rightarrow> 'a set" where
"nonzero R = {a \<in> carrier R. a \<noteq> \<zero>\<^bsub>R\<^esub>}"

lemma(in domain) nonzero_is_submonoid:
"submonoid R (nonzero R)"
proof
  show " nonzero R \<subseteq> carrier R"
    using nonzero_def by fastforce
  show "\<And>x y. x \<in> nonzero R \<Longrightarrow> y \<in> nonzero R \<Longrightarrow> x \<otimes> y \<in> nonzero R" 
    by (metis (mono_tags, lifting) local.integral m_closed mem_Collect_eq nonzero_def)
  show "\<one> \<in> nonzero R"
    by (simp add: nonzero_def)
qed

lemma(in domain) eq_obj_rng_of_frac_nonzero:
  "eq_obj_rng_of_frac R (nonzero R)"
  using nonzero_is_submonoid by (simp add: eq_obj_rng_of_frac.intro 
      is_cring local.ring_axioms mult_submonoid_of_crng_def mult_submonoid_of_rng_def)

lemma(in eq_obj_rng_of_frac) one_over0:
  assumes "domain R"
  assumes "a \<in> S"
  shows "(\<one>, a) \<in> carrier rel"
  by (simp add: assms(2) rel_def) 

lemma(in eq_obj_rng_of_frac) one_over:
  assumes "domain R"
  assumes "a \<in> S"
  shows "rng_to_rng_of_frac a \<in> Units rec_rng_of_frac"
proof-
  let ?b = "(\<one> |\<^bsub>rel\<^esub> a)"
  have "(a, \<one>) \<in> carrier rel" using rel_def assms(2)  
    using subset by fastforce 
  then have "?b \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac a = \<one>\<^bsub>rec_rng_of_frac\<^esub>" 
    using one_over0 mult_rng_of_frac_fundamental_lemma 
      assms(1) assms(2) rec_monoid_rng_of_frac_def 
      rec_rng_of_frac_def rng_to_rng_of_frac_def simp_in_frac subset by auto
  then show ?thesis 
    using Im_rng_to_rng_of_frac_unit assms(2) by blast 
qed

text\<open>choice function for numerator\<close>

definition(in eq_obj_rng_of_frac) denom where
"denom a = (if (a = \<zero>\<^bsub>rec_rng_of_frac\<^esub>) then \<one> else ( snd (SOME x. x \<in> a)))"
      
text\<open>choice function for numerator, which is compatible with denom\<close>

definition(in eq_obj_rng_of_frac) numer where
"numer a = (if (a = \<zero>\<^bsub>rec_rng_of_frac\<^esub>) then \<zero> else (fst (SOME x. x \<in> a \<and> (snd x = denom a))))"


text\<open>Fundamental properties of numer and denom\<close>
lemma(in eq_obj_rng_of_frac) numer_denom_facts0:
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  assumes "a \<in> carrier rec_rng_of_frac"
  assumes "a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>"
  shows "a = ((numer a) |\<^bsub>rel\<^esub> (denom a))"
        "(numer a) \<in> carrier R"
        "(denom a) \<in> S"
        "numer a = \<zero> \<Longrightarrow> a = \<zero>\<^bsub>rec_rng_of_frac\<^esub>"
        "a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (rng_to_rng_of_frac(denom a)) = rng_to_rng_of_frac (numer a)"
proof-       
  have 1: "(numer a, denom a) \<in> a" 
  proof-
   have "carrier rel \<noteq> {}" 
     by (metis assms(1) empty_iff one_closed one_over0) 
   have "\<exists> r s. (r \<in> carrier R \<and> s \<in> S \<and> (a = (r |\<^bsub>rel\<^esub> s)))" 
     using rel_def assms(3) assms(1) set_eq_class_of_rng_of_frac_def rec_rng_of_frac_def  
     by (smt mem_Collect_eq mem_Sigma_iff partial_object.select_convs(1))
   then obtain r s where "r \<in> carrier R \<and> s \<in> S \<and> (a = (r |\<^bsub>rel\<^esub> s))" 
     by blast
   then have "a = class_of\<^bsub>rel\<^esub> (r, s)" 
     by (simp add: class_of_to_rel)
   then have "(r,s) \<in> a" using  eq_class_of_def rel_def  
     using \<open>r \<in> carrier R \<and> s \<in> S \<and> a = (r |\<^bsub>rel\<^esub> s)\<close> equiv_obj_rng_of_frac equivalence.refl by fastforce
   then have "(\<exists> x. x \<in> a)"
     by blast 
   then have "(SOME x. x \<in> a) \<in> a" 
      by (meson some_eq_ex) 
   then have "(\<exists> x. x \<in> a \<and> (snd x = denom a))" 
      using denom_def assms  by metis 
   then have "\<exists>x. x \<in> a \<and> (snd x = denom a) \<and> (fst x = numer a)" 
     using numer_def assms  by (metis (mono_tags, lifting) exE_some) 
   then show ?thesis
    by simp 
  qed
  have "carrier rel \<noteq> {}"   
    by (metis assms(1) empty_iff one_closed one_over0) 
  have "a \<in> {r |\<^bsub>rel\<^esub> s |r s. (r, s) \<in> carrier rel}" 
    using assms(3) rec_rng_of_frac_def set_eq_class_of_rng_of_frac_def by auto 
  then have "\<exists> x y. a = (x |\<^bsub>rel\<^esub> y) \<and> (x,y) \<in> carrier rel"    
    using  rec_rng_of_frac_def  eq_class_of_rng_of_frac_def set_eq_class_of_rng_of_frac_def
    by blast 
  then obtain x y where "a = (x |\<^bsub>rel\<^esub> y)" and P0:"(x,y) \<in> carrier rel" 
    by blast 
  then have P1: "(numer a, denom a) \<in>(x |\<^bsub>rel\<^esub> y)" 
    using "1" by blast 
  then show 2:"a = ((numer a) |\<^bsub>rel\<^esub> (denom a))"
  proof-
     have P2:"(numer a, denom a) \<in> carrier rel \<and> (x, y).=\<^bsub>rel\<^esub> (numer a, denom a)  "
      using eq_class_of_rng_of_frac_def P1 by fastforce 
    then have "(x, y).=\<^bsub>rel\<^esub> (numer a, denom a)" 
      by blast 
    then have "(numer a, denom a).=\<^bsub>rel\<^esub>(x, y)"
      using equiv_obj_rng_of_frac by (simp add: equivalence.sym P0 P2) 
    then show ?thesis 
      by (metis P0 P2 \<open>a = (x |\<^bsub>rel\<^esub> y)\<close> class_of_to_rel elem_eq_class equiv_obj_rng_of_frac) 
    qed
  have 3:"(numer a, denom a) \<in> carrier rel" 
    using P1 by (simp add: eq_class_of_rng_of_frac_def) 
  then show 4: "numer a \<in> carrier R" 
    by (simp add: rel_def) 
  show 5: "denom a \<in> S" 
    using "3" rel_def by auto 
  show "numer a = \<zero> \<Longrightarrow> a = \<zero>\<^bsub>rec_rng_of_frac\<^esub>" 
  proof-
    assume "numer a = \<zero>"
    then have "a = (\<zero> |\<^bsub>rel\<^esub> (denom a))" 
      using "2" by auto 
    then show ?thesis 
      using "5" class_of_zero_rng_of_frac by auto 
  qed
  show "a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac (denom a) = rng_to_rng_of_frac (numer a)"
  proof-
    have S: "(denom a, \<one>) \<in>carrier rel" 
      using "5" rel_def subset by auto 
    then have "a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac (denom a) = (((numer a) \<otimes> (denom a)) |\<^bsub>rel\<^esub> ((denom a) \<otimes> \<one>)) "
      using 2 3 mult_rng_of_frac_fundamental_lemma rng_to_rng_of_frac_def 
      rec_monoid_rng_of_frac_def rec_rng_of_frac_def by fastforce
    then have "a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac (denom a) = (((denom a)\<otimes> (numer a)) |\<^bsub>rel\<^esub> ((denom a) \<otimes> \<one>))"
      using "4" "5" m_comm subset by auto 
    then have "a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac (denom a) = ((denom a) |\<^bsub>rel\<^esub> (denom a)) \<otimes>\<^bsub>rec_rng_of_frac\<^esub>( (numer a) |\<^bsub>rel\<^esub> \<one>)"
      using mult_rng_of_frac_fundamental_lemma  "4" "5" S 
        rec_monoid_rng_of_frac_def rec_rng_of_frac_def rel_def by auto
    then show ?thesis 
      using "4" "5" \<open>a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac 
      (denom a) = (denom a \<otimes> numer a |\<^bsub>rel\<^esub> denom a \<otimes> \<one>)\<close> rel_def 
        rng_to_rng_of_frac_def simp_in_frac by auto
  qed
qed


lemma(in eq_obj_rng_of_frac) frac_zero:
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  assumes "a \<in> carrier R"
  assumes "b \<in> S"
  assumes "(a |\<^bsub>rel\<^esub> b) = \<zero>\<^bsub>rec_rng_of_frac\<^esub>"
  shows "a = \<zero>"
proof-
  have 0: "(a |\<^bsub>rel\<^esub> b) = (\<zero> |\<^bsub>rel\<^esub> \<one>)" 
    by (simp add: assms(5) class_of_zero_rng_of_frac) 
  have 1: "(a,b) \<in> carrier rel" 
    by (simp add: assms(3) assms(4) rel_def) 
  have 2: "(\<zero>, \<one>) \<in> carrier rel" 
    by (simp add: rel_def) 
  have 3: "(b, \<one>) \<in> carrier rel" 
    using assms(4) rel_def subset by auto 
  have "(a,b) .=\<^bsub>rel\<^esub> (\<zero>, \<one>)" 
    by (metis (no_types, lifting) "0" "1" "2" eq_class_to_rel partial_object.select_convs(1) rel_def) 
  have "(a |\<^bsub>rel\<^esub> b) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (b |\<^bsub>rel\<^esub>\<one>) = (\<zero> |\<^bsub>rel\<^esub> b)" 
    by (metis (no_types, hide_lams) assms(4) assms(5) 
       basic_trans_rules(31) class_of_zero_rng_of_frac cring.axioms(1) 
       crng_rng_of_frac ring.ring_simprules(24) ring_hom_closed 
       rng_to_rng_of_frac_def rng_to_rng_of_frac_is_ring_hom subset) 
  then have 4: "((a \<otimes> b) |\<^bsub>rel\<^esub> b)  = (\<zero> |\<^bsub>rel\<^esub> b)" 
    using "1" "3" assms(4) mult_rng_of_frac_fundamental_lemma
      rec_monoid_rng_of_frac_def rec_rng_of_frac_def subset by auto 
  have S: "((a \<otimes> b) , b) \<in> carrier rel" 
      using assms(3) assms(4) rel_def subset by auto 
  have T: "(\<zero>, b) \<in>carrier rel" 
      by (simp add: assms(4) rel_def) 
  then have " ((a \<otimes> b) , b).=\<^bsub>rel\<^esub> (\<zero> , b)"
    using 4 S eq_class_to_rel rel_def by auto   
  then have "eq rel ((a \<otimes> b) , b) (\<zero> , b)" 
    by blast 
  then have "\<exists>t\<in>S. t \<otimes> (b \<otimes> (a \<otimes> b) \<ominus> b \<otimes> \<zero>) = \<zero>"
    using  rel_def by auto 
  then obtain t where "t \<in> S" and "t \<otimes> (b \<otimes> (a \<otimes> b) \<ominus> b \<otimes> \<zero>) = \<zero>" 
    by blast 
  have "t \<noteq>\<zero>" 
    using \<open>t \<in> S\<close> assms(2) by blast 
  then have "(b \<otimes> (a \<otimes> b) \<ominus> b \<otimes> \<zero>) = \<zero>" 
    by (meson \<open>t \<in> S\<close> \<open>t \<otimes> (b \<otimes> (a \<otimes> b) \<ominus> b \<otimes> \<zero>) = \<zero>\<close> assms(1) assms(3) 
        assms(4) domain.integral_iff minus_closed semiring_simprules(3)
        set_mp subset zero_closed)
  then have "b \<otimes> (a \<otimes> b) = \<zero>" 
    using "3" S rel_def abelian_group.minus_to_eq is_abelian_group by fastforce 
  then show "a = \<zero>" 
    by (metis (no_types, lifting) assms(1) assms(2) 
        assms(3) assms(4) domain.integral_iff 
        semiring_simprules(3) subset subsetCE) 
qed


text\<open>************************************************************************************************\<close>
text\<open>************************************************************************************************\<close>
text\<open>************When S does not contain 0, and R is a domain, the localization is a domain.*********\<close>
text\<open>************************************************************************************************\<close>
text\<open>************************************************************************************************\<close>


lemma(in eq_obj_rng_of_frac) rec_rng_of_frac_is_domain:
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  shows "domain rec_rng_of_frac"
proof(rule domainI)
  show "cring rec_rng_of_frac" 
   by (simp add: crng_rng_of_frac) 
  show "\<one>\<^bsub>rec_rng_of_frac\<^esub> \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>" 
 proof-
    have  " \<one>\<^bsub>R\<^esub> \<noteq> \<zero>\<^bsub>R\<^esub>" 
      by (simp add: assms domain.one_not_zero) 
    then have 0: " \<one>\<^bsub>R\<^esub> \<notin> (a_kernel  R  rec_rng_of_frac rng_to_rng_of_frac)"  
      using assms(1) rng_to_rng_of_frac_without_zero_div_is_inj 
      by (simp add: assms(2) domain_axioms_def domain_def) 
    then have "rng_to_rng_of_frac \<one> \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>" 
      by (simp add: a_kernel_def') 
    then show ?thesis 
      using ring_hom_one rng_to_rng_of_frac_is_ring_hom by blast 
  qed 
  show "\<And>a b. a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> b = \<zero>\<^bsub>rec_rng_of_frac\<^esub> \<Longrightarrow>
           a \<in> carrier rec_rng_of_frac \<Longrightarrow>
           b \<in> carrier rec_rng_of_frac \<Longrightarrow> 
           a = \<zero>\<^bsub>rec_rng_of_frac\<^esub> \<or> b = \<zero>\<^bsub>rec_rng_of_frac\<^esub>"
  proof-
    fix a b
    assume A1: "a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> b = \<zero>\<^bsub>rec_rng_of_frac\<^esub>"
    assume A2: " a \<in> carrier rec_rng_of_frac"
    assume A3: "b \<in> carrier rec_rng_of_frac"
    show "a = \<zero>\<^bsub>rec_rng_of_frac\<^esub> \<or> b = \<zero>\<^bsub>rec_rng_of_frac\<^esub>"
    proof(rule disjCI)
      assume "b \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>" 
      have "\<not> a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub> "
      proof
        assume "a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>"
        have B1: "numer a \<noteq> \<zero>" 
          using A2 \<open>a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> assms(1) assms(2) numer_denom_facts0(4) by blast 
        have B2: "numer b \<noteq> \<zero>" 
          using A3 \<open>b \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> assms(1) assms(2) numer_denom_facts0(4) by blast 
        have B3: "denom a \<noteq>\<zero>" 
          using A2 \<open>a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> assms(1) assms(2)
            eq_obj_rng_of_frac.numer_denom_facts0(1) eq_obj_rng_of_frac_axioms 
            using numer_denom_facts0(3) by force 
        have B4: "denom b \<noteq>\<zero>" 
          using A3 \<open>b \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> assms(1) assms(2) 
            eq_obj_rng_of_frac_axioms by (metis (no_types, lifting) numer_denom_facts0(3)) 
        have "a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> b = (((numer a) \<otimes> (numer b)) |\<^bsub>rel\<^esub> ((denom a) \<otimes> (denom b)))"
        proof-
          have S0: "a = (numer a |\<^bsub>rel\<^esub> denom a)"
            by (simp add: A2 \<open>a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> assms(1) assms(2) numer_denom_facts0(1)) 
          have S1: "b= (numer b |\<^bsub>rel\<^esub> denom b)" 
            by (simp add: A3 \<open>b \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> assms(1) assms(2) numer_denom_facts0(1))    
          have S2: "(numer a, denom a) \<in> carrier rel" 
            using A2 \<open>a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> assms(1) assms(2) 
              eq_obj_rng_of_frac.numer_denom_facts0(2) eq_obj_rng_of_frac.numer_denom_facts0(3)
              eq_obj_rng_of_frac_axioms rel_def by fastforce 
          have S3: "(numer b, denom b) \<in> carrier rel" 
            using A3 \<open>b \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> assms(1) assms(2)
              eq_obj_rng_of_frac.numer_denom_facts0(2) eq_obj_rng_of_frac_axioms
              numer_denom_facts0(3) rel_def by auto 
          show ?thesis using S0 S1 S2 S3 mult_rng_of_frac_fundamental_lemma 
            using rec_monoid_rng_of_frac_def rec_rng_of_frac_def by force 
        qed 
        then have "(((numer a) \<otimes> (numer b)) |\<^bsub>rel\<^esub> ((denom a) \<otimes> (denom b))) = \<zero>\<^bsub>rec_rng_of_frac\<^esub>" 
          using A1 by blast 
        then have "(numer a) \<otimes> (numer b) = \<zero>" 
          by (meson A2 A3 \<open>a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> \<open>b \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close>
              assms(1) assms(2) eq_obj_rng_of_frac.numer_denom_facts0(2) 
              eq_obj_rng_of_frac.numer_denom_facts0(3) eq_obj_rng_of_frac_axioms
              frac_zero m_closed semiring_simprules(3))
        then show False 
          by (meson A2 A3 B1 B2 \<open>a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> 
              \<open>b \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> assms(1) assms(2) 
              domain.integral_iff eq_obj_rng_of_frac.numer_denom_facts0(2) 
              eq_obj_rng_of_frac_axioms)
      qed
      then show "a = \<zero>\<^bsub>rec_rng_of_frac\<^esub>" 
        by auto 
    qed
  qed
qed

lemma(in eq_obj_rng_of_frac) numer_denom_facts:
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  assumes "a \<in> carrier rec_rng_of_frac"
  shows "a = ((numer a) |\<^bsub>rel\<^esub> (denom a))"
        "(numer a) \<in> carrier R"
        "(denom a) \<in> S"
        "a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub> \<Longrightarrow> (numer a) \<noteq>\<zero>"
        "a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (rng_to_rng_of_frac(denom a)) = rng_to_rng_of_frac (numer a)"
  using assms(1) assms(2) assms(3) class_of_zero_rng_of_frac denom_def
    numer_def numer_denom_facts0(1) apply auto[1] 
  using assms(1) assms(2) assms(3) numer_def numer_denom_facts0(2) apply auto[1] 
  using assms(1) assms(2) assms(3) denom_def numer_denom_facts0(3) apply auto[1] 
  using assms(1) assms(2) assms(3) numer_denom_facts0(4) apply blast 
  by (metis (mono_tags, hide_lams) assms(1) assms(2) assms(3)
      class_of_zero_rng_of_frac denom_def monoid.simps(1) 
      monoid.simps(2) numer_def numer_denom_facts0(5) 
      one_closed partial_object.select_convs(1) rec_rng_of_frac_def
      ring.ring_simprules(24) ring.ring_simprules(6) rng_rng_of_frac rng_to_rng_of_frac_def)

lemma(in eq_obj_rng_of_frac) numer_denom_facts2:
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  assumes "a \<in> carrier rec_rng_of_frac"
  shows "(numer a, denom a) \<in> carrier rel"
  by (simp add: assms(1) assms(2) assms(3) numer_denom_facts(2) numer_denom_facts(3) rel_def) 


text\<open>************************************************************************************************\<close>
text\<open>************************************************************************************************\<close>
text\<open>****************Fraction function which suppresses the "rel" argument***************************\<close>
text\<open>************************************************************************************************\<close>
text\<open>************************************************************************************************\<close>

definition(in eq_obj_rng_of_frac) fraction where
"fraction x y = (x |\<^bsub>rel\<^esub> y)"

lemma(in eq_obj_rng_of_frac) a_is_fraction:
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  assumes "a \<in> carrier rec_rng_of_frac" 
  shows "a = fraction (numer a) (denom a)"
  by (simp add: assms(1) assms(2) assms(3) fraction_def numer_denom_facts(1))  

lemma(in eq_obj_rng_of_frac) add_fraction:
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  assumes "a \<in> carrier R"
  assumes "b \<in> S"
  assumes "c \<in> carrier R"
  assumes "d \<in> S"
  shows "(fraction a b) \<oplus>\<^bsub>rec_rng_of_frac\<^esub> (fraction c d) = (fraction ((d \<otimes> a) \<oplus> (b \<otimes> c)) (b \<otimes> d))"
proof-
  have 0:"(a,b) \<in> carrier rel"
    by (simp add: assms(3) assms(4) rel_def) 
  have 1:"(c,d) \<in> carrier rel" 
    by (simp add: assms(5) assms(6) rel_def) 
  show ?thesis
    using 0 1 add_rng_of_frac_fundamental_lemma 
      numer_denom_facts fraction_def by simp
qed

lemma(in eq_obj_rng_of_frac) mult_fraction:
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  assumes "a \<in> carrier R"
  assumes "b \<in> S"
  assumes "c \<in> carrier R"
  assumes "d \<in> S"
  shows "(fraction a b) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (fraction c d) = (fraction (a \<otimes> c) (b \<otimes> d))"
proof-
  have 0:"(a,b) \<in> carrier rel"
    by (simp add: assms(3) assms(4) rel_def) 
  have 1:"(c,d) \<in> carrier rel" 
    by (simp add: assms(5) assms(6) rel_def) 
  show ?thesis using 0 1 mult_rng_of_frac_fundamental_lemma 
    by (simp add: fraction_def rec_monoid_rng_of_frac_def rec_rng_of_frac_def)
qed

lemma(in eq_obj_rng_of_frac) fraction_zero:
"\<zero>\<^bsub>rec_rng_of_frac\<^esub> = fraction \<zero> \<one> " 
  by (simp add: class_of_zero_rng_of_frac fraction_def) 

lemma(in eq_obj_rng_of_frac) fraction_zero':
  assumes "a \<in> S"
  assumes "\<zero> \<notin> S"
  shows "\<zero>\<^bsub>rec_rng_of_frac\<^esub> = fraction \<zero> a" 
  by (simp add: assms(1) class_of_zero_rng_of_frac fraction_def) 

lemma(in eq_obj_rng_of_frac) fraction_one:
"\<one>\<^bsub>rec_rng_of_frac\<^esub> = fraction \<one> \<one>"
  by (simp add: fraction_def rec_rng_of_frac_def) 

lemma(in eq_obj_rng_of_frac) fraction_one':
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  assumes "a \<in> S"
  shows "fraction a a = \<one>\<^bsub>rec_rng_of_frac\<^esub>"
using fraction_def add_fraction assms(1) assms(2) assms(3) fraction_one
      fraction_zero' l_one one_closed r_one r_zero set_mp subset zero_closed
  by smt
lemma(in eq_obj_rng_of_frac) fraction_im:
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  assumes "a \<in> carrier R"
  assumes "b \<in> S"
  shows "fraction a b \<in>carrier rec_rng_of_frac" 
proof-
  have "(a,b) \<in> carrier rel" 
    by (simp add: assms(3) assms(4) rel_def) 
  then have "(a |\<^bsub>rel\<^esub> b) \<in> set_class_of\<^bsub>rel\<^esub>"  
    using  set_eq_class_of_rng_of_frac_def  
    by blast
  then show ?thesis using fraction_def 
    by (simp add: rec_rng_of_frac_def) 
qed

text\<open>************************************************************************************************\<close>
text\<open>************************************************************************************************\<close>
text\<open>*************************Defining the Field of Fractions****************************************\<close>
text\<open>************************************************************************************************\<close>
text\<open>************************************************************************************************\<close>

definition(in domain) Frac where
"Frac  = eq_obj_rng_of_frac.rec_rng_of_frac R (nonzero R)"

lemma(in domain) fraction_field_is_domain:
"domain Frac"
  using domain_axioms eq_obj_rng_of_frac.rec_rng_of_frac_is_domain 
    eq_obj_rng_of_frac_nonzero Frac_def nonzero_def by fastforce 

definition(in domain) numer where
"numer = eq_obj_rng_of_frac.numer R (nonzero R)"

definition(in domain) denom where
"denom = eq_obj_rng_of_frac.denom  R (nonzero R)"

definition(in domain) frac where
"frac = eq_obj_rng_of_frac.fraction  R (nonzero R)"

text\<open>************************************************************************************************\<close>
text\<open>************************************************************************************************\<close>
text\<open>***************************The inclusion of R into its fraction field***************************\<close>
text\<open>************************************************************************************************\<close>
text\<open>************************************************************************************************\<close>

definition(in domain) inc ("\<iota>") where
"inc =  eq_obj_rng_of_frac.rng_to_rng_of_frac R (nonzero R)"

lemma(in domain) inc_equation:
  assumes "a \<in> carrier R"
  shows "\<iota> a = frac a \<one>"
  using inc_def  
  by (simp add: eq_obj_rng_of_frac.rng_to_rng_of_frac_def
      eq_obj_rng_of_frac.fraction_def eq_obj_rng_of_frac_nonzero local.frac_def) 


lemma(in domain) inc_is_hom:
"inc \<in> ring_hom R Frac"
  by (simp add: eq_obj_rng_of_frac.rng_to_rng_of_frac_is_ring_hom Frac_def 
      eq_obj_rng_of_frac_nonzero local.inc_def) 

lemma(in domain) inc_is_hom1:
"ring_hom_ring R Frac inc"
  apply(intro ring_hom_ringI2)
  apply(auto simp:inc_is_hom)
  apply (simp add: local.ring_axioms)
  using cring_def domain.axioms(1)
    fraction_field_is_domain by auto 

text\<open>Inclusion map is injective\<close>

lemma(in domain) inc_inj0:
"a_kernel R Frac inc = {\<zero>}"
proof-
  have 0: "\<zero> \<notin> nonzero R" 
    by (simp add: nonzero_def) 
  have 1: "eq_obj_rng_of_frac R (nonzero R)" 
    by (simp add: eq_obj_rng_of_frac_nonzero) 
  have 2: "\<forall> a\<in> carrier R. \<forall> b\<in>carrier R. a \<otimes> b = \<zero> \<longrightarrow> a = \<zero> \<or> b = \<zero>" 
    using local.integral by blast 
  show ?thesis using 0 1 2  
    by (simp add: eq_obj_rng_of_frac.rng_to_rng_of_frac_without_zero_div_is_inj
        Frac_def local.inc_def) 
qed

lemma(in domain) inc_inj1:
  assumes "a \<in> carrier R"
  assumes "inc a = \<zero>\<^bsub>Frac\<^esub>"
  shows "a = \<zero>"
proof-
  have "a \<in> a_kernel R Frac inc" using  a_kernel_def' assms(2)  
    by (simp add: a_kernel_def' assms(1)) 
  then show ?thesis
    using inc_inj0  by blast 
qed

lemma(in domain) inc_inj2:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "inc a = inc b"
  shows "a = b"
proof-
  have "inc (a \<ominus> b) = (inc a) \<oplus>\<^bsub>Frac\<^esub> (inc (\<ominus> b))" 
    using inc_is_hom by (simp add: ring_hom_add assms(1) assms(2) minus_eq) 
  then have "inc (a \<ominus> b) = \<zero>\<^bsub>Frac\<^esub>" using assms inc_is_hom 
    by (smt Frac_def add.inv_closed eq_obj_rng_of_frac.rng_rng_of_frac
        eq_obj_rng_of_frac_nonzero local.ring_axioms r_neg ring_hom_add ring_hom_zero) 
  then show ?thesis 
    by (meson abelian_group.minus_to_eq assms(1) assms(2)
        domain.inc_inj1 domain_axioms is_abelian_group minus_closed) 
qed

text\<open>Image of inclusion map is a subring\<close>

lemma(in domain) inc_im_is_subring:
"subring (\<iota> ` (carrier R)) Frac" 
  using carrier_is_subring inc_is_hom1 ring_hom_ring.img_is_subring by blast 

text\<open>Fundamental properties of numer , denom, and frac\<close>

lemma(in domain) numer_denom_facts:
  assumes "a \<in> carrier Frac"
  shows "(numer a) \<in> carrier R"
        "(denom a) \<in> nonzero R"
        "a \<noteq>  \<zero>\<^bsub>Frac\<^esub> \<Longrightarrow> numer a \<noteq> \<zero> "
        "a \<otimes>\<^bsub>Frac\<^esub> (inc (denom a)) = inc (numer a)"
        "a = frac (numer a) (denom a)"
proof
  show "(numer a) \<in> carrier R" 
    using Frac_def assms domain_axioms eq_obj_rng_of_frac.numer_denom_facts(2)
      eq_obj_rng_of_frac_nonzero nonzero_def numer_def by fastforce 
  show "(denom a) \<in> nonzero R"
    using Frac_def assms denom_def domain_axioms eq_obj_rng_of_frac.numer_denom_facts(3)
    eq_obj_rng_of_frac_nonzero nonzero_def by fastforce 
  show "a \<noteq>  \<zero>\<^bsub>Frac\<^esub> \<Longrightarrow> numer a \<noteq> \<zero> "
    using Frac_def assms domain_axioms eq_obj_rng_of_frac.numer_denom_facts(4)
      eq_obj_rng_of_frac_nonzero nonzero_def numer_def by fastforce 
  show "a \<otimes>\<^bsub>Frac\<^esub> (inc (denom a)) = inc (numer a)" 
    using Frac_def assms denom_def domain_axioms eq_obj_rng_of_frac.numer_denom_facts(5)
      eq_obj_rng_of_frac_nonzero local.inc_def nonzero_def numer_def by fastforce 
  show "a = frac (numer a) (denom a)"
    using  eq_obj_rng_of_frac.a_is_fraction frac_def assms 
      Frac_def denom_def domain_axioms eq_obj_rng_of_frac_nonzero 
      nonzero_def numer_def by fastforce
  show "carrier R \<subseteq> carrier R" by auto
qed

lemma(in domain) frac_add:
  assumes "a \<in> carrier R"
  assumes "b \<in> nonzero R"
  assumes "c \<in> carrier R"
  assumes "d \<in> nonzero R"
  shows "(frac a b) \<oplus>\<^bsub>Frac\<^esub> (frac c d) = (frac ((a \<otimes> d) \<oplus> (b \<otimes> c)) (b \<otimes> d))"
  using eq_obj_rng_of_frac.add_fraction Frac_def assms(1) assms(2) assms(3) assms(4)
    domain_axioms eq_obj_rng_of_frac_nonzero frac_def m_comm mem_Collect_eq nonzero_def by fastforce 

lemma(in domain) frac_mult:
  assumes "a \<in> carrier R"
  assumes "b \<in> nonzero R"
  assumes "c \<in> carrier R"
  assumes "d \<in> nonzero R"
  shows "(frac a b) \<otimes>\<^bsub>Frac\<^esub> (frac c d) = (frac (a \<otimes> c) (b \<otimes> d))"
  using eq_obj_rng_of_frac.mult_fraction Frac_def assms(1) assms(2) assms(3) assms(4) 
    domain_axioms eq_obj_rng_of_frac_nonzero frac_def nonzero_def by fastforce

lemma(in domain) frac_one:
  assumes "a \<in> nonzero R"
  shows "frac a a = \<one>\<^bsub>Frac\<^esub>"
  using eq_obj_rng_of_frac.fraction_one' Frac_def 
    assms domain_axioms eq_obj_rng_of_frac_nonzero frac_def nonzero_def by fastforce 

lemma(in domain) frac_im:
  assumes "a \<in> carrier R"
  assumes "b \<in> nonzero R"
  shows "frac a b \<in> carrier Frac"
  using Frac_def eq_obj_rng_of_frac.fraction_im  assms(1) assms(2)
    domain_axioms eq_obj_rng_of_frac_nonzero frac_def nonzero_def by fastforce 


lemma(in domain) nonzero_fraction:
  assumes "a \<in> nonzero R"
  assumes "b \<in> nonzero R"
  shows "frac a b \<noteq> \<zero>\<^bsub>Frac\<^esub>"
proof
  assume "frac a b = \<zero>\<^bsub>Frac\<^esub>"
  then have "(frac a b) \<otimes>\<^bsub>Frac\<^esub> (frac b a) = \<zero>\<^bsub>Frac\<^esub> \<otimes>\<^bsub>Frac\<^esub> (frac b a)"
    by simp 
  then have "(frac a b) \<otimes>\<^bsub>Frac\<^esub> (frac b a) = \<zero>\<^bsub>Frac\<^esub>"
    by (metis Localization.submonoid.subset assms(1) assms(2) cring.cring_simprules(26) 
      domain.axioms(1) frac_im fraction_field_is_domain nonzero_is_submonoid subsetCE) 
  then have "frac (a \<otimes>b)  (b \<otimes> a)  = \<zero>\<^bsub>Frac\<^esub>"
    by (metis (no_types, lifting) Localization.submonoid.subset 
        assms(1) assms(2) frac_mult nonzero_is_submonoid subsetCE) 
  then have "frac (a \<otimes>b)  (a \<otimes> b)  = \<zero>\<^bsub>Frac\<^esub>"
    by (metis (no_types, lifting) Localization.submonoid.subset assms(1) assms(2) m_comm nonzero_is_submonoid subsetCE) 
  then have "\<one>\<^bsub>Frac\<^esub> = \<zero>\<^bsub>Frac\<^esub>" 
    using Localization.submonoid.m_closed assms(1) assms(2) frac_one nonzero_is_submonoid by force 
  then show False 
    using domain.one_not_zero fraction_field_is_domain by blast 
qed

lemma(in domain) units_of_fraction_field0:
  assumes "a \<in> carrier Frac"
  assumes "a \<noteq> \<zero>\<^bsub>Frac\<^esub>"
  shows "inv\<^bsub>Frac\<^esub> a = frac (denom a) (numer a)"
        "a\<otimes>\<^bsub>Frac\<^esub> (inv\<^bsub>Frac\<^esub> a)   = \<one>\<^bsub>Frac\<^esub>"
proof-
  have 0: "a \<otimes>\<^bsub>Frac\<^esub> (frac (denom a) (numer a)) =
    frac ((numer a) \<otimes> (denom a)) ((numer a) \<otimes> (denom a))"
  proof -
    have "denom a \<in> {a \<in> carrier R. a \<noteq> \<zero>}"
      by (metis (no_types) assms(1) nonzero_def numer_denom_facts(2))
    then have "frac (numer a) (denom a) \<otimes>\<^bsub>Frac\<^esub> frac (denom a) (numer a)
      = frac (numer a \<otimes> denom a) (denom a \<otimes> numer a)"
      by (simp add: assms(1) assms(2) frac_mult nonzero_def numer_denom_facts(1) numer_denom_facts(3))
    then show ?thesis
      using assms(1) numer_denom_facts(5) 
        \<open>denom a \<in> {a \<in> carrier R. a \<noteq> \<zero>}\<close> domain.numer_denom_facts(1)
        domain_axioms m_comm by fastforce 
  qed 
  have 1:"((numer a) \<otimes> (denom a)) \<in> nonzero R"
    by (metis (mono_tags, lifting) Localization.submonoid.m_closed assms(1)
        assms(2) domain.nonzero_is_submonoid domain.numer_denom_facts(1)
        domain.numer_denom_facts(2) domain.numer_denom_facts(3)
        domain_axioms mem_Collect_eq nonzero_def) 
  have  2: "a \<otimes>\<^bsub>Frac\<^esub> (frac (denom a) (numer a)) = \<one>\<^bsub>Frac\<^esub>" 
    using 0 1 frac_one by blast
  have "(frac (denom a) (numer a)) \<in> carrier Frac" 
    using assms  by (metis (full_types, lifting) 
        Localization.submonoid.subset domain.frac_im domain.numer_denom_facts(1)
        domain.numer_denom_facts(3) domain_axioms 
        mem_Collect_eq nonzero_def nonzero_is_submonoid numer_denom_facts(2) subsetCE) 
  then have "(frac (denom a) (numer a)) \<in> carrier Frac \<and>
             a \<otimes>\<^bsub>Frac\<^esub> (frac (denom a) (numer a))  = \<one>\<^bsub>Frac\<^esub> \<and> 
           (frac (denom a) (numer a))  \<otimes>\<^bsub>Frac\<^esub> a  = \<one>\<^bsub>Frac\<^esub>"
    by (simp add: "2" assms(1) cring.cring_simprules(14) domain.axioms(1) fraction_field_is_domain)
  then show "inv\<^bsub>Frac\<^esub> a = frac (denom a) (numer a)"
    using m_inv_def 2 assms(1) comm_monoid.comm_inv_char cring_def
      domain_def fraction_field_is_domain by fastforce
  then show "a\<otimes>\<^bsub>Frac\<^esub> (inv\<^bsub>Frac\<^esub> a)   = \<one>\<^bsub>Frac\<^esub>" 
    by (simp add: "2") 
qed

lemma(in domain) units_of_fraction_field:
"Units Frac = carrier Frac - {\<zero>\<^bsub>Frac\<^esub>}"
proof
  show "Units Frac \<subseteq> carrier Frac - {\<zero>\<^bsub>Frac\<^esub>}"
  proof fix x assume "x \<in> Units Frac"
    have "x \<in> carrier Frac" 
      using Units_def \<open>x \<in> Units Frac\<close> by force 
    then have "x \<noteq> \<zero>\<^bsub>Frac\<^esub>" 
      by (smt Units_def \<open>x \<in> Units Frac\<close> cring.cring_simprules(26) 
          domain.axioms(1) domain.one_not_zero fraction_field_is_domain mem_Collect_eq)
    then show "x \<in> carrier Frac - {\<zero>\<^bsub>Frac\<^esub>}" 
      by (simp add: \<open>x \<in> carrier Frac\<close>) 
  qed
  show "carrier Frac - {\<zero>\<^bsub>Frac\<^esub>} \<subseteq> Units Frac"
  proof fix x assume "x \<in> carrier Frac - {\<zero>\<^bsub>Frac\<^esub>}"
    then show "x \<in> Units Frac"
      using units_of_fraction_field0(2) 
      by (smt DiffD1 DiffD2 Units_def domain.numer_denom_facts(1)
          domain.numer_denom_facts(2) domain.numer_denom_facts(3)
          domain.units_of_fraction_field0(1) domain.units_of_fraction_field0(2)
          domain_axioms frac_im frac_mult insertCI m_comm mem_Collect_eq 
          nonzero_def numer_denom_facts(5)) 
  qed
qed



text\<open>The fraction field is a field!\<close>

lemma(in domain) fraction_field_is_field:
"field Frac"
proof(rule Ring.field.intro)
  show "domain Frac" apply(auto simp: fraction_field_is_domain)
    done
  show "field_axioms Frac"
  proof
    show "Units Frac = carrier Frac - {\<zero>\<^bsub>Frac\<^esub>}" 
      using units_of_fraction_field by blast 
  qed
qed

lemma(in domain) frac_inv:
  assumes "a \<in> nonzero R"
  assumes "b \<in> nonzero R" 
  shows "inv\<^bsub>Frac\<^esub> (frac a b) = (frac b a)"
proof-
  have "(frac a b) \<otimes>\<^bsub>Frac\<^esub> (frac b a) = frac (a \<otimes> b) (b \<otimes> a)" 
    by (meson Localization.submonoid.subset assms(1) assms(2) frac_mult nonzero_is_submonoid subsetCE) 
  then have 0:"(frac a b) \<otimes>\<^bsub>Frac\<^esub> (frac b a) = \<one>\<^bsub>Frac\<^esub>"
    by (metis Localization.submonoid.m_closed Localization.submonoid.subset assms(1) assms(2) frac_one m_comm nonzero_is_submonoid subsetCE) 
  have 1: "(frac a b)  \<in> carrier Frac" 
    using Localization.submonoid.subset assms(1) assms(2) frac_im nonzero_is_submonoid by blast 
  have 2: "(frac b a) \<in> carrier Frac " 
    using Localization.submonoid.subset assms(1) assms(2) frac_im nonzero_is_submonoid by blast 
  have 3: "(frac b a) \<noteq> \<zero>\<^bsub>Frac\<^esub>" 
    by (simp add: assms(1) assms(2) nonzero_fraction) 
  have 4: "(frac a b) \<noteq> \<zero>\<^bsub>Frac\<^esub>" 
    by (simp add: assms(1) assms(2) nonzero_fraction) 
  show ?thesis using 0 1 2 3 4 fraction_field_is_field field_def domain_def cring_def 
    by (simp add: comm_monoid.comm_inv_char cring.axioms(2) fieldE(1)) 
qed

lemma(in domain) frac_inv_id:
  assumes "a \<in> nonzero R"
  assumes "b \<in> nonzero R" 
  assumes "c \<in> nonzero R"
  assumes "d \<in> nonzero R" 
  assumes "frac a b = frac c d"
  shows "frac b a = frac d c"
  using frac_inv assms  by metis  

lemma(in domain) frac_uminus:
  assumes "a \<in> carrier  R"
  assumes "b \<in> nonzero R"
  shows "\<ominus>\<^bsub>Frac\<^esub> (frac a b) = frac (\<ominus> a) b" 
proof-
  have "frac (\<ominus> a) b \<oplus>\<^bsub>Frac\<^esub> (frac a b) = frac (((\<ominus> a)\<otimes>b) \<oplus> (a \<otimes>b)) (b\<otimes>b)"
    using frac_add  by (smt Localization.submonoid.subset add.inv_closed
        assms(1) assms(2) m_comm nonzero_is_submonoid subsetCE) 
  then have "frac (\<ominus> a) b \<oplus>\<^bsub>Frac\<^esub> (frac a b) = frac (b \<otimes>((\<ominus> a) \<oplus> a)) (b\<otimes>b)" 
    by (metis (no_types, lifting) add.inv_closed  assms(1) assms(2)
        local.ring_axioms m_comm mem_Collect_eq nonzero_def ringE(4) )
  then have "frac (\<ominus> a) b \<oplus>\<^bsub>Frac\<^esub> (frac a b) = (frac \<zero> (b \<otimes>b))"  
    using Localization.submonoid.subset assms(1) assms(2) l_neg nonzero_is_submonoid by fastforce 
  then have "frac (\<ominus> a) b \<oplus>\<^bsub>Frac\<^esub> (frac a b) = (frac \<zero> \<one>) \<otimes>\<^bsub>Frac\<^esub>  (frac \<zero> (b \<otimes>b))"
    using frac_mult    by (smt Localization.submonoid.m_closed Localization.submonoid.one_closed
        Localization.submonoid.subset assms(2) l_one nonzero_is_submonoid r_null subsetCE zero_closed) 
  then have "frac (\<ominus> a) b \<oplus>\<^bsub>Frac\<^esub> (frac a b) = \<zero>\<^bsub>Frac\<^esub> \<otimes>\<^bsub>Frac\<^esub>  (frac \<zero> (b \<otimes>b))" 
    using Frac_def eq_obj_rng_of_frac.fraction_zero' eq_obj_rng_of_frac_nonzero local.frac_def nonzero_def by fastforce 
  then have "frac (\<ominus> a) b \<oplus>\<^bsub>Frac\<^esub> (frac a b) = \<zero>\<^bsub>Frac\<^esub>"
    using fraction_field_is_field 
    by (simp add: Localization.submonoid.m_closed assms(2) cring.cring_simprules(26)
        domain.axioms(1) frac_im fraction_field_is_domain nonzero_is_submonoid)
  then show ?thesis 
    by (metis add.inv_closed assms(1) assms(2) cring.sum_zero_eq_neg
        domain.axioms(1) frac_im fraction_field_is_domain) 
qed

lemma(in domain) frac_cancel_l:
  assumes "a \<in>nonzero R"
  assumes "b \<in>nonzero R"
  assumes "c \<in>carrier R"
  shows "frac (a \<otimes>c) (a \<otimes>b) = frac c b" 
proof-
  have 0: "frac (a \<otimes>c) (a \<otimes>b) =(frac b b) \<otimes>\<^bsub>Frac\<^esub> (frac c b)" 
    by (metis (no_types, lifting) assms(1) assms(2) assms(3)
        frac_mult frac_one mem_Collect_eq nonzero_def)  
  have 1: "frac b b = \<one>\<^bsub>Frac\<^esub>" 
    by (simp add: assms(2) frac_one) 
  show ?thesis using 0 1 
    using Frac_def assms(2) assms(3) eq_obj_rng_of_frac.rng_rng_of_frac 
      eq_obj_rng_of_frac_nonzero frac_im ring.ring_simprules(12) by fastforce 
qed

lemma(in domain) frac_cancel_r:
  assumes "a \<in>nonzero R"
  assumes "b \<in>nonzero R"
  assumes "c \<in>carrier R"
  shows "frac (c \<otimes>a) (b \<otimes>a) = frac c b"
  by (metis (no_types, lifting) Localization.submonoid.subset assms(1)
      assms(2) assms(3) frac_cancel_l m_comm nonzero_is_submonoid subsetCE) 

lemma(in domain) frac_cancel_lr:
  assumes "a \<in>nonzero R"
  assumes "b \<in>nonzero R"
  assumes "c \<in>carrier R"
  shows "frac (a \<otimes>c) (b \<otimes>a) = frac c b"
  by (metis (no_types, lifting) Localization.submonoid.subset assms(1)
      assms(2) assms(3) frac_cancel_l m_comm nonzero_is_submonoid subsetCE) 

lemma(in domain) frac_cancel_rl:
  assumes "a \<in>nonzero R"
  assumes "b \<in>nonzero R"
  assumes "c \<in>carrier R"
  shows "frac (c \<otimes>a) (a \<otimes>b) = frac c b"
  by (metis (no_types, lifting) Localization.submonoid.subset assms(1)
      assms(2) assms(3) frac_cancel_l m_comm nonzero_is_submonoid subsetCE)

lemma(in domain) i_mult:
  assumes "a \<in> carrier R"
  assumes "c \<in> carrier R"
  assumes "d \<in> nonzero R"
  shows "(\<iota> a) \<otimes>\<^bsub>Frac\<^esub> (frac c d) = frac (a \<otimes> c) d"
proof-
  have "(\<iota> a) \<otimes>\<^bsub>Frac\<^esub> (frac c d) = (frac a \<one>) \<otimes>\<^bsub>Frac\<^esub> (frac c d)" 
    by (simp add: assms(1) inc_equation)
  then show ?thesis 
    by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) cring_simprules(12) 
        cring_simprules(6) frac_mult local.one_not_zero mem_Collect_eq nonzero_def)
qed

lemma(in domain) frac_eq:
  assumes "a \<in> carrier R"
  assumes "b \<in> nonzero R"
  assumes "c \<in> carrier R"
  assumes "d \<in> nonzero R"
  assumes "frac a b = frac c d"
  shows "a \<otimes> d = b \<otimes> c"
proof-
  have "(\<iota> b) \<otimes>\<^bsub>Frac\<^esub> (frac a b) = (\<iota> b) \<otimes>\<^bsub>Frac\<^esub> (frac c d)" 
    by (simp add: assms(5))
  then have "(frac (a \<otimes> b)  b) = (frac (c \<otimes> b) d)" 
    using i_mult 
    by (metis (no_types, lifting) Localization.submonoid.subset assms(1) 
        assms(2) assms(3) assms(4) m_comm nonzero_is_submonoid subsetCE)
  then have "(frac a  \<one>) = (frac (c \<otimes> b) d)"
    by (smt assms(1) assms(2) frac_cancel_r l_one mem_Collect_eq nonzero_def one_closed zero_not_one)
  then have "(\<iota> d) \<otimes>\<^bsub>Frac\<^esub>(frac a  \<one>) =(\<iota> d) \<otimes>\<^bsub>Frac\<^esub> (frac (c \<otimes> b) d)"
    by auto
  then have "(frac (a \<otimes> d) \<one>) =(frac ((c \<otimes> b)\<otimes> d) d)"
    using i_mult    
    by (smt Localization.submonoid.m_closed Localization.submonoid.subset assms(1) assms(2) assms(3)
        assms(4) cring_simprules(27) cring_simprules(6) local.one_not_zero m_comm
        mem_Collect_eq nonzero_def nonzero_is_submonoid)
  then have "(frac (a \<otimes> d) \<one>) =(frac (c \<otimes> b) \<one>)" 
    by (smt Localization.submonoid.subset assms(2) assms(3) assms(4) cring_simprules(5)
        cring_simprules(6) frac_one i_mult inc_equation inc_is_hom nonzero_is_submonoid
        r_one ring_hom_mult ring_hom_one subsetCE)
  then show ?thesis 
    by (metis (no_types, lifting) Localization.submonoid.subset assms(1) assms(2) assms(3) assms(4)
        domain.inc_inj2 domain_axioms inc_equation m_closed m_comm nonzero_is_submonoid subsetCE)
qed

lemma(in domain) frac_add_common_denom:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "c \<in> nonzero R"
  shows "(frac a c) \<oplus>\<^bsub>Frac\<^esub> (frac b c) = frac (a \<oplus> b) c"
proof-
  have "(frac a c) \<oplus>\<^bsub>Frac\<^esub> (frac b c) = frac ((a \<otimes> c) \<oplus> (b \<otimes> c)) (c \<otimes> c)"
    using assms(1) assms(2) assms(3) domain.frac_add domain_axioms local.frac_eq by fastforce
  then have "(frac a c) \<oplus>\<^bsub>Frac\<^esub> (frac b c) = frac ((a \<oplus> b) \<otimes> c) (c \<otimes> c)"
    by (metis Localization.submonoid.subset assms(1) assms(2) assms(3) l_distr nonzero_is_submonoid subsetCE)
  then show ?thesis 
    by (simp add: assms(1) assms(2) assms(3) frac_cancel_r)
qed

lemma(in domain) common_denominator:
  assumes "x \<in> carrier Frac"
  assumes "y \<in> carrier Frac"
  obtains a b c where
    "a \<in> carrier R"
    "b \<in> carrier R" 
    "c \<in> nonzero R"
    "x = frac a c"
    "y = frac b c"
proof-
  obtain x1 x2 where X1: "x1 \<in> carrier R" and X2: "x2 \<in> nonzero R" and Fx: "x = frac x1 x2"
    by (meson assms(1) numer_denom_facts(1) numer_denom_facts(2) numer_denom_facts(5))
  obtain y1 y2 where Y1: "y1 \<in> carrier R" and Y2: "y2 \<in> nonzero R" and Fy: "y = frac y1 y2"
    by (meson assms(2) numer_denom_facts(1) numer_denom_facts(2) numer_denom_facts(5))
  let ?a = "x1 \<otimes> y2"
  let ?b = "y1 \<otimes> x2"
  let ?c = "x2 \<otimes> y2"
  have 0: "?a \<in> carrier R" 
    using X1 Y2  by (simp add: nonzero_def)
  have 1: "?b \<in> carrier R" using Y1 X2 
    by (simp add: nonzero_def)
  have 2: "?c \<in> nonzero R" using X2 Y2 
    by (simp add: Localization.submonoid.m_closed nonzero_is_submonoid)
  have 3: "x = frac ?a ?c" 
    using Fx X1 X2 Y2 frac_cancel_r by auto
  have 4: "y = frac ?b ?c" 
    using Fy X2 Y1 Y2 frac_cancel_rl by auto
  then show ?thesis using 0 1 2 3 4 
    using that by blast
qed

text\<open>inclusions of natural numbers into Frac\<close>

lemma(in domain) nat_0:
"[(0::nat)]\<cdot>\<one> = \<zero>"
  by simp

lemma(in domain) nat_suc:
"[Suc n]\<cdot>\<one> = \<one> \<oplus> [n]\<cdot>\<one>"
  using add.nat_pow_Suc2 by auto

lemma(in domain) nat_inc_rep:
  fixes n::nat
  shows "[n]\<cdot>\<^bsub>Frac\<^esub> \<one>\<^bsub>Frac\<^esub> = frac ([n]\<cdot>\<one>) \<one>"
proof(induction n)
  case 0
  have "[(0::nat)] \<cdot>\<^bsub>Frac\<^esub> \<one>\<^bsub>Frac\<^esub> = \<zero>\<^bsub>Frac\<^esub>"
    using fraction_field_is_domain by (simp add: domain.nat_0)
  then show ?case 
    by (simp add: Frac_def eq_obj_rng_of_frac.fraction_zero eq_obj_rng_of_frac_nonzero local.frac_def)
next
  case (Suc n)
  assume A:  "[n] \<cdot>\<^bsub>Frac\<^esub> \<one>\<^bsub>Frac\<^esub> = frac ([n] \<cdot> \<one>) \<one>"
  have "[Suc n] \<cdot>\<^bsub>Frac\<^esub> \<one>\<^bsub>Frac\<^esub> = \<one>\<^bsub>Frac\<^esub> \<oplus>\<^bsub>Frac\<^esub> [n] \<cdot>\<^bsub>Frac\<^esub> \<one>\<^bsub>Frac\<^esub>" 
    by (simp add: domain.nat_suc fraction_field_is_domain)
  then have "[Suc n] \<cdot>\<^bsub>Frac\<^esub> \<one>\<^bsub>Frac\<^esub> = (frac \<one> \<one>) \<oplus>\<^bsub>Frac\<^esub> (frac ([n] \<cdot> \<one>) \<one>)"
    by (simp add: Suc.IH frac_one nonzero_def)
  then have "[Suc n] \<cdot>\<^bsub>Frac\<^esub> \<one>\<^bsub>Frac\<^esub> = (frac (\<one>\<oplus>[n] \<cdot> \<one>) \<one>)"
    by (simp add: frac_add_common_denom nonzero_def)
  then show ?case 
    using nat_suc by auto
qed

lemma(in domain) pow_0:
  assumes "a \<in> nonzero R"
  shows "a[^](0::nat) = \<one>"
  by simp

lemma(in domain) pow_suc:
  assumes "a \<in> carrier R"
  shows "a[^](Suc n) = a \<otimes>(a[^]n)"
  using assms nat_pow_Suc2 by auto
end