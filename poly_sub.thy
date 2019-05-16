theory poly_sub
imports "~~/src/HOL/Algebra/UnivPoly"
begin

(**************************************************************************************************)
(**************************************************************************************************)
(**********************************    Polynomial Substitution   **********************************)
(**************************************************************************************************)
(**************************************************************************************************)
context UP_cring 
begin 
(*The inclusion of Z\<^sub>p into Zp_x*)
definition(in UP_ring) to_poly where
"to_poly  = (\<lambda>a. monom P a 0)"

lemma(in UP_ring) to_poly_is_ring_hom:
"to_poly \<in> ring_hom R P"
  unfolding to_poly_def
  unfolding P_def
  using UP_ring.const_ring_hom[of R]
  UP_ring_axioms by simp 
  
definition(in UP_ring) sub  (infixl "\<circ>" 70) where
"sub f g = eval R P to_poly g f"

definition(in UP_ring) rev_sub  where
"rev_sub g f = eval R P to_poly g f"

lemma(in UP_ring) sub_rev_sub:
"sub f g = rev_sub g f"
  unfolding sub_def rev_sub_def by simp

lemma(in UP_cring) to_poly_UP_pre_univ_prop:
"UP_pre_univ_prop R P to_poly"
proof 
  show "to_poly \<in> ring_hom R P" 
    by (simp add: to_poly_is_ring_hom)
qed

lemma rev_sub_is_hom:
  assumes "g \<in> carrier P"
  shows "rev_sub g \<in> ring_hom P P"
  unfolding rev_sub_def
  using to_poly_UP_pre_univ_prop assms(1) UP_pre_univ_prop.eval_ring_hom[of R P to_poly g] 
  unfolding P_def apply auto 
  done

lemma rev_sub_add:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "h \<in>carrier P"
  shows "rev_sub g (f \<oplus>\<^bsub>P\<^esub> h) = (rev_sub g f) \<oplus>\<^bsub>P\<^esub> (rev_sub g h)"
  using rev_sub_is_hom assms ring_hom_add by fastforce

lemma rev_sub_mult:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "h \<in>carrier P"
  shows "rev_sub g (f \<otimes>\<^bsub>P\<^esub> h) = (rev_sub g f) \<otimes>\<^bsub>P\<^esub> (rev_sub g h)"
  using rev_sub_is_hom assms ring_hom_mult  by fastforce

lemma rev_sub_to_poly:
  assumes "g \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "rev_sub g (to_poly a) = to_poly a"
  unfolding to_poly_def rev_sub_def
  using to_poly_UP_pre_univ_prop 
  unfolding to_poly_def 
     using P_def UP_pre_univ_prop.eval_const assms(1) assms(2) by fastforce


 

end 
end