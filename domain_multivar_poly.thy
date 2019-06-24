theory domain_multivar_poly
imports "HOL-Algebra.Indexed_Polynomials"
begin

abbreviation var_set :: "nat \<Rightarrow> nat set" where
"var_set n \<equiv> {(m::nat). m < n}"

lemma var_set_zero:
"var_set 0 = {}"
  by simp

lemma var_set_finite[simp]:
"finite (var_set n)"
  by blast

lemma var_set_card:
"card (var_set n) = n"
  by simp  







end