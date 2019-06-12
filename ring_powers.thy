theory ring_powers
  imports "HOL-Algebra.Chinese_Remainder" full_hensel
begin

(*Powers of a ring*)

fun R_list :: "nat \<Rightarrow> 'a ring \<Rightarrow> ('a ring) list" where
"R_list 0 R = []"|
"R_list (Suc n) R = R#(R_list n R)"

definition cartesian_power :: "'a ring \<Rightarrow> nat \<Rightarrow> ('a list) ring" ("Pow _ _") where
"cartesian_power R n= RDirProd_list (R_list n R)"

lemma R_list_length: 
"length (R_list n R) = n"
  apply(induction n) by auto 

definition(in padic_integers) Q where 
"Q n m = 0"


end