theory hensel
  imports Main "~~/src/HOL/Algebra/UnivPoly" "~~/src/HOL/Algebra/Valued_Fields/padic_construction"
begin

definition p_UP :: "nat \<Rightarrow> (nat \<Rightarrow> int, nat \<Rightarrow> nat \<Rightarrow> int) up_ring" where
  "p_UP p = UP (padic_int p)"

fun shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "shift b n = b (n + 1)"

fun mult :: "('a, 'b) ring_scheme \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "mult R b n = add_pow R n (b n)"

definition derivative :: "('a, 'b) ring_scheme \<Rightarrow> (nat \<Rightarrow> 'a ) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "derivative R b n = shift (mult R b) n"
