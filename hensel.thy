theory hensel
  imports Main "~~/src/HOL/Algebra/UnivPoly" "~~/src/HOL/Algebra/Valued_Fields/padic_construction"
begin

definition p_UP :: "nat \<Rightarrow> (nat \<Rightarrow> int, nat \<Rightarrow> nat \<Rightarrow> int) up_ring" where
  "p_UP p = UP (padic_int p)"

fun shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "shift b n = b (n + 1)"

fun mult :: "('a, 'b) ring_scheme \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "mult R b n = add_pow R n (b n)"

definition deriv :: "('a, 'b) ring_scheme \<Rightarrow> (nat \<Rightarrow> 'a ) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "deriv R b n = shift (mult R b) n"

lemma mult_in_up_ring:
  "mult R b \<in> up R" 
proof
  fix n
  have "hensel.mult R b n \<in> carrier R" sledgehammer

(* deriv also returns a polynomial *)
lemma deriv_in_up_ring:
  "(deriv R p) \<in> up R"
proof-
  assume "p \<in> up R"
  then have "p n \<in> carrier R" 
    by (simp add: mem_upD)
  then have "shift p n \<in> carrier R"
    by (simp add: \<open>p \<in> up R\<close> mem_upD)
  have "mult R b n \<in> carrier R" using add_pow_def mult_def sledgehammer


(*
  obtain n where "deg R p = n" by simp
  then have "n = (LEAST n. bound \<zero>\<^bsub>R\<^esub> n (coeff (UP R) p))" using deg_def  sledgehammer*)
