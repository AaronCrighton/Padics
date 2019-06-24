theory poly_function_ring
  imports domain_poly "HOL-Algebra.UnivPoly"
begin

definition function_mult:: "'a ring \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
"function_mult R f g = (\<lambda>x. (f x) \<otimes>\<^bsub>R\<^esub> (g x))"

definition function_add:: "'a ring \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
"function_add R f g = (\<lambda>x. (f x) \<oplus>\<^bsub>R\<^esub> (g x))"

definition function_one:: "'a ring \<Rightarrow> ('a \<Rightarrow> 'a)" where
"function_one R = (\<lambda>x. \<one>\<^bsub>R\<^esub>)"

definition function_zero:: "'a ring \<Rightarrow> ('a \<Rightarrow> 'a)" where
"function_zero R = (\<lambda>x. \<zero>\<^bsub>R\<^esub>)"

definition eq_on_car: 

definition poly_ring:: "'a ring \<Rightarrow> ('a \<Rightarrow> 'a) ring" ("PR") where
  where "PR R = \<lparr>
   carrier = fun_of ` (carrier (UP R)),
   mult = (fun_mult,
   one = (\<lambda>i. if i=0 then \<one>\<^bsub>R\<^esub> else \<zero>\<^bsub>R\<^esub>),
   zero = (\<lambda>i. \<zero>\<^bsub>R\<^esub>),
   add = (\<lambda>p\<in>up R. \<lambda>q\<in>up R. \<lambda>i. p i \<oplus>\<^bsub>R\<^esub> q i),
end