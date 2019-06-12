theory test
imports Main
begin 

definition is_increasing :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
"is_increasing f = (\<forall>n m::nat . n> m \<longrightarrow> f n > f m)"

lemma is_increasing_prop:
 "is_increasing f \<Longrightarrow> f n \<ge>n"
  apply(induction n)
   apply simp
  by (meson Suc_leI Suc_le_mono is_increasing_def le_trans less_Suc_eq)
end 