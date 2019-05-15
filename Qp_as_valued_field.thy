theory Qp_as_valued_field
imports "padic_field"
        "Valued_Fields"
begin

lemma(in padic_integers) val_is_valuation:
"val \<in> valuation Q\<^sub>p G"
proof(rule valuationI)
  show "val \<in> carrier Q\<^sub>p \<rightarrow> vals G" 
    by (simp add: G_def val_def)
  show "(\<forall>x. x \<in> carrier Q\<^sub>p \<longrightarrow> val x \<in> vals G) \<and> 
        (\<forall>x y. x \<in> carrier Q\<^sub>p \<and> y \<in> carrier Q\<^sub>p \<longrightarrow> val (x \<oplus>\<^bsub>Q\<^sub>p\<^esub> y) \<succeq>\<^bsub>G\<^esub> Min\<^bsub>G\<^esub> (val x) (val y))" 
    using \<open>val \<in> carrier Q\<^sub>p \<rightarrow> vals G\<close> val_ultrametric by auto
  show " \<forall>x y. x \<in> Valued_Fields.nonzero Q\<^sub>p \<and> y \<in> Valued_Fields.nonzero Q\<^sub>p \<longrightarrow> 
          val (x \<otimes>\<^bsub>Q\<^sub>p\<^esub> y) = val x \<oplus>\<^bsub>G\<^esub> val y" 
    by (simp add: val_mult)
  show "nonzero_to_group Q\<^sub>p G val" 
    by (simp add: G_def val_def)
  show "val \<zero>\<^bsub>Q\<^sub>p\<^esub> = \<infinity>\<^bsub>G\<^esub>" 
    by (simp add: val_def)
  show "val \<one>\<^bsub>Q\<^sub>p\<^esub> = \<zero>\<^bsub>G\<^esub>" 
    by (simp add: val_one)
qed

definition(in padic_integers) Qp:
"Qp = \<lparr>ring = Q\<^sub>p, val_group = G, ord = val\<rparr>"

lemma(in padic_integers) Qp_is_valued_ring:
 "valued_ring Qp"
proof(rule valued_ringI)
  show "domain K\<^bsub>Qp\<^esub>" 
    by (simp add: Q\<^sub>p_def Qp Zp_is_domain domain.fraction_field_is_domain)
  show "extended_ordered_abelian_group \<Gamma>\<^bsub>Qp\<^esub>" 
    by (simp add: G_EOAG Qp)
  show "\<nu>\<^bsub>Qp\<^esub> \<in> valuation K\<^bsub>Qp\<^esub> \<Gamma>\<^bsub>Qp\<^esub>"
    by (simp add: Qp val_is_valuation)
qed

lemma(in padic_integers) Qp_is_valued_field:
 "valued_field Qp"
  apply(rule valued_fieldI)
  apply(auto simp:Qp_is_valued_ring)
proof-
  have "K\<^bsub>Qp\<^esub> = Q\<^sub>p" 
    by (simp add: Qp)
  then show "field K\<^bsub>Qp\<^esub>" 
    using Qp_is_field by simp 
  show "\<And>x. x \<in> range \<nu>\<^bsub>Qp\<^esub>"
  proof-
    fix x::"int option"
    show " x \<in> range \<nu>\<^bsub>Qp\<^esub>" 
    proof(cases "x = \<infinity>\<^bsub>G\<^esub>")
      case True
      have "\<nu>\<^bsub>Qp\<^esub> \<zero>\<^bsub>Q\<^sub>p\<^esub> = x" 
        by (simp add: Qp True local.val_zero)
      then show ?thesis 
        by blast
    next
      case False
      then obtain n where "x = *n*"
      
qed
  
  
end