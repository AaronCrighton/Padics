theory extended_int
imports Ordered_Abelian_Group Main Extended_OAG
begin

abbreviation int_group :: "int monoid" 
  where "int_group \<equiv> \<lparr>carrier = UNIV, mult = (+), one = 0\<rparr>"

abbreviation int_oag :: "int ordered_monoid" 
  where "int_oag \<equiv> \<lparr>carrier = UNIV, mult = (+), one = 0, le = (\<le>) \<rparr>"

lemma int_oag_is_oag:
"ordered_abelian_group int_oag"
proof(rule oagI)
  show "comm_group int_oag" 
    apply(rule comm_groupI)
    apply(simp)
    apply(simp)
    apply(simp)
    apply(simp)
    apply(simp)
    apply(simp)
    apply presburger 
    done 
  show "has_order int_oag"
  proof    
    show "\<And>x. x \<in> carrier (underlying_order int_oag) \<Longrightarrow> x .=\<^bsub>underlying_order int_oag\<^esub> x" 
      by simp
    show " \<And>x y. x .=\<^bsub>underlying_order int_oag\<^esub> y \<Longrightarrow>
           x \<in> carrier (underlying_order int_oag) \<Longrightarrow> y \<in> carrier (underlying_order int_oag) \<Longrightarrow> y .=\<^bsub>underlying_order int_oag\<^esub> x"
      by auto
    show "\<And>x y z.
       x .=\<^bsub>underlying_order int_oag\<^esub> y \<Longrightarrow>
       y .=\<^bsub>underlying_order int_oag\<^esub> z \<Longrightarrow>
       x \<in> carrier (underlying_order int_oag) \<Longrightarrow>
       y \<in> carrier (underlying_order int_oag) \<Longrightarrow> z \<in> carrier (underlying_order int_oag) \<Longrightarrow> x .=\<^bsub>underlying_order int_oag\<^esub> z"
      by simp
    show " \<And>x. x \<in> carrier (underlying_order int_oag) \<Longrightarrow> x \<sqsubseteq>\<^bsub>underlying_order int_oag\<^esub> x"
      by simp
    show "\<And>x y. x \<sqsubseteq>\<^bsub>underlying_order int_oag\<^esub> y \<Longrightarrow>
           y \<sqsubseteq>\<^bsub>underlying_order int_oag\<^esub> x \<Longrightarrow>
           x \<in> carrier (underlying_order int_oag) \<Longrightarrow> y \<in> carrier (underlying_order int_oag) \<Longrightarrow> x .=\<^bsub>underlying_order int_oag\<^esub> y"
      by auto
    show "\<And>x y z.
       x \<sqsubseteq>\<^bsub>underlying_order int_oag\<^esub> y \<Longrightarrow>
       y \<sqsubseteq>\<^bsub>underlying_order int_oag\<^esub> z \<Longrightarrow>
       x \<in> carrier (underlying_order int_oag) \<Longrightarrow>
       y \<in> carrier (underlying_order int_oag) \<Longrightarrow> z \<in> carrier (underlying_order int_oag) \<Longrightarrow> x \<sqsubseteq>\<^bsub>underlying_order int_oag\<^esub> z"
      by simp
    show "\<And>x y z w.
       x .=\<^bsub>underlying_order int_oag\<^esub> y \<Longrightarrow>
       z .=\<^bsub>underlying_order int_oag\<^esub> w \<Longrightarrow>
       x \<in> carrier (underlying_order int_oag) \<Longrightarrow>
       y \<in> carrier (underlying_order int_oag) \<Longrightarrow>
       z \<in> carrier (underlying_order int_oag) \<Longrightarrow>
       w \<in> carrier (underlying_order int_oag) \<Longrightarrow> (x \<sqsubseteq>\<^bsub>underlying_order int_oag\<^esub> z) = (y \<sqsubseteq>\<^bsub>underlying_order int_oag\<^esub> w)"
      by auto
    show "(.=\<^bsub>underlying_order int_oag\<^esub>) = (=)" 
      by simp
    show " \<And>x y. x \<in> carrier (underlying_order int_oag) \<Longrightarrow>
           y \<in> carrier (underlying_order int_oag) \<Longrightarrow> x \<sqsubseteq>\<^bsub>underlying_order int_oag\<^esub> y \<or> y \<sqsubseteq>\<^bsub>underlying_order int_oag\<^esub> x" 
      by (simp add: linear)
  qed
  show " le_resp_mult int_oag" 
    by (simp add: le_resp_mult_def)
qed

abbreviation int_eoag :: "int option extended_ordered_monoid" where
  "int_eoag \<equiv> (extended int_oag)"

lemma int_eoag_is_eoag:
"extended_ordered_abelian_group int_eoag"
 using ordered_abelian_group.extended_is_eoag  int_oag_is_oag by blast


end