theory x64_encode_negl_r_3
imports
  Main
  rBPFCommType
  x64Syntax BitsOpMore
begin

lemma encode_negl_3_subgoal_1 : "\<not> bit (v::u8) 3 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow> \<not> bit (v >> 2) 0 \<Longrightarrow> \<not> bit v 0
                                   \<Longrightarrow>  and 15 v = 0"
  apply (rule bit_eqI)
  apply (simp add: bit_simps)
  subgoal for n
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal
        using numeral_2_eq_2 by argo 
          subgoal for n3 apply (cases n3, simp_all)
            using numeral_3_eq_3 by argo
              done
            done
          done
        done


lemma encode_negl_r_3: "
    and 15 (v >> 4) = 4 \<Longrightarrow> and 15 v \<noteq> 0 \<Longrightarrow>
    and 3 (k >> 6) = 3 \<Longrightarrow> and 7 (k >> 3) = 3 \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 k) (and 1 v)) = Some dst \<Longrightarrow>
    \<not> bit v 3 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow>
    \<not> bit v (Suc 0) \<Longrightarrow>
    bitfield_insert_u8 4 4
     (bitfield_insert_u8 3 (Suc 0)
       (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0)) 0) 0) 0)
     4 = 64  \<Longrightarrow> False"
  apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
  apply (unfold bitfield_insert_u8_def u8_of_bool_def Let_def)
  apply simp
  apply (cases "bit v 0 ", simp_all)
  using encode_negl_3_subgoal_1
  by (meson bit_0 bit_iff_odd_drop_bit)

end