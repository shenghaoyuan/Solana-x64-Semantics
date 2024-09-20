theory x64_encode_movl_rr_3
imports
  Main
  rBPFCommType 
  x64Syntax BitsOpMore
begin

lemma encode_movl_rr_3_subgoal_1:"
  \<not>bit v 3 \<Longrightarrow> \<not>bit v (Suc 0) \<Longrightarrow> \<not> bit (v >> 2) 0 \<Longrightarrow> \<not> bit v 0 \<Longrightarrow> and 15 (v::u8) = 0 
"
  apply (rule bit_eqI)
  apply (auto simp add: bit_simps)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        apply (metis numeral_2_eq_2)
        subgoal for n4 apply (cases n4, simp_all)
          by (metis numeral_3_eq_3)
        done
      done
    done
  done

lemma encode_movl_rr_3: "
    and 15 (v >> 4) = 4 \<Longrightarrow> and 15 v \<noteq> 0 \<Longrightarrow> and 3 (k >> 6) = 3 \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (k >> 3)) (and 1 (v >> 2))) = Some src \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 k) (and 1 v)) = Some dst \<Longrightarrow>
    \<not> bit v 3 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow>
    bitfield_insert_u8 4 4
     (bitfield_insert_u8 3 (Suc 0)
       (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0)) 0)
         (u8_of_bool (and (u8_of_ireg src) 8 \<noteq> 0)))
       0)
     4 = 64 \<Longrightarrow>False"
  apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp add: bitfield_insert_u8_def Let_def u8_of_bool_def and_1_eq_1)
  apply (cases "bit (v >> 2) 0"; cases "bit v 0", simp_all)
  using encode_movl_rr_3_subgoal_1 by blast

end