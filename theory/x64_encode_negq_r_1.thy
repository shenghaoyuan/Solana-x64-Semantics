theory x64_encode_negq_r_1
imports
  Main
  rBPFCommType
  x64Syntax BitsOpMore
begin

lemma encode_negq_r_1_subgoal_1: 
" and 15 (v >> 4) = 4 \<Longrightarrow> and 15 v \<noteq> 0 \<Longrightarrow> and 3 (k >> 6) = 3 \<Longrightarrow> and 7 (k >> 3) = 3 \<Longrightarrow>
  bit v 3 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow>\<not> bit v (Suc 0) \<Longrightarrow> bit v 0 \<Longrightarrow>
  bit k 0 = bit (or 192 (and (or 24 (and (and 7 (or (and 8 (v << 3)) (and 7 k))) (- 57))) (- 193))) 0"



lemma encode_negq_r_1_subgoal_k: " and 15 (v >> 4) = 4 \<Longrightarrow> and 15 v \<noteq> 0 \<Longrightarrow>
    and 3 (k >> 6) = 3 \<Longrightarrow> and 7 (k >> 3) = 3 \<Longrightarrow>
    u8_of_ireg dst = or (and 8 (v << 3)) (and 7 k) \<Longrightarrow>
    bit v 3 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow> bit v 0 \<Longrightarrow> 
    v = 73 \<and> k = or 192 (and (or 24 (and (and 7 (or (and 8 (v << 3)) (and 7 k))) (- 57))) (- 193))"
  apply (rule conjI)
   apply (rule bit_eqI)

  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal
          using numeral_2_eq_2 by argo
        subgoal for n4 apply (cases n4, simp_all)
          subgoal
            using numeral_3_eq_3 by argo
          subgoal for n5 apply (cases n5, simp_all)
            subgoal
              by (metis add_2_eq_Suc' bit_1_0 bit_and_iff bit_numeral_Bit1_0 bit_word_iff_drop_bit_and not_bit_numeral_Bit0_0 numeral_2_eq_2 numeral_Bit0) 
            subgoal for n6 apply (cases n6, simp_all)
              subgoal for n7 apply (cases n7, simp_all)
              done
            done
          done
        done
      done
    done
  done

  apply (rule bit_eqI)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal






lemma encode_negq_r_1: "
    and 15 (v >> 4) = 4 \<Longrightarrow> and 15 v \<noteq> 0 \<Longrightarrow>
    and 3 (k >> 6) = 3 \<Longrightarrow> and 7 (k >> 3) = 3 \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 k) (and 1 v)) = Some dst \<Longrightarrow>
    bit v 3 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow>
    v =
    bitfield_insert_u8 4 4
     (bitfield_insert_u8 3 (Suc 0) (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0)) 0) 0) 1)
     4 \<and>
    k = bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg dst)) 3) 3
"

  apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
  apply (unfold bitfield_insert_u8_def u8_of_bool_def Let_def)
  apply simp
  subgoal
    apply (cases "bit v 0", simp_all)
    subgoal
      using 
  done

end

