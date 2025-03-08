theory x64_encode_movl_ri_4
imports
  Main
  rBPFCommType 
  x64Syntax BitsOpMore BitsOpMore3
begin

lemma encode_movl_ri_4_subgoal_1:"and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> and 15 v \<noteq> 0 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow>
    \<not> bit v 3  \<Longrightarrow> bit v 0  \<Longrightarrow> n < 8 \<Longrightarrow> bit v n = bit (65::int) n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal
        by (metis numeral_2_eq_2) 
      subgoal for n3 apply (cases n3, simp_all)
        subgoal
          by (metis numeral_3_eq_3)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal
            by (metis add_2_eq_Suc' bit_1_0 bit_and_iff bit_numeral_Bit1_0 bit_word_iff_drop_bit_and not_bit_numeral_Bit0_0 numeral_2_eq_2 numeral_Bit0)
          subgoal for n5 apply (cases n5, simp_all)
            subgoal for n6 apply (cases n6, simp_all)
              done
            done
          done
        done
      done
    done
  done

lemma encode_movl_ri_4_subgoal_2_1 [simp]:"and 7 ((k::u8) >> 3) = 0 \<Longrightarrow>bit k (Suc (Suc (Suc (Suc 0)))) \<Longrightarrow> False"
  apply (simp add: bit_eq_iff Suc3_eq_add_3)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="1" in spec) by simp

lemma encode_movl_ri_4_subgoal_2_2 [simp]:"and 7 ((k::u8) >> 3) = 0 \<Longrightarrow>bit k  (Suc (Suc (Suc(Suc (Suc 0))))) \<Longrightarrow> False"
  apply (simp add: bit_eq_iff Suc3_eq_add_3)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="2" in spec) by simp

lemma encode_movl_ri_4_subgoal_2:"
    and 7 ((k::u8) >> 3) = 0 \<Longrightarrow> and 3 (k >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow> bit k n \<Longrightarrow> \<not> bit (192::u8) n \<Longrightarrow> bit (7::u8) n
"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all) 
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal
          by (metis and_8_shl_3_neq_0 and_zero_eq bit_0 bit_and_iff bit_iff_odd_drop_bit bit_numeral_Bit1_0 numeral_3_eq_3 push_bit_of_0)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal using encode_movl_ri_4_subgoal_2_1 by blast
          subgoal for n5 apply (cases n5, simp_all)
            subgoal using encode_movl_ri_4_subgoal_2_2 by blast
            subgoal for n5 apply (cases n5, simp_all)
              done
            done
          done
        done
      done
    done
  done

lemma encode_movl_ri_4_subgoal_3:"
    and 7 ((k::u8) >> 3) = 0 \<Longrightarrow> and 3 (k >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow> bit k n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow> bit (56::u8) n \<Longrightarrow> False
"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all) 
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal
          by (metis and_8_shl_3_neq_0 and_zero_eq bit_0 bit_and_iff bit_iff_odd_drop_bit bit_numeral_Bit1_0 numeral_3_eq_3 push_bit_of_0)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal using encode_movl_ri_4_subgoal_2_1 by blast
          subgoal for n5 apply (cases n5, simp_all)
            subgoal using encode_movl_ri_4_subgoal_2_2 by blast
            done
          done
        done
      done
    done
  done


lemma encode_movl_ri_4_subgoal_k:"
    and 15 (v >> 4) = 4 \<Longrightarrow> and 15 v \<noteq> 0 \<Longrightarrow>
    u8_of_ireg dst = or (and 8 (v << 3)) (and 7 k) \<Longrightarrow>
    u32_of_u8_list [l ! (pc + 3), l ! (pc + 4), l ! (pc + 5), l ! (pc + 6)] = Some imm \<Longrightarrow>
    and 7 (k >> 3) = 0 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow> and 3 (k >> 6) = 3 \<Longrightarrow> \<not> bit v 3 \<Longrightarrow>
    or 64 (and (and (and (and (case bit v 0 of True \<Rightarrow> 1 | False \<Rightarrow> 0) (- 3)) (- 5)) (- 9)) (- 241)) \<noteq> 64 \<Longrightarrow>
    v = or 64 (and (and (and (and (case bit v 0 of True \<Rightarrow> 1 | False \<Rightarrow> 0) (- 3)) (- 5)) (- 9)) (- 241)) \<and>
    k = or 192 (and (and (and 7 (or (and 8 (v << 3)) (and 7 k))) (- 57)) (- 193)) \<and>
    [l ! Suc (Suc (Suc pc)), l ! Suc (Suc (Suc (Suc pc))), l ! Suc (Suc (Suc (Suc (Suc pc)))), l ! Suc (Suc (Suc (Suc (Suc (Suc pc)))))] =
    u8_list_of_u32 imm
"
  apply (rule conjI)
  subgoal 
    apply(cases "bit v 0", simp_all)
    subgoal
      apply (rule bit_eqI)
      subgoal for n
        apply (auto simp add: bit_simps)
        subgoal using encode_movl_ri_4_subgoal_1 by blast
        subgoal using encode_movl_ri_4_subgoal_1 by blast
        done
      done
    done

  apply (rule conjI)
  subgoal 
    apply(cases "bit v 0", simp_all)
    subgoal
      apply (rule bit_eqI)
      subgoal for n
        apply (auto simp add: bit_simps)
        subgoal using encode_movl_ri_4_subgoal_2
          using bit_numeral_word_iff by blast
        subgoal 
          using \<open>\<lbrakk>and 15 (v >> 4) = 4; and 15 v \<noteq> 0; u8_of_ireg dst = or (and 8 (v << 3)) (and 7 k); 
                  u32_of_u8_list [l ! (pc + 3), l ! (pc + 4), l ! (pc + 5), l ! (pc + 6)] = Some imm; 
                  and 7 (k >> 3) = 0; \<not> bit v 2; \<not> bit v (Suc 0); and 3 (k >> 6) = 3; \<not> bit v 3; 
                  or 64 (and (and (and (and 1 (- 3)) (- 5)) (- 9)) (- 241)) \<noteq> 64; bit v 0; n < 8; bit k n; \<not> bit 192 n\<rbrakk> \<Longrightarrow> bit 7 n\<close> by blast 
        subgoal
          using \<open>\<lbrakk>and 15 (v >> 4) = 4; and 15 v \<noteq> 0; u8_of_ireg dst = or (and 8 (v << 3)) (and 7 k); 
                  u32_of_u8_list [l ! (pc + 3), l ! (pc + 4), l ! (pc + 5), l ! (pc + 6)] = Some imm; 
                  and 7 (k >> 3) = 0; \<not> bit v 2; \<not> bit v (Suc 0); and 3 (k >> 6) = 3; \<not> bit v 3; 
                  or 64 (and (and (and (and 1 (- 3)) (- 5)) (- 9)) (- 241)) \<noteq> 64; bit v 0; n < 8; bit k n; \<not> bit 192 n\<rbrakk> \<Longrightarrow> bit 7 n\<close> by blast
        subgoal
          using encode_movl_ri_4_subgoal_3 by (meson bit_numeral_word_iff encode_movl_ri_4_subgoal_2)
        subgoal using encode_movl_ri_4_subgoal_3
          using encode_movl_rr_1_subgoal_4 by blast
        done
      done
    done

  subgoal 
    apply (simp add: Suc3_eq_add_3)
    using u32_of_u8_list_same
    by (metis add.commute) 
  done

lemma encode_movl_ri_4: "
    and 15 (v >> 4) = 4 \<Longrightarrow> and 15 v \<noteq> 0 \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 k) (and 1 v)) = Some dst \<Longrightarrow>
    u32_of_u8_list [l ! (pc + 3), l ! (pc + 4), l ! (pc + 5), l ! (pc + 6)] = Some imm \<Longrightarrow>
    and 7 (k >> 3) = 0 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow>
    and 3 (k >> 6) = 3 \<Longrightarrow>\<not> bit v 3 \<Longrightarrow>
    bitfield_insert_u8 4 4
     (bitfield_insert_u8 3 (Suc 0) (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0)) 0) 0) 0)
     4 \<noteq> 64 \<Longrightarrow>
    v =
    bitfield_insert_u8 4 4
     (bitfield_insert_u8 3 (Suc 0) (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0)) 0) 0) 0)
     4 \<and>
    k = bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg dst)) 0) 3 \<and>
    [l ! Suc (Suc (Suc pc)), l ! Suc (Suc (Suc (Suc pc))), l ! Suc (Suc (Suc (Suc (Suc pc)))), l ! Suc (Suc (Suc (Suc (Suc (Suc pc)))))] =
    u8_list_of_u32 imm
"
  apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
  apply (unfold bitfield_insert_u8_def u8_of_bool_def Let_def )
  apply simp
  using encode_movl_ri_4_subgoal_k by blast

end