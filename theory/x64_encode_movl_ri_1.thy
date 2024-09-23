theory x64_encode_movl_ri_1
imports
  Main
  rBPFCommType 
  x64Syntax BitsOpMore BitsOpMore3
begin

lemma [simp]: " and 7 ((v::u8) >> 3) = 0 \<Longrightarrow>\<not> bit v (Suc (Suc (Suc (Suc 0)))) "
  apply (simp add: bit_eq_iff Suc3_eq_add_3 )
  apply (auto simp add: bit_simps)
  apply (drule_tac x="1" in spec) by simp

lemma [simp]: " and 7 ((v::u8) >> 3) = 0 \<Longrightarrow>\<not> bit v (Suc (Suc (Suc (Suc (Suc 0)))))
 "
  apply (simp add: bit_eq_iff Suc3_eq_add_3)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="2" in spec) by simp


lemma encode_movl_ri_1_subgoal_1: "
    and 3 ((v::u8) >> 6) = 3 \<Longrightarrow> and 7 (v >> 3) = 0 \<Longrightarrow> n < 8 \<Longrightarrow> bit v n \<Longrightarrow> \<not> bit (192::u8) n \<Longrightarrow> bit (7::u8) n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal
          by (metis bit.conj_zero_left bit_0 bit_and_iff bit_iff_odd_drop_bit bit_numeral_Bit1_0 even_word_def even_word_iff numeral_3_eq_3)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal for n5 apply (cases n5, simp_all)
            subgoal for n6 apply (cases n6, simp_all)
              done
            done
          done
        done
      done
    done
  done

lemma encode_movl_ri_1_subgoal_2: "
    and 3 ((v::u8) >> 6) = 3 \<Longrightarrow> and 7 (v >> 3) = 0 \<Longrightarrow> n < 8 \<Longrightarrow> bit v n \<Longrightarrow> \<not> bit (192::u8) n \<Longrightarrow> bit (56::u8) n \<Longrightarrow> False"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal
          by (metis bit.conj_zero_left bit_0 bit_and_iff bit_iff_odd_drop_bit bit_numeral_Bit1_0 even_word_def even_word_iff numeral_3_eq_3)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal for n5 apply (cases n5, simp_all)
            done
          done
        done
      done
    done
  done


lemma encode_movl_ri_1_subgoal_k:" u8_of_ireg dst = and 7 v \<Longrightarrow>
    u32_of_u8_list [l ! pc, l ! (Suc pc), l !(Suc (Suc pc)), l !(Suc(Suc (Suc pc)))] = Some imm \<Longrightarrow>
    and 3 (v >> 6) = 3 \<Longrightarrow>
    and 7 (v >> 3) = 0 \<Longrightarrow> v = or 192 (and (and (and 7 v) (- 57)) (- 193)) \<and>
    [l ! pc, l ! (Suc pc), l !(Suc (Suc pc)), l !(Suc(Suc (Suc pc)))] = u8_list_of_u32 imm"
  apply (rule conjI)

  subgoal
    apply (rule bit_eqI)
    subgoal for n
      apply (auto simp add: bit_simps)
      subgoal using encode_movl_ri_1_subgoal_1 by simp
      subgoal using encode_movl_ri_1_subgoal_2 by simp
      done
    done

  subgoal
    using u32_of_u8_list_same by fastforce
  done


lemma encode_movl_ri_1: "
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 v) 0) = Some dst \<Longrightarrow>
    u32_of_u8_list [l ! pc, l ! (Suc pc), l !(Suc (Suc pc)), l !(Suc(Suc (Suc pc)))] = Some imm \<Longrightarrow>
    and 3 (v >> 6) = 3 \<Longrightarrow> and 7 (v >> 3) = 0 \<Longrightarrow>
    bitfield_insert_u8 4 4
     (bitfield_insert_u8 3 (Suc 0)
       (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0)) 0) 0) 0)
     4 = 64 \<Longrightarrow>
    v = bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg dst)) 0) 3 \<and>
    [l ! pc, l ! (Suc pc), l !(Suc (Suc pc)), l !(Suc(Suc (Suc pc)))] = u8_list_of_u32 imm"
  apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
  apply (unfold bitfield_insert_u8_def u8_of_bool_def Let_def )
  apply simp
  using encode_movl_ri_1_subgoal_k by simp

end