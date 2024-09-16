theory x64_encode_cmovl_1
imports
  Main
  rBPFCommType
  x64Syntax BitsOpMore
begin

lemma Suc4_eq_add_4: "(Suc (Suc (Suc (Suc pc)))) = pc + 4" by simp

lemma encode_cmovl_1_subgoal_1: "and 15 ((v::u8) >> 4) = 4  \<Longrightarrow> n < 8 \<Longrightarrow> bit v n 
                                \<Longrightarrow> \<not> bit (64::u8) n \<Longrightarrow> bit (15::u8) n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal
            by (metis bit_1_0 bit_and_iff bit_numeral_Bit1_0 bit_word_iff_drop_bit_and eval_nat_numeral(2) not_bit_numeral_Bit0_0 numeral_3_eq_3 semiring_norm(26) semiring_norm(27))
          subgoal for n5 apply (cases n5, simp_all)
            subgoal for n6 apply (cases n6, simp_all)
              done
            done
          done
        done
      done
    done
  done

lemma encode_cmovl_1_subgoal_2: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow>
    and 3 ((k::u8) >> 6) = 3 \<Longrightarrow>
    and 31 (v >> 3) \<noteq> 25 \<Longrightarrow>
    u8_of_cond test = and 15 v \<Longrightarrow>
    u8_of_ireg dst = and 7 (k >> 3) \<Longrightarrow> u8_of_ireg src = and 7 k \<Longrightarrow> n < 8 \<Longrightarrow> bit (64::u8) n \<Longrightarrow> bit v n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
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

lemma encode_cmovl_1_subgoal_k : "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow>
    and 3 ((k::u8) >> 6) = 3 \<Longrightarrow>
    and 31 (v >> 3) \<noteq> 25 \<Longrightarrow>
    u8_of_cond test = and 15 v \<Longrightarrow>
    u8_of_ireg dst = and 7 (k >> 3) \<Longrightarrow>
    u8_of_ireg src = and 7 k \<Longrightarrow>
    v = or (and 15 v) 64 \<and> k = or 192 (and (or (and 56 ((k >> 3) << 3)) (and (and 7 k) (- 57))) (- 193))"
  apply (rule conjI)
  subgoal
    apply (rule bit_eqI)
    subgoal for n
      apply (auto simp add: bit_simps)
      subgoal using encode_cmovl_1_subgoal_1 by simp
      subgoal using encode_cmovl_1_subgoal_2 by simp
      done
    done

  subgoal
    apply (rule bit_eqI)
    subgoal for n
      apply (auto simp add: bit_simps)
      done
    done
  done

lemma encode_cmovl_1: "
    and 15 (v >> 4) = 4 \<Longrightarrow> and 3 (k >> 6) = 3 \<Longrightarrow>
    and 31 (v >> 3) \<noteq> 25 \<Longrightarrow>
    cond_of_u8 (and 15 v) = Some test \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (k >> 3)) 0) = Some dst \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (k)) 0) = Some src \<Longrightarrow>
    v = bitfield_insert_u8 0 4 64 (u8_of_cond test) \<and>
    k = bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg src)) (and 7 (u8_of_ireg dst))) 3"
  apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp add: u8_of_cond_of_u8_iff[symmetric])
  apply (unfold bitfield_insert_u8_def u8_of_bool_def Let_def)
  apply simp
  using encode_cmovl_1_subgoal_k by simp
end