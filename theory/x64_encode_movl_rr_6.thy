theory x64_encode_movl_rr_6
imports
  Main
  rBPFCommType
  x64Syntax BitsOpMore
begin


lemma encode_movl_rr_6_subgoal_1: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> and 3 ((k::u8) >> 6) = 3 \<Longrightarrow>
  \<not> bit v 3 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow> and 1 v = 1 \<Longrightarrow> bit v 2 \<Longrightarrow>
  n < 8 \<Longrightarrow> bit v n \<Longrightarrow> bit (69::int) n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal
          by (simp add: bit_iff_odd_drop_bit even_iff_mod_2_eq_zero numeral_3_eq_3 one_and_eq) 
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

lemma encode_movl_rr_6_subgoal_2: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> and 3 ((k::u8) >> 6) = 3 \<Longrightarrow>
  \<not> bit v 3 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow> and 1 v = 1 \<Longrightarrow> bit v 2 \<Longrightarrow>
  n < 8 \<Longrightarrow> bit (69::int) n \<Longrightarrow> bit v n"
  apply (cases n, simp_all)
  subgoal
    by (metis bit_1_0 bit_and_iff) 
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

lemma encode_movl_rr_6_subgoal_3: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow>
    and 15 v \<noteq> 0 \<Longrightarrow> and 3 ((k::u8) >> 6) = 3 \<Longrightarrow>
    u8_of_ireg src = or (and 8 ((v >> 2) << 3)) (and 7 (k >> 3)) \<Longrightarrow>
    u8_of_ireg dst = or 8 (and 7 k) \<Longrightarrow> \<not> bit v 3 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow> and 1 v = 1 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow> n < 8 \<Longrightarrow> bit v n \<Longrightarrow> bit (65::int) n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal
        by (metis numeral_2_eq_2)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal
          by (simp add: bit_iff_odd_drop_bit even_iff_mod_2_eq_zero numeral_3_eq_3 one_and_eq) 
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

lemma encode_movl_rr_6_subgoal_4 : "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> and 3 ((k::u8) >> 6) = 3 \<Longrightarrow>
  \<not> bit v 3 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow> and 1 v = 1 \<Longrightarrow>
  \<not> bit v 2 \<Longrightarrow> n < 8 \<Longrightarrow> bit (65::int) n \<Longrightarrow> bit v n"
  apply (cases n, simp_all)
  subgoal
    by (metis bit_1_0 bit_and_iff) 
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


lemma encode_movl_rr_6_subgoal_k : "and 15 (v >> 4) = 4 \<Longrightarrow>
    and 15 v \<noteq> 0 \<Longrightarrow>
    and 3 (k >> 6) = 3 \<Longrightarrow>
    u8_of_ireg src = or (and 8 ((v >> 2) << 3)) (and 7 (k >> 3)) \<Longrightarrow>
    u8_of_ireg dst = or 8 (and 7 k) \<Longrightarrow>
    \<not> bit v 3 \<Longrightarrow>
    \<not> bit v (Suc 0) \<Longrightarrow>
    and 1 v = 1 \<Longrightarrow>
    or 64 (and (and (or (and 4 ((case bit (v >> 2) 0 of True \<Rightarrow> 1 | False \<Rightarrow> 0) << 2)) 1) (- 9)) (- 241)) \<noteq> 64 \<Longrightarrow>
    v = or 64 (and (and (or (and 4 ((case bit (v >> 2) 0 of True \<Rightarrow> 1 | False \<Rightarrow> 0) << 2)) 1) (- 9)) (- 241)) \<and>
    k =
    or 192 (and (or (and 56 (or (and 64 ((v >> 2) << 6)) (and 56 ((k >> 3) << 3)))) (and (and 7 (or 8 (and 7 k))) (- 57))) (- 193))"
  apply (rule conjI)
  subgoal
    apply (cases "bit (v >> 2) 0", simp_all)
    subgoal
      apply (rule bit_eqI)
      subgoal for n
        apply (auto simp add: bit_simps)
        subgoal using encode_movl_rr_6_subgoal_1 by blast
        subgoal using encode_movl_rr_6_subgoal_2 by blast
        done
      done
    subgoal
      apply (rule bit_eqI)
      subgoal for n
        apply (auto simp add: bit_simps)
        subgoal using encode_movl_rr_6_subgoal_3 by blast
        subgoal using encode_movl_rr_6_subgoal_4 by blast
        done
      done
    done

  subgoal
    apply (cases "bit (v >> 2) 0", simp_all)
    subgoal
      apply (rule bit_eqI)
      subgoal for n
        apply (simp add: bit_or_iff)
        apply (auto simp add: bit_simps)
        subgoal
          using encode_movl_rr_1_subgoal_1 by blast
        subgoal
          using encode_movl_rr_1_subgoal_1 by blast
        subgoal
          using encode_movl_rr_1_subgoal_4 by blast
        done
      done
    subgoal
      apply (rule bit_eqI)
      subgoal for n
        apply (simp add: bit_or_iff)
        apply (auto simp add: bit_simps)
        subgoal
          using encode_movl_rr_1_subgoal_1 by blast 
        subgoal
          using encode_movl_rr_1_subgoal_1 by blast 
        subgoal
          using BitsOpMore.encode_movl_rr_1_subgoal_4 by blast
        done
      done                                      
    done
  done

lemma encode_movl_rr_6: "
    and 15 (v >> 4) = 4 \<Longrightarrow>  and 15 v \<noteq> 0 \<Longrightarrow> and 3 (k >> 6) = 3 \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (k >> 3)) (and 1 (v >> 2))) = Some src \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (k)) (and 1 v)) = Some dst \<Longrightarrow>
    \<not> bit v 3 \<Longrightarrow>  \<not> bit v (Suc 0) \<Longrightarrow> and 1 v \<noteq> 0 \<Longrightarrow>
    bitfield_insert_u8 4 4
     (bitfield_insert_u8 3 (Suc 0)
       (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0)) 0)
         (u8_of_bool (and (u8_of_ireg src) 8 \<noteq> 0)))
       0) 4 \<noteq> 64 \<Longrightarrow>
    v = bitfield_insert_u8 4 4
         (bitfield_insert_u8 3 (Suc 0)
           (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0)) 0)
             (u8_of_bool (and (u8_of_ireg src) 8 \<noteq> 0)))
           0) 4 \<and>
    k = bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg dst)) (and 7 (u8_of_ireg src))) 3"
  apply (simp add: u8_of_ireg_of_u8_iff[symmetric] and_1_eq_1)
  apply (unfold bitfield_insert_u8_def u8_of_bool_def Let_def)
  apply simp
  using encode_movl_rr_6_subgoal_k by blast

end