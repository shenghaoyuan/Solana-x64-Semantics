theory x64_encode_negl_r_4
imports
  Main
  rBPFCommType
  x64Syntax BitsOpMore
begin


lemma encode_negl_r_4_subgoal_1: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> and 15 v \<noteq> 0 \<Longrightarrow>
    \<not> bit v 3 \<Longrightarrow>  \<not> bit v 2 \<Longrightarrow>
    \<not> bit v (Suc 0)  \<Longrightarrow> bit v 0 \<Longrightarrow> n < 8 \<Longrightarrow> bit v n \<Longrightarrow> bit (65::u8) n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      apply (metis numeral_2_eq_2)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal
          by (simp add: numeral_3_eq_3)
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

lemma encode_negl_r_4_subgoal_2: " and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> and 15 v \<noteq> 0 \<Longrightarrow>
    \<not> bit v 3 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow>
    \<not> bit v (Suc 0)  \<Longrightarrow> bit v 0 \<Longrightarrow> n < 8 \<Longrightarrow> bit (65::u8) n \<Longrightarrow> bit v n"
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


lemma encode_negl_4_aux : "\<not> bit (v::u8) 3 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow> \<not> bit (v >> 2) 0 \<Longrightarrow> \<not> bit v 0
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


lemma encode_negl_r_4_subgoal_3 : "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> and 15 v \<noteq> 0 \<Longrightarrow>
    \<not> bit v 3 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow> \<not> bit v 0 \<Longrightarrow> n < 8 \<Longrightarrow> bit v n \<Longrightarrow> bit (64::u8) n"
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


lemma encode_negl_r_4_subgoal_4: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> and 15 v \<noteq> 0 \<Longrightarrow>
    \<not> bit v 3 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow> \<not> bit v 0 \<Longrightarrow> n < 8 \<Longrightarrow> bit (64::u8) n \<Longrightarrow> bit v n"
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

lemma encode_negl_r_1_subgoal_1: " and 7 ((v::u8) >> 3) = 3 \<Longrightarrow> bit v (Suc (Suc (Suc (Suc (Suc 0))))) \<Longrightarrow> False
 "
  apply (simp add: bit_eq_iff Suc3_eq_add_3)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="2" in spec) by simp

lemma encode_negl_r_4_subgoal_5 : " and 3 ((k::u8) >> 6) = 3 \<Longrightarrow> and 7 (k >> 3) = 3 \<Longrightarrow> 
      n < 8 \<Longrightarrow> bit k n \<Longrightarrow> \<not> bit (192::u8) n \<Longrightarrow> \<not> bit (24::u8) n \<Longrightarrow> bit (7::u8) n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal for n5 apply (cases n5, simp_all)
            subgoal
              using encode_negl_r_1_subgoal_1 by blast
            subgoal for n6 apply (cases n6, simp_all)
              done
            done
          done
        done
      done
    done
  done

lemma encode_negl_r_4_subgoal_6: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> and 15 v \<noteq> 0 \<Longrightarrow>
    and 3 ((k::u8) >> 6) = 3 \<Longrightarrow> and 7 (k >> 3) = 3 \<Longrightarrow>
    \<not> bit v 3 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow> n < 8 \<Longrightarrow> bit k n \<Longrightarrow> \<not> bit (192::u8) n \<Longrightarrow> \<not> bit (24::u8) n \<Longrightarrow> bit (56::u8) n \<Longrightarrow> False"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal for n5 apply (cases n5, simp_all)
            subgoal
              using encode_negl_r_1_subgoal_1 by blast
              done
            done
          done
        done
      done
    done

lemma encode_negl_r_1_subgoal_2: " and 7 ((v::u8) >> 3) = 3 \<Longrightarrow> bit v (Suc (Suc (Suc (Suc 0)))) "
  apply (simp add: bit_eq_iff Suc3_eq_add_3 )
  apply (auto simp add: bit_simps)
  apply (drule_tac x="1" in spec) by simp

lemma encode_negl_r_4_subgoal_7: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> and 15 v \<noteq> 0 \<Longrightarrow>
    and 3 ((k::u8) >> 6) = 3 \<Longrightarrow> and 7 (k >> 3) = 3 \<Longrightarrow>
    \<not> bit v 3 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow> n < 8 \<Longrightarrow> \<not> bit (192::u8) n \<Longrightarrow> bit (24::u8) n \<Longrightarrow> bit k n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal
          by (metis bit_0 bit_and_iff bit_iff_odd_drop_bit bit_numeral_Bit1_0 numeral_3_eq_3)
        subgoal for n4 apply (cases n4, simp_all)
          using encode_negl_r_1_subgoal_2 by blast
              done
            done
          done
        done

lemma encode_negl_r_4_subgoal_8: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow>  and 15 v \<noteq> 0 \<Longrightarrow>
    and 3 ((k::u8) >> 6) = 3 \<Longrightarrow> and 7 (k >> 3) = 3 \<Longrightarrow>
    \<not> bit v 3 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow> n < 8 \<Longrightarrow> 
    \<not> bit (192::u8) n \<Longrightarrow> bit (7::u8) n \<Longrightarrow> \<not> bit (56::u8) n \<Longrightarrow> bit 8 n \<Longrightarrow> 3 \<le> n \<Longrightarrow> bit v (n - 3) \<Longrightarrow> bit k n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done


lemma encode_negl_r_4_subgoal_k : "and 15 (v >> 4) = 4 \<Longrightarrow>
    and 15 v \<noteq> 0 \<Longrightarrow>
    and 3 (k >> 6) = 3 \<Longrightarrow>
    and 7 (k >> 3) = 3 \<Longrightarrow>
    u8_of_ireg dst = or (and 8 (v << 3)) (and 7 k) \<Longrightarrow>
    \<not> bit v 3 \<Longrightarrow>
    \<not> bit v 2 \<Longrightarrow>
    \<not> bit v (Suc 0) \<Longrightarrow>
    v = or 64 (and (and (and (and (case bit v 0 of True \<Rightarrow> 1 | False \<Rightarrow> 0) (- 3)) (- 5)) (- 9)) (- 241)) \<and>
    k = or 192 (and (or 24 (and (and 7 (or (and 8 (v << 3)) (and 7 k))) (- 57))) (- 193))"
  apply (rule conjI)
  subgoal
    apply (cases "bit v 0", simp_all)
    subgoal
      apply (rule bit_eqI)
      subgoal for n
        apply (auto simp add: bit_simps)
        subgoal using encode_negl_r_4_subgoal_1 by simp
        subgoal using encode_negl_r_4_subgoal_2 by simp
        done
      done

    subgoal
      apply (rule bit_eqI)
      subgoal for n
        apply (auto simp add: bit_simps)
        subgoal using encode_negl_r_4_subgoal_3 by simp
        subgoal using encode_negl_r_4_subgoal_4 by simp
        done                          
      done
    done

    subgoal
      apply (rule bit_eqI)
      subgoal for n
        apply (auto simp add: bit_simps)
        subgoal using encode_negl_r_4_subgoal_5 by simp
        subgoal using encode_negl_r_4_subgoal_5 by simp
        subgoal using encode_negl_r_4_subgoal_5 by simp
        subgoal using encode_negl_r_4_subgoal_6 by simp
        subgoal using encode_negl_r_4_subgoal_7 by simp
        subgoal using encode_negl_r_4_subgoal_8 by simp
        done
      done
    done

lemma encode_negl_r_4: "
    and 15 (v >> 4) = 4 \<Longrightarrow> and 15 v \<noteq> 0 \<Longrightarrow> and 3 (k >> 6) = 3 \<Longrightarrow> and 7 (k >> 3) = 3 \<Longrightarrow>      
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 k) (and 1 v)) = Some dst \<Longrightarrow>
    \<not> bit v 3 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow>
    bitfield_insert_u8 4 4
     (bitfield_insert_u8 3 (Suc 0)
       (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0)) 0) 0) 0)
     4 \<noteq> 64 \<Longrightarrow>
    v =
    bitfield_insert_u8 4 4
     (bitfield_insert_u8 3 (Suc 0)
       (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0)) 0) 0) 0)
     4 \<and>
    k = bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg dst)) 3) 3"
  apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
  apply (unfold bitfield_insert_u8_def u8_of_bool_def Let_def)
  apply simp
  using encode_negl_r_4_subgoal_k by simp

end