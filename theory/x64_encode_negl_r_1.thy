theory x64_encode_negl_r_1
imports
  Main
  rBPFCommType
  x64Syntax BitsOpMore
begin


lemma encode_negl_r_1_subgoal_1: " and 7 ((v::u8) >> 3) = 3 \<Longrightarrow> bit v (Suc (Suc (Suc (Suc (Suc 0))))) \<Longrightarrow> False
 "
  apply (simp add: bit_eq_iff Suc3_eq_add_3)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="2" in spec) by simp


lemma encode_negl_r_1_subgoal_2: " and 7 ((v::u8) >> 3) = 3 \<Longrightarrow> bit v (Suc (Suc (Suc (Suc 0)))) "
  apply (simp add: bit_eq_iff Suc3_eq_add_3 )
  apply (auto simp add: bit_simps)
  apply (drule_tac x="1" in spec) by simp


lemma encode_negl_r_1: "
    and 3 ((v::u8) >> 6) = 3 \<Longrightarrow>
    and 7 (v >> 3) = 3 \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 v) 0) = Some dst \<Longrightarrow>
    bitfield_insert_u8 4 4
     (bitfield_insert_u8 3 (Suc 0) 
       (bitfield_insert_u8 2 (Suc 0) 
         (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0)) 0) 0) 0) 4 = 64 \<Longrightarrow>
     v = bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg dst)) 3) 3"
  apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
  apply (unfold bitfield_insert_u8_def u8_of_bool_def Let_def)
  apply simp
  apply (rule bit_eqI)
  apply (auto simp add: bit_simps)

  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal for n5 apply (cases n5, simp_all)
            subgoal for n6 apply (cases n6, simp_all)
              subgoal 
                using encode_negl_r_1_subgoal_1 by blast
              subgoal for n7 apply (cases n7, simp_all)
                done
              done
            done
          done
        done
      done
    done

  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal for n5 apply (cases n5, simp_all)
            subgoal for n6 apply (cases n6, simp_all)
              subgoal
                using encode_negl_r_1_subgoal_1 by blast 
                done
              done
            done
          done
        done
      done
 
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal
            by (metis bit_0 bit_and_iff bit_iff_odd_drop_bit bit_numeral_Bit1_0 numeral_3_eq_3)
          subgoal for n5 apply (cases n5, simp_all)
                using encode_negl_r_1_subgoal_2 by blast
              done
            done
          done
        done
      done

end