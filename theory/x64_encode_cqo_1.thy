theory x64_encode_cqo_1
imports
  Main
  rBPFCommType
  x64Syntax BitsOpMore
begin


lemma x64_encode_cqo_1: "    and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> 
    bit v 3 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow> and 1 v = 0 \<Longrightarrow>  v = 72"
  apply (rule bit_eqI)
  apply (auto simp add: bit_simps)

  subgoal for n
    subgoal
      apply (cases n, simp_all)
      subgoal
        by (simp add: bit_0 even_iff_mod_2_eq_zero one_and_eq)
      subgoal for n1 apply (cases n1, simp_all)
        subgoal for n2 apply (cases n2, simp_all)
          subgoal
            by (metis numeral_2_eq_2)
          subgoal for n3 apply (cases n3, simp_all)
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
    done

  subgoal for n
    subgoal
      apply (cases n, simp_all)
      subgoal for n1 apply (cases n1, simp_all)
        subgoal for n2 apply (cases n2, simp_all)
          subgoal for n3 apply (cases n3, simp_all)
            subgoal
              using numeral_3_eq_3 by argo 
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
    done
  done










end