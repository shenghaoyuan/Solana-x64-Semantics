theory x64ConsistencyProof2Pmov0
imports
  Main
  rBPFCommType rBPFSyntax
  x64Assembler x64Disassembler
begin

lemma [simp]: "((and (and 7 d) (- 9))) = ((and 7 d)::u8)"
  apply (rule bit_eqI)
  subgoal for n apply (auto simp add: bit_simps)
    apply (simp add: bit_iff_odd)
    apply (cases n, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        done
      done
    done
  done

lemma [simp]: "and 15 ((rex::u8) >> 4) = 4 \<Longrightarrow>
    bit 64 (Suc (Suc (Suc (Suc (Suc (Suc 0)))))) \<Longrightarrow>
      bit rex (Suc (Suc (Suc (Suc (Suc (Suc 0))))))"
  apply (simp add: bit_eq_iff) (**r I get this dependent type? `\<forall>n<8.` *)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="2" in spec)
  apply (simp add: eval_nat_numeral(2) eval_nat_numeral(3))
  done

lemma mov_subgoal1: "and 15 (rex >> 4) = (4::u8) \<Longrightarrow> n < 8 \<Longrightarrow> bit 64 n \<Longrightarrow> bit rex n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal by (simp add: bit_numeral_Bit0_iff)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal by (simp add: bit_numeral_Bit0_iff)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal by (simp add: bit_numeral_Bit0_iff)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal by (simp add: bit_numeral_Bit0_iff)
          subgoal for n5 apply (cases n5, simp_all)
            subgoal by (simp add: bit_numeral_Bit0_iff)
            subgoal for n6 apply (cases n6, simp_all)
              subgoal for n7
                by (metis bit_double_Suc_iff bit_exp_iff mult_1_right not_bit_numeral_Bit0_0 numeral_Bit0_eq_double power.simps(1))
              done
            done
          done
        done
      done
    done
  done

lemma [simp]: "and 1 ((rex::u8) >> 3) = 1 \<Longrightarrow> bit rex (Suc (Suc (Suc 0)))"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="0" in spec)
  apply (simp add: eval_nat_numeral(2) eval_nat_numeral(3))
  done

lemma mov_subgoal2: "and 1 ((rex::u8) >> 3) = 1 \<Longrightarrow> n < 8 \<Longrightarrow> bit 8 n \<Longrightarrow> bit rex n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal by (simp add: bit_numeral_Bit0_iff)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal by (simp add: bit_numeral_Bit0_iff)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4
          by (simp add: bit_1_iff bit_numeral_Bit0_iff)
        done
      done
    done
  done

lemma mov_subgoal3_1: "and (or (and 8 (((rex::u8) >> 2) << 3)) (and (7::u8) (rop >> 3))) 8 \<noteq> 0 \<Longrightarrow>
    bit rex (Suc (Suc 0))"
  apply (erule contrapos_pp)
  apply simp
  apply (rule bit_eqI)
  subgoal for n
    apply (simp add: bit_or_iff)
    apply (auto simp add: bit_simps)
    subgoal
      by (metis One_nat_def Suc_diff_diff bit_2_iff bit_numeral_Bit0_iff diff_zero numeral_3_eq_3)
    subgoal 
      apply (cases n, simp_all)
      subgoal for n1 apply (cases n1, simp_all)
        subgoal for n2 apply (cases n2, simp_all)
          done
        done
      done
    done
  done

lemma mov_subgoal3: "and 15 ((rex::u8) >> 4) = 4 \<Longrightarrow>
    and 1 (rex >> 3) = 1 \<Longrightarrow>
    n < 8 \<Longrightarrow>
    2 \<le> n \<Longrightarrow>
    bit (case and (or (and 8 ((rex >> 2) << 3)) (and 7 (rop >> 3))) 8 \<noteq> 0 of True \<Rightarrow> 1
         | False \<Rightarrow> 0)
     (n - 2) \<Longrightarrow>
    bit rex n"
  apply (cases "and (or (and 8 ((rex >> 2) << 3)) (and 7 (rop >> 3))) 8 \<noteq> 0", simp_all)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal using mov_subgoal3_1 by blast
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal using bit_1_iff by blast
          subgoal for n5 apply (cases n5, simp_all)
            subgoal using bit_1_iff by blast
            subgoal for n6 apply (cases n6, simp_all)
              subgoal using bit_1_iff by blast
              subgoal for n7 apply (cases n7, simp_all)
                subgoal using bit_1_iff by blast
                done
              done
            done
          done
        done
      done
    done
  done

lemma [simp]: "and (or (and 8 ((rex::u8) << 3)) (and 7 rop)) 8 \<noteq> 0 \<Longrightarrow> bit rex 0"
  apply (erule contrapos_pp)
  apply simp
  apply (rule bit_eqI)
  subgoal for n
    apply (simp add: bit_or_iff)
    apply (auto simp add: bit_simps)
    subgoal
      by (metis One_nat_def Suc_diff_diff bit_2_iff bit_numeral_Bit0_iff diff_zero numeral_3_eq_3)
    subgoal 
      apply (cases n, simp_all)
      subgoal for n1 apply (cases n1, simp_all)
        subgoal for n2 apply (cases n2, simp_all)
          done
        done
      done
    done
  done

lemma mov_subgoal4: "and 15 ((rex::u8) >> 4) = 4 \<Longrightarrow>
    and 1 (rex >> 3) = 1 \<Longrightarrow>
    and 1 (rex >> Suc 0) = 0 \<Longrightarrow>
    n < 8 \<Longrightarrow>
    bit (case and (or (and 8 (rex << 3)) (and 7 rop)) 8 \<noteq> 0 of True \<Rightarrow> 1 | False \<Rightarrow> 0) n \<Longrightarrow>
    bit rex n"
  apply (cases "and (or (and 8 (rex << 3)) (and 7 rop)) 8 \<noteq> 0", simp_all)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal using bit_1_iff by blast
    subgoal for n2 apply (cases n2, simp_all)
      subgoal using bit_1_iff by blast
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal using bit_1_iff by blast
          subgoal for n5 apply (cases n5, simp_all)
            subgoal using bit_1_iff by blast
            subgoal for n6 apply (cases n6, simp_all)
              subgoal using bit_1_iff by blast
              subgoal for n7 apply (cases n7, simp_all)
                subgoal using bit_1_iff by blast
                done
              done
            done
          done
        done
      done
    done
  done

lemma mov_subgoal5_1 [simp]: "and 15 ((rex::u8) >> 4) = 4 \<Longrightarrow>
    bit rex (Suc (Suc (Suc (Suc 0)))) \<Longrightarrow> False"
  by (metis bit_1_0 bit_and_iff bit_iff_and_drop_bit_eq_1 bit_numeral_Bit1_0 eval_nat_numeral(2) not_bit_numeral_Bit0_0 numeral_3_eq_3 semiring_norm(26) semiring_norm(27)) 
          
lemma mov_subgoal5_2 [simp]: "and 15 ((rex::u8) >> 4) = 4 \<Longrightarrow>
    bit rex (Suc (Suc (Suc (Suc (Suc 0))))) \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="1" in spec)
  apply (simp add: eval_nat_numeral(2) eval_nat_numeral(3))
  done

lemma mov_subgoal5_3 [simp]: "and 15 ((rex::u8) >> 4) = 4 \<Longrightarrow>
    bit rex (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="3" in spec)
  apply (simp add: eval_nat_numeral(2) eval_nat_numeral(3))
  done

lemma mov_subgoal5_4 [simp]: "bit (rex::u8) 0 \<Longrightarrow>
    and (or (and 8 (rex << 3)) (and 7 rop)) 8 = 0 \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="3" in spec)
  apply (simp add: eval_nat_numeral(2) eval_nat_numeral(3))
  done

lemma mov_subgoal5: "and 15 ((rex::u8) >> 4) = 4 \<Longrightarrow>
    and 1 (rex >> 3) = 1 \<Longrightarrow>
    and 1 (rex >> Suc 0) = 0 \<Longrightarrow>
    n < 8 \<Longrightarrow> bit rex n \<Longrightarrow>
    \<not> bit (64::int) n \<Longrightarrow>
    \<not> bit (8::int) n \<Longrightarrow>
    \<not> bit (case and (or (and 8 (rex << 3)) (and 7 rop)) 8 \<noteq> 0 of True \<Rightarrow> 1 | False \<Rightarrow> 0)
        n \<Longrightarrow>
    bit (4::int) n"
  apply (cases "and (or (and 8 (rex << 3)) (and 7 rop)) 8 \<noteq> 0", simp_all)
  subgoal
    apply (cases n, simp_all)
    subgoal using bit_1_iff by blast
    subgoal for n1 apply (cases n1, simp_all)
      subgoal by (simp add: bit_word_iff_drop_bit_and word_bw_comms(1))
      subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal using mov_subgoal5_1 by blast
          subgoal for n5 apply (cases n5, simp_all)
            subgoal using mov_subgoal5_2 by blast
            subgoal for n6 apply (cases n6, simp_all)
              subgoal for n7 apply (cases n7, simp_all)
                subgoal using mov_subgoal5_3 by blast
                done
              done
            done
          done
        done
      done
    done
  done
  subgoal
    apply (cases n, simp_all)
    subgoal using mov_subgoal5_4 by blast
    subgoal for n1 apply (cases n1, simp_all)
      subgoal by (simp add: bit_word_iff_drop_bit_and word_bw_comms(1))
      subgoal for n2 apply (cases n2, simp_all)
        subgoal for n3 apply (cases n3, simp_all)
          subgoal for n4 apply (cases n4, simp_all)
            subgoal using mov_subgoal5_1 by blast
            subgoal for n5 apply (cases n5, simp_all)
              subgoal using mov_subgoal5_2 by blast
              subgoal for n6 apply (cases n6, simp_all)
                subgoal for n7 apply (cases n7, simp_all)
                  subgoal using mov_subgoal5_3 by blast
                  done
                done
              done
            done
          done
        done
      done
    done
  done


lemma mov_subgoal6_1: "bit rex 0 \<Longrightarrow> and (or (and 8 (rex << 3)) (and 7 rop)) (8::u8) = 0 \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="3" in spec)
  apply (simp add: eval_nat_numeral(2) eval_nat_numeral(3))
  done

lemma mov_subgoal6_2: "and 1 (rex >> Suc 0) = 0 \<Longrightarrow> bit rex (Suc 0) \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  done

lemma mov_subgoal6: "and 15 ((rex::u8) >> 4) = 4 \<Longrightarrow>
    and 1 (rex >> 3) = 1 \<Longrightarrow>
    and 1 (rex >> Suc 0) = 0 \<Longrightarrow>
    n < 8 \<Longrightarrow>
    bit rex n \<Longrightarrow>
    \<not> bit (64::int) n \<Longrightarrow>
    \<not> bit (8::int) n \<Longrightarrow>
    \<not> bit (case and (or (and 8 (rex << 3)) (and 7 rop)) 8 \<noteq> 0 of True \<Rightarrow> 1
            | False \<Rightarrow> 0)
        n \<Longrightarrow>
    2 \<le> n"
  apply (cases "and (or (and 8 (rex << 3)) (and 7 rop)) 8 \<noteq> 0", simp_all)
  subgoal
    apply (cases n, simp_all)
    subgoal using bit_1_iff by blast
    subgoal for n1 apply (cases n1, simp_all)
      by (simp add: and.commute bit_iff_and_drop_bit_eq_1)
    done
  subgoal
    apply (cases n, simp_all)
    subgoal using mov_subgoal6_1 by blast
    subgoal for n1 apply (cases n1, simp_all)
      subgoal using mov_subgoal6_2 by blast
      done
    done
  done

lemma not_bit_8_3_false [simp]: "\<not> bit (8::int) (Suc (Suc (Suc 0))) = False" by simp  

lemma  [simp]: "and 15 ((rex::u8) >> 4) = 4 \<Longrightarrow>
    and 1 (rex >> 3) = 1 \<Longrightarrow>
    and 1 (rex >> Suc 0) = 0 \<Longrightarrow>
    n < 8 \<Longrightarrow>
    bit rex n \<Longrightarrow>
    \<not> bit (64::int) n \<Longrightarrow>
    \<not> bit (8::int) n \<Longrightarrow>
    \<not> bit (case and (or (and 8 (rex << 3)) (and 7 rop)) 8 \<noteq> 0 of True \<Rightarrow> 1 | False \<Rightarrow> 0) n \<Longrightarrow>
    bit (case and (or (and 8 ((rex >> 2) << 3)) (and 7 (rop >> 3))) 8 \<noteq> 0 of True \<Rightarrow> 1
         | False \<Rightarrow> 0)
     (n - 2)"
  apply (cases "and (or (and 8 (rex << 3)) (and 7 rop)) 8 \<noteq> 0", simp_all)
  subgoal
    apply (cases n, simp_all)
    subgoal using bit_1_iff by blast
    subgoal for n1 apply (cases n1, simp_all)
      subgoal using mov_subgoal6_2 by blast
      subgoal for n2 apply (cases n2, simp_all)
        subgoal
          by (smt (verit, best) bit_0 bit_and_iff bit_iff_and_drop_bit_eq_1 mov_subgoal6_1 numeral_2_eq_2 odd_one)
        subgoal for n3 apply (cases n3, simp_all)
          subgoal for n4 apply (cases n4, simp_all)
            subgoal
              using mov_subgoal5_1 by blast 
            subgoal for n5 apply (cases n5, simp_all)
            subgoal
              using mov_subgoal5_2 by blast
            subgoal for n6 apply (cases n6, simp_all)
              subgoal for n7 apply (cases n7, simp_all)
                subgoal
                  using mov_subgoal5_3 by blast
                done
              done
            done
          done
        done
      done
    done
  done
  subgoal
    apply (cases n, simp_all)
    subgoal using mov_subgoal6_1 by blast
    subgoal for n1 apply (cases n1, simp_all)
      subgoal using mov_subgoal6_2 by blast
      subgoal for n2 apply (cases n2, simp_all)
        subgoal
          by (smt (verit, best) bit_0 bit_and_iff bit_iff_and_drop_bit_eq_1 mov_subgoal6_1 numeral_2_eq_2 odd_one)
        subgoal for n3 apply (cases n3, simp_all)
          subgoal for n4 apply (cases n4, simp_all)
            subgoal
              using mov_subgoal5_1 by blast 
            subgoal for n5 apply (cases n5, simp_all)
              subgoal
                using mov_subgoal5_2 by blast
              subgoal for n6 apply (cases n6, simp_all)
                subgoal for n7 apply (cases n7, simp_all)
                  subgoal
                    using mov_subgoal5_3 by blast
                  done
                done
              done
            done
          done
        done
      done
    done
  done

lemma mov_subgoal7 [simp]: "and 15 ((rex::u8) >> 4) = 4 \<Longrightarrow>
    and 1 (rex >> 3) = 1 \<Longrightarrow>
    and 1 (rex >> Suc 0) = 0 \<Longrightarrow>
    bit rex (Suc 0) \<Longrightarrow> n = Suc 0 \<Longrightarrow> False"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal using mov_subgoal6_2 by blast
    done
  done


lemma [simp]: "and 15 ((rex::u8) >> 4) = 4 \<Longrightarrow>
    and 1 (rex >> 3) = 1 \<Longrightarrow>
    and 1 (rex >> Suc 0) = 0 \<Longrightarrow>
    bit rex (Suc 0) \<Longrightarrow>
    n = Suc 0 \<Longrightarrow>
    bit (case and (or (and 8 ((rex >> 2) << 3)) (and 7 (rop >> 3))) 8 \<noteq> 0 of True \<Rightarrow> 1
         | False \<Rightarrow> 0) 0"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal using mov_subgoal6_2 by blast
    done
  done

lemma [simp]: "and 15 ((rex::u8) >> 4) = 4 \<Longrightarrow>
    and 1 (rex >> 3) = 1 \<Longrightarrow>
    and 1 (rex >> Suc 0) = 0 \<Longrightarrow>
    n < 8 \<Longrightarrow> bit rex n \<Longrightarrow> \<not> bit (64::int) n \<Longrightarrow>
    \<not> bit (8::int) n \<Longrightarrow> bit (4::int) n \<Longrightarrow> 2 \<le> n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    done
  done

(*
lemma mov_subgoal8_1: "and 15 ((rex::u8) >> 4) = 4 \<Longrightarrow>
    bit rex (Suc (Suc (Suc (Suc 0)))) \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="0" in spec)
  apply (simp add: eval_nat_numeral(2) eval_nat_numeral(3))
  done

lemma mov_subgoal8_2: "and 15 (rex >> 4) = (4::u8) \<Longrightarrow>
    bit rex (Suc (Suc (Suc (Suc (Suc 0))))) \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="1" in spec)
  apply (simp add: eval_nat_numeral(2) eval_nat_numeral(3))
  done *)

lemma [simp]: "\<not> bit (64::int) (Suc (Suc (Suc (Suc (Suc (Suc 0)))))) \<Longrightarrow> False" by simp

(*
lemma mov_subgoal8_3: "and 15 (rex >> 4) = (4::u8) \<Longrightarrow>
    bit rex (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="3" in spec)
  apply (simp add: eval_nat_numeral(2) eval_nat_numeral(3))
  done

lemma mov_subgoal8_4: "and 1 (rex >> Suc 0) = (0::u8) \<Longrightarrow>
    bit rex (Suc 0) \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="0" in spec)
  apply (simp add: eval_nat_numeral(2) eval_nat_numeral(3))
  done

lemma mov_subgoal8_5: "bit rex (Suc (Suc 0)) \<Longrightarrow>
    and (or (and 8 ((rex >> 2) << 3)) (and 7 (rop >> 3))) 8 = (0::u8) \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="3" in spec)
  apply (simp add: eval_nat_numeral(2) eval_nat_numeral(3))
  done

lemma mov_subgoal8_6: "bit rex 0 \<Longrightarrow>
    and (or (and 8 (rex << 3)) (and 7 rop)) 8 = (0::u8) \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="3" in spec)
  apply (simp add: eval_nat_numeral(2) eval_nat_numeral(3))
  done *)

lemma mov_subgoal8: "and 15 ((rex::u8) >> 4) = 4 \<Longrightarrow>
    and 1 (rex >> 3) = 1 \<Longrightarrow>
    and 1 (rex >> Suc 0) = 0 \<Longrightarrow>
    n < 8 \<Longrightarrow>
    bit rex n \<Longrightarrow>
    \<not> bit (64::int) n \<Longrightarrow>
    \<not> bit (8::int) n \<Longrightarrow>
    bit 4 n \<Longrightarrow>
    bit (case and (or (and 8 ((rex >> 2) << 3)) (and 7 (rop >> 3))) 8 \<noteq> 0 of True \<Rightarrow> 1
         | False \<Rightarrow> 0)
     (n - 2)"
  apply (cases "and (or (and 8 (rex << 3)) (and 7 rop)) 8 \<noteq> 0", simp_all)
  subgoal
    apply (cases n, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        subgoal
          by (smt (verit, best) bit_0 bit_and_iff bit_iff_and_drop_bit_eq_1 mov_subgoal6_1 numeral_2_eq_2 odd_one)
        subgoal for n3 apply (cases n3, simp_all)
          subgoal for n4 apply (cases n4, simp_all)
            subgoal
              using mov_subgoal5_1 by blast 
            subgoal for n5 apply (cases n5, simp_all)
              subgoal
                using mov_subgoal5_2 by blast
              subgoal for n6 apply (cases n6, simp_all)
                subgoal for n7 apply (cases n7, simp_all)
                  subgoal
                    using mov_subgoal5_3 by blast
                  done
                done
              done
            done
          done
        done
      done
    done
  done

lemma mov_subgoal9 [simp]: "and 15 ((rex::u8) >> 4) = 4 \<Longrightarrow>
    and 1 (rex >> 3) = 1 \<Longrightarrow>
    and 1 (rex >> Suc 0) = 0 \<Longrightarrow>
    n < 8 \<Longrightarrow>
    bit rex n \<Longrightarrow>
    \<not> bit (64::int) n \<Longrightarrow> bit (240::int) n \<Longrightarrow> False"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal
            using mov_subgoal5_1 by blast 
          subgoal for n5 apply (cases n5, simp_all)
            subgoal
              using mov_subgoal5_2 by blast
            subgoal for n6 apply (cases n6, simp_all)
              subgoal for n7 apply (cases n7, simp_all)
                subgoal
                  using mov_subgoal5_3 by blast
                done
              done
            done
          done
        done
      done
    done
  done


lemma mov_goal_0: " and 15 ((rex::u8) >> 4) = 4 \<Longrightarrow>
    and 1 (rex >> 3) = 1 \<Longrightarrow>
    and 1 (rex >> Suc 0) = 0 \<Longrightarrow>
    and 3 (rop >> 6) = 3 \<Longrightarrow>
    construct_rex_to_u8 True
     (and (bitfield_insert_u8 3 (Suc 0) (and 7 (rop >> 3)) (and 1 (rex >> 2))) 8 \<noteq>
      0)
     False (and (bitfield_insert_u8 3 (Suc 0) (and 7 rop) (and 1 rex)) 8 \<noteq> 0) =
    rex"
  apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
  apply simp
  apply (unfold bitfield_insert_u8_def u8_of_bool_def)
  apply simp
  apply (rule bit_eqI)
  subgoal for n
    apply (simp add: bit_or_iff)
    apply (auto simp add: bit_simps)
    subgoal using mov_subgoal1 by blast
    subgoal using mov_subgoal2 by blast
    subgoal using mov_subgoal3 by blast
    subgoal using mov_subgoal4 by blast
    subgoal using mov_subgoal5 by blast
    subgoal using mov_subgoal6 by blast
    subgoal using mov_subgoal7 by blast
    subgoal using mov_subgoal7 by blast
    subgoal using mov_subgoal8 by blast
    subgoal using mov_subgoal9 by blast
    done
  done
(* 64 = 0b1000000

rewrite goal using iff
    apply (simp add: bit_or_iff) *)

end