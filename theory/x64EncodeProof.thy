 theory x64EncodeProof
imports
  Main
  rBPFCommType BitExtractInsert
  x64Assembler x64Disassembler
(*  x64_encode_movl_rr_1 x64_encode_movl_rr_3  x64_encode_movl_rr_4
  x64_encode_movq_rr_1
  x64_encode_mov_rm_1 x64_encode_mov_rm_2 x64_encode_mov_rm_3 x64_encode_mov_rm_4
  x64_encode_cmovl_1 x64_encode_cmovl_3 x64_encode_cmovl_4
  x64_encode_cmovq_1
  x64_encode_cqo_1
  x64_encode_negl_r_1 x64_encode_negl_r_2 x64_encode_negl_r_3 x64_encode_negl_r_4
  x64_encode_negq_r_1 
  x64_encode_movl_ri_1 x64_encode_movl_ri_2 x64_encode_movl_ri_3 x64_encode_movl_ri_4
  x64_encode_subl_ri_1 x64_encode_subl_ri_2   x64_encode_movl_ri_3*)
begin




(*
lemma bitfield_insert_3_1_1: "ireg_of_u8 (bitfield_insert 3 1 n 1) = Some dst \<Longrightarrow>
    and (u8_of_ireg dst) 8 = 1"
  apply (drule u8_of_ireg_of_u8_implies, simp)
  apply (simp add: bitfield_insert_def bitfield_extract_def ireg_of_u8_def split: if_split_asm)
  apply (simp add: and.assoc)
  done *)


lemma and_8_neq_0_eq [extract_simp]: "(and x 8\<noteq>0) = (bitfield_extract 3 1 (x:: u8)\<noteq>0)"
  apply (simp add: bitfield_extract_def)
  apply (subgoal_tac "(8::u8) = 2^3")
  prefer 2 subgoal by simp
  using and_pow_n_shr_eq [of x 3]
  by simp

lemma "
  bitfield_extract 6 2 reg = 3 \<Longrightarrow>
  bitfield_insert 3 (Suc 0) (bitfield_extract 3 3 reg) 0 = 0 \<Longrightarrow>
  ireg_of_u8 (bitfield_insert 3 (Suc 0) (bitfield_extract 0 3 reg) 0) = Some dst \<Longrightarrow>
  construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64 
     \<Longrightarrow> construct_modsib_to_u8 3 0 (u8_of_ireg dst) = reg"
  apply (drule u8_of_ireg_of_u8_implies, simp add: construct_modsib_to_u8_def)
  apply (rule extract_simp; simp?)
  apply (simp add: extract_simp)
  apply (rule bitfield_extract_0_3_3_eq; simp?)
  apply (simp add: bitfield_extract_split_eq [of 3 3]) 





declare if_split_asm [split]

declare Let_def [simp]
declare x64_decode_op_not_rex_def [simp]
declare x64_decode_op_0x66_def [simp]
declare x64_decode_op_0x0f_def [simp]
declare x64_decode_op_0x81_def [simp]

lemma x64_decode_encode_consistency:
  "list_in_list l_bin pc l \<Longrightarrow> x64_decode pc l = Some (length l_bin, ins) \<Longrightarrow>  Some l_bin = x64_encode ins"
  apply (simp add: x64_decode_def)
                     
  apply (cases "nth_error l pc"; simp)
  subgoal for h
    by (cases l_bin; simp)

  subgoal for h
    by (cases l_bin; simp)

  subgoal for h
    by (cases l_bin; simp)

  subgoal for h
    apply (cases "nth_error l (Suc pc)"; simp)
    subgoal for h1 
      apply (cases "nth_error l (Suc (Suc pc))"; simp)
      subgoal for reg
        apply (cases "nth_error l (pc + 3)"; simp)
        subgoal for imm
          apply (cases "ireg_of_u8 (bitfield_insert 3 (Suc 0) (bitfield_extract 0 3 reg) 0)"; simp)
          subgoal for dst
            apply (erule conjE)
            apply (drule sym[of _ ins], simp)
            apply (rule conjI; rule impI)
            subgoal 
              apply (cases l_bin; simp)
              subgoal for l1
                apply (cases l1; simp)
                subgoal for l2
                  apply (cases l2; simp)
                  subgoal for l3
                    apply (cases l3; simp)
                    subgoal for i1 l4
                      apply (cases "nth_error l (Suc (Suc (Suc pc)))" ; simp)
                      subgoal for i2
                        apply (rule conjI)
                        subgoal 








(*
Proof done
  subgoal for dst src
  \<comment> \<open> Pmovl_rr 1\<close> 
    apply (unfold Let_def)
    apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (unfold x64_decode_def Let_def, auto simp add: split: option.splits)
    subgoal
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for t l_bin2
          using encode_movl_rr_1 by blast
        done
      done

    subgoal by (unfold bitfield_insert_def;simp)

    subgoal 
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
        apply (cases l_bin2, simp_all)
        subgoal for t l_bin3
          using encode_movl_rr_3 by blast
        done
      done
    done

    subgoal
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
          apply (cases l_bin2, simp_all)
          subgoal for t l_bin3
            using encode_movl_rr_4 by blast
          done
        done
      done
    done


  subgoal for dst src
  \<comment> \<open> Pmovq_rr 2\<close> 
    apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (unfold x64_decode_def Let_def, auto simp add: split: option.splits)
    apply (cases l_bin, simp_all)
    subgoal for l_bin1
      apply (cases l_bin1, simp_all)
      subgoal for l_bin2
        apply (cases l_bin2, simp_all)
        subgoal for t l_bin3
          subgoal
            using encode_movq_rr_1 by blast
          done
        done
      done
    done

  subgoal for dst imm
  \<comment> \<open> Pmovl_ri 3\<close> 
    apply (unfold Let_def)
    apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (unfold x64_decode_def Let_def, auto simp add: split: option.splits)
    subgoal 
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
          apply (cases l_bin2, simp_all)
          subgoal for l_bin3
            apply (cases l_bin3, simp_all)
            subgoal for l_bin4
              apply (cases l_bin4, simp_all)
              subgoal for l_bin5
                apply (cases l_bin5, simp_all)
                subgoal for t l_bin6 
                  using encode_movl_ri_1 [of _ _ _ "(Suc (Suc pc))"]
                  by (smt (verit, best) BitM.simps(1) BitM.simps(2) Suc3_eq_add_3 add.commute eval_nat_numeral(3) nat_arith.suc1 numeral_nat(2))
                done
              done
            done
          done
        done
      done

    subgoal 
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
          apply (cases l_bin2, simp_all)
          subgoal for l_bin3
            apply (cases l_bin3, simp_all)
            subgoal for l_bin4
              apply (cases l_bin4, simp_all)
              subgoal for l_bin5
                apply (cases l_bin5, simp_all)
                subgoal for t l_bin6 
                  using encode_movl_ri_2
                  by (metis One_nat_def Suc_eq_plus1 list.sel(3) list.size(3) list.size(4) nat_1_add_1 numeral_3_eq_3 numeral_eq_iff semiring_norm(88) u32_of_u8_list_same) 
                done
              done
            done
          done
        done
      done

    subgoal 
      using encode_movl_ri_3 by blast

    subgoal 
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
          apply (cases l_bin2, simp_all)
          subgoal for l_bin3
            apply (cases l_bin3, simp_all)
            subgoal for l_bin4
              apply (cases l_bin4, simp_all)
              subgoal for l_bin5
                apply (cases l_bin5, simp_all)
                subgoal for l_bin6
                  apply (cases l_bin6, simp_all)
                  subgoal for t l_bin7
                    apply (cases l_bin7, simp_all)
                    using encode_movl_ri_4 by blast
                  done
                done
              done
            done
          done
        done
      done
    done

  subgoal for test dst src
  \<comment> \<open> Pcmovl 8\<close> 
    apply (unfold Let_def)
    apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (unfold x64_decode_def Let_def, auto simp add: split: option.splits)
    subgoal
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
          apply (cases l_bin2, simp_all)
          subgoal for t l_bin3
            using encode_cmovl_1 by simp
          done
        done
      done

    subgoal by (unfold bitfield_insert_def;simp)

    subgoal 
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
        apply (cases l_bin2, simp_all)
          subgoal for l_bin3
            apply (cases l_bin3, simp_all)
            subgoal for t l_bin4
              using encode_cmovl_3 by blast
            done
          done
        done
      done

    subgoal
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
        apply (cases l_bin2, simp_all)
          subgoal for l_bin3
            apply (cases l_bin3, simp_all)
            subgoal for t l_bin4
              using encode_cmovl_4
              by (simp add: Suc3_eq_add_3 add.commute)
            done
          done
        done
      done
    done
          

  subgoal for test dst src
  \<comment> \<open> Pcmovq 9\<close> 
    apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (unfold x64_decode_def Let_def, simp add: split: option.splits)

    subgoal
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
        apply (cases l_bin2, simp_all)
          subgoal for l_bin3
            apply (cases l_bin3, simp_all)
            subgoal for t l_bin4
              using encode_cmovq_1
              by (simp add: Suc3_eq_add_3 add.commute)
            done
          done
        done
      done
    done
          
  subgoal for dst src
  \<comment> \<open> Pxchgq_rr 10\<close> 
    apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (unfold x64_decode_def Let_def, auto simp add: split: option.splits)
    apply (cases l_bin, simp_all)
    subgoal for l_bin1
      apply (cases l_bin1, simp_all)
      subgoal for l_bin2
        apply (cases l_bin2, simp_all)
        subgoal for t l_bin3
          subgoal
            using encode_movq_rr_1 by blast
          done
        done
      done
    done

  subgoal for dst src
  \<comment> \<open> Pmovsq_rr 12\<close> 
    apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (unfold x64_decode_def Let_def, auto simp add: split: option.splits)
    apply (cases l_bin, simp_all)
    subgoal for l_bin1
      apply (cases l_bin1, simp_all)
      subgoal for l_bin2
        apply (cases l_bin2, simp_all)
        subgoal for t l_bin3
          subgoal
            using encode_movq_rr_1 by blast
          done
        done
      done
    done

  subgoal
  \<comment> \<open> Pcdq 13\<close> 
    apply (unfold x64_decode_def Let_def, auto simp add: split: option.splits)
    apply (cases l_bin, simp_all)
    done

  subgoal
  \<comment> \<open> Pcqo 14\<close> 
    apply (unfold x64_decode_def Let_def,auto simp add: split: option.splits)
    apply (cases l_bin, simp_all)
    subgoal for l_bin1
      apply (cases l_bin1, simp_all)
      subgoal for t l_bin2
        using x64_encode_cqo_1 by blast
      done
    done
  done

  subgoal for dst  
    \<comment> \<open> Pnegl_r 16\<close> 
    apply (unfold Let_def)
    apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (unfold x64_decode_def Let_def, auto simp add: split: option.splits)
    subgoal 
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for t l_bin2
          using encode_negl_r_1 by blast 
        done
      done

    subgoal 
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for t l_bin2
          using encode_negl_r_2 by blast 
        done
      done

    subgoal 
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
          apply (cases l_bin2, simp_all)
        subgoal for t l_bin3
          using encode_negl_r_3 by blast 
        done
      done
    done

    subgoal 
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
          apply (cases l_bin2, simp_all)
        subgoal for t l_bin3
          using encode_negl_r_4 by blast 
        done
      done
    done
  done

  subgoal for dst  
    \<comment> \<open> Pnegq_r 17\<close> 
    apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (unfold x64_decode_def Let_def, auto simp add: split: option.splits)
    subgoal 
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
          apply (cases l_bin2, simp_all)
          subgoal for t l_bin3
            using encode_negq_r_1 by blast  \<comment> \<open> TODO\<close> 

        done
      done

  subgoal for dst src
  \<comment> \<open> Paddq_rr 18\<close> 
    apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (unfold x64_decode_def Let_def, auto simp add: split: option.splits)
    subgoal
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
          apply (cases l_bin2, simp_all)
          subgoal for t l_bin3
          using encode_movq_rr_1 by blast
        done
      done
    done
  done


  subgoal for dst src
  \<comment> \<open> Paddl_rr 19\<close> 
    apply (unfold Let_def)
    apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (unfold x64_decode_def Let_def, auto simp add: split: option.splits)
    subgoal
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for t l_bin2
          using encode_movl_rr_1 by blast
        done
      done

    subgoal by (unfold bitfield_insert_def;simp)

    subgoal 
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
        apply (cases l_bin2, simp_all)
        subgoal for t l_bin3
          using encode_movl_rr_3 by blast
        done
      done
    done

    subgoal
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
          apply (cases l_bin2, simp_all)
          subgoal for t l_bin3
            using encode_movl_rr_4 by blast
          done
        done
      done
    done

  subgoal for dst imm
  \<comment> \<open> Paddl_ri 20\<close> 
    apply (unfold Let_def)
    apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (unfold x64_decode_def Let_def, auto simp add: split: option.splits)
    subgoal 
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
          apply (cases l_bin2, simp_all)
          subgoal for l_bin3
            apply (cases l_bin3, simp_all)
            subgoal for l_bin4
              apply (cases l_bin4, simp_all)
              subgoal for l_bin5
                apply (cases l_bin5, simp_all)
                subgoal for t l_bin6 
                  using encode_movl_ri_1 [of _ _ _ "(Suc (Suc pc))"]
                  by (smt (verit, best) BitM.simps(1) BitM.simps(2) Suc3_eq_add_3 add.commute eval_nat_numeral(3) nat_arith.suc1 numeral_nat(2))
                done
              done
            done
          done
        done
      done

    subgoal 
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
          apply (cases l_bin2, simp_all)
          subgoal for l_bin3
            apply (cases l_bin3, simp_all)
            subgoal for l_bin4
              apply (cases l_bin4, simp_all)
              subgoal for l_bin5
                apply (cases l_bin5, simp_all)
                subgoal for t l_bin6 
                  using encode_movl_ri_2
                  by (metis One_nat_def Suc_eq_plus1 list.sel(3) list.size(3) list.size(4) nat_1_add_1 numeral_3_eq_3 numeral_eq_iff semiring_norm(88) u32_of_u8_list_same) 
                done
              done
            done
          done
        done
      done

    subgoal 
      using encode_movl_ri_3 by blast

    subgoal 
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
          apply (cases l_bin2, simp_all)
          subgoal for l_bin3
            apply (cases l_bin3, simp_all)
            subgoal for l_bin4
              apply (cases l_bin4, simp_all)
              subgoal for l_bin5
                apply (cases l_bin5, simp_all)
                subgoal for l_bin6
                  apply (cases l_bin6, simp_all)
                  subgoal for t l_bin7
                    apply (cases l_bin7, simp_all)
                    using encode_movl_ri_4 by blast
                  done
                done
              done
            done
          done
        done
      done
    done

  subgoal for dst src
  \<comment> \<open> Psubl_rr 23\<close> 
    apply (unfold Let_def)
    apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (unfold x64_decode_def Let_def, auto simp add: split: option.splits)
    subgoal
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for t l_bin2
          using encode_movl_rr_1 by blast
        done
      done

    subgoal
      apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
      apply (unfold bitfield_insert_def u8_of_bool_def Let_def)
      apply simp
      done

    subgoal 
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
        apply (cases l_bin2, simp_all)
        subgoal for t l_bin3
          using encode_movl_rr_3 by blast
        done
      done
    done

    subgoal
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
          apply (cases l_bin2, simp_all)
          subgoal for t l_bin3
            using encode_movl_rr_4 by blast
          done
        done
      done
    done

  subgoal for dst src
  \<comment> \<open> Psubq_rr 24\<close> 
    apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (unfold x64_decode_def Let_def, auto simp add: split: option.splits)
    apply (cases l_bin, simp_all)
    subgoal for l_bin1
      apply (cases l_bin1, simp_all)
      subgoal for l_bin2
        apply (cases l_bin2, simp_all)
        subgoal for t l_bin3
          subgoal
            using encode_movq_rr_1 by blast
          done
        done
      done
    done



*)



(*


  subgoal for dst addr mc
  \<comment> \<open> Pmov_rm 5\<close> 
    apply (cases addr)
    subgoal for src1 x2 x3
      apply simp
      apply (cases src1, simp_all)
      subgoal
        apply (unfold x64_decode_def Let_def, auto simp add: split: option.splits)
        done
      subgoal for src
        apply (cases x2, simp_all)
         prefer 2
        subgoal
          apply (unfold x64_decode_def Let_def, auto simp add: split: option.splits)
          done
        subgoal
          apply (simp add: construct_rex_to_u8_def construct_modsib_to_u8_def)
          apply (unfold x64_decode_def Let_def,
                  auto simp add: split: option.splits; cases l_bin, simp_all)

          subgoal for l_bin1
            apply (cases l_bin1, simp_all)
            subgoal for l_bin2
              apply (cases l_bin2, simp_all)
              using encode_mov_rm_1 by blast
            done

          subgoal for l_bin1
            using encode_mov_rm_2 by blast

          subgoal for l_bin1
            apply (cases l_bin1, simp_all)
            subgoal for l_bin2
              apply (cases l_bin2, simp_all)
              subgoal for l_bin3 
                apply (cases l_bin3, simp_all)
                subgoal for t l_bin4
                  using encode_mov_rm_3 by blast
                done
              done
            done

          subgoal for l_bin1
            apply (cases l_bin1, simp_all)
            subgoal for l_bin2
              apply (cases l_bin2, simp_all)
              subgoal for l_bin3 
                apply (cases l_bin3, simp_all)
                subgoal for t l_bin4
                  using encode_mov_rm_4 by blast
                done
              done
            done


                      prefer 25
  subgoal for dst imm
  \<comment> \<open> Psubl_ri 25\<close> 
    apply (unfold Let_def)
    apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (unfold x64_decode_def Let_def, auto simp add: split: option.splits)
    subgoal 
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
          apply (cases l_bin2, simp_all)
          subgoal for l_bin3
            apply (cases l_bin3, simp_all)
            subgoal for l_bin4
              apply (cases l_bin4, simp_all)
              subgoal for l_bin5
                apply (cases l_bin5, simp_all)
                subgoal for t l_bin6 
                  using encode_subl_ri_1 by presburger
                done
              done
            done
          done
        done
      done

    subgoal 
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
          apply (cases l_bin2, simp_all)
          subgoal for l_bin3
            apply (cases l_bin3, simp_all)
            subgoal for l_bin4
              apply (cases l_bin4, simp_all)
              subgoal for l_bin5
                apply (cases l_bin5, simp_all)
                subgoal for t l_bin6 
                  using encode_subl_ri_2
                  by (metis One_nat_def Suc_eq_plus1 list.sel(3) list.size(3) list.size(4) nat_1_add_1 numeral_3_eq_3 numeral_eq_iff semiring_norm(88) u32_of_u8_list_same) 
                done
              done
            done
          done
        done
      done

    subgoal 
      using encode_movl_ri_3 by blast

    subgoal 
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
          apply (cases l_bin2, simp_all)
          subgoal for l_bin3
            apply (cases l_bin3, simp_all)
            subgoal for l_bin4
              apply (cases l_bin4, simp_all)
              subgoal for l_bin5
                apply (cases l_bin5, simp_all)
                subgoal for l_bin6
                  apply (cases l_bin6, simp_all)
                  subgoal for t l_bin7
                    apply (cases l_bin7, simp_all)
                    using x64_encode_subl_ri_3
                  done
                done
              done
            done
          done
        done
      done
    done


  \<comment> \<open> stop here \<close>
          subgoal for l_bin1
            apply (cases l_bin1, simp_all)
            subgoal for l_bin2
              apply (cases l_bin2, simp_all)
              subgoal for l_bin3 
                apply (cases l_bin3, simp_all)
                subgoal for t l_bin4
                  using encode_mov_rm_5 by blast
                done
              done
            done

          done
    done

  sorry

declare if_split_asm [split del]*)

end