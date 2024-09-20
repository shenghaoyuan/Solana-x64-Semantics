theory x64EncodeProof
imports
  Main
  rBPFCommType
  x64Assembler x64Disassembler
(*  x64_encode_movl_rr_1 x64_encode_movl_rr_3  x64_encode_movl_rr_4
  x64_encode_movq_rr_1
  x64_encode_mov_rm_1 x64_encode_mov_rm_2 x64_encode_mov_rm_3 x64_encode_mov_rm_4
  x64_encode_cmovl_1 x64_encode_cmovl_3 x64_encode_cmovl_4
  x64_encode_cmovq_1
  x64_encode_cqo_1
  x64_encode_negl_r_1 x64_encode_negq_r_1*)x64_encode_negl_r_1 x64_encode_negl_r_2 x64_encode_negl_r_3 x64_encode_negl_r_4
begin

declare if_split_asm [split]

lemma [simp]: "
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (v >> 3)) 0) = Some dst \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 v) 0) = Some src \<Longrightarrow>
      bitfield_insert_u8 3 (Suc 0) (bitfield_insert_u8 2 (Suc 0)
      (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg src) 8 \<noteq> 0)) 0)
        (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0))) 0 = 0"
  apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
  apply (unfold bitfield_insert_u8_def u8_of_bool_def Let_def)
  apply simp
  done



lemma x64_decode_encode_consistency:
  "list_in_list l_bin pc l \<Longrightarrow> x64_decode pc l = Some (length l_bin, ins) \<Longrightarrow> 
    Some l_bin = x64_encode ins"
  apply (cases ins; simp_all)
                      prefer 3
  subgoal for dst imm
  \<comment> \<open> Pmovl_ri 20\<close> 
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

    subgoal by (unfold bitfield_insert_u8_def;simp)

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

    subgoal by (unfold bitfield_insert_u8_def;simp)

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

    subgoal by (unfold bitfield_insert_u8_def;simp)

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