theory x64DecodeProp1
imports
  Main
  rBPFCommType
  x64Disassembler x64Assembler
begin

declare if_split_asm [split]
declare Let_def [simp]
declare x64_decode_op_not_rex_def [simp]
declare x64_decode_op_0x66_def [simp]
declare x64_decode_op_0x0f_def [simp]
declare x64_decode_op_0x81_def [simp]

lemma x64_decode_sz_gt_0: "x64_decode pc l = Some (sz, ins) \<Longrightarrow> 0 < sz"
  apply (simp add: x64_decode_def nth_error_def;
      (erule case_option_eq_NE; simp?)+)
  done

declare x64_decode_op_not_rex_def [simp del]
declare x64_decode_op_0x66_def [simp del]
declare x64_decode_op_0x0f_def [simp del]
declare x64_decode_op_0x81_def [simp del]

fun x64_bin_update ::"nat \<Rightarrow> x64_bin \<Rightarrow> nat \<Rightarrow> u8 list \<Rightarrow> x64_bin " where
  "x64_bin_update 0 l _ _ = l" |
  "x64_bin_update (Suc n) l pc u8_list =  (
  case u8_list of
  [] \<Rightarrow> l |
  x#xs \<Rightarrow> x64_bin_update n (l[pc := x]) (pc+1) xs
)"

lemma x64_bin_update_nth_other: "(xpc1 + sz1 \<le> xpc \<or> xpc+sz \<le> xpc1) \<Longrightarrow> xpc1 < length l \<Longrightarrow>
  sz = (length l1) \<Longrightarrow> 0 < sz1 \<Longrightarrow> 
  (x64_bin_update (length l1) l xpc l1)!xpc1 = l!xpc1"
  apply (induction l1 arbitrary: xpc sz xpc1 sz1 l ; simp)
  subgoal for a al xpc sz xpc1 sz1 l
    by (smt (verit, ccfv_threshold) add.commute add_Suc_right leD length_list_update less_add_same_cancel2 list.size(3) not_less_eq_eq nth_list_update_neq x64_bin_update.simps(1) zero_less_Suc)
  done

lemma x64_bin_update_length_eq: "x64_bin_update (length l1) l xpc l1 = l2 \<Longrightarrow> length l = length l2"
  apply (induction l1 arbitrary: xpc l l2; simp)
  subgoal for a al xpc l l2
    by auto 
  done

lemma x64_bin_update_nth_error_other: "(xpc1 + sz1 \<le> xpc \<or> xpc+sz \<le> xpc1) \<Longrightarrow> 
  sz = (length l1) \<Longrightarrow> 0 < sz1 \<Longrightarrow> 
  nth_error l xpc1 = Some v \<Longrightarrow> 
  nth_error (x64_bin_update (length l1) l xpc l1) xpc1 = Some v"
  apply (subgoal_tac "length (x64_bin_update (length l1) l xpc l1) = length l")
   prefer 2
  subgoal using x64_bin_update_length_eq
    by metis
  apply (simp add: nth_error_def)
  apply (cases "length l \<le> xpc1"; simp)
  apply (erule subst [of _v])
  apply (rule x64_bin_update_nth_other [of xpc1 sz1 xpc sz]; simp?)
  done

lemma x64_decode_op_0x66_jcc_false: "x64_decode_op_0x66 xpc l = Some (length u8_list, Pjcc cond d0) \<Longrightarrow> False"
  apply (simp add: x64_decode_op_0x66_def)
  apply (erule case_option_eq_NE; simp?)+
  done

lemma x64_decode_op_0x66_jcc_other: "xpc1 + sz1 \<le> xpc \<or> xpc + length u8_list \<le> xpc1 \<Longrightarrow>
    x64_decode_op_0x0f xpc l = Some (length u8_list, Pjcc cond d0) \<Longrightarrow>
    x64_decode_op_0x66 xpc1 l = Some (sz1, ins1) \<Longrightarrow>
    x64_decode_op_0x66 xpc1 (x64_bin_update (length u8_list) l xpc u8_list) = Some (sz1, ins1)"
  apply (simp add: x64_decode_op_0x0f_def x64_decode_op_0x66_def)
  apply (erule case_option_eq_NE; simp?)
  subgoal for op
    apply (erule case_option_eq_NE; simp?)+
    done
  subgoal for op
    apply (erule case_option_eq_NE; simp?)+
    done
  subgoal for op
    apply (erule case_option_eq_NE; simp?)+
    subgoal for h1 i1 reg i2 imm i3 dst i4
      apply (erule conjE)+
      apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc xpc1) = Some 193")
      subgoal
        apply simp
        apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc (Suc xpc1)) = Some reg", simp)
        subgoal
          apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (xpc1 + 3) = Some imm", simp)
          apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
          apply auto
          done
        apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
        apply auto
        done
      apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
      apply auto
      done
    subgoal for h1 i1 reg 
      apply (erule case_option_eq_NE; simp?)+
      subgoal for i2 dst i3 i1a i4 i2a imm
        apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc xpc1) = Some 129")
        subgoal
          apply simp
          apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc (Suc xpc1)) = Some reg", simp)
          subgoal
            apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (xpc1 + 3) = Some i1a", simp)
            subgoal
              apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (xpc1 + 4) = Some i2a", simp)
              apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
              apply auto
              done
            apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
            apply auto
            done
          apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
          apply auto
          done
        apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
        apply auto
        done
      done
    subgoal for h1 i1 reg 
      apply (erule case_option_eq_NE; simp?)+
      subgoal for i2 dis i3 src i4 dst
        apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc xpc1) = Some 137")
        subgoal
          apply simp
          apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc (Suc xpc1)) = Some reg", simp)
          subgoal
            apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (xpc1 + 3) = Some dis", simp)
            subgoal
              apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
              apply auto
              done
            done
          apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
          apply auto
          done
        apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
        apply auto
        done
      done
    subgoal for h1
      apply (erule case_option_eq_NE; simp?)+
      subgoal for i1 opa i2 reg i3 imm i4 dst
        apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc xpc1) = Some h1")
        subgoal
          apply simp
          apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc (Suc xpc1)) = Some 193", simp)
          subgoal
            apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (xpc1 + 3) = Some reg", simp)
            subgoal
              apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (xpc1 + 4) = Some imm", simp)
              apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
              apply auto
              done
            subgoal
              apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
              apply auto
              done
            done
          apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
          apply auto
          done
        apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
        apply auto
        done
      subgoal for i1 opa i2 reg
        apply (erule case_option_eq_NE; simp?)+
        subgoal for i3 dst i4 i1a i2a imm
        apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc xpc1) = Some h1")
        subgoal
          apply simp
          apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc (Suc xpc1)) = Some 129", simp)
          subgoal
            apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (xpc1 + 3) = Some reg", simp)
            subgoal
              apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (xpc1 + 4) = Some i1a", simp)
              subgoal
                apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (xpc1 + 5) = Some i2a", simp)
                apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
                apply auto
                done
              apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
              apply auto
              done
            subgoal
              apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
              apply auto
              done
            done
          apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
          apply auto
          done
        apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
        apply auto
        done
      done
      subgoal for i1 opa i2 reg
        apply (erule case_option_eq_NE; simp?)+
        subgoal for i3 dis i4 src dst
        apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc xpc1) = Some h1")
        subgoal
          apply simp
          apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc (Suc xpc1)) = Some 137", simp)
          subgoal
            apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (xpc1 + 3) = Some reg", simp)
            subgoal
              apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (xpc1 + 4) = Some dis", simp)
              apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
              apply auto
              done
            subgoal
              apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
              apply auto
              done
            done
          apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
          apply auto
          done
        apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
        apply auto
        done
      done
    done
  done
  done

lemma x64_decode_op_0x0f_jcc_other: "xpc1 + sz1 \<le> xpc \<or> xpc + length u8_list \<le> xpc1 \<Longrightarrow>
    x64_decode_op_0x0f xpc l = Some (length u8_list, Pjcc cond d0) \<Longrightarrow>
    x64_decode_op_0x0f xpc1 l = Some (sz1, ins1) \<Longrightarrow>
      x64_decode_op_0x0f xpc1 (x64_bin_update (length u8_list) l xpc u8_list) = Some (sz1, ins1)"
  apply (simp add: x64_decode_op_0x0f_def x64_decode_op_0x66_def)
  apply (erule case_option_eq_NE; simp?)
  subgoal for op
    apply (erule case_option_eq_NE; simp?)+
    done
  subgoal for op
    apply (erule case_option_eq_NE; simp?)+
    done
  subgoal for op
    apply (erule case_option_eq_NE; simp?)+
    subgoal for opa i1 i2 i3 i4
      apply (erule conjE)+
      apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc xpc1) = Some 49")
      subgoal
        apply simp
        done
        apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
        apply auto
        done
    subgoal for opa
      apply (erule case_option_eq_NE; simp?)+
      subgoal for i1 dst i2 i3 i4
      apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc xpc1) = Some opa")
      subgoal
        apply simp
        done
        apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
        apply auto
        done
      done
    subgoal for opa
      apply (erule case_option_eq_NE; simp?)+
      subgoal for i1 reg i2 t i3 src i4 dst
        apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc xpc1) = Some opa", simp)
        subgoal
          apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc (Suc xpc1)) = Some reg", simp)
          apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
          apply auto
          done
        apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
        apply auto
        done
      done
    subgoal for opa
      apply (erule case_option_eq_NE; simp?)+
      subgoal for i1 i1a i2 i2a i3 i3a i4 i4a da t
        apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc xpc1) = Some opa", simp)
        subgoal
          apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc (Suc xpc1)) = Some i1a", simp)
          subgoal
            apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (xpc1 + 3) = Some i2a", simp)
            subgoal
              apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (xpc1 + 4) = Some i3a", simp)
              subgoal
                apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (xpc1 + 5) = Some i4a", simp)
                apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
                apply auto
                done
              apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
              apply auto
              done
            apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
            apply auto
            done
          apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
          apply auto
          done
        apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
        apply auto
        done
      done
    done
  done

lemma x64_decode_op_not_rex_jcc_other: "xpc1 + sz1 \<le> xpc \<or> xpc + length u8_list \<le> xpc1 \<Longrightarrow>
    x64_decode_op_0x0f xpc l = Some (length u8_list, Pjcc cond d0) \<Longrightarrow>
    x64_decode_op_not_rex a1 xpc1 l = Some (sz1, ins1) \<Longrightarrow>
    x64_decode_op_not_rex a1 xpc1 (x64_bin_update (length u8_list) l xpc u8_list) = Some (sz1, ins1)"
  apply (simp add: x64_decode_op_0x0f_def x64_decode_op_not_rex_def)
  apply (erule case_option_eq_NE; simp?)
  subgoal for op
    apply (erule case_option_eq_NE; simp?)+
    done
  subgoal for op
    apply (erule case_option_eq_NE; simp?)+
    done
  subgoal for op
    apply (erule case_option_eq_NE; simp?)+
    subgoal for dst i1 i2 i3 i4
      apply (erule conjE)+
      apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc xpc1) = Some 49")
      subgoal
        apply simp
        done
        apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
        apply auto
        done
    subgoal for opa
      apply (erule case_option_eq_NE; simp?)+
      subgoal for i1 dst i2 i3 i4
      apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc xpc1) = Some opa")
      subgoal
        apply simp
        done
        apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
        apply auto
        done
      done
    subgoal for opa
      apply (erule case_option_eq_NE; simp?)+
      subgoal for i1 reg i2 t i3 src i4 dst
        apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc xpc1) = Some opa", simp)
        subgoal
          apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc (Suc xpc1)) = Some reg", simp)
          apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
          apply auto
          done
        apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
        apply auto
        done
      done
    subgoal for opa
      apply (erule case_option_eq_NE; simp?)+
      subgoal for i1 i1a i2 i2a i3 i3a i4 i4a da t
        apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc xpc1) = Some opa", simp)
        subgoal
          apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (Suc (Suc xpc1)) = Some i1a", simp)
          subgoal
            apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (xpc1 + 3) = Some i2a", simp)
            subgoal
              apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (xpc1 + 4) = Some i3a", simp)
              subgoal
                apply (subgoal_tac "nth_error (x64_bin_update (length u8_list) l xpc u8_list) (xpc1 + 5) = Some i4a", simp)
                apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
                apply auto
                done
              apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
              apply auto
              done
            apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
            apply auto
            done
          apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
          apply auto
          done
        apply (rule x64_bin_update_nth_error_other [of _ 1]; simp?)
        apply auto
        done
      done
    done
  done

lemma x64_encode_x64_decode_other:
  "(xpc1 + sz1 \<le> xpc \<or> xpc+sz \<le> xpc1) \<Longrightarrow>
  x64_decode xpc l = Some (sz, Pjcc cond d0) \<Longrightarrow>
  x64_decode xpc1 l = Some (sz1, ins1) \<Longrightarrow>
  sz = length u8_list \<Longrightarrow>
  l1 = x64_bin_update (length u8_list) l xpc u8_list \<Longrightarrow>
    x64_decode xpc1 l1 = Some (sz1, ins1)"
  apply (simp add: x64_decode_def)
  apply (erule case_option_eq_NE; simp?)
  subgoal
    using x64_decode_op_0x66_jcc_false by blast
  subgoal a
    apply (erule case_option_eq_NE; simp?)
    subgoal for a1
      using x64_bin_update_nth_error_other 
      apply simp
      done
    subgoal for a1 apply (erule conjE)
      using x64_bin_update_nth_error_other 
      apply simp
      by auto
    subgoal for a1 apply (erule conjE)
      using x64_bin_update_nth_error_other 
      apply simp
      by auto
    subgoal for a1
      apply (subgoal_tac "0 < sz1")
      subgoal
        using x64_bin_update_nth_error_other [of xpc1 sz1 xpc sz u8_list l 102]
        apply simp
        using x64_decode_op_0x66_jcc_other by blast
      subgoal
        apply (simp add: x64_decode_op_0x66_def nth_error_def;
      (erule case_option_eq_NE; simp?)+)
        done
      done

    subgoal for a1
      apply (subgoal_tac "0 < sz1")
      subgoal
        using x64_bin_update_nth_error_other [of xpc1 sz1 xpc sz u8_list l 15]
        apply simp
        using x64_decode_op_0x0f_jcc_other by blast
      subgoal
        apply (simp add: x64_decode_op_0x0f_def nth_error_def;
      (erule case_option_eq_NE; simp?)+)
        done
      done

    subgoal for a1
      apply (subgoal_tac "0 < sz1")
      subgoal
        using x64_bin_update_nth_error_other [of xpc1 sz1 xpc sz u8_list l a1]
        apply simp
        using x64_decode_op_not_rex_jcc_other by blast
      subgoal
        apply (simp add: x64_decode_op_not_rex_def nth_error_def;
      (erule case_option_eq_NE; simp?)+)
        done
      done
    subgoal for a1
      sorry
    subgoal for a1
      sorry
    done
  subgoal for a
(**x64_decode_op_not_rex a xpc l = Some (length u8_list, Pjcc cond d0) \<Longrightarrow> False *)
    sorry
  subgoal for a
    apply (cases "nth_error l xpc1"; simp add: split: if_split_asm)

end