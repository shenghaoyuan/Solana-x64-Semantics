theory x64DecodeProp1
imports
  Main
  rBPFCommType
  x64Disassembler x64Assembler
begin

declare if_split_asm [split]
declare Let_def [simp]
declare x64_decode_op_0x81_def [simp]

fun x64_bin_update ::"nat \<Rightarrow> x64_bin \<Rightarrow> nat \<Rightarrow> u8 list \<Rightarrow> x64_bin " where
  "x64_bin_update 0 l _ _ = l" |
  "x64_bin_update (Suc n) l pc u8_list =  (
  case u8_list of
  [] \<Rightarrow> l |
  x#xs \<Rightarrow> x64_bin_update n (l[pc := x]) (pc+1) xs
)"

lemma x64_bin_update_nth_other: "(xpc1 < xpc \<or> xpc+sz \<le> xpc1) \<Longrightarrow> xpc1 < length l \<Longrightarrow>
  sz = (length l1) \<Longrightarrow> 
  (x64_bin_update (length l1) l xpc l1)!xpc1 = l!xpc1"
  apply (induction l1 arbitrary: xpc sz xpc1 l ; simp)
  subgoal for a al xpc sz xpc1 l
    using add.commute add_Suc_right leD length_list_update less_add_same_cancel2 list.size(3)
      not_less_eq_eq nth_list_update_neq x64_bin_update.simps(1) zero_less_Suc
    using add_Suc less_SucI less_add_Suc1 by fastforce

  done

lemma x64_bin_update_length_eq: "x64_bin_update (length l1) l xpc l1 = l2 \<Longrightarrow> length l = length l2"
  apply (induction l1 arbitrary: xpc l l2; simp)
  subgoal for a al xpc l l2
    by auto 
  done

lemma x64_bin_update_nth_error_other: "
   x64_bin_update sz l xpc l1 = l2 \<Longrightarrow>
(xpc1 < xpc \<or> xpc+sz \<le> xpc1) \<Longrightarrow>
  sz = (length l1) \<Longrightarrow>
  nth_error l xpc1 = Some v \<Longrightarrow> 
  nth_error l2 xpc1 = Some v"
  apply (subgoal_tac "length (x64_bin_update (length l1) l xpc l1) = length l")
   prefer 2
  subgoal using x64_bin_update_length_eq
    by metis
  apply (simp add: nth_error_def)
  apply (cases "length l \<le> xpc1"; simp)
  apply (erule subst [of _ v])
  apply (erule subst [of _ l2])
  apply (rule x64_bin_update_nth_other [of xpc1 xpc sz]; simp?)
  done

lemma x64_decode_op_0x66_jcc_false: "x64_decode_op_0x66 xpc l = Some (length u8_list, Pjcc cond d0) \<Longrightarrow> False"
  apply (simp add: x64_decode_op_0x66_def)
  apply (erule case_option_eq_NE; simp?)+
  done

lemma bitfield_extract_3_5_10_neq_233: "bitfield_extract 3 5 (a1::u8) = 10 \<Longrightarrow> a1 \<noteq> 233"
  apply (simp add: bitfield_extract_def)
  apply (simp add: bit_eq_iff)
  apply (drule_tac x= "2" in spec)
  apply (simp add: bit_simps)
  apply (rule_tac x= "5" in exI)
  apply simp
  done

lemma bitfield_extract_3_5_10_neq_232: "bitfield_extract 3 5 (a1::u8) = 10 \<Longrightarrow> a1 \<noteq> 232"
  apply (simp add: bitfield_extract_def)
  apply (simp add: bit_eq_iff)
  apply (drule_tac x= "2" in spec)
  apply (simp add: bit_simps)
  apply (rule_tac x= "5" in exI)
  apply simp
  done

lemma bitfield_extract_3_5_11_neq_232: "bitfield_extract 3 5 (a1::u8) = 11 \<Longrightarrow>a1 \<noteq> 232"
  apply (simp add: bitfield_extract_def)
  apply (simp add: bit_eq_iff)
  apply (drule_tac x= "2" in spec)
  apply (simp add: bit_simps)
  apply (rule_tac x= "5" in exI)
  apply simp
  done

lemma bitfield_extract_3_5_11_neq_233: "bitfield_extract 3 5 (a1::u8) = 11 \<Longrightarrow>a1 \<noteq> 233"
  apply (simp add: bitfield_extract_def)
  apply (simp add: bit_eq_iff)
  apply (drule_tac x= "2" in spec)
  apply (simp add: bit_simps)
  apply (rule_tac x= "5" in exI)
  apply simp
  done

declare if_split_asm [split del]


lemma ifE:
  assumes c: "(if Q then x else y) = R"
  obtains
    "Q = True \<and> x = R" 
  | "Q = False \<and> y = R"
  using c by argo

declare add_2_eq_Suc [simp del]
declare add_2_eq_Suc' [simp del]
declare One_nat_def [simp del]

lemma x64_encode_x64_decode_other_x64_decode_op_0x66_0: "
  xpc1 + sz1 \<le> xpc \<or> xpc + sz \<le> xpc1 \<Longrightarrow> length u8_list = sz \<Longrightarrow>
  x64_bin_update sz l xpc u8_list = l1 \<Longrightarrow> nth_error l xpc1 = Some 102 \<Longrightarrow> h = 102 \<Longrightarrow>
  x64_decode_op_0x66 xpc1 l = Some (sz1, ins1) \<Longrightarrow> xpc1 < xpc \<or> xpc + sz \<le> xpc1"
  apply (simp add: x64_decode_op_0x66_def)
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for h1 reg imm dst
    by linarith
  subgoal for h1 reg
    apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
    subgoal for dst i1 i2 imm
      by linarith
    apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
    subgoal
      by linarith
    done
  subgoal
    apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
    subgoal
      by linarith
    apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
    subgoal
      by linarith
    subgoal
    apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
      by linarith
    done
  done

lemma x64_encode_x64_decode_other_x64_decode_op_0x66_1: "
  xpc1 + sz1 \<le> xpc \<or> xpc + sz \<le> xpc1 \<Longrightarrow> length u8_list = sz \<Longrightarrow>
  x64_bin_update sz l xpc u8_list = l1 \<Longrightarrow> nth_error l xpc1 = Some 102 \<Longrightarrow> h = 102 \<Longrightarrow>
  x64_decode_op_0x66 xpc1 l = Some (sz1, ins1) \<Longrightarrow> x64_decode_op_0x66 xpc1 l1 = Some (sz1, ins1)"
  apply (simp add: x64_decode_op_0x66_def)
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for h1 reg imm dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" h1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" imm]; simp?; linarith?)
    done

  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for h1 reg dst i1 i2 imm
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" h1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i2]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for h1 reg dis src dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" h1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" dis]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for h1 op reg imm dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" h1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" op]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" imm]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for h1 op reg dst i1 i2 imm
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" h1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" op]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i2]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for h1 op reg dis src dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" h1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" op]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" dis]; simp?; linarith?)
    done
  done



lemma x64_encode_x64_decode_other_x64_decode_op_0x0f_0: "
  xpc1 + sz1 \<le> xpc \<or> xpc + sz \<le> xpc1 \<Longrightarrow> length u8_list = sz \<Longrightarrow>
  x64_bin_update sz l xpc u8_list = l1 \<Longrightarrow> nth_error l xpc1 = Some 15 \<Longrightarrow> h = 15 \<Longrightarrow>
  x64_decode_op_0x0f xpc1 l = Some (sz1, ins1) \<Longrightarrow> xpc1 < xpc \<or> xpc + sz \<le> xpc1"
  apply (simp add: x64_decode_op_0x0f_def)
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for op
    by linarith
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal
    by linarith

    apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
    subgoal
      by linarith
    apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
    subgoal
      by linarith
    done

lemma x64_encode_x64_decode_other_x64_decode_op_0x0f_1: "
  xpc1 + sz1 \<le> xpc \<or> xpc + sz \<le> xpc1 \<Longrightarrow> length u8_list = sz \<Longrightarrow>
  x64_bin_update sz l xpc u8_list = l1 \<Longrightarrow> nth_error l xpc1 = Some 15 \<Longrightarrow> h = 15 \<Longrightarrow> 
  x64_decode_op_0x0f xpc1 l = Some (sz1, ins1) \<Longrightarrow> x64_decode_op_0x0f xpc1 l1 = Some (sz1, ins1)"
  apply (simp add: x64_decode_op_0x0f_def)
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for op
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
    done

  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for op dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for op reg t src dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for op i1 i2 i3 i4 d t
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" i1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i2]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i3]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i4]; simp?; linarith?)
    done
  done


lemma x64_encode_x64_decode_other_x64_decode_op_not_rex_0: "
  xpc1 + sz1 \<le> xpc \<or> xpc + sz \<le> xpc1 \<Longrightarrow> length u8_list = sz \<Longrightarrow>
  x64_bin_update sz l xpc u8_list = l1 \<Longrightarrow> nth_error l xpc1 = Some h \<Longrightarrow> h \<noteq> 144 \<Longrightarrow>
  h \<noteq> 153 \<Longrightarrow> h \<noteq> 195 \<Longrightarrow> h \<noteq> 102 \<Longrightarrow> h \<noteq> 15 \<Longrightarrow> bitfield_extract 4 4 h \<noteq> 4 \<Longrightarrow>
  x64_decode_op_not_rex h xpc1 l = Some (sz1, ins1) \<Longrightarrow> xpc1 < xpc \<or> xpc + sz \<le> xpc1"
  apply (simp add: x64_decode_op_not_rex_def)
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp) | linarith)+
  done


lemma x64_encode_x64_decode_other_x64_decode_op_not_rex_1: "
  xpc1 + sz1 \<le> xpc \<or> xpc + sz \<le> xpc1 \<Longrightarrow> length u8_list = sz \<Longrightarrow>
    x64_bin_update sz l xpc u8_list = l1 \<Longrightarrow>
    nth_error l xpc1 = Some h \<Longrightarrow> h \<noteq> 144 \<Longrightarrow> h \<noteq> 153 \<Longrightarrow> h \<noteq> 195 \<Longrightarrow> h \<noteq> 102 \<Longrightarrow> h \<noteq> 15 \<Longrightarrow>
  bitfield_extract 4 4 h \<noteq> 4 \<Longrightarrow> x64_decode_op_not_rex h xpc1 l = Some (sz1, ins1) \<Longrightarrow>
  x64_decode_op_not_rex h xpc1 l1 = Some (sz1, ins1)"
  apply (simp add: x64_decode_op_not_rex_def)
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for dst
    using bitfield_extract_3_5_10_neq_233 by auto
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for dst
    using bitfield_extract_3_5_10_neq_233 by auto
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for i1 i2 i3 i4 d 
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" i1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" i2]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i3]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i4]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for i1 i2 i3 i4 d 
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" i1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" i2]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i3]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i4]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg src dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dis src dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" dis]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg d1 d2 d3 d4 dis src dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" d1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" d2]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d3]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d4]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg src dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg i1 i2 i3 i4 dst imm
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" i1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i2]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i3]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i4]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg src dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg src dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg src dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg src dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg i1 i2 i3 i4 dst imm
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" i1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i2]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i3]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i4]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg imm dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" imm]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg imm dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" imm]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg imm dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" imm]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dst i1 i2 i3 i4 imm
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" i1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i2]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i3]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i4]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dst i1 i2 i3 i4 imm
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" i1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i2]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i3]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i4]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dst i1 i2 i3 i4 imm
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" i1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i2]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i3]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i4]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dst i1 i2 i3 i4 imm
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" i1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i2]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i3]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i4]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dst i1 i2 i3 i4 imm
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" i1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i2]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i3]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i4]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dst i1 i2 i3 i4 imm
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" i1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i2]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i3]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i4]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dis src dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" dis]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg dis src dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" dis]; simp?; linarith?)
    done
  apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
  subgoal for reg d1 d2 d3 d4 dis src dst
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" reg]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" d1]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" d2]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d3]; simp?; linarith?)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d4]; simp?; linarith?)
    done
  done

lemma x64_encode_x64_decode_other:
  "(xpc1 + sz1 \<le> xpc \<or> xpc+sz \<le> xpc1) \<Longrightarrow>
  x64_decode xpc1 l = Some (sz1, ins1) \<Longrightarrow>
  length u8_list = sz \<Longrightarrow>
  x64_bin_update sz l xpc u8_list = l1 \<Longrightarrow>
    x64_decode xpc1 l1 = Some (sz1, ins1)"
  apply (simp add: x64_decode_def)
  apply (erule case_option_eq_NE; (simp add: split: if_split_asm)?)+
  subgoal for h apply (erule conjE)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
    done
  subgoal for h apply (erule conjE)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
    done
  subgoal for h apply (erule conjE)
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
    done
  subgoal for h
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
    subgoal using x64_encode_x64_decode_other_x64_decode_op_0x66_0 by blast
    subgoal using x64_encode_x64_decode_other_x64_decode_op_0x66_1 by blast
    done
  subgoal for h
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
    subgoal using x64_encode_x64_decode_other_x64_decode_op_0x0f_0 by blast
    subgoal using x64_encode_x64_decode_other_x64_decode_op_0x0f_1 by blast
    done
  subgoal for h
    apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
    subgoal using x64_encode_x64_decode_other_x64_decode_op_not_rex_0 by blast
    subgoal using x64_encode_x64_decode_other_x64_decode_op_not_rex_1 by blast
    done
  subgoal for h
    apply (erule case_option_eq_NE; simp?)+
    subgoal for op
      apply (erule ifE; erule conjE; simp)
      subgoal
        apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
        apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
        done
      apply (erule ifE; erule conjE; simp)
      subgoal
        by (erule case_option_eq_NE; simp?)+
      apply (erule ifE; erule conjE; simp)
      subgoal
        by (erule case_option_eq_NE; simp?)

      apply (erule ifE; erule conjE; simp)
      subgoal
        apply (erule case_option_eq_NE; simp?)+
        subgoal for i1 i2 i3 i4 i5 i6 i7 i8 dst imm
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" i1]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i2]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i3]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i4]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" i5]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+7" i6]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+8" i7]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+9" i8]; simp?; linarith?)
          done
        done

      apply (erule ifE; erule conjE; simp)
      subgoal
        apply (erule case_option_eq_NE; simp?)+
        subgoal for i1 i2 i3 i4 imm
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" i1]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i2]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i3]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i4]; simp?; linarith?)
          done
        done

      apply (erule ifE; erule conjE; simp)
      subgoal
        apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
        subgoal for op1 dst
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" op1]; simp?; linarith?)
          done
        subgoal for op1
          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for reg t src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" op1]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" reg]; simp?; linarith?)
            done
          done
        done

      apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
      subgoal for reg src dst
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
          done
        subgoal for reg
          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for dis src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" dis]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for d1 d2 d3 d4 dis src rb
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" d1]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d2]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d3]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d4]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for sib d1 d2 d3 d4 dis src ri rb
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" sib]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d1]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d2]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d3]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+7" d4]; simp?; linarith?)
            done
          done
        subgoal for reg
          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done

          subgoal
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for sib d1 d2 d3 d4 dis src ri rb
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" sib]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+7" d4]; simp?; linarith?)
              done
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done
          subgoal
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done


            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for i1 i2 i3 i4 dst imm
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" i4]; simp?; linarith?)
              done
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done
          subgoal
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done
            done
          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for sib d1 d2 d3 d4 dis
            apply (erule conjE)
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for ri rb
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" sib]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+7" d4]; simp?; linarith?)
              done
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for i1 i2 i3 i4 dst imm dis
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" dis]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "4+xpc1" i1]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "5+xpc1" i2]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "6+xpc1" i3]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "7+xpc1" i4]; simp?; linarith?)
            done
          subgoal for i1 i2 i3 i4 dst imm
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for d1 d2 d3 d4 dis
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "7+xpc1" i1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "8+xpc1" i2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "9+xpc1" i3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "10+xpc1" i4]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" d1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d4]; simp?; linarith?)
              done
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for dst i1 i2 i3 i4 imm
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i1]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i2]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i3]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" i4]; simp?; linarith?)
            done

           apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for sib d1 d2 d3 d4 dis
            apply (erule conjE)
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for i1 i2 i3 i4 imm ri rb
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" sib]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+7" d4]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+8" i1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+9" i2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+10" i3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+11" i4]; simp?; linarith?)
              done
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for imm dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" imm]; simp?; linarith?)
            done

          subgoal for imm
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" imm]; simp?; linarith?)
              done
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" imm]; simp?; linarith?)
              done
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for dis src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" dis]; simp?; linarith?)
            done
          subgoal 
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for d1 d2 d3 d4 dis src dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" d1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d4]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for sib d1 d2 d3 d4 dis src ri rb
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" sib]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+7" d4]; simp?; linarith?)
              done
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for dis src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" dis]; simp?; linarith?)
            done
          subgoal
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for d1 d2 d3 d4 dis src dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" d1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d4]; simp?; linarith?)
              done
            done
          done
        done
      done


  subgoal for h
    apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
    subgoal for op i1 i2 i3 i4 i5 i6 i7 i8 dst imm
      apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
      apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
      apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" i1]; simp?; linarith?)
      apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i2]; simp?; linarith?)
      apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i3]; simp?; linarith?)
      apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i4]; simp?; linarith?)
      apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" i5]; simp?; linarith?)
      apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+7" i6]; simp?; linarith?)
      apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+8" i7]; simp?; linarith?)
      apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+9" i8]; simp?; linarith?)
      done
    subgoal for op
      apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
      subgoal for op1 dst
        apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
        apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
        apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" op1]; simp?; linarith?)
        done
      subgoal for op1
        apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
        subgoal for reg t src dst
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" op1]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" reg]; simp?; linarith?)
          done
        done

      apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
      subgoal for reg src dst
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
          done
        subgoal for reg
          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for dis src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" dis]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for d1 d2 d3 d4 dis src rb
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" d1]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d2]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d3]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d4]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for sib d1 d2 d3 d4 dis src ri rb
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" sib]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d1]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d2]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d3]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+7" d4]; simp?; linarith?)
            done
          done
        subgoal for reg
          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done

          subgoal
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for sib d1 d2 d3 d4 dis src ri rb
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" sib]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+7" d4]; simp?; linarith?)
              done
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done
          subgoal
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done


            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for i1 i2 i3 i4 dst imm
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" i4]; simp?; linarith?)
              done
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done
          subgoal
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done
            done
          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for sib d1 d2 d3 d4 dis
            apply (erule conjE)
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for ri rb
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" sib]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+7" d4]; simp?; linarith?)
              done
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for i1 i2 i3 i4 dst imm
            apply (erule conjE)+
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dis
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "4+xpc1" i1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "5+xpc1" i2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "6+xpc1" i3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "7+xpc1" i4]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" dis]; simp?; linarith?)
              done
            subgoal
              apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
              subgoal for d1 d2 d3 d4 dis
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "7+xpc1" i1]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "8+xpc1" i2]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "9+xpc1" i3]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "10+xpc1" i4]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" d1]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d2]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d3]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d4]; simp?; linarith?)
                done
              done
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for dst i1 i2 i3 i4 imm
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i1]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i2]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i3]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" i4]; simp?; linarith?)
            done

           apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for sib d1 d2 d3 d4 dis
            apply (erule conjE)
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for i1 i2 i3 i4 imm ri rb
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" sib]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+7" d4]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+8" i1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+9" i2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+10" i3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+11" i4]; simp?; linarith?)
              done
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for imm dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" imm]; simp?; linarith?)
            done

          subgoal for imm
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" imm]; simp?; linarith?)
              done
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" imm]; simp?; linarith?)
              done
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for dis src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" dis]; simp?; linarith?)
            done
          subgoal 
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for d1 d2 d3 d4 dis src dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" d1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d4]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for sib d1 d2 d3 d4 dis src ri rb
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" sib]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+7" d4]; simp?; linarith?)
              done
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for dis src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" dis]; simp?; linarith?)
            done
          subgoal
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for d1 d2 d3 d4 dis src dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (rule conjI, rule impI)
          subgoal by blast
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" d1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d4]; simp?; linarith?)
              done
            done
          done
        done
      done



  subgoal for h
    apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
    subgoal for op dst
      apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
      apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
      done
    subgoal for op
      apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
      subgoal for dst
        apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
        apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
        done
      subgoal
        apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
        subgoal for op1 dst
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" op1]; simp?; linarith?)
          done
        subgoal for op1
          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for reg t src dst
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" op1]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" reg]; simp?; linarith?)
          done
        done

      apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
      subgoal for reg src dst
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
          apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
          done
        subgoal for reg
          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for dis src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" dis]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for d1 d2 d3 d4 dis src rb
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" d1]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d2]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d3]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d4]; simp?; linarith?)
            done

          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          done
        subgoal for reg
          apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
          subgoal for src dst
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
            apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
            done

          subgoal
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for src dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done
            subgoal
              apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
              subgoal for dst
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
                done
              apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
              subgoal for dst
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
                done
              apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
              subgoal for dst
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
                done
              apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
              subgoal for dst
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
                done
              apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
              subgoal for i1 i2 i3 i4 dst imm
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i1]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i2]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i3]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" i4]; simp?; linarith?)
                done
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for src dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for src dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for src dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done
            subgoal
              apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
              subgoal for dst
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
                done

              apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
              subgoal for dst
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
                done
              done
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for src dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for i1 i2 i3 i4 dst imm
              apply (erule conjE)+
              apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (erule conjE)+
              apply (subgoal_tac "nth_error l1 (xpc1 + 3) = Some i1"; simp?)
               prefer 2
              subgoal
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i1]; simp?; linarith?)
                done
              apply (subgoal_tac "nth_error l1 (xpc1 + 4) = Some i2"; simp?)
               prefer 2
              subgoal
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i2]; simp?; linarith?)
                done
              apply (subgoal_tac "nth_error l1 (xpc1 + 5) = Some i3"; simp?)
               prefer 2
              subgoal
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i3]; simp?; linarith?)
                done
              apply (subgoal_tac "nth_error l1 (xpc1 + 6) = Some i4"; simp?)
              subgoal
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" i4]; simp?; linarith?)
                done
              done
            subgoal for i1 i2 i3 i4 dst imm
              apply (erule conjE)+
              apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst i1 i2 i3 i4 imm
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" i4]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst i1 i2 i3 i4 imm
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" i4]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst i1 i2 i3 i4 imm
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" i4]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst i1 i2 i3 i4 imm
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" i4]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst i1 i2 i3 i4 imm
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" i4]; simp?; linarith?)
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dst i1 i2 i3 i4 imm
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" i1]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" i2]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" i3]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" i4]; simp?; linarith?)
              done

            subgoal
              apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
              subgoal for sib d1 d2 d3 d4 dis
                apply (erule conjE)
                apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
                done
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for imm dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" imm]; simp?; linarith?)
              done
            subgoal for imm
              apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
              subgoal for dst
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" imm]; simp?; linarith?)
                done
              apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
              subgoal for dst
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" imm]; simp?; linarith?)
                done
              done

            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dis src dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" dis]; simp?; linarith?)
              done
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            subgoal for dis src dst
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
              apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" dis]; simp?; linarith?)
              done
            subgoal
              apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
              subgoal for d1 d2 d3 d4 dis src dst
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 xpc1 h]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+1" op]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+2" reg]; simp?; linarith?)
                apply (erule conjE)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+3" d1]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+4" d2]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+5" d3]; simp?; linarith?)
                apply (subst x64_bin_update_nth_error_other [of sz l xpc u8_list l1 "xpc1+6" d4]; simp?; linarith?)
                done
              apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
              done
            apply ((erule case_option_eq_NE; simp?) | (erule ifE; erule conjE; simp))+
            done
          done
        done
      done
    done
  done

end