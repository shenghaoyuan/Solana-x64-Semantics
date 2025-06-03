theory x64DecodeProofAux
imports
  Main
  rBPFCommType
  x64Assembler x64Disassembler BitsOpMore BitsOpMore2 BitsOpMore3 BitsOpMore4
  x64BitSimp
begin

named_theorems nat_simp
declare Suc3_eq_add_3 [nat_simp]

lemma Suc4_eq_add_4[nat_simp]: \<open>Suc (Suc (Suc (Suc n))) = 4 + n\<close>
  by simp

lemma Suc5_eq_add_5[nat_simp]: \<open>Suc (Suc (Suc (Suc (Suc n)))) = 5 + n\<close>
  by simp

lemma Suc6_eq_add_6[nat_simp]: \<open>Suc (Suc (Suc (Suc (Suc (Suc n))))) = 6 + n\<close>
  by simp

lemma Suc7_eq_add_7[nat_simp]: \<open>Suc (Suc (Suc (Suc (Suc (Suc (Suc n)))))) = 7 + n\<close>
  by simp

lemma Suc8_eq_add_8[nat_simp]: \<open>Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n))))))) = 8 + n\<close>
  by simp

lemma Suc9_eq_add_9[nat_simp]: \<open>Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n)))))))) = 9 + n\<close>
  by simp

lemma Suc10_eq_add_10[nat_simp]: \<open>Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n))))))))) = 10 + n\<close>
  by simp


  \<comment> \<open> u16 \<close> 

lemma length_u8_list_of_u16_eq_2 : "length (u8_list_of_u16 imm) = 2"
  by (simp add: u8_list_of_u16_def)

lemma list_in_list_u8_list_of_u16_simp_0 : "list_in_list (u8_list_of_u16 imm) pc l \<Longrightarrow>
  nth_error l pc = Some (l!pc)"
  apply (simp add: u8_list_of_u16_def nth_error_def)
    by force

lemma list_in_list_u8_list_of_u16_simp_1 : "list_in_list (u8_list_of_u16 imm) pc l \<Longrightarrow>
  nth_error l (pc + 1) = Some (l!(pc+1))"
  apply (simp add: u8_list_of_u16_def nth_error_def)
    by force

lemma list_in_list_u8_list_of_u16_simp : "list_in_list (u8_list_of_u16 imm) pc l \<Longrightarrow>
  u16_of_u8_list [l!pc, l!(pc+1)] = Some imm"
  apply (rule sym [of "Some imm"])
  apply (simp add: u16_of_u8_list_same u8_list_of_u16_def nth_error_def
      Suc3_eq_add_3 add.commute)
  apply (cases "length l \<le> Suc pc"; simp)
  done

  \<comment> \<open> u32 \<close>
lemma length_u8_list_of_u32_eq_4 : "length (u8_list_of_u32 imm) = 4"
  by (simp add: u8_list_of_u32_def)

lemma list_in_list_u8_list_of_u32_simp_0 : "list_in_list (u8_list_of_u32 imm) pc l \<Longrightarrow>
  nth_error l pc = Some (l!pc)"
  apply (simp add: u8_list_of_u32_def nth_error_def)
    by force

lemma list_in_list_u8_list_of_u32_simp_1 : "list_in_list (u8_list_of_u32 imm) pc l \<Longrightarrow>
  nth_error l (pc+1) = Some (l!(pc+1))"
  apply (simp add: u8_list_of_u32_def nth_error_def)
    by force

lemma list_in_list_u8_list_of_u32_simp_2 : "list_in_list (u8_list_of_u32 imm) pc l \<Longrightarrow>
  nth_error l (pc+2) = Some (l!(pc+2))"
  apply (simp add: u8_list_of_u32_def nth_error_def)
    by force

lemma list_in_list_u8_list_of_u32_simp_3 : "list_in_list (u8_list_of_u32 imm) pc l \<Longrightarrow>
  nth_error l (pc+3) = Some (l!(pc+3))"
  apply (simp add: u8_list_of_u32_def nth_error_def)
    by force

lemma list_in_list_u8_list_of_u32_simp : "list_in_list (u8_list_of_u32 imm) pc l \<Longrightarrow>
  u32_of_u8_list [l!pc, l!(pc+1), l!(pc+2), l!(pc+3)] = Some imm"
  apply (rule sym [of "Some imm"])
  apply (simp add: u32_of_u8_list_same u8_list_of_u32_def nth_error_def
      Suc3_eq_add_3 add.commute)
  apply (cases "length l \<le> pc + 3"; simp)
  done


  \<comment> \<open> u64 \<close> 
lemma list_in_list_u8_list_of_u64_simp_0 : "list_in_list (u8_list_of_u64 imm) pc l \<Longrightarrow>
  nth_error l pc = Some (l!pc)"
  apply (simp add: u8_list_of_u64_def nth_error_def)
  by force

lemma list_in_list_u8_list_of_u64_simp_1 : "list_in_list (u8_list_of_u64 imm) pc l \<Longrightarrow>
  nth_error l (pc+1) = Some (l!(pc+1))"
  apply (simp add: u8_list_of_u64_def nth_error_def)
  by force

lemma list_in_list_u8_list_of_u64_simp_2 : "list_in_list (u8_list_of_u64 imm) pc l \<Longrightarrow>
  nth_error l (pc+2) = Some (l!(pc+2))"
  apply (simp add: u8_list_of_u64_def nth_error_def)
  by force

lemma list_in_list_u8_list_of_u64_simp_3 : "list_in_list (u8_list_of_u64 imm) pc l \<Longrightarrow>
  nth_error l (pc+3) = Some (l!(pc+3))"
  apply (simp add: u8_list_of_u64_def nth_error_def)
  by force

lemma list_in_list_u8_list_of_u64_simp_4 : "list_in_list (u8_list_of_u64 imm) pc l \<Longrightarrow>
  nth_error l (pc+4) = Some (l!(pc+4))"
  apply (simp add: u8_list_of_u64_def nth_error_def)
  by force

lemma list_in_list_u8_list_of_u64_simp_5 : "list_in_list (u8_list_of_u64 imm) pc l \<Longrightarrow>
  nth_error l (pc+5) = Some (l!(pc+5))"
  apply (simp add: u8_list_of_u64_def nth_error_def)
  by force

lemma list_in_list_u8_list_of_u64_simp_6 : "list_in_list (u8_list_of_u64 imm) pc l \<Longrightarrow>
  nth_error l (pc+6) = Some (l!(pc+6))"
  apply (simp add: u8_list_of_u64_def nth_error_def)
  by force

lemma list_in_list_u8_list_of_u64_simp_7 : "list_in_list (u8_list_of_u64 imm) pc l \<Longrightarrow>
  nth_error l (pc+7) = Some (l!(pc+7))"
  apply (simp add: u8_list_of_u64_def nth_error_def)
  by force

lemma list_in_list_u8_list_of_u64_simp : "list_in_list (u8_list_of_u64 imm) pc l \<Longrightarrow>
  u64_of_u8_list [l!pc, l!(pc+1), l!(pc+2), l!(pc+3), l!(pc+4), l!(pc+5), l!(pc+6), l!(pc+7)] = Some imm"
  apply (rule sym [of "Some imm"])
  apply (simp add: u64_of_u8_list_same u8_list_of_u64_def nth_error_def
      Suc3_eq_add_3 add.commute)
  apply (cases "length l \<le> pc + 7"; simp)
  done

lemma length_u8_list_of_u64_eq_8 : "length (u8_list_of_u64 imm) = 8"
  by (simp add: u8_list_of_u64_def)

lemma list_in_list_concat: "list_in_list (l1 @ l2) pc l = (list_in_list l1 pc l \<and> list_in_list l2 (pc + length l1) l)"
(*
l1 = h # t
list_in_list ((h # t) @ l2) pc l                    \<Longrightarrow> (h = l!pc \<and> list_in_list (t @ l2) (pc+1) l) by def of list_in_list
                                                      \<Longrightarrow> list_in_list (t @ l2) (pc+1) l
list_in_list l1 pc l \<Longrightarrow> list_in_list (h # t) pc l  \<Longrightarrow> (h = l!pc \<and> list_in_list t (pc+1) l)
                                                      \<Longrightarrow> list_in_list t (pc+1) l
list_in_list l2 (pc + length l1) l                  \<Longrightarrow> list_in_list l2 (pc + 1+ length t) l 
                                                          \<Longrightarrow> by IH *)
  apply (induction l1 arbitrary: l2 pc l; simp add: nth_error_def)
  subgoal for a l1 l2 pc l
    by auto
  done

lemma construct_modsib_to_u8_imply_base_reg_simp: "
  rex = construct_rex_to_u8 b0 b (and (u8_of_ireg index_reg) 8 \<noteq> 0)
    (and (u8_of_ireg base_reg) 8 \<noteq> 0) \<Longrightarrow>
  v = construct_modsib_to_u8 scale (u8_of_ireg index_reg) (u8_of_ireg base_reg) \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 1 (unsigned_bitfield_extract_u8 0 3 v)
      (unsigned_bitfield_extract_u8 0 1 rex)) = Some base_reg"
  apply (simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
      bitfield_insert_u8_def unsigned_bitfield_extract_u8_def Let_def)
  apply (simp only: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp add: bit_simp bit_simps)
  apply (simp add: bit.conj_disj_distrib) (**TODO: here could we find a way to solve it automatically, NP hard? *)
  apply (simp add: and.left_commute and.commute and.assoc and.assoc[symmetric])
  apply (simp add: bit.conj_disj_distrib)
  apply (simp add: and.assoc[symmetric])
  apply (simp add: and.commute)
  apply (simp add: and.assoc[symmetric])
  apply (cases base_reg; simp)
  done

lemma construct_modsib_to_u8_imply_base_reg: "
  construct_rex_to_u8 b0 b (and (u8_of_ireg index_reg) 8 \<noteq> 0)
    (and (u8_of_ireg base_reg) 8 \<noteq> 0) = rex \<Longrightarrow>
  construct_modsib_to_u8 scale (u8_of_ireg index_reg) (u8_of_ireg base_reg) = v \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 1 (unsigned_bitfield_extract_u8 0 3 v)
      (unsigned_bitfield_extract_u8 0 1 rex)) = Some base_reg"
  using construct_modsib_to_u8_imply_base_reg_simp by blast

lemma construct_modsib_to_u8_imply_index_reg_simp: "
  rex = construct_rex_to_u8 True b (and (u8_of_ireg index_reg) 8 \<noteq> 0)
    (and (u8_of_ireg base_reg) 8 \<noteq> 0) \<Longrightarrow>
  v = construct_modsib_to_u8 scale (u8_of_ireg index_reg) (u8_of_ireg base_reg) \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 1 (unsigned_bitfield_extract_u8 3 3 v)
      (unsigned_bitfield_extract_u8 1 1 rex)) = Some index_reg"
  apply (simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
      bitfield_insert_u8_def unsigned_bitfield_extract_u8_def Let_def)
  apply (simp only: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp only: bit_simp)
  apply (simp add: bit.conj_disj_distrib) (**TODO: here could we find a way to solve it automatically, NP hard? *)
  apply (simp add: and.left_commute and.commute and.assoc and.assoc[symmetric])
  apply (simp add: bit.conj_disj_distrib)
  apply (simp add: and.assoc[symmetric])
  apply (cases index_reg; simp)
  done

lemma construct_modsib_to_u8_imply_index_reg: "
  construct_rex_to_u8 True b (and (u8_of_ireg index_reg) 8 \<noteq> 0)
    (and (u8_of_ireg base_reg) 8 \<noteq> 0) = rex \<Longrightarrow>
  construct_modsib_to_u8 scale (u8_of_ireg index_reg) (u8_of_ireg base_reg) = v \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 1 (unsigned_bitfield_extract_u8 3 3 v)
      (unsigned_bitfield_extract_u8 1 1 rex)) = Some index_reg"
  using construct_modsib_to_u8_imply_index_reg_simp by blast

lemma word_of_nat_3_eq: "word_of_nat n \<le> (3::u8) \<longleftrightarrow> ((word_of_nat n) ::u8) \<le> word_of_nat 3"
  by simp

lemma u8_le3_eq1: "(scale::u8) \<le> 3 \<Longrightarrow> scale = 0 \<or> scale = 1 \<or> scale = 2 \<or> scale = 3"
  apply (cases scale, simp_all)
  subgoal for n
    apply (simp only: word_of_nat_3_eq)
    apply (simp only: word_of_nat_less_eq_iff)
    apply simp
    apply (simp only: take_bit_eq_mod)
    apply simp
    by (metis Abs_fnat_hom_0 One_nat_def le_neq_implies_less less_2_cases less_Suc_eq
        numeral_2_eq_2 numeral_3_eq_3 of_nat_1 of_nat_numeral)
  done

lemma u8_le3_eq2: "scale = 0 \<or> scale = 1 \<or> scale = 2 \<or> scale = 3 \<Longrightarrow> (scale::u8) \<le> 3"
  apply (erule disjE, simp)
  apply (erule disjE, simp)
  apply (erule disjE, simp)
  apply simp
  done

lemma u8_le3_eq: "(scale::u8) \<le> 3 \<longleftrightarrow> scale = 0 \<or> scale = 1 \<or> scale = 2 \<or> scale = 3"
  using u8_le3_eq1 u8_le3_eq2 by blast


lemma scale_le3_eq_simp: "scale \<le> 3 \<Longrightarrow> and 3 ((scale << 6) >> 6) = (scale::u8)"
  apply (simp only: u8_le3_eq)
  apply (erule disjE, simp)
  apply (erule disjE, simp)
  apply (erule disjE, simp)
  apply simp
  done

lemma scale_le3_eq: "\<not> 3 < scale \<Longrightarrow> and 3 ((scale << 6) >> 6) = (scale::u8)"
  using scale_le3_eq_simp
  using linorder_le_less_linear by blast 

lemma construct_modsib_to_u8_imply_scale_simp: " \<not> 3 < scale \<Longrightarrow>
  v = construct_modsib_to_u8 scale (u8_of_ireg index_reg) (u8_of_ireg base_reg) \<Longrightarrow>
    unsigned_bitfield_extract_u8 6 2 v = scale"
  apply (simp add: construct_modsib_to_u8_def bitfield_insert_u8_def unsigned_bitfield_extract_u8_def Let_def)
  using scale_le3_eq by blast

lemma construct_modsib_to_u8_imply_scale: " \<not> 3 < scale \<Longrightarrow>
  construct_modsib_to_u8 scale (u8_of_ireg index_reg) (u8_of_ireg base_reg) = v \<Longrightarrow>
    unsigned_bitfield_extract_u8 6 2 v = scale"
  using construct_modsib_to_u8_imply_scale_simp by blast

lemma bit_n_ge: "bit v n \<Longrightarrow> (v::u32) \<ge> 2^n"
  apply (simp only: bit_iff_odd)
  by (metis div_word_less dvd_0_right verit_comp_simplify1(3))

lemma bit_n_plus_ge: "bit v (n+m) \<Longrightarrow> (v::u32) \<ge> 2^n"
  apply (simp only: bit_iff_odd)
  by (metis (no_types, lifting) div_0 div_exp_eq div_word_less even_zero verit_comp_simplify1(3))

lemma bit_n_plus_lt: "(v::u32) < 2^n \<Longrightarrow> bit v (n+m) = False" using bit_n_plus_ge
  using verit_comp_simplify1(3) by blast

lemma bit_n_plus_le: "(v::u32) \<le> 2^n - 1 \<Longrightarrow> bit v (n+m) = False" using bit_n_plus_lt
  by (meson bit_n_plus_ge exp_add_not_zero_imp_left exp_eq_0_imp_not_bit one_neq_zero
      order_trans sub_wrap word_less_1)

lemma word_not_set_inverse:"(ofs::('a::len) word) \<le> 2^n-1 \<longleftrightarrow> - (2^n) \<le> (not ofs)"
  apply (induction n arbitrary: ofs)
  subgoal for ofs
    by (simp add: not_eq_complement word_order.extremum_unique) 
  subgoal for n1 ofs
    by (metis (no_types, opaque_lifting) add.inverse_inverse max_word_max minus_diff_commute minus_eq_not_minus_1 not_eq_complement
        word_le_minus_mono)
  done
 
lemma bit_n_plus_le_7: "(v::u32) \<le> 127 \<Longrightarrow> bit v (7+m) = False"
  using bit_n_plus_le [of v 7 m] by simp

lemma u32_le_127_ge_7_False: "(ofs::u32) \<le> 127 \<Longrightarrow>
    bit ofs (Suc (Suc (Suc (Suc (Suc (Suc (Suc n))))))) = False"
  apply (simp only: Suc7_eq_add_7)
  using bit_n_plus_le_7 [of ofs n] by simp

lemma len_word:
  "m < LENGTH ('a) \<Longrightarrow> bit (k::'a::len word) m \<longleftrightarrow> \<not>(bit (not k) m)"
  by (simp add: bit_not_iff)
 
lemma bit_n_plus_gt: 
  assumes a0:"m + n < 32" and a1:"-(2^m) \<le> (v::u32)" shows "bit v (m + n) = True"
proof-
  have v0:"m + n < LENGTH(32)" using a0 by auto
  
  have u:"\<forall>v \<le> ((2::u32)^m)-1. bit v (m + n) = False"
    by (simp add: bit_n_plus_le)
  then obtain v' where "bit v' (m + n) = False" and "v'\<le>((2::u32)^m)-1"
    by auto
  then have "not v' \<ge> -((2::u32)^m)" and "bit v' (m + n) = False"
    by (auto simp add: word_not_set_inverse)
  then show ?thesis using len_word[OF v0, of v']
    by (metis a1 bit.double_compl len_word u v0 word_not_set_inverse) 
qed
  
declare [[show_types]]
lemma u32_ge_minus_128_ge_7_True: "n < 25 \<Longrightarrow> -128 \<le> (ofs::u32) \<Longrightarrow>
  bit ofs (Suc (Suc (Suc (Suc (Suc (Suc (Suc n))))))) = True"
  apply (simp only: Suc7_eq_add_7)
  using bit_n_plus_gt by auto
 
lemma scast_un_aa:
   assumes a0:"LENGTH('a) = m" and a1:"LENGTH('b) = n" and a2:"m \<le> n"
 shows "\<forall>k. k \<le> m - 1 \<longrightarrow> bit ((scast (ofs::('b::len word)))::'a::len word) k = bit ofs k"
  using a0 a1 a2 bit_ucast_iff down_cast_same is_down.rep_eq by fastforce
  

lemma scast_un_bb:
   assumes a0:"LENGTH('a) = m" and a1:"LENGTH('b) = n" and a2:"m \<le> n" and
    a3: "\<forall>k. k \<le> m - 1 \<longrightarrow> bit ((v::'a::len word)) k = bit (ofs::('b::len word)) k" and
    a4:"v\<le>0" and a5:"\<forall>k. k \<ge>  m - 1 \<and> k \<le> n - 1 \<longrightarrow> (bit ofs k)"
  shows "(scast v)  = ofs"
  using a0 a2 a3 a4 a5 bit_last_iff by auto

lemma scast_u32_scast_u8_eq_simp: "ofs \<le> 127 \<or> - 128 \<le> ofs \<Longrightarrow>
  (v::u8) = scast (ofs::u32) \<Longrightarrow> (scast v) = ofs"
  apply simp                   
  apply (simp only: scast_eq)

  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
     apply (metis BitM.simps(1) BitM.simps(2) BitM.simps(3) 
           eval_nat_numeral(3) min_def numeral_3_eq_3 numeral_nat(2) u32_le_127_ge_7_False)
    apply (metis bit_n_plus_le_7 min.absorb2 nat_le_linear 
           ordered_cancel_comm_monoid_diff_class.add_diff_inverse)

  subgoal for n
    apply (drule_tac x="n" in spec)
    apply (cases n, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        subgoal for n3 apply (cases n3, simp_all)
          subgoal for n4 apply (cases n4, simp_all)
            subgoal for n5 apply (cases n5, simp_all)
              subgoal for n6 apply (cases n6, simp_all add: u32_ge_minus_128_ge_7_True)
                done
              done
            done
          done
        done
      done
    done

  subgoal for n
    apply (drule_tac x="n" in spec)
    apply (cases n, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        subgoal for n3 apply (cases n3, simp_all)
          subgoal for n4 apply (cases n4, simp_all)
            subgoal for n5 apply (cases n5, simp_all)
              subgoal for n6 apply (cases n6, simp_all add: u32_ge_minus_128_ge_7_True)
                done
              done
            done
          done
        done
      done
    done
done
  
lemma scast_u32_scast_u8_eq: "ofs \<le> 127 \<or> - 128 \<le> ofs \<Longrightarrow>
  scast (ofs::u32) = (v::u8) \<Longrightarrow> (scast v) = ofs"
  using scast_u32_scast_u8_eq_simp by blast

end