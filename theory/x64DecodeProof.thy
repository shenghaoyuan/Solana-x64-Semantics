theory x64DecodeProof
imports
  Main
  rBPFCommType
  x64Assembler x64Disassembler BitsOpMore BitsOpMore2 BitsOpMore3 BitsOpMore4
  x64DecodeProofAux
begin
(* It may take more than two hour to run this proof *)

named_theorems rex_simp

lemma construct_rex_to_u8_min [rex_simp]:"64 \<le> construct_rex_to_u8 w r x b"
  using construct_rex_to_u8_def bitfield_insert_u8_def Let_def
  by (cases w; cases r; cases x; cases b; simp)

lemma construct_rex_to_u8_max [rex_simp]:"construct_rex_to_u8 w r x b \<le> 79"
  using construct_rex_to_u8_def bitfield_insert_u8_def Let_def
  by (cases w; cases r; cases x; cases b; simp)

lemma construct_rex_to_u8_src [rex_simp]: "construct_rex_to_u8 b0 (and (u8_of_ireg src) (8::8 word) \<noteq> 0) b1 b2 = (64::8 word) \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (u8_of_ireg src)) 0) =
    Some src"
  apply (simp only: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (simp add: and.left_commute and.commute and.assoc and.assoc[symmetric]) (**TODO: here could we find a way to solve it automatically, NP hard? *)
  apply (simp add: bit.conj_disj_distrib)
  apply (simp add: and.assoc[symmetric])
  apply (simp add: and.commute [of _ "(- (3::8 word))"])
  apply (simp add: and.assoc[symmetric])
  apply (cases b0; cases b1; cases b2; cases src; simp)
  done

lemma construct_rex_to_u8_and_1_src [rex_simp]: "
    ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (u8_of_ireg src)) (u8_of_bool (and (u8_of_ireg src) (8::8 word) \<noteq> 0))) =
    Some src"
  apply (simp only: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (cases src; simp)
  done

lemma construct_rex_to_u8_dst [rex_simp]: "construct_rex_to_u8 b0 b1 b2 (and (u8_of_ireg dst) (8::8 word) \<noteq> 0) = (64::8 word) \<Longrightarrow>
    construct_modsib_to_u8 s1 s2 (u8_of_ireg dst) = v1 \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) v1) 0) =
    Some dst"
  apply (drule sym [of _ v1])
  apply (simp only: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def unsigned_bitfield_extract_u8_def)
  apply (simp add: bit_simp)
  apply (cases b0; cases b1; cases b2; cases dst; simp)
  done

lemma construct_rex_to_u8_neq_195 [rex_simp]: "
  construct_rex_to_u8 b0 b1 b2 b3 = v \<Longrightarrow>
    v \<noteq> 195"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (cases b0; cases b1; cases b2; cases b3; simp)
  done

lemma construct_rex_to_u8_neq_153 [rex_simp]: "
  construct_rex_to_u8 b0 b1 b2 b3 = v \<Longrightarrow>
    v \<noteq> 153"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (cases b0; cases b1; cases b2; cases b3; simp)
  done

lemma construct_rex_to_u8_neq_144 [rex_simp]: "
  construct_rex_to_u8 b0 b1 b2 b3 = v \<Longrightarrow>
    v \<noteq> 144"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (cases b0; cases b1; cases b2; cases b3; simp)
  done

lemma construct_rex_to_u8_neq_102 [rex_simp]: "
  construct_rex_to_u8 b0 b1 b2 b3 = v \<Longrightarrow>
    v \<noteq> 102"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (cases b0; cases b1; cases b2; cases b3; simp)
  done

lemma construct_rex_to_u8_neq_15 [rex_simp]: "
  construct_rex_to_u8 b0 b1 b2 b3 = v \<Longrightarrow>
    v \<noteq> 15"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (cases b0; cases b1; cases b2; cases b3; simp)
  done

lemma construct_rex_to_u8_neq_11 [rex_simp]: "
  construct_rex_to_u8 b0 b1 b2 b3 = v \<Longrightarrow>
    and (31::8 word) (v >> (3::nat)) \<noteq> 11"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (cases b0; cases b3; simp)
  done

lemma construct_rex_to_u8_neq_10 [rex_simp]: "
  construct_rex_to_u8 b0 b1 b2 b3 = v \<Longrightarrow>
    and (31::8 word) (v >> (3::nat)) \<noteq> 10"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (cases b0; cases b3; simp)
  done

lemma construct_rex_to_u8_neq_64_neq_0 [rex_simp]: "
  v \<noteq> (64::8 word) \<Longrightarrow>
  construct_rex_to_u8 b0 b1 b2 b3 = v \<Longrightarrow>
    and (15::8 word) v \<noteq> 0"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (cases b0; cases b1; cases b2; cases b3; simp)
  done

lemma construct_rex_to_u8_b0_neq_0 [rex_simp]: "
  construct_rex_to_u8 True b1 b2 b3 = v \<Longrightarrow>
    and (15::8 word) v \<noteq> 0"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (cases b1; cases b2; cases b3; simp)
  done

lemma construct_rex_to_u8_b1_neq_0 [rex_simp]: "
  construct_rex_to_u8 b0 True b2 b3 = v \<Longrightarrow>
    and (15::8 word) v \<noteq> 0"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (cases b0; cases b2; cases b3; simp)
  done

lemma construct_rex_to_u8_b2_neq_0 [rex_simp]: "
  construct_rex_to_u8 b0 b1 True b3 = v \<Longrightarrow>
    and (15::8 word) v \<noteq> 0"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (cases b0; cases b1; cases b3; simp)
  done

lemma construct_rex_to_u8_b3_neq_0 [rex_simp]: "
  construct_rex_to_u8 b0 b1 b2 True = v \<Longrightarrow>
    and (15::8 word) v \<noteq> 0"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (cases b0; cases b1; cases b2; simp)
  done

lemma construct_rex_to_u8_eq_4 [rex_simp]: "
  construct_rex_to_u8 b0 b1 b2 b3 = v \<Longrightarrow>
  and (15::8 word) (v >> (4::nat)) = 4"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  done

lemma construct_rex_to_u8_eq_bit_3 [rex_simp]: "
  construct_rex_to_u8 b0 b1 b2 b3 = v \<Longrightarrow>
  bit v 3 = b0"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (cases b0; cases b1; cases b2; cases b3; simp)
  done

lemma construct_rex_to_u8_eq_bit_2 [rex_simp]: "
  construct_rex_to_u8 b0 b1 b2 b3 = v \<Longrightarrow>
  bit v 2 = b1"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (cases b0; cases b1; cases b2; cases b3; simp)
  done

lemma construct_rex_to_u8_eq_bit_1 [rex_simp]: "
  construct_rex_to_u8 b0 b1 b2 b3 = v \<Longrightarrow>
  bit v 1 = b2"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (cases b0; cases b1; cases b2; cases b3; simp)
  done

lemma construct_rex_to_u8_eq_bit_0 [rex_simp]: "
  construct_rex_to_u8 b0 b1 b2 b3 = v \<Longrightarrow>
  bit v 0 = b3"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (cases b0; cases b1; cases b2; cases b3; simp)
  done

lemma construct_rex_to_u8_eq_bit_1_neg [rex_simp]: "
  construct_rex_to_u8 b0 b1 False b3 = v \<Longrightarrow>
  \<not> bit v (Suc 0)"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (cases b0; cases b1; cases b3; simp)
  done


lemma construct_rex_to_u8_eq_and_1 [rex_simp]: "
  construct_rex_to_u8 b0 b1 b2 b3 = v \<Longrightarrow>
  and 1 v = u8_of_bool b3"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def u8_of_bool_def)
  apply (cases b0; cases b1; cases b2; cases b3; simp)
  done

lemma construct_rex_to_u8_eq_and_1_shr_1 [rex_simp]: "
  construct_rex_to_u8 b0 b1 b2 b3 = v \<Longrightarrow>
  and 1 (v>>1) = u8_of_bool b2"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def u8_of_bool_def)
  apply (cases b0; cases b1; cases b2; cases b3; simp)
  done

lemma construct_rex_to_u8_eq_and_1_shr_2 [rex_simp]: "
  construct_rex_to_u8 b0 b1 b2 b3 = v \<Longrightarrow>
  and 1 (v>>2) = u8_of_bool b1"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def u8_of_bool_def)
  apply (cases b0; cases b1; cases b2; cases b3; simp)
  done

lemma construct_rex_to_u8_eq_and_1_shr_3 [rex_simp]: "
  construct_rex_to_u8 b0 b1 b2 b3 = v \<Longrightarrow>
  and 1 (v>>3) = u8_of_bool b0"
  apply (drule sym [of _ v])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def u8_of_bool_def)
  apply (cases b0; cases b1; cases b2; cases b3; simp)
  done


(** bit insert related *)
lemma bitfield_insert_u8_184_neq_15 [rex_simp]: "
  bitfield_insert_u8 0 (3::nat) (184::8 word) (u8_of_ireg dst) = v1 \<Longrightarrow>
  v1 \<noteq> 15"
  using bitfield_insert_u8_def Let_def
  by (cases dst; simp)

lemma bitfield_insert_u8_184_neq_104 [rex_simp]: "
  bitfield_insert_u8 0 (3::nat) (184::8 word) (u8_of_ireg dst) = v1 \<Longrightarrow>
  v1 \<noteq> 104"
  using bitfield_insert_u8_def Let_def
  by (cases dst; simp)

lemma bitfield_insert_u8_184_neq_153 [rex_simp]: "
  bitfield_insert_u8 0 (3::nat) (184::8 word) (u8_of_ireg dst) = v1 \<Longrightarrow>
  v1 \<noteq> 153"
  using bitfield_insert_u8_def Let_def
  by (cases dst; simp)

lemma bitfield_insert_u8_184_eq_23 [rex_simp]: "
  bitfield_insert_u8 0 (3::nat) (184::8 word) (u8_of_ireg dst) = v1 \<Longrightarrow>
  and (31::8 word) (v1 >> (3::nat)) = 23"
  using bitfield_insert_u8_def Let_def
  by (cases dst; simp)

lemma bitfield_insert_u8_dst [rex_simp]: "
  bitfield_insert_u8 0 3 184 (u8_of_ireg dst) = v \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) v) (u8_of_bool (and (u8_of_ireg dst) (8::8 word) \<noteq> 0))) =
    Some dst"
  apply (drule sym [of _ v])
  apply (simp only: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (cases dst; simp)
  done

lemma bitfield_insert_u8_and_15_neq_8 [rex_simp]: "
  bitfield_insert_u8 0 (4::nat) (64::8 word) (u8_of_cond test) = v \<Longrightarrow>
    and (15::8 word) (v >> (4::nat)) \<noteq> 8"
  apply (drule sym [of _ v])
  apply (simp add: bitfield_insert_u8_def)
  done

lemma bitfield_insert_u8_and_15_neq_25 [rex_simp]: "
  bitfield_insert_u8 0 (4::nat) (64::8 word) (u8_of_cond test) = v \<Longrightarrow>
    and (31::8 word) (v >> (3::nat)) \<noteq> 25"
  apply (drule sym [of _ v])
  apply (simp add: bitfield_insert_u8_def)
  apply (cases test; simp)
  done

lemma bitfield_insert_u8_neq_49 [rex_simp]: "
  bitfield_insert_u8 0 (4::nat) (64::8 word) (u8_of_cond test) = v \<Longrightarrow>
    v \<noteq> 49"
  apply (drule sym [of _ v])
  apply (simp add: bitfield_insert_u8_def)
  apply (cases test; simp)
  done

lemma bitfield_insert_u8_and_15_eq_4 [rex_simp]: "
  bitfield_insert_u8 0 (4::nat) (64::8 word) (u8_of_cond test) = v \<Longrightarrow>
    and (15::8 word) (v >> (4::nat)) = 4"
  apply (drule sym [of _ v])
  apply (simp add: bitfield_insert_u8_def)
  done


lemma bitfield_insert_u8_and_15_eq_test [rex_simp]: "
  bitfield_insert_u8 0 (4::nat) (64::8 word) (u8_of_cond test) = v \<Longrightarrow>
    cond_of_u8 (and (15::8 word) v) = Some test"
  apply (drule sym [of _ v])
  apply (cases test; simp add: bitfield_insert_u8_def cond_of_u8_def)
  done

lemma bitfield_insert_u8_200_and_15_neq_8 [rex_simp]: "
  bitfield_insert_u8 0 3 (200::8 word) (u8_of_ireg dst) = v \<Longrightarrow>
    and (15::8 word) (v >> (4::nat)) \<noteq> 8"
  apply (drule sym [of _ v])
  apply (cases dst; simp add: bitfield_insert_u8_def cond_of_u8_def)
  done

lemma bitfield_insert_u8_200_and_15_neq_4 [rex_simp]: "
  bitfield_insert_u8 0 3 (200::8 word) (u8_of_ireg dst) = v \<Longrightarrow>
    and (15::8 word) (v >> (4::nat)) \<noteq> 4"
  apply (drule sym [of _ v])
  apply (cases dst; simp add: bitfield_insert_u8_def cond_of_u8_def)
  done

lemma bitfield_insert_u8_200_and_15_neq_49 [rex_simp]: "
  bitfield_insert_u8 0 3 (200::8 word) (u8_of_ireg dst) = v \<Longrightarrow>
    v \<noteq> 49"
  apply (drule sym [of _ v])
  apply (cases dst; simp add: bitfield_insert_u8_def cond_of_u8_def)
  done

lemma bitfield_insert_u8_200_and_31_eq_25 [rex_simp]: "
  bitfield_insert_u8 0 3 (200::8 word) (u8_of_ireg dst) = v \<Longrightarrow>
    and (31::8 word) (v >> (3::nat)) = 25"
  apply (drule sym [of _ v])
  apply (cases dst; simp add: bitfield_insert_u8_def cond_of_u8_def)
  done

lemma bitfield_insert_u8_80_neq_15 [rex_simp]: "
  bitfield_insert_u8 0 3 (80::8 word) (u8_of_ireg dst) = v \<Longrightarrow>
    v \<noteq> 15"
  apply (drule sym [of _ v])
  apply (cases dst; simp add: bitfield_insert_u8_def cond_of_u8_def)
  done

lemma bitfield_insert_u8_80_neq_153 [rex_simp]: "
  bitfield_insert_u8 0 3 (80::8 word) (u8_of_ireg dst) = v \<Longrightarrow>
    v \<noteq> 153"
  apply (drule sym [of _ v])
  apply (cases dst; simp add: bitfield_insert_u8_def cond_of_u8_def)
  done

lemma bitfield_insert_u8_80_neq_104 [rex_simp]: "
  bitfield_insert_u8 0 3 (80::8 word) (u8_of_ireg dst) = v \<Longrightarrow>
    v \<noteq> 104"
  apply (drule sym [of _ v])
  apply (cases dst; simp add: bitfield_insert_u8_def cond_of_u8_def)
  done

lemma bitfield_insert_u8_80_and_31_neq_23 [rex_simp]: "
  bitfield_insert_u8 0 3 (80::8 word) (u8_of_ireg dst) = v \<Longrightarrow>
    and (31::8 word) (v >> (3::nat)) \<noteq> 23"
  apply (drule sym [of _ v])
  apply (cases dst; simp add: bitfield_insert_u8_def cond_of_u8_def)
  done

lemma bitfield_insert_u8_80_and_31_neq_11 [rex_simp]: "
  bitfield_insert_u8 0 3 (80::8 word) (u8_of_ireg dst) = v \<Longrightarrow>
    and (31::8 word) (v >> (3::nat)) \<noteq> 11"
  apply (drule sym [of _ v])
  apply (cases dst; simp add: bitfield_insert_u8_def cond_of_u8_def)
  done

lemma bitfield_insert_u8_80_and_31_eq_10 [rex_simp]: "
  bitfield_insert_u8 0 3 (80::8 word) (u8_of_ireg dst) = v \<Longrightarrow>
    and (31::8 word) (v >> (3::nat)) = 10"
  apply (drule sym [of _ v])
  apply (cases dst; simp add: bitfield_insert_u8_def cond_of_u8_def)
  done

lemma bitfield_insert_u8_128_and_15_neq_25 [rex_simp]: "
  bitfield_insert_u8 (0::nat) (4::nat) (128::8 word) (u8_of_cond test) = v \<Longrightarrow>
   and (31::8 word) (v >> (3::nat)) \<noteq> (25::8 word)"
  apply (drule sym [of _ v])
  apply (cases test; simp add: bitfield_insert_u8_def cond_of_u8_def)
  done

lemma bitfield_insert_u8_128_neq_49 [rex_simp]: "
  bitfield_insert_u8 (0::nat) (4::nat) (128::8 word) (u8_of_cond test) = v \<Longrightarrow>
   v \<noteq> 49"
  apply (drule sym [of _ v])
  apply (cases test; simp add: bitfield_insert_u8_def cond_of_u8_def)
  done

lemma bitfield_insert_u8_128_and_15_neq_8 [rex_simp]: "
  bitfield_insert_u8 (0::nat) (4::nat) (128::8 word) (u8_of_cond test) = v \<Longrightarrow>
   and (15::8 word) (v >> (4::nat)) = 8"
  apply (drule sym [of _ v])
  apply (cases test; simp add: bitfield_insert_u8_def cond_of_u8_def)
  done

lemma bitfield_insert_u8_128_test [rex_simp]: "
  bitfield_insert_u8 (0::nat) (4::nat) (128::8 word) (u8_of_cond test) = v \<Longrightarrow>
   cond_of_u8 (and (15::8 word) v) = Some test"
  apply (drule sym [of _ v])
  apply (cases test; simp add: bitfield_insert_u8_def cond_of_u8_def)
  done

lemma bitfield_insert_u8_80_dst [rex_simp]: "
  bitfield_insert_u8 0 3 (80::8 word) (u8_of_ireg dst) = v \<Longrightarrow>
  ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) v) (u8_of_bool (and (u8_of_ireg dst) (8::8 word) \<noteq> (0::8 word)))) =
     Some dst"
  apply (drule sym [of _ v])
  apply (simp only: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (simp add: bit.conj_disj_distrib)
  apply (simp add: and.left_commute and.commute and.assoc and.assoc[symmetric]) (**TODO: here could we find a way to solve it automatically, NP hard? *)
  apply (cases dst; simp)
  done

lemma bitfield_insert_u8_200_src [rex_simp]: "
  construct_rex_to_u8 False False False (and (u8_of_ireg dst) (8::8 word) \<noteq> 0) = (64::8 word) \<Longrightarrow>
    bitfield_insert_u8 0 (3::nat) (200::8 word) (u8_of_ireg dst) = v \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) v) 0) = Some dst"
  apply (drule sym [of _ v])
  apply (simp only: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (simp add: bit.conj_disj_distrib)
  apply (simp add: and.left_commute and.commute and.assoc and.assoc[symmetric]) (**TODO: here could we find a way to solve it automatically, NP hard? *)
  apply (cases dst; simp)
  done

lemma bitfield_insert_u8_200_dst [rex_simp]: "
    bitfield_insert_u8 0 (3::nat) (200::8 word) (u8_of_ireg dst) = v \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) v) (u8_of_bool (and (u8_of_ireg dst) (8::8 word) \<noteq> 0))) =
     Some dst"
  apply (drule sym [of _ v])
  apply (simp only: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (simp add: bit.conj_disj_distrib)
  apply (simp add: and.left_commute and.commute and.assoc and.assoc[symmetric]) (**TODO: here could we find a way to solve it automatically, NP hard? *)
  apply (cases dst; simp)
  done

lemma construct_rex_to_u8_reg [rex_simp]: "
  construct_rex_to_u8 b0 b1 (and (u8_of_ireg r) (8::8 word) \<noteq> 0) b3 = v \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (u8_of_ireg r)) (and 1 (v >> Suc 0))) =
    Some r"
  apply (drule sym [of _ v])
  apply (simp only: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (simp add: bit.conj_disj_distrib)
  apply (simp add: and.left_commute and.commute and.assoc and.assoc[symmetric]) (**TODO: here could we find a way to solve it automatically, NP hard? *)
  apply (cases b0; cases b1; cases b3; cases r; simp)
  done

named_theorems modsib_simp

lemma construct_modsib_to_u8_op1 [modsib_simp]: "
  \<not> (3::8 word) < op1 \<Longrightarrow>
  construct_modsib_to_u8 op1 op2 op3 = v \<Longrightarrow>
    and (3::8 word) (v >> (6::nat)) = op1"
  apply (drule sym [of _ v])
  apply (simp only: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply (erule subst [of v])
  using scale_le3_eq by blast

lemma construct_modsib_to_u8_and_7_eq_4 [modsib_simp]: "
  construct_modsib_to_u8 x y (4::8 word) = v1 \<Longrightarrow>
    and (7::8 word) v1 = 4"
  apply (drule sym [of _ v1])
  apply (simp only: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def unsigned_bitfield_extract_u8_def)
  apply (simp add: bit_simp)
  done

lemma construct_modsib_to_u8_and_1_dst [modsib_simp]: "
  construct_modsib_to_u8 s1 s2 (u8_of_ireg dst) = v1 \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) v1) (u8_of_bool (and (u8_of_ireg dst) (8::8 word) \<noteq> 0))) =
    Some dst"
  apply (drule sym [of _ v1])
  apply (simp only: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp add: construct_rex_to_u8_def
      construct_modsib_to_u8_def bitfield_insert_u8_def unsigned_bitfield_extract_u8_def)
  apply (simp add: bit_simp)
  apply (simp add: and.left_commute and.commute and.assoc and.assoc[symmetric]) (**TODO: here could we find a way to solve it automatically, NP hard? *)
  apply (simp add: bit.conj_disj_distrib)
  apply (simp add: and.assoc[symmetric])
  apply (cases dst; simp)
  done

lemma construct_modsib_to_u8_0 [modsib_simp]: "
  construct_modsib_to_u8 0 x y = v1 \<Longrightarrow>
    and (3::8 word) (v1 >> (6::nat)) = 0"
  apply (drule sym [of _ v1])
  apply (simp add: construct_modsib_to_u8_def bitfield_insert_u8_def)
  done

lemma construct_modsib_to_u8_1 [modsib_simp]: "
  construct_modsib_to_u8 1 x y = v1 \<Longrightarrow>
    and (3::8 word) (v1 >> (6::nat)) = 1"
  apply (drule sym [of _ v1])
  apply (simp add: construct_modsib_to_u8_def bitfield_insert_u8_def)
  done

lemma construct_modsib_to_u8_2 [modsib_simp]: "
  construct_modsib_to_u8 2 x y = v1 \<Longrightarrow>
    and (3::8 word) (v1 >> (6::nat)) = 2"
  apply (drule sym [of _ v1])
  apply (simp add: construct_modsib_to_u8_def bitfield_insert_u8_def)
  done

lemma construct_modsib_to_u8_3 [modsib_simp]: "
  construct_modsib_to_u8 3 x y = v1 \<Longrightarrow>
    and (3::8 word) (v1 >> (6::nat)) = 3"
  apply (drule sym [of _ v1])
  apply (simp add: construct_modsib_to_u8_def bitfield_insert_u8_def)
  done

lemma construct_modsib_to_u8_and_7 [modsib_simp]: "construct_modsib_to_u8 a b c = v1 \<Longrightarrow>
  and (7::8 word) (v1 >> (3::nat)) = and 7 b"
  apply (drule sym [of _ v1])
  apply (simp add: construct_modsib_to_u8_def bitfield_insert_u8_def unsigned_bitfield_extract_u8_def)
  apply (simp add: bit_simp)
  apply (simp add: and.left_commute and.commute and.assoc and.assoc[symmetric]) (**TODO: here could we find a way to solve it automatically, NP hard? *)

  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for n apply (cases n, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        done
      done
    done
  done

lemma construct_modsib_to_u8_and_7_neq [modsib_simp]: "
  and (u8_of_ireg r) (7::8 word) \<noteq> z \<Longrightarrow>
  construct_modsib_to_u8 x y (u8_of_ireg r) = v1 \<Longrightarrow>
    and 7 v1 \<noteq> z"
  apply (drule sym [of _ v1])
  apply (simp add: construct_modsib_to_u8_def bitfield_insert_u8_def unsigned_bitfield_extract_u8_def)
  apply (simp add: bit.conj_disj_distrib)
  apply (simp add: and.left_commute and.assoc[symmetric])
  apply (simp add: and.commute [of _ "(- (57::8 word))"])
  apply (simp add: and.assoc[symmetric])
  apply (simp add: bit.conj_disj_distrib)
  apply (simp add: and.assoc[symmetric])
  apply (simp add: and.commute [of _ "(- (193::8 word))"])
  apply (simp add: and.assoc[symmetric])
  apply (simp add: and.commute)
  done

declare if_split_asm [split]
(*
declare Let_def Suc3_eq_add_3
  Suc4_eq_add_4 Suc5_eq_add_5 Suc6_eq_add_6 Suc7_eq_add_7 Suc8_eq_add_8 Suc9_eq_add_9 Suc10_eq_add_10
  [simp]

TODO:  if I add this many-declaration, 
the simp can not simple most of those defs
 *)
declare Let_def [simp]
declare unsigned_bitfield_extract_u8_def [simp]
declare x64_decode_op_not_rex_def [simp]
declare x64_decode_op_0x66_def [simp]
declare x64_decode_op_0x0f_def [simp]
declare x64_decode_op_0x81_def [simp]

lemma x64_encode_decode_consistency:
  "list_in_list l_bin pc l \<Longrightarrow> Some l_bin = x64_encode ins \<Longrightarrow>  x64_decode pc l = Some (length l_bin, ins)"

  apply (cases ins; simp)
  subgoal for dst src
  \<comment> \<open> Pmovl_rr \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def modsib_simp rex_simp)
      done
    done

  subgoal for dst src
  \<comment> \<open> Pmovl_rr \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v2 v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp)
      done
    done

  subgoal for dst src
  \<comment> \<open> Pmovq_rr \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v2 v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp)
      done
    done

  subgoal for dst sr
  \<comment> \<open> Pmovl_ri + rex = 0x40 \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "Suc (Suc pc)" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "Suc (Suc pc)" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "Suc (Suc pc)" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "Suc (Suc pc)" _]
      apply (simp add: nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "(Suc (Suc pc))" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done

  subgoal for dst src
  \<comment> \<open> Pmovl_ri + rex <> 0x40 \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v2 v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "(Suc (Suc (Suc pc)))" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "(Suc (Suc (Suc pc)))" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "(Suc (Suc (Suc pc)))" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "(Suc (Suc (Suc pc)))" _]
      using add.commute [of _ pc]
      apply (simp add: nat_simp)
      using list_in_list_u8_list_of_u32_simp [of _ "(Suc (Suc (Suc pc)))" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done

  subgoal for dst imm
 \<comment> \<open> Pmovq_ri\<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp)
      using list_in_list_u8_list_of_u64_simp_0 [of _ "Suc (Suc pc)" _]
      using list_in_list_u8_list_of_u64_simp_1 [of _ "Suc (Suc pc)" _]
      using list_in_list_u8_list_of_u64_simp_2 [of _ "Suc (Suc pc)" _]
      using list_in_list_u8_list_of_u64_simp_3 [of _ "Suc (Suc pc)" _]
      using list_in_list_u8_list_of_u64_simp_4 [of _ "Suc (Suc pc)" _]
      using list_in_list_u8_list_of_u64_simp_5 [of _ "Suc (Suc pc)" _]
      using list_in_list_u8_list_of_u64_simp_6 [of _ "Suc (Suc pc)" _]
      using list_in_list_u8_list_of_u64_simp_7 [of _ "Suc (Suc pc)" _]
      using add.commute [of _ pc]
      apply (simp add: modsib_simp rex_simp nat_simp)
      using list_in_list_u8_list_of_u64_simp [of _ "(Suc (Suc pc))" _]
      using length_u8_list_of_u64_eq_8
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done

  subgoal for dst addr chunk
  \<comment> \<open> Pmov_rm \<close>
    apply (cases addr, simp)
    subgoal for base index2 ofs
      apply (cases base; simp)
      subgoal for base_reg
        apply (cases index2; simp) (** TODO: why the previous declaration of Let_def doesn't work? *)
        subgoal \<comment> \<open> ofs < u8 /\ index2 = None  /\ not rex \<close>
          apply (cases chunk; simp)
          apply (erule conjE)+
          apply ((erule case_optionE), simp)+
          subgoal for v2 v1 v0
            apply (simp add: x64_decode_def scast_u32_scast_u8_eq modsib_simp rex_simp)
            done
          done

        subgoal \<comment> \<open> ofs < u8 /\ index2 = None  /\ has rex \<close>
          using scast_u32_scast_u8_eq
          apply (cases chunk; simp)
          subgoal \<comment> \<open> index2 = None  /\ has rex  /\ M32 \<close>
            apply (erule conjE)+
            apply ((erule case_optionE), simp)+
            subgoal for v3 v2 v1 v0
              apply (simp add: x64_decode_def modsib_simp rex_simp nat_simp add.commute)
              done
            done
          subgoal \<comment> \<open> index2 = None  /\ has rex  /\ M64 \<close>
            apply (erule conjE)+
            apply ((erule case_optionE), simp)+
            subgoal for v3 v2 v1 v0
              apply (simp add: x64_decode_def modsib_simp rex_simp nat_simp add.commute)
              done
            done
          done

        subgoal \<comment> \<open> ofs > u8 /\ index2 = None  /\ not rex \<close>
          apply (cases chunk; simp)
            apply (erule conjE)+
            apply ((erule case_optionE), simp)+
            subgoal for v1 v0
              apply (simp add: x64_decode_def modsib_simp rex_simp nat_simp add.commute)
              using list_in_list_u8_list_of_u32_simp_0 [of _ "(Suc (Suc pc))" _]
              using list_in_list_u8_list_of_u32_simp_1 [of _ "(Suc (Suc pc))" _]
              using list_in_list_u8_list_of_u32_simp_2 [of _ "(Suc (Suc pc))" _]
              using list_in_list_u8_list_of_u32_simp_3 [of _ "(Suc (Suc pc))" _]
              using add.commute [of _ pc]
              apply (simp add: nat_simp)
              using list_in_list_u8_list_of_u32_simp [of _ "(Suc (Suc pc))" _]
              using length_u8_list_of_u32_eq_4
              apply (simp add: modsib_simp rex_simp nat_simp add.commute)
              done
            done

          subgoal \<comment> \<open> ofs > u8 /\ index2 = None  /\ has rex \<close>
            apply (cases chunk; simp; (erule conjE)+; ((erule case_optionE), simp)+)
            subgoal for v2 v1 v0  \<comment> \<open> M32 \<close>
              apply (simp add: x64_decode_def modsib_simp rex_simp nat_simp add.commute)
              using list_in_list_u8_list_of_u32_simp_0 [of _ "pc + 3" _]
              using list_in_list_u8_list_of_u32_simp_1 [of _ "pc + 3" _]
              using list_in_list_u8_list_of_u32_simp_2 [of _ "pc + 3" _]
              using list_in_list_u8_list_of_u32_simp_3 [of _ "pc + 3" _]
              using add.commute [of _ pc]
              apply (simp add: nat_simp)
              using list_in_list_u8_list_of_u32_simp [of _ "pc + 3" _]
              using length_u8_list_of_u32_eq_4
              apply (simp add: modsib_simp rex_simp nat_simp add.commute)
              done
            subgoal for v2 v1 v0  \<comment> \<open> M64 \<close>
              apply (simp add: x64_decode_def modsib_simp rex_simp nat_simp add.commute)
              using list_in_list_u8_list_of_u32_simp_0 [of _ "pc + 3" _]
              using list_in_list_u8_list_of_u32_simp_1 [of _ "pc + 3" _]
              using list_in_list_u8_list_of_u32_simp_2 [of _ "pc + 3" _]
              using list_in_list_u8_list_of_u32_simp_3 [of _ "pc + 3" _]
              using add.commute [of _ pc]
              apply (simp add: nat_simp)
              using list_in_list_u8_list_of_u32_simp [of _ "pc + 3" _]
              using length_u8_list_of_u32_eq_4
              apply (simp add: modsib_simp rex_simp nat_simp add.commute)
              done
            done

          subgoal for index22\<comment> \<open> index2 = Some \<close>
            apply(cases chunk; cases index22;simp_all)
            subgoal for index_reg scale
            apply (erule conjE)+
            apply ((erule case_optionE), simp)+
            subgoal for v3 v2 v1 v0
              apply (simp add: x64_decode_def modsib_simp rex_simp nat_simp add.commute)
              using list_in_list_u8_list_of_u32_simp_0 [of _ "pc + 4" _]
              using list_in_list_u8_list_of_u32_simp_1 [of _ "pc + 4" _]
              using list_in_list_u8_list_of_u32_simp_2 [of _ "pc + 4" _]
              using list_in_list_u8_list_of_u32_simp_3 [of _ "pc + 4" _]
              using add.commute [of _ pc]
              apply (simp add: nat_simp)
              using list_in_list_u8_list_of_u32_simp [of _ "pc + 4" _]
              using length_u8_list_of_u32_eq_4
              apply (simp add: modsib_simp rex_simp nat_simp add.commute)
              done
            done
          done
        done
      done
    done

  subgoal for addr r1 chunk
    \<comment> \<open> Pmov_mr \<close> 
    apply (cases addr; simp)
    subgoal for base index2 ofs
      apply (cases base; simp)
      subgoal for base_reg
        apply (cases index2; simp)

        subgoal \<comment> \<open> ofs < u8 \<and> index2 = None \<and>  not rex \<close>
          using scast_u32_scast_u8_eq
          apply (cases chunk; simp add: x64_decode_def modsib_simp rex_simp nat_simp add.commute)
          subgoal
            apply (erule conjE)+
            apply ((erule case_optionE), simp)+
            subgoal for v2 v1 v0
              apply (simp add: modsib_simp rex_simp nat_simp add.commute)
              done
            done
          subgoal
            apply (erule conjE)+
            apply ((erule case_optionE), simp)+
            subgoal for v2 v1 v0
              apply (simp add: modsib_simp rex_simp nat_simp add.commute)
              done
            done
          subgoal
            apply (erule conjE)+
            apply ((erule case_optionE), simp)+
            subgoal for v2 v1 v0
              apply (simp add: modsib_simp rex_simp nat_simp add.commute)
              done
            done
          done
        subgoal \<comment> \<open> ofs < u8 \<and> index2 = None \<and> has rex \<close>
          using scast_u32_scast_u8_eq
          apply (cases chunk; simp add: x64_decode_def modsib_simp rex_simp nat_simp add.commute)
          subgoal
            apply (erule conjE)+
            apply ((erule case_optionE), simp)+
            subgoal for v2 v1 v0
              apply (simp add: modsib_simp rex_simp nat_simp add.commute)
              done
            done
          subgoal
            apply (erule conjE)+
            apply ((erule case_optionE), simp)+
            subgoal for v2 v1 v0
              apply (simp add: modsib_simp rex_simp nat_simp add.commute)
              done
            done
          subgoal
            apply (erule conjE)+
            apply ((erule case_optionE), simp)+
            subgoal for v2 v1 v0
              apply (simp add: modsib_simp rex_simp nat_simp add.commute)
              done
            done
          subgoal
            apply (erule conjE)+
            apply ((erule case_optionE), simp)+
            subgoal for v2 v1 v0
              apply (simp add: modsib_simp rex_simp nat_simp add.commute)
              done
            done
          done
        subgoal \<comment> \<open> ofs > u8 /\ index2 = None  /\ not rex \<close>
          apply (cases chunk; simp add: x64_decode_def modsib_simp rex_simp nat_simp add.commute)
          apply (erule conjE)+
          apply ((erule case_optionE), simp)+
          subgoal for v1 v0
            apply (simp add: modsib_simp rex_simp nat_simp add.commute)
            using list_in_list_u8_list_of_u32_simp_0 [of _ "(Suc (Suc pc))" _]
            using list_in_list_u8_list_of_u32_simp_1 [of _ "(Suc (Suc pc))" _]
            using list_in_list_u8_list_of_u32_simp_2 [of _ "(Suc (Suc pc))" _]
            using list_in_list_u8_list_of_u32_simp_3 [of _ "(Suc (Suc pc))" _]
            using add.commute [of _ pc]
            apply (simp add: nat_simp)
            using list_in_list_u8_list_of_u32_simp [of _ "(Suc (Suc pc))" _]
            using length_u8_list_of_u32_eq_4
            apply (simp add: modsib_simp rex_simp nat_simp add.commute)
            done
          done
        subgoal \<comment> \<open> ofs > u8 /\ index2 = None  /\ has rex \<close>
          apply (cases chunk; simp; (erule conjE)+; ((erule case_optionE), simp)+;
              simp add: x64_decode_def modsib_simp rex_simp nat_simp add.commute)
          subgoal for v2 v1 v0 \<comment> \<open> M32 \<close>
            using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+3" _]
            using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+3" _]
            using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+3" _]
            using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+3" _]
            using add.commute [of _ pc]
            apply (simp add: nat_simp)
            using list_in_list_u8_list_of_u32_simp [of _ "pc+3" _]
            using length_u8_list_of_u32_eq_4
            apply (simp add: modsib_simp rex_simp nat_simp add.commute)
            done
          subgoal for v2 v1 v0  \<comment> \<open> M64 \<close>
            using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+3" _]
            using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+3" _]
            using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+3" _]
            using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+3" _]
            using add.commute [of _ pc]
            apply (simp add: nat_simp)
            using list_in_list_u8_list_of_u32_simp [of _ "pc+3" _]
            using length_u8_list_of_u32_eq_4
            apply (simp add: modsib_simp rex_simp nat_simp add.commute)
            done
          done
        subgoal for index22\<comment> \<open> index2 = Some \<close>
          apply(cases chunk; cases index22; simp; (erule conjE)+; ((erule case_optionE), simp)+;
              simp add: x64_decode_def modsib_simp rex_simp nat_simp add.commute)
          subgoal for index_reg scale v3 v2 v1 v0
            using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+4" _]
            using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+4" _]
            using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+4" _]
            using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+4" _]
            using add.commute [of _ pc]
            apply (simp add: nat_simp)
            using list_in_list_u8_list_of_u32_simp [of _ "pc+4" _]
            using length_u8_list_of_u32_eq_4
            apply (simp add: modsib_simp rex_simp nat_simp add.commute)
            done
          done
        done
      done
    done

  subgoal for addr imm chunk
    \<comment> \<open> Pmov_mi \<close> 
    apply(cases chunk; simp)
    apply (cases addr, simp)
    subgoal for base index2 ofs
      apply (cases base, simp_all)
      subgoal for base_reg
        apply (cases index2; simp; (erule conjE)+; ((erule case_optionE), simp)+;
            simp add: x64_decode_def modsib_simp rex_simp nat_simp add.commute)
        subgoal for v3 v2 v1 v0
          using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+4" _]
          using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+4" _]
          using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+4" _]
          using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+4" _]
          using add.commute [of _ pc]
          apply (simp add: nat_simp)
          using list_in_list_u8_list_of_u32_simp [of _ "pc+4" _]
          using length_u8_list_of_u32_eq_4
          using scast_u32_scast_u8_eq
          apply (simp add: modsib_simp rex_simp nat_simp add.commute)
          done
        subgoal for v2 v1 v0
          apply (simp only: list_in_list_concat length_u8_list_of_u32_eq_4)
          apply (erule conjE, simp add: add.commute)
          using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+7" _]
          apply (simp add: add.commute)
          using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+7" _]
          apply (simp add: add.commute)
          using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+7" _]
          apply (simp add: add.commute)
          using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+7" _]
          apply (simp add: add.commute)
          using list_in_list_u8_list_of_u32_simp [of _ "pc+7" _]
          using length_u8_list_of_u32_eq_4
          apply (simp add: modsib_simp rex_simp nat_simp add.commute)
          using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+3" _]
          using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+3" _]
          using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+3" _]
          using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+3" _]
          apply (simp add: add.commute)
          using list_in_list_u8_list_of_u32_simp [of _ "pc+3" _]
          using length_u8_list_of_u32_eq_4
          apply (simp add: modsib_simp rex_simp nat_simp add.commute)
          done
        done
      done
    done


  subgoal for test dst src
    \<comment> \<open> Pcmovl \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v2 v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp)
      done
    done


  subgoal for test dst src
    \<comment> \<open> Pcmovl \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v3 v2 v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done


  subgoal for test dst src
    \<comment> \<open> Pcmovq \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v3 v2 v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done


  subgoal for dst src
    \<comment> \<open> Pxchgq_rr \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v2 v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst addr chunk
    \<comment> \<open> Pxchgq_rm \<close> 
    apply (cases chunk; simp_all)
    apply (cases addr, simp)
    subgoal for base index2 ofs
      apply (cases base;simp)
      subgoal for base_reg
        apply (cases index2; simp)
        subgoal for index22
          apply (cases index22, simp_all)
          subgoal for index_reg scale
            apply (erule conjE)+
            apply ((erule case_optionE), simp)+
            subgoal for v3 v2 v1 v0
              apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
              using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+4" _]
              using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+4" _]
              using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+4" _]
              using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+4" _]
              using add.commute [of _ pc]
              apply (simp add: nat_simp)
              using list_in_list_u8_list_of_u32_simp [of _ "pc+4" _]
              using length_u8_list_of_u32_eq_4
              using scast_u32_scast_u8_eq
              apply (simp add: modsib_simp rex_simp nat_simp add.commute)
              done
            done
          done
        done
      done
    done
  

  subgoal for dst src
    \<comment> \<open> Pmovsq_rr \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v2 v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal 
    \<comment> \<open> Pcdq \<close>
    apply ((erule case_optionE), simp)+
    subgoal for v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal 
    \<comment> \<open> Pcqo \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst addr
    \<comment> \<open> Pleaq \<close>
    apply (cases addr, simp)
    subgoal for base index2 ofs
      apply (cases base;simp)
      subgoal for base_reg
        apply (cases index2; simp; (erule conjE)+; ((erule case_optionE), simp)+;
            simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
        subgoal for v3 v2 v1 v0
          using scast_u32_scast_u8_eq
          apply simp
          done
        subgoal for v2 v1 v0
          using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+3" _]
          using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+3" _]
          using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+3" _]
          using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+3" _]
          apply (simp add: add.commute)
          using list_in_list_u8_list_of_u32_simp [of _ "pc+3" _]
          using length_u8_list_of_u32_eq_4
          using scast_u32_scast_u8_eq
          apply (simp add: modsib_simp rex_simp nat_simp add.commute)
          done
        done
      done
    done


  subgoal for dst
    \<comment> \<open> Pnegl \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst
    \<comment> \<open> Pnegl \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst
    \<comment> \<open> Pnegq \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst src 
    \<comment> \<open> Paddq_rr \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst src 
    \<comment> \<open> Paddl_rr \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst imm 
    \<comment> \<open> Paddl_rr \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst imm 
    \<comment> \<open> Paddl_ri \<close>  \<comment> \<open> rex = 0x40  \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+2" _]
      apply (simp add: add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+2" _]
      using length_u8_list_of_u32_eq_4
      using scast_u32_scast_u8_eq
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done

  subgoal for dst imm 
    \<comment> \<open> Paddl_ri \<close>  \<comment> \<open> rex <> 0x40  \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v2 v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+3" _]
      apply (simp add: add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+3" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done

  subgoal for dst imm 
    \<comment> \<open> Paddw_ri \<close>  \<comment> \<open> rex = 0x40  \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v2 v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u16_simp_0 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u16_simp_1 [of _ "pc+3" _]
      apply (simp add: add.commute)
      using list_in_list_u8_list_of_u16_simp [of _ "pc+3" _]
      using length_u8_list_of_u16_eq_2
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done

  subgoal for dst imm 
    \<comment> \<open> Paddw_ri \<close>  \<comment> \<open> rex <> 0x40  \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v2 v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u16_simp_0 [of _ "pc+4" _]
      using list_in_list_u8_list_of_u16_simp_1 [of _ "pc+4" _]
      apply (simp add: add.commute)
      using list_in_list_u8_list_of_u16_simp [of _ "pc+4" _]
      using length_u8_list_of_u16_eq_2
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done


  subgoal for addr imm chunk
  \<comment> \<open> Paddq_mi \<close> 
    apply (cases chunk, simp_all)
    apply (cases addr)
    subgoal for base index2 ofs
      apply simp
      apply (cases base, simp_all)
      subgoal for base_reg
        apply (cases index2, simp_all)
        subgoal for index22
          apply (cases index22, simp_all)
          subgoal for index_reg scale
          apply (erule conjE)+
          apply ((erule case_optionE), simp)+
          subgoal for v3 v2 v1 v0
            apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
            apply (simp only: list_in_list_concat length_u8_list_of_u32_eq_4)
            apply (erule conjE, simp add: add.commute)
            using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+4" _]
            using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+4" _]
            using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+4" _]
            using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+4" _]
            apply (simp add: add.commute)
            using list_in_list_u8_list_of_u32_simp [of _ "pc+4" _]
            using length_u8_list_of_u32_eq_4
            apply (simp add: modsib_simp rex_simp nat_simp add.commute)
            using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+8" _]
            using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+8" _]
            using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+8" _]
            using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+8" _]
            apply (simp add: add.commute)
            using list_in_list_u8_list_of_u32_simp [of _ "pc+8" _]
            using length_u8_list_of_u32_eq_4
            apply (simp add: modsib_simp rex_simp nat_simp add.commute)
            done
          done
        done
      done
    done
  done


  subgoal for dst src 
    \<comment> \<open> Psubl_rr \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done
  subgoal for dst src 
    \<comment> \<open> Psubl_rr \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst src 
    \<comment> \<open> Psubq_rr \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst imm 
    \<comment> \<open> Psubl_ri \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+2" _]
      apply (simp add: nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+2" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done
  subgoal for dst imm 
    \<comment> \<open> Psubl_ri \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+3" _]
      apply (simp add: nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+3" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done


  subgoal for dst 
    \<comment> \<open> Pmull_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst 
    \<comment> \<open> Pmulq_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done
  subgoal for dst 
    \<comment> \<open> Pmulq_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst 
    \<comment> \<open> Pimull_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst 
    \<comment> \<open> Pimulq_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done
  subgoal for dst 
    \<comment> \<open> Pimulq_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst 
    \<comment> \<open> Pdivl_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst 
    \<comment> \<open> Pdivq_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done
  subgoal for dst 
    \<comment> \<open> Pdivq_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst 
    \<comment> \<open> Pidivl_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done
  subgoal for dst 
    \<comment> \<open> Pidivl_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst 
    \<comment> \<open> Pidivq_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst src 
    \<comment> \<open> Pandl_rr \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done
  subgoal for dst src 
    \<comment> \<open> Pandl_rr \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst imm 
    \<comment> \<open> Pandl_ri\<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+2" _]
      apply (simp add: nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+2" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done
  subgoal for dst imm 
    \<comment> \<open> Pandl_ri\<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+3" _]
      apply (simp add: nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+3" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done

  subgoal for dst src
    \<comment> \<open> Pandq_rr \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done


  subgoal for dst src 
    \<comment> \<open> Porl_rr \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done
  subgoal for dst src 
    \<comment> \<open> Porl_rr \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done


  subgoal for dst imm 
    \<comment> \<open> Porl_ri\<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+2" _]
      apply (simp add: nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+2" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done
  subgoal for dst imm 
    \<comment> \<open> Porl_ri\<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+3" _]
      apply (simp add: nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+3" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done


  subgoal for dst src
    \<comment> \<open> Porq_rr \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst src 
    \<comment> \<open> Pxorl_rr \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst src
    \<comment> \<open> Pxorq_rr \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done
  subgoal for dst src
    \<comment> \<open> Pxorq_rr \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst imm 
    \<comment> \<open> Pxorl_ri\<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+2" _]
      apply (simp add: nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+2" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done
  subgoal for dst imm 
    \<comment> \<open> Pxorl_ri\<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+3" _]
      apply (simp add: nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+3" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done

  
  subgoal for dst imm
    \<comment> \<open> Pshll_ri \<close>  \<comment> \<open> rex = 0x40 \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done
  subgoal for dst imm
    \<comment> \<open> Pshll_ri \<close>  \<comment> \<open> rex <> 0x40 \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done


  subgoal for dst
    \<comment> \<open> Pshlq_ri \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst
  \<comment> \<open> Pshll_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done
  subgoal for dst
  \<comment> \<open> Pshll_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst
  \<comment> \<open> Pshlq_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst imm
    \<comment> \<open> Pshrl_ri \<close> \<comment> \<open> rex = 0x40 \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done
  subgoal for dst imm
    \<comment> \<open> Pshrl_ri \<close> \<comment> \<open> rex <> 0x40 \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst
    \<comment> \<open> Pshrq_ri \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done


  subgoal for dst
  \<comment> \<open> Pshrl_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done
  subgoal for dst
  \<comment> \<open> Pshrl_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst
  \<comment> \<open> Pshrq_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst imm
    \<comment> \<open> Psarl_ri \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done
  subgoal for dst imm
    \<comment> \<open> Psarl_ri \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst
  \<comment> \<open> Psarq_ri \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done
  subgoal for dst
  \<comment> \<open> Psarq_ri \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst
  \<comment> \<open> Psarl_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst
  \<comment> \<open> Psarq_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst imm
    \<comment> \<open> Prolw_ri \<close> \<comment> \<open> rex = 0x40 \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v3 v2 v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using bitfield_insert_u8_def by simp
    done
  subgoal for dst imm
    \<comment> \<open> Prolw_ri \<close> \<comment> \<open> rex <> 0x40 \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v4 v3 v2 v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using bitfield_insert_u8_def by simp
    done


  subgoal for dst
    \<comment> \<open> Pbswapl \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done
  subgoal for dst
    \<comment> \<open> Pbswapl \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst
    \<comment> \<open> Pbswapq \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v2 v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst
    \<comment> \<open> Ppushl_r \<close> 
    apply ((erule case_optionE), simp)+
    subgoal for v0
      apply (cases dst; simp add: x64_decode_def construct_rex_to_u8_def bitfield_insert_u8_def ireg_of_u8_def)
      done
    done
  subgoal for dst
    \<comment> \<open> Ppushl_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done


  subgoal for imm
    \<comment> \<open> Ppushl_i \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+2" _]
      apply (simp add: nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+2" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done


  subgoal for addr chunk 
    \<comment> \<open> Ppushq_m \<close> 
    apply (cases chunk,simp_all)
    apply (cases addr, simp_all)
    subgoal for base index2 ofs
      apply (cases base;simp)
      subgoal for base_reg
        apply (cases index2; simp)
        subgoal for index22
          apply (cases index22; simp; (erule conjE)+; ((erule case_optionE), simp)+;
              simp add: x64_decode_def modsib_simp rex_simp nat_simp add.commute)
          subgoal for index_reg scale v3 v2 v1 v0
            using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+4" _]
            using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+4" _]
            using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+4" _]
            using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+4" _]
            apply (simp add: nat_simp add.commute)
            using list_in_list_u8_list_of_u32_simp [of _ "pc+4" _]
            using length_u8_list_of_u32_eq_4
            apply (simp add: modsib_simp rex_simp nat_simp add.commute)
            done
          done
        done
      done
    done

  subgoal for dst
    \<comment> \<open> Ppopl_i \<close> 
    apply ((erule case_optionE), simp)+
    subgoal for v0
      apply (cases dst; simp add: x64_decode_def construct_rex_to_u8_def bitfield_insert_u8_def ireg_of_u8_def)
      done
    done

  subgoal for dst
    \<comment> \<open> Ppopl_i \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (cases dst; simp add: x64_decode_def construct_rex_to_u8_def bitfield_insert_u8_def ireg_of_u8_def)
      done
    done

  subgoal for dst src
    \<comment> \<open> Ptestl_rr \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst src
    \<comment> \<open> Ptestq_rr \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done
  subgoal for dst src
    \<comment> \<open> Ptestq_rr \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst imm
  \<comment> \<open> Ptestl_ri  \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+2" _]
      apply (simp add: nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+2" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done
  subgoal for dst imm
  \<comment> \<open> Ptestl_ri  \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+3" _]
      apply (simp add: nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+3" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done


  subgoal for dst imm
  \<comment> \<open> Ptestq_ri  \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+3" _]
      apply (simp add: nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+3" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done

  subgoal for dst src
    \<comment> \<open> Pcmpl_rr \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst src
    \<comment> \<open> Pcmpq_rr \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done
  subgoal for dst src
    \<comment> \<open> Pcmpq_rr \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for dst imm
  \<comment> \<open> Pcmpl_ri  \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+2" _]
      apply (simp add: nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+2" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done
  subgoal for dst imm
  \<comment> \<open> Pcmpl_ri  \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+3" _]
      apply (simp add: nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+3" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done

  subgoal for dst imm
  \<comment> \<open> Pcmpq_ri\<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+3" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+3" _]
      apply (simp add: nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+3" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done

  subgoal for test imm
    \<comment> \<open> Pjcc \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+2" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+2" _]
      apply (simp add: nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+2" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done

  subgoal for imm
    \<comment> \<open> Pjmp \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+1" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+1" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+1" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+1" _]
      apply (simp add: nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+1" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done

  subgoal for dst 
    \<comment> \<open> Pcall_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done
  subgoal for dst 
    \<comment> \<open> Pcall_r \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal for imm 
    \<comment> \<open> Pcall_i \<close> 
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp_0 [of _ "pc+1" _]
      using list_in_list_u8_list_of_u32_simp_1 [of _ "pc+1" _]
      using list_in_list_u8_list_of_u32_simp_2 [of _ "pc+1" _]
      using list_in_list_u8_list_of_u32_simp_3 [of _ "pc+1" _]
      apply (simp add: nat_simp add.commute)
      using list_in_list_u8_list_of_u32_simp [of _ "pc+1" _]
      using length_u8_list_of_u32_eq_4
      apply (simp add: modsib_simp rex_simp nat_simp add.commute)
      done
    done

  subgoal 
    \<comment> \<open> Pret \<close>
    apply ((erule case_optionE), simp)+
    subgoal for v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal 
    \<comment> \<open> Prdtsc \<close>
    apply (erule conjE)+
    apply ((erule case_optionE), simp)+
    subgoal for v1 v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done

  subgoal 
    \<comment> \<open> Pnop \<close>
    apply ((erule case_optionE), simp)+
    subgoal for v0
      apply (simp add: x64_decode_def rex_simp modsib_simp nat_simp add.commute)
      done
    done
  done

declare if_split_asm [split del]

declare Let_def [simp del]
declare unsigned_bitfield_extract_u8_def [simp del]
declare x64_decode_op_not_rex_def [simp del]
declare x64_decode_op_0x66_def [simp del]
declare x64_decode_op_0x0f_def [simp del]
declare x64_decode_op_0x81_def [simp del]

end