theory x64_encode_movl_ri_2
imports
  Main
  rBPFCommType 
  x64Syntax BitsOpMore BitsOpMore3
begin

lemma encode_movl_ri_2: "
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 v) 0) = Some dst \<Longrightarrow>
    u32_of_u8_list [l ! Suc (Suc pc), l ! (pc + 3), l ! (pc + 4), l ! (pc + 5)] = Some imm \<Longrightarrow>
    and 3 (v >> 6) = 3 \<Longrightarrow> and 7 (v >> 3) = 0 \<Longrightarrow>
    bitfield_insert_u8 4 4
     (bitfield_insert_u8 3 (Suc 0) (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0)) 0) 0) 0)
     4 \<noteq> 64 \<Longrightarrow>
    bitfield_insert_u8 4 4
     (bitfield_insert_u8 3 (Suc 0) (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0)) 0) 0) 0)
     4 =  199 \<and>
    l ! Suc (Suc pc) = bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg dst)) 0) 3 \<and>
    [l ! Suc (Suc (Suc pc)), l ! Suc (Suc (Suc (Suc pc))), l ! Suc (Suc (Suc (Suc (Suc pc))))] = u8_list_of_u32 imm
"
  apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
  apply (unfold bitfield_insert_u8_def u8_of_bool_def Let_def )
  apply simp
  done

end