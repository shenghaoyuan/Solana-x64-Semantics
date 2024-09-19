theory x64_encode_movl_ri_1
imports
  Main
  rBPFCommType 
  x64Syntax BitsOpMore BitsOpMore3
begin

lemma encode_movl_ri_1_subgoal_1: "and 3 ((v::u8) >> 6) = 3 \<Longrightarrow>
    and 7 (v >> 3) = 0 \<Longrightarrow> n < 8 \<Longrightarrow> bit v n \<Longrightarrow> \<not> bit 192 n \<Longrightarrow> bit 7 n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal 
      apply (simp add: bit_iff_odd_drop_bit even_iff_mod_2_eq_zero numeral_3_eq_3 one_and_eq) 



    

lemma encode_movl_ri_1: "
    and 3 (v >> 6) = 3 \<Longrightarrow> and 7 (v >> 3) = 0 \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 v) 0) = Some dst \<Longrightarrow>
    bitfield_insert_u8 4 4
     (bitfield_insert_u8 3 (Suc 0)
       (bitfield_insert_u8 2 (Suc 0)
         (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0)) 0) 0)
       0) 4 = 64 \<Longrightarrow>
    v = bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg dst)) 0) 3"
  apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
  apply (unfold bitfield_insert_u8_def u8_of_bool_def Let_def)
  apply simp
  apply (rule bit_eqI)
  subgoal for n
    apply (auto simp add: bit_simps)
    subgoal 
      done
end