theory BitExtractInsert
  imports Main rBPFCommType
begin

lemma and_pow_n_shr_eq: "(and (x::'a :: len word) (2^n) = 0) = (and 1 (x >> n) = 0)"
  apply (induction n arbitrary: x; simp)
  subgoal for x
    using and.commute
    by metis
  subgoal for n1 x
    apply (cases "even x"; simp?)
    subgoal
      by (metis and_exp_eq_0_iff_not_bit bit_0 bit_iff_odd_drop_bit power_0 power_Suc word_bw_comms(1))
    subgoal
      by (metis and_exp_eq_0_iff_not_bit even_drop_bit_iff_not_bit even_iff_mod_2_eq_zero one_and_eq power_Suc)
    done
  done

lemma word_and_le_2: "and x y = z \<Longrightarrow> (y :: 'a :: len word) < z \<Longrightarrow> False"
  using word_le_def AND_upper2'' word_and_le1
  using leD by blast

lemma and_length_eq: "and (2^LENGTH('a) -1) x = (x::'a :: len word)"
  by simp

lemma and_length_eq_u8: "and 255 x = (x::8 word)"
  apply (subgoal_tac "2^LENGTH(8)-1 = (255::u8)")
  subgoal using and_length_eq
    by metis 
  subgoal by simp
  done

lemma bitfield_extract_0_8_eq: "bitfield_extract 0 8 x = (x::u8)"
  by (simp add: bitfield_extract_def Let_def and_length_eq_u8)

lemma bit_power_k_add_m_low: "bit (2 ^ (m + n) - 2 ^ n) k \<Longrightarrow> n \<le> k"
  apply (induction n arbitrary: m k; simp)
  subgoal for n1 m k
    apply (cases k; simp)
    subgoal
      by (metis bit_double_iff right_diff_distrib')
    subgoal for k1
      by (metis bit_double_Suc_iff right_diff_distrib')
    done
  done

lemma bit_power_k_minus_1_lt: "k \<le> LENGTH('a) \<Longrightarrow> bit ((2^k -1)::'a :: len word) n \<longleftrightarrow> n < k"
  apply (simp only: bit_iff_odd)
  using even_decr_exp_div_exp_iff' linorder_not_le
  using even_mask_div_iff by fastforce

lemma bit_power_k_add_m_high: "m + n \<le> LENGTH('a) \<Longrightarrow> bit ((2 ^ (m + n) - 2 ^ n)::'a :: len word) k \<Longrightarrow> k < m + n"
  apply (induction n arbitrary: m k; simp)
  subgoal for m k using bit_power_k_minus_1_lt by blast
  subgoal for n1 m k
    apply (cases k; simp)
    subgoal
      by (metis One_nat_def Suc_leD bit_double_iff diff_Suc_1' right_diff_distrib')
    done
  done

lemma bit_power_k_add_m_iff: "m + n \<le> LENGTH('a) \<Longrightarrow> bit ((2 ^ (m + n) - 2 ^ n)::'a :: len word) k = (n \<le> k \<and> k < m + n)"
  apply (induction n arbitrary: m k; simp)
  subgoal for m k using bit_power_k_minus_1_lt by blast
  subgoal for n1 m k
    apply (cases k; simp)
    subgoal
      by (metis bit_double_iff right_diff_distrib')
    subgoal for k1
      by (metis (no_types, lifting) add_leD2 bit_double_Suc_iff nat_add_left_cancel_less order_less_le_trans plus_1_eq_Suc possible_bit_word right_diff_distrib_numeral)
    done
  done


lemma and_power_m_add_n_shift_n_eq: "m + n \<le> LENGTH('a) \<Longrightarrow> and (2^(m+n) - 2^n) ((x >> n) << n) =
  and (2^(m+n) - 2^n) (x::'a :: len word)"
  apply (simp add: bit_eq_iff)
  apply (simp add: bit_simps)
  apply (rule allI)
  subgoal for n1
    apply (cases "n \<le> n1"; simp)
    apply (rule impI)
    apply (simp add: bit_power_k_add_m_low)
    done
  done


lemma and_shr_shl_eq: "and (2^LENGTH('a) - 2^n) ((x >> n) << n) =
  and (2^LENGTH('a) - 2^n) (x::'a :: len word)"
  apply (simp add: bit_eq_iff)
  apply (simp add: bit_simps)
  by (metis add_diff_inverse_nat bit_iff_odd even_mask_div_iff exp_eq_0_imp_not_bit linorder_not_le)

lemma and_shr_shl_eq_u8_6: "(and 192 ((x >> 6) << 6)) = and 192 (x:: 8 word)"
  apply (subgoal_tac "2^LENGTH(8) - 2^6 = (192::u8)")
  subgoal using and_shr_shl_eq
    by metis

  subgoal by simp
  done


lemma pow_2_m1_shl_eq: "m + n \<le> LENGTH('a) \<Longrightarrow> 2 ^ n - 1 << m = 2^(m+n) - (2^m ::'a :: len word)"
  apply (induction m arbitrary: n; simp)
  subgoal for m1 n
    apply (simp only: Nat.add_Suc_right[symmetric])
    apply (subgoal_tac"2 ^ n * 2 = (2 ^ (Suc n) ::'a :: len word)")
     prefer 2 subgoal by simp
    by (simp add: mult.commute power_add push_bit_eq_mult right_diff_distrib')
  done

lemma bitfield_extract_split_eq :"
  m + n \<le> LENGTH('a) \<Longrightarrow>
  bitfield_extract 0 m r = x \<Longrightarrow>
  bitfield_extract m n r = v \<Longrightarrow>
    bitfield_insert m n x v = bitfield_extract 0 (m+n) (r::'a :: len word)"
  apply (erule subst [of _ v])
  apply (erule subst [of _ x])
  apply (simp add: bitfield_insert_def bitfield_extract_def Let_def)
  apply (simp only: pow_2_m1_shl_eq)
  apply (simp only: add.commute [of m n])
  apply (simp add: and_power_m_add_n_shift_n_eq)
  apply (simp add: bit_eq_iff bit_simps)

  apply (rule allI, rule impI)
  subgoal for n1
    apply (cases "bit r n1"; simp)
    apply (cases "m \<le> n1"; simp?)
    prefer 2
    subgoal 
      by (simp add: bit_power_k_minus_1_lt)

    apply (subgoal_tac "bit ((2 ^ m - 1)::'a :: len word) n1 = False"; simp)
     prefer 2 subgoal
      using bit_iff_odd even_mask_div_iff by blast
    apply (cases "n+m \<le> n1"; simp add: bit_power_k_add_m_iff)
    prefer 2
    subgoal
      using bit_power_k_minus_1_lt [of "n+m" n1]
      using linorder_not_le by blast
    subgoal
      using bit_iff_odd even_mask_div_iff by blast
    done
  done
named_theorems extract_simp

lemma bitfield_extract_0_6_2_eq [extract_simp] :"
  bitfield_extract 0 6 r = x \<Longrightarrow>
  bitfield_extract 6 2 r = v \<Longrightarrow>
    bitfield_insert 6 2 x v = (r::u8)"
  apply (simp add: bitfield_extract_split_eq)
  apply (simp add: bitfield_extract_0_8_eq)
  done

lemma bitfield_extract_0_3_3_eq :"
  bitfield_extract 0 3 r = x \<Longrightarrow>
  bitfield_extract 3 3 r = v \<Longrightarrow>
    bitfield_insert 3 3 x v = bitfield_extract 0 6 (r::u8)"
  apply (simp add: bitfield_extract_split_eq)
  done

lemma "m + n \<le> LENGTH('a) \<Longrightarrow>
  (2 ^ n - 1 << m) >> m = ((2 ^ n - 1)::'a :: len word)"

lemma "
  m + n \<le> LENGTH('a) \<Longrightarrow>
  bitfield_extract m n (bitfield_insert m n k v) =
  bitfield_extract 0 n (v::'a :: len word)"
  apply (simp add: bitfield_extract_def bitfield_insert_def)

end