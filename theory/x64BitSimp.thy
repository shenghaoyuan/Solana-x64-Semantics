theory x64BitSimp
imports
  Main
  rBPFCommType
begin
named_theorems bit_simp

lemma and_and_left [bit_simp]: "and a (and (and a v) k) = and (and a v) k"
  by (simp add: and.commute and.left_commute)

lemma and_and_right [bit_simp]: "and a (and k (and a v)) = and (and a v) k"
  by (simp add: and.commute and.left_commute)

lemma and_7_or_24_simp [bit_simp]: "and 7 (or (and 24 k) v) = and 7 (v::'a :: len word)"
  apply (simp add: bit.conj_disj_distrib)
  apply (simp add: and.assoc[symmetric])
  done

lemma and_7_or_192_simp [bit_simp]: "(and 7 (or (and 192 k) v ) ) = and 7 (v::'a :: len word)"
  apply (simp add: bit.conj_disj_distrib)
  apply (simp add: and.left_commute and.assoc[symmetric])
  done

lemma and_7_and_or_56_simp [bit_simp]: "and (7::8 word) (and (or (and 56 (s2 << 3)) v) (- (193::8 word))) = and 7 v"
  apply (simp add: and.left_commute and.assoc[symmetric])
  apply (simp add: bit.conj_disj_distrib)
  apply (simp add: and.commute and.assoc[symmetric])
  apply (simp add: and.assoc)
  done

end