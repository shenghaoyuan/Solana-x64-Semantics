theory x64DecodeProp
imports
  Main
  rBPFCommType
  x64Disassembler
begin

lemma list_in_list_nth_error_0:
  "list_in_list l0 pc l \<Longrightarrow> nth_error l0 0 = Some v \<Longrightarrow> nth_error l pc = Some v"
  apply (induction l0 arbitrary: l pc)
  subgoal for l pc
    by (simp add: nth_error_def)
  subgoal for a l0 l pc
    apply (simp add: nth_error_def)
    apply (cases "length l \<le> pc"; simp)
    done
  done

lemma list_in_list_nth_error:
  "list_in_list l0 pc l \<Longrightarrow> nth_error l0 n = Some v \<Longrightarrow> nth_error l (pc+n) = Some v"
  apply (induction n arbitrary: l0 l pc)
  subgoal for l0 l pc
    apply simp
    using list_in_list_nth_error_0 by metis
  subgoal for n l0 l pc
    apply (simp add: nth_error_def)
    apply (cases l0)
    subgoal by auto
    subgoal for a tl0
      apply simp
      apply (cases "nth_error l pc"; simp)
      apply (cases "length tl0 \<le> n"; simp)
      by fastforce
    done
  done

lemma list_in_list_x64_decode:
  "list_in_list l_bin pc l \<Longrightarrow> x64_decode 0 l_bin = Some v \<Longrightarrow> x64_decode pc l = Some v"
  apply (simp add: x64_decode_def)
  apply (cases "nth_error l_bin 0"; simp)
  apply (frule list_in_list_nth_error [of _ _ _ 0 _], assumption, simp)
  subgoal for h
    apply (cases "h = 144"; simp)
    apply (cases "h = 153"; simp)
    apply (cases "h = 195"; simp)
    apply (cases "h = 102"; simp)
     prefer 2
     apply (cases "h = 15"; simp)
      prefer 2
      apply (cases "and 15 (h >> 4) \<noteq> 4"; simp)
    prefer 2
      apply (cases "and 15 h = 0"; simp)
       apply (cases "nth_error l_bin (Suc 0)"; simp)
      apply (frule list_in_list_nth_error [of _ _ _ "Suc 0" _], assumption, simp)
    subgoal for op
      apply (cases "op = 153"; simp)
      apply (cases "and 31 (op >> 3) = 10"; simp)
      apply (cases "and 31 (op >> 3) = 11"; simp)
      apply (cases "and 31 (op >> 3) = 23"; simp)

      subgoal
        apply (cases "nth_error l_bin (Suc (Suc 0))"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ "Suc (Suc 0)" _], assumption, simp)
        subgoal for i1 apply (cases "nth_error l_bin 3"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ 3 _], assumption, simp)
        subgoal for i2 apply (cases "nth_error l_bin 4"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ 4 _], assumption, simp)
        subgoal for i3 apply (cases "nth_error l_bin 5"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ 5 _], assumption, simp)
        subgoal for i4 apply (cases "nth_error l_bin 6"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ 6 _], assumption, simp)
        subgoal for i5 apply (cases "nth_error l_bin 7"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ 7 _], assumption, simp)
        subgoal for i6 apply (cases "nth_error l_bin 8"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ 8 _], assumption, simp)
        subgoal for i7 apply (cases "nth_error l_bin 9"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ 9 _], assumption, simp)
          done done done done done done done done

        apply (cases "op = 104"; simp)
        subgoal
          apply (cases "nth_error l_bin (Suc (Suc 0))"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ "Suc (Suc 0)" _], assumption, simp)
          subgoal for i1 apply (cases "nth_error l_bin 3"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ 3 _], assumption, simp)
          subgoal for i2 apply (cases "nth_error l_bin 4"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ 4 _], assumption, simp)
          subgoal for i3 apply (cases "nth_error l_bin 5"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ 5 _], assumption, simp)
          done done done done 

        apply (cases "op = 15"; simp)
        subgoal
          apply (cases "nth_error l_bin (Suc (Suc 0))"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ "Suc (Suc 0)" _], assumption, simp)
          subgoal for i1 apply (cases "and 31 (i1 >> 3) = 25"; simp)
            apply (cases "and 15 (i1 >> 4) = 4"; simp)
            apply (cases "nth_error l_bin 3"; simp)
            apply (frule list_in_list_nth_error [of _ _ _ 3 _], assumption, simp)
            done done

        apply (cases "nth_error l_bin (Suc (Suc 0))"; simp)
        apply (frule list_in_list_nth_error [of _ _ _ "Suc (Suc 0)" _], assumption, simp)
        subgoal for reg apply (cases "op = 137"; simp)
          subgoal apply (simp add: Let_def) 
            apply (cases "and 3 (reg >> 6) = 3"; simp)
            apply (cases "and 3 (reg >> 6) = 1"; simp)
              subgoal
                apply (cases "nth_error l_bin 3"; simp)
                by (frule list_in_list_nth_error [of _ _ _ 3 _], assumption, simp)

            apply (cases "and 3 (reg >> 6) = 2"; simp)
            apply (cases "and 7 reg \<noteq> 4"; simp)
              subgoal
                apply (cases "nth_error l_bin 3"; simp)
                apply (frule list_in_list_nth_error [of _ _ _ 3 _], assumption, simp)
                subgoal for d1 apply (cases "nth_error l_bin 4"; simp)
                apply (frule list_in_list_nth_error [of _ _ _ 4 _], assumption, simp)
                subgoal for d2 apply (cases "nth_error l_bin 5"; simp)
                apply (frule list_in_list_nth_error [of _ _ _ 5 _], assumption, simp)
                subgoal for d3 apply (cases "nth_error l_bin 6"; simp)
                apply (frule list_in_list_nth_error [of _ _ _ 6 _], assumption, simp)
                subgoal for d4 apply (cases "u32_of_u8_list [d1, d2, d3, d4]"; simp)
                subgoal for dis apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (reg >> 3)) (and 1 (h >> 2)))"; simp)
                subgoal for src apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 reg) (and 1 h))"; simp)
                subgoal for rb 
                  by argo
                done done done done done done done
              
              apply (cases "nth_error l_bin 3"; simp)
              apply (frule list_in_list_nth_error [of _ _ _ 3 _], assumption, simp)
              subgoal for d1 apply (cases "nth_error l_bin 4"; simp)
              apply (frule list_in_list_nth_error [of _ _ _ 4 _], assumption, simp)
              subgoal for d2 apply (cases "nth_error l_bin 5"; simp)
              apply (frule list_in_list_nth_error [of _ _ _ 5 _], assumption, simp)
              subgoal for d3 apply (cases "nth_error l_bin 6"; simp)
              apply (frule list_in_list_nth_error [of _ _ _ 6 _], assumption, simp)
              subgoal for d4 apply (cases "nth_error l_bin 7"; simp)
              apply (frule list_in_list_nth_error [of _ _ _ 7 _], assumption, simp)
              done done done done done

            apply (cases "op = 135"; simp)
            subgoal 
              apply (simp add: Let_def)
              apply (cases "and 3 (reg >> 6) = 3"; simp)
              apply (cases "and 3 (reg >> 6) = 2"; simp)
              apply (cases " and 7 reg = 4"; simp)
              apply (cases "nth_error l_bin 3"; simp)
              apply (frule list_in_list_nth_error [of _ _ _ 3 _], assumption, simp)
              subgoal for d1 apply (cases "nth_error l_bin 4"; simp)
              apply (frule list_in_list_nth_error [of _ _ _ 4 _], assumption, simp)
              subgoal for d2 apply (cases "nth_error l_bin 5"; simp)
              apply (frule list_in_list_nth_error [of _ _ _ 5 _], assumption, simp)
              subgoal for d3 apply (cases "nth_error l_bin 6"; simp)
              apply (frule list_in_list_nth_error [of _ _ _ 6 _], assumption, simp)
              subgoal for d4 apply (cases "nth_error l_bin 7"; simp)
              apply (frule list_in_list_nth_error [of _ _ _ 7 _], assumption, simp)
              done done done done done

            apply (cases "op = 99"; simp)
            apply (cases "op = 1"; simp)
            apply (cases "op = 41"; simp)
            apply (cases "op = 247"; simp)
            subgoal
              apply (simp add: Let_def)

              apply (cases "and 3 (reg >> 6) = 3 \<and> and 7 (reg >> 3) = 3"; simp)
              apply (cases "and 3 (reg >> 6) = 3 \<and> and 7 (reg >> 3) = 4"; simp)
              apply (cases "and 3 (reg >> 6) = 3 \<and> and 7 (reg >> 3) = 5"; simp)
              apply (cases "and 3 (reg >> 6) = 3 \<and> and 7 (reg >> 3) = 6"; simp)
              apply (cases "and 3 (reg >> 6) = 3 \<and> and 7 (reg >> 3) = 7"; simp)
              apply (cases "and 3 (reg >> 6) = 3 \<and> and 7 (reg >> 3) = 0"; simp)
              apply (cases "nth_error l_bin 3"; simp)
              apply (frule list_in_list_nth_error [of _ _ _ 3 _], assumption, simp)
              subgoal for d1 apply (cases "nth_error l_bin 4"; simp)
              apply (frule list_in_list_nth_error [of _ _ _ 4 _], assumption, simp)
              subgoal for d2 apply (cases "nth_error l_bin 5"; simp)
              apply (frule list_in_list_nth_error [of _ _ _ 5 _], assumption, simp)
              subgoal for d3 apply (cases "nth_error l_bin 6"; simp)
              apply (frule list_in_list_nth_error [of _ _ _ 6 _], assumption, simp)
              done done done done

            apply (cases "op = 9"; simp)
            apply (cases "op = 33"; simp)
            apply (cases "op = 49"; simp)
            apply (cases "op = 211"; simp)
            apply (cases "op = 133"; simp)
            apply (cases "op = 57"; simp)
            apply (cases "op = 255"; simp)
            subgoal
              apply (simp add: Let_def)

              apply (cases "and 3 (reg >> 6) = 3 \<and> and 7 (reg >> 3) = 2"; simp)
              apply (cases "and 3 (reg >> 6) = 2 \<and> and 7 reg = 4"; simp)
              apply (cases "nth_error l_bin 3"; simp)
              apply (frule list_in_list_nth_error [of _ _ _ 3 _], assumption, simp)
              subgoal for sib apply (cases "nth_error l_bin 4"; simp)
              apply (frule list_in_list_nth_error [of _ _ _ 4 _], assumption, simp)
              subgoal for d1 apply (cases "nth_error l_bin 5"; simp)
              apply (frule list_in_list_nth_error [of _ _ _ 5 _], assumption, simp)
              subgoal for d2 apply (cases "nth_error l_bin 6"; simp)
              apply (frule list_in_list_nth_error [of _ _ _ 6 _], assumption, simp)
              subgoal for d3 apply (cases "nth_error l_bin 7"; simp)
              apply (frule list_in_list_nth_error [of _ _ _ 7 _], assumption, simp)
              done done done done done

            apply (cases "op = 199"; simp)
            subgoal
              apply (simp only: Let_def)

              apply (cases "and 3 (reg >> 6) = 1"; simp)
              subgoal apply (cases "nth_error l_bin 4"; simp)
                subgoal for i1 apply (frule list_in_list_nth_error [of _ _ _ 4 i1]) apply blast
                  apply (rule subst [of "pc+4" "4+pc"]; simp)

                  apply (cases "nth_error l_bin 5"; simp)
                  subgoal for i2 apply (frule list_in_list_nth_error [of _ _ _ 5 i2]) apply blast
                  apply (rule subst [of "pc+5" "5+pc"]; simp)

                  apply (cases "nth_error l_bin 6"; simp)
                  subgoal for i3 apply (frule list_in_list_nth_error [of _ _ _ 6 i3]) apply blast
                  apply (rule subst [of "pc+6" "6+pc"]; simp)

                  apply (cases "nth_error l_bin 7"; simp)
                  subgoal for i4 apply (frule list_in_list_nth_error [of _ _ _ 7 i4]) apply blast
                  apply (rule subst [of "pc+7" "7+pc"]; simp)
                  apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 reg) (and 1 h))"; simp)
                  subgoal for dst apply (cases "u32_of_u8_list [i1, i2, i3, i4]"; simp)
                  subgoal for imm apply (cases "and 7 (reg >> 3) = 0 \<and> and 1 (h >> 2) = 0 \<and> and 1 (h >> Suc 0) = 0"; simp)
                    apply (cases "and 1 (h >> 3) = 1"; simp)
                    apply (cases "nth_error l_bin 3"; simp)
                    apply (frule list_in_list_nth_error [of _ _ _ 3 _], assumption, simp)
                    done done done done done done done

                  apply (cases "and 3 (reg >> 6) = 2"; simp)
                  subgoal
                    apply (cases "nth_error l_bin 7"; simp)
                    apply (frule list_in_list_nth_error [of _ _ _ 7 _], assumption)
                    apply (rule subst [of "pc+7" "7+pc"]; simp)

                    subgoal for i1
                      apply (cases "nth_error l_bin 8"; simp)
                      subgoal for i2 apply (frule list_in_list_nth_error [of _ _ _ 8 i2]) apply blast
                        apply (rule subst [of "pc+8" "8+pc"]; simp)

                      apply (cases "nth_error l_bin 9"; simp)
                      subgoal for i3 apply (frule list_in_list_nth_error [of _ _ _ 9 i3]) apply blast
                        apply (rule subst [of "pc+9" "9+pc"]; simp)

                      apply (cases "nth_error l_bin 10"; simp)
                      subgoal for i4 apply (frule list_in_list_nth_error [of _ _ _ 10 i4]) apply blast
                        apply (rule subst [of "pc+10" "10+pc"]; simp)

                        apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 reg) (and 1 h))"; simp)
                        subgoal for dst apply (cases "u32_of_u8_list [i1, i2, i3, i4]"; simp)
                          apply (cases "and 7 (reg >> 3) = 0 \<and> and 1 (h >> 2) = 0 \<and> and 1 (h >> Suc 0) = 0"; simp)

                          apply (cases "nth_error l_bin 3"; simp)
                          apply (frule list_in_list_nth_error [of _ _ _ 3 _], assumption, simp)
                          subgoal for sib apply (cases "nth_error l_bin 4"; simp)
                          apply (frule list_in_list_nth_error [of _ _ _ 4 _], assumption, simp)
                          subgoal for d1 apply (cases "nth_error l_bin 5"; simp)
                          apply (frule list_in_list_nth_error [of _ _ _ 5 _], assumption, simp)
                          subgoal for d2 apply (cases "nth_error l_bin 6"; simp)
                          apply (frule list_in_list_nth_error [of _ _ _ 6 _], assumption, simp)
                            done done done done done done done done done

                  apply (cases "nth_error l_bin 3"; simp)
                  apply (frule list_in_list_nth_error [of _ _ _ 3 _], assumption, simp)
                  subgoal for i1 apply (cases "nth_error l_bin 4"; simp)
                  apply (frule list_in_list_nth_error [of _ _ _ 4 _], assumption, simp)
                  subgoal for i2 apply (cases "nth_error l_bin 5"; simp)
                  apply (frule list_in_list_nth_error [of _ _ _ 5 _], assumption, simp)
                  subgoal for i3 apply (cases "nth_error l_bin 6"; simp)
                  apply (frule list_in_list_nth_error [of _ _ _ 6 _], assumption, simp)
                  subgoal for i4 apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 reg) (and 1 h))"; simp)
                  subgoal for dst apply (cases "u32_of_u8_list [i1, i2, i3, i4]"; simp)
                  subgoal for imm apply (cases "and 7 (reg >> 3) = 0 \<and> and 1 (h >> 2) = 0 \<and> and 1 (h >> Suc 0) = 0"; simp)
                  apply (cases "and 3 (reg >> 6) = 3"; simp)
                  apply (cases "and 1 (h >> 3) = 0"; simp)
                    done done done done done done done

                  apply (cases "op = 129"; simp)
                  subgoal 
                    apply (simp add: Let_def)
                    sorry

                  apply (cases "op = 193"; simp)
                  subgoal
                    apply (cases "nth_error l_bin 3"; simp)
                    apply (frule list_in_list_nth_error [of _ _ _ 3 _], assumption, simp)
                    done

                  apply (cases "op = 136"; simp)
                  subgoal
                    apply (cases "and 3 (reg >> 6) = 1 \<and> and 1 (h >> Suc 0) = 0 \<and> and 1 (h >> 3) = 0"; simp)
                    apply (cases "nth_error l_bin 3"; simp)
                    apply (frule list_in_list_nth_error [of _ _ _ 3 _], assumption, simp)
                    done

                  apply (cases "op = 139"; simp)
                  subgoal
                    apply (simp add: Let_def)
                    apply (cases "and 3 (reg >> 6) = 1 \<and> and 1 (h >> Suc 0) = 0"; simp)
                    apply (cases "nth_error l_bin 3"; simp)
                    apply (frule list_in_list_nth_error [of _ _ _ 3 _], assumption, simp)
                    subgoal for dis apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (reg >> 3)) (and 1 (h >> 2)))"; simp)
                    subgoal for src apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 reg) (and 1 h))"; simp)
                    subgoal for dst by force 
                    done done

                  apply (cases "and 3 (reg >> 6) = 2"; simp)
                  apply (cases "and 7 reg \<noteq> 4"; simp)
                  subgoal
                    apply (cases "nth_error l_bin 3"; simp)
                    apply (frule list_in_list_nth_error [of _ _ _ 3 _], assumption, simp)
                    apply (cases "nth_error l_bin 4"; simp)
                    apply (frule list_in_list_nth_error [of _ _ _ 4 _], assumption, simp)
                    apply (cases "nth_error l_bin 5"; simp)
                    apply (frule list_in_list_nth_error [of _ _ _ 5 _], assumption, simp)
                    apply (cases "nth_error l_bin 6"; simp)
                    apply (frule list_in_list_nth_error [of _ _ _ 6 _], assumption, simp)
                    subgoal for d1 d2 d3 d4 apply (cases "u32_of_u8_list [d1, d2, d3, d4]"; simp)
                    subgoal for dis apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (reg >> 3)) (and 1 (h >> 2)))"; simp)
                    subgoal for src apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 reg) (and 1 h))"; simp)
                    subgoal for dst apply (cases "and 1 (h >> Suc 0) = 0"; simp)
                      by argo
                    done done done done

                  apply (cases "nth_error l_bin 3"; simp)
                  apply (frule list_in_list_nth_error [of _ _ _ 3 _], assumption, simp)
                  apply (cases "nth_error l_bin 4"; simp)
                  apply (frule list_in_list_nth_error [of _ _ _ 4 _], assumption, simp)
                  apply (cases "nth_error l_bin 5"; simp)
                  apply (frule list_in_list_nth_error [of _ _ _ 5 _], assumption, simp)
                  apply (cases "nth_error l_bin 6"; simp)
                  apply (frule list_in_list_nth_error [of _ _ _ 6 _], assumption, simp)
                  apply (cases "nth_error l_bin 7"; simp)
                  apply (frule list_in_list_nth_error [of _ _ _ 7 _], assumption, simp)
                  done

                apply (cases "op = 141"; simp)
                subgoal
                  apply (simp add: Let_def)
                  apply (cases "and 3 (reg >> 6) = 1"; simp)
                  subgoal
                    apply (cases "nth_error l_bin 3"; simp)
                    apply (frule list_in_list_nth_error [of _ _ _ 3 _], assumption, simp)
                    done
                  apply (cases "and 3 (reg >> 6) = 2"; simp)
                  subgoal
                    apply (cases "nth_error l_bin 3"; simp)
                    apply (frule list_in_list_nth_error [of _ _ _ 3 _], assumption, simp)
                    apply (cases "nth_error l_bin 4"; simp)
                    apply (frule list_in_list_nth_error [of _ _ _ 4 _], assumption, simp)
                    apply (cases "nth_error l_bin 5"; simp)
                    apply (frule list_in_list_nth_error [of _ _ _ 5 _], assumption, simp)
                    apply (cases "nth_error l_bin 6"; simp)
                    apply (frule list_in_list_nth_error [of _ _ _ 6 _], assumption, simp)
                    done done done done

                  done

end