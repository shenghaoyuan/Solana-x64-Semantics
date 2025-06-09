theory x64DecodeProp
imports
  Main
  rBPFCommType
  x64Disassembler
begin

lemma x64_decode_length_none: "
  x64_decode (length l) l = None"
  apply (simp add: x64_decode_def nth_error_def)
  done

lemma list_in_list_implies_set_relation:
  "list_in_list [x] pos l_jump \<Longrightarrow> x \<in> set l_jump"
  apply simp
  apply (cases "nth_error l_jump pos"; simp)
  by (metis in_set_conv_nth le_eq_less_or_eq linorder_le_cases
      nth_error_def option.inject option.simps(3))

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

lemma list_in_list_x64_decode_op_0x66_prop: "
  list_in_list l_bin pc l \<Longrightarrow>
  x64_decode_op_0x66 n l_bin = Some v \<Longrightarrow>
    x64_decode_op_0x66 (pc+n) l = Some v"
  apply (simp add: x64_decode_op_0x66_def)
  apply (cases "nth_error l_bin (Suc n)"; simp)
  apply (frule list_in_list_nth_error [of _ _ _ "Suc n" _], assumption, simp)
  subgoal for h1 apply (cases "bitfield_extract 4 4 h1 \<noteq> 4"; simp)
    subgoal
      apply (cases "nth_error l_bin (Suc (Suc n))"; simp) 
      apply (frule list_in_list_nth_error [of _ _ _ "Suc (Suc n)" _], assumption, simp add: Let_def)
      subgoal for reg apply (cases "h1 = 193"; simp)
        subgoal apply (cases "nth_error l_bin (n + 3)"; simp)
          apply (subst add.assoc [of pc n 3])
          apply (frule list_in_list_nth_error [of _ _ _ "n + 3" _], assumption, simp)
          done

        apply (cases "h1 = 129"; simp)
        subgoal apply (cases "bitfield_extract 6 2 reg = 3"; simp)
          apply (cases "ireg_of_u8 (bitfield_insert 3 (Suc 0) (bitfield_extract 0 3 reg) 0)"; simp)
          subgoal for dst apply (cases "nth_error l_bin (n + 3)"; simp)
            apply (subst add.assoc [of pc n 3])
            apply (frule list_in_list_nth_error [of _ _ _ "n + 3" _], assumption, simp)
            subgoal for i1 apply (cases "nth_error l_bin (n + 4)"; simp)
              apply (subst add.assoc [of pc n 4])
              apply (frule list_in_list_nth_error [of _ _ _ "n + 4" _], assumption, simp)
              done
            done
          done

        apply (cases "h1 = 137"; simp)
        apply (cases "bitfield_extract 6 2 reg = 1"; simp)
        apply (cases "nth_error l_bin (n+3)"; simp)
        apply (subst add.assoc [of pc n 3])
        apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
        done
      done

    apply (cases "nth_error l_bin (Suc (Suc n))"; simp) 
    apply (frule list_in_list_nth_error [of _ _ _ "Suc (Suc n)" _], assumption, simp)
      subgoal for op apply (cases "nth_error l_bin (n+3)"; simp)
        apply (subst add.assoc [of pc n 3])
        apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp add: Let_def)
        subgoal for reg apply (cases "op = 193"; simp)
          subgoal apply (cases "nth_error l_bin (n+4)"; simp)
            apply (subst add.assoc [of pc n 4])
            apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
          done
        apply (cases "op = 129"; simp)
        subgoal apply (cases "bitfield_extract 6 2 reg = 3"; simp)
          apply (cases "ireg_of_u8 (bitfield_insert 3 (Suc 0) (bitfield_extract 0 3 reg) (bitfield_extract 0 (Suc 0) h1))"; simp)
          subgoal for dst apply (cases "nth_error l_bin (n+4)"; simp)
            apply (subst add.assoc [of pc n 4])
            apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
            subgoal for i1 apply (cases "nth_error l_bin (n+5)"; simp)
              apply (subst add.assoc [of pc n 5])
              apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption, simp)
              done
            done
          done
        apply (cases "op = 137"; simp)
        apply (cases "bitfield_extract 6 2 reg = 1"; simp)
        apply (cases "nth_error l_bin (n+4)"; simp)
        apply (subst add.assoc [of pc n 4])
        apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
        done
      done
    done
  done

lemma list_in_list_x64_decode_op_0x0f_prop: "list_in_list l_bin pc l \<Longrightarrow>
  x64_decode_op_0x0f n l_bin = Some v \<Longrightarrow> x64_decode_op_0x0f (pc+n) l = Some v"
  apply (simp add: x64_decode_op_0x0f_def)
  apply (cases "nth_error l_bin (Suc n)"; simp)
  apply (frule list_in_list_nth_error [of _ _ _ "Suc n" _], assumption, simp)
  subgoal for op apply (cases "op = 49"; simp)
    apply (cases "bitfield_extract 3 5 op = 25"; simp)
    apply (cases "bitfield_extract 4 4 op = 4"; simp)
    subgoal
      apply (cases "nth_error l_bin (Suc (Suc n))"; simp)
      apply (frule list_in_list_nth_error [of _ _ _ "Suc (Suc n)" _], assumption, simp add: Let_def)
      done

    apply (cases "bitfield_extract 4 4 op = 8"; simp)
    apply (cases "nth_error l_bin (Suc (Suc n))"; simp)
    apply (frule list_in_list_nth_error [of _ _ _ "Suc (Suc n)" _], assumption, simp add: Let_def)
    subgoal for i1 apply (cases "nth_error l_bin (n+3)"; simp)
      apply (subst add.assoc [of pc n 3])
      apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
    subgoal for i2 apply (cases "nth_error l_bin (n+4)"; simp)
      apply (subst add.assoc [of pc n 4])
      apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
    subgoal for i3 apply (cases "nth_error l_bin (n+5)"; simp)
      apply (subst add.assoc [of pc n 5])
      apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption, simp)
      done done done done done

lemma list_in_list_x64_decode_op_not_rex_prop: "list_in_list l_bin pc l \<Longrightarrow>
    x64_decode_op_not_rex h n l_bin = Some v \<Longrightarrow> x64_decode_op_not_rex h (pc+n) l = Some v"
  apply (simp add: x64_decode_op_not_rex_def)
  apply (cases "bitfield_extract 3 5 h = 10"; simp)
  subgoal apply (cases "ireg_of_u8 (bitfield_insert 3 (Suc 0) (bitfield_extract 0 3 h) 0)"; simp)
    subgoal for dst apply (cases "nth_error l (Suc (pc + n))", fastforce, simp)
      subgoal for i1 apply (cases "nth_error l (Suc (Suc (pc + n)))", fastforce, simp)
        subgoal for i2 apply (cases "nth_error l (pc + n + 3)", fastforce, simp)
          subgoal for i3 apply (cases "nth_error l (pc + n + 4)", fastforce, simp)  
            subgoal for i4 apply (cases "u32_of_u8_list [i1, i2, i3, i4]"; fastforce)
              done
            done
          done
        done
      done
    done

  apply (cases "bitfield_extract 3 5 h = 11"; simp)
  subgoal apply (cases "ireg_of_u8 (bitfield_insert 3 (Suc 0) (bitfield_extract 0 3 h) 0)"; simp)
    subgoal for dst apply (cases "nth_error l (Suc (pc + n))", fastforce, simp)
      subgoal for i1 apply (cases "nth_error l (Suc (Suc (pc + n)))", fastforce, simp)
        subgoal for i2 apply (cases "nth_error l (pc + n + 3)", fastforce, simp)
          subgoal for i3 apply (cases "nth_error l (pc + n + 4)", fastforce, simp)  
            subgoal for i4 apply (cases "u32_of_u8_list [i1, i2, i3, i4]"; fastforce)
              done
            done
          done
        done
      done
    done

  apply (cases "h = 232"; simp)
  subgoal apply (cases "nth_error l_bin (Suc n) "; simp)
    apply (frule list_in_list_nth_error [of _ _ _ "Suc n" _], assumption, simp)
    subgoal for i1 apply (cases "nth_error l_bin (Suc (Suc n))"; simp)
      apply (frule list_in_list_nth_error [of _ _ _ "(Suc (Suc n))" _], assumption, simp)
    subgoal for i2 apply (cases "nth_error l_bin (n+3)"; simp)
      apply (subst add.assoc [of pc n 3])
      apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
    subgoal for i3 apply (cases "nth_error l_bin (n+4)"; simp)
      apply (subst add.assoc [of pc n 4])
      apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
      done done done done

  apply (cases "h = 233"; simp)
  subgoal apply (cases "nth_error l_bin (Suc n) "; simp)
    apply (frule list_in_list_nth_error [of _ _ _ "Suc n" _], assumption, simp)
    subgoal for i1 apply (cases "nth_error l_bin (Suc (Suc n))"; simp)
      apply (frule list_in_list_nth_error [of _ _ _ "(Suc (Suc n))" _], assumption, simp)
    subgoal for i2 apply (cases "nth_error l_bin (n+3)"; simp)
      apply (subst add.assoc [of pc n 3])
      apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
    subgoal for i3 apply (cases "nth_error l_bin (n+4)"; simp)
      apply (subst add.assoc [of pc n 4])
      apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
      done done done done

    apply (cases "nth_error l_bin (Suc n) "; simp)
    apply (frule list_in_list_nth_error [of _ _ _ "Suc n" _], assumption, simp)
    subgoal for reg apply (cases "h = 137"; simp)
      subgoal apply (simp add: Let_def)
        apply (cases "bitfield_extract 6 2 reg = 3"; simp)
        apply (cases "bitfield_extract 6 2 reg = 1"; simp)
        subgoal
          apply (cases "nth_error l_bin (Suc (Suc n))"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ "(Suc (Suc n))" _], assumption, simp)
          done

        apply (cases "bitfield_extract 6 2 reg = 2"; simp)
        apply (cases "nth_error l_bin (Suc (Suc n))"; simp)
        apply (frule list_in_list_nth_error [of _ _ _ "(Suc (Suc n))" _], assumption, simp)
        subgoal for i2 apply (cases "nth_error l_bin (n+3)"; simp)
          apply (subst add.assoc [of pc n 3])
          apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
        subgoal for i3 apply (cases "nth_error l_bin (n+4)"; simp)
          apply (subst add.assoc [of pc n 4])
          apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
        subgoal for i4 apply (cases "nth_error l_bin (n+5)"; simp)
          apply (subst add.assoc [of pc n 5])
          apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption, simp)
          done done done done

        apply (cases "h = 1"; simp)
        apply (cases "h = 247"; simp)
        subgoal apply (simp add: Let_def)
          apply (cases "bitfield_extract 6 2 reg = 3 \<and> bitfield_extract 3 3 reg = 3"; simp)
          apply (cases "bitfield_extract 6 2 reg = 3 \<and> bitfield_extract 3 3 reg = 4"; simp)
          apply (cases "bitfield_extract 6 2 reg = 3 \<and> bitfield_extract 3 3 reg = 5"; simp)
          apply (cases "bitfield_extract 6 2 reg = 3 \<and> bitfield_extract 3 3 reg = 6"; simp)
          apply (cases "bitfield_extract 6 2 reg = 3 \<and> bitfield_extract 3 3 reg = 7"; simp)
          apply (cases "bitfield_extract 6 2 reg = 3 \<and> bitfield_extract 3 3 reg = 0"; simp)
          apply (cases "nth_error l_bin (Suc (Suc n))"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ "(Suc (Suc n))" _], assumption, simp)
          subgoal for i2 apply (cases "nth_error l_bin (n+3)"; simp)
          apply (subst add.assoc [of pc n 3])
          apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
          subgoal for i3 apply (cases "nth_error l_bin (n+4)"; simp)
            apply (subst add.assoc [of pc n 4])
            apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
          subgoal for i4 apply (cases "nth_error l_bin (n+5)"; simp)
            apply (subst add.assoc [of pc n 5])
            apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption, simp)
            done done done done

        apply (cases "h = 41"; simp)
        apply (cases "h = 33"; simp)
        apply (cases "h = 9"; simp)
        apply (cases "h = 49"; simp)
        apply (cases "h = 211"; simp)
        apply (cases "h = 133"; simp)
        apply (cases "h = 57"; simp)
        apply (cases "h = 255"; simp)
        apply (cases "h = 199"; simp)
        apply (cases "nth_error l_bin (Suc (Suc n))"; simp)
        apply (frule list_in_list_nth_error [of _ _ _ "(Suc (Suc n))" _], assumption, simp)
        subgoal for i2 apply (cases "nth_error l_bin (n+3)"; simp)
          apply (subst add.assoc [of pc n 3])
        apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
        subgoal for i3 apply (cases "nth_error l_bin (n+4)"; simp)
          apply (subst add.assoc [of pc n 4])
          apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
        subgoal for i4 apply (cases "nth_error l_bin (n+5)"; simp)
          apply (subst add.assoc [of pc n 5])
          apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption, simp)
          done done done

        apply (cases "h = 193"; simp)
        subgoal
          apply (cases "nth_error l_bin (Suc (Suc n))"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ "(Suc (Suc n))" _], assumption, simp)
          done
        apply (cases "h = 129"; simp)
        apply (cases "bitfield_extract 6 2 reg = 3"; simp)
        apply (cases "ireg_of_u8 (bitfield_insert 3 (Suc 0) (bitfield_extract 0 3 reg) 0)"; simp)
        subgoal for dst apply (cases "nth_error l_bin (Suc (Suc n))"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ "(Suc (Suc n))" _], assumption, simp)
        subgoal for i2 apply (cases "nth_error l_bin (n+3)"; simp)
          apply (subst add.assoc [of pc n 3])
          apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
        subgoal for i3 apply (cases "nth_error l_bin (n+4)"; simp)
          apply (subst add.assoc [of pc n 4])
          apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
        subgoal for i4 apply (cases "nth_error l_bin (n+5)"; simp)
          apply (subst add.assoc [of pc n 5])
          apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption, simp)
          done done done done

        apply (cases "h = 136"; simp)
        subgoal
          apply (cases "bitfield_extract 6 2 reg = 1"; simp)
          apply (cases "nth_error l_bin (Suc (Suc n))"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ "(Suc (Suc n))" _], assumption, simp)
          done
        apply (cases "h = 139"; simp add: Let_def)
        apply (cases "bitfield_extract 6 2 reg = 1"; simp)
        subgoal
          apply (cases "nth_error l_bin (Suc (Suc n))"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ "(Suc (Suc n))" _], assumption, simp)
          done

        apply (cases "bitfield_extract 6 2 reg = 2"; simp)
        apply (cases "nth_error l_bin (Suc (Suc n))"; simp)
        apply (frule list_in_list_nth_error [of _ _ _ "(Suc (Suc n))" _], assumption, simp)
        subgoal for i2 apply (cases "nth_error l_bin (n+3)"; simp)
          apply (subst add.assoc [of pc n 3])
          apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
        subgoal for i3 apply (cases "nth_error l_bin (n+4)"; simp)
          apply (subst add.assoc [of pc n 4])
          apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
        subgoal for i4 apply (cases "nth_error l_bin (n+5)"; simp)
          apply (subst add.assoc [of pc n 5])
          apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption, simp)
          done done done done
        done

lemma list_in_list_x64_decode_op_0x81_prop: "list_in_list l_bin pc l \<Longrightarrow>
    x64_decode_op_0x81 modrm dst reg1 reg2 w r x b n l_bin = Some v \<Longrightarrow>
    x64_decode_op_0x81 modrm dst reg1 reg2 w r x b (pc+n) l = Some v"
  apply (simp add: x64_decode_op_0x81_def)
  apply (cases "modrm = 3"; simp)
  subgoal apply (cases "ireg_of_u8 dst"; simp)
    subgoal for dst apply (cases "nth_error l_bin (n+3)"; simp)
      apply (subst add.assoc [of pc n 3])
      apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
      subgoal for i1 apply (cases "nth_error l_bin (n+4)"; simp)
        apply (subst add.assoc [of pc n 4])
        apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
        subgoal for i2 apply (cases "nth_error l_bin (n+5)"; simp)
          apply (subst add.assoc [of pc n 5])
          apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption, simp)
          subgoal for i3 apply (cases "nth_error l_bin (n+6)"; simp)
            apply (subst add.assoc [of pc n 6])
            apply (frule list_in_list_nth_error [of _ _ _ "n+6" _], assumption, simp)
            done
          done
        done
      done
    done
  apply (cases "modrm = 2 \<and> reg2 = 4"; simp)
  apply (cases "nth_error l_bin (n+3)"; simp)
  apply (subst add.assoc [of pc n 3])
  apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
  subgoal for sib apply (cases "nth_error l_bin (n+4)"; simp)
    apply (subst add.assoc [of pc n 4])
    apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
    subgoal for d1 apply (cases "nth_error l_bin (n+5)"; simp)
      apply (subst add.assoc [of pc n 5])
      apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption, simp)
    subgoal for d2 apply (cases "nth_error l_bin (n+6)"; simp)
      apply (subst add.assoc [of pc n 6])
      apply (frule list_in_list_nth_error [of _ _ _ "n+6" _], assumption, simp)
    subgoal for d3 apply (cases "nth_error l_bin (n+7)"; simp)
      apply (subst add.assoc [of pc n 7])
      apply (frule list_in_list_nth_error [of _ _ _ "n+7" _], assumption, simp)
    subgoal for d4 apply (cases "u32_of_u8_list [d1, d2, d3, d4]"; simp)
    subgoal for dis apply (cases "reg1 = 0"; simp)
      apply (cases "nth_error l_bin (n+8)"; simp)
      apply (subst add.assoc [of pc n 8])
      apply (frule list_in_list_nth_error [of _ _ _ "n+8" _], assumption, simp)
      subgoal for i1 apply (cases "nth_error l_bin (n+9)"; simp)
        apply (subst add.assoc [of pc n 9])
      apply (frule list_in_list_nth_error [of _ _ _ "n+9" _], assumption, simp)
      subgoal for i2 apply (cases "nth_error l_bin (n+10)"; simp)
        apply (subst add.assoc [of pc n 10])
      apply (frule list_in_list_nth_error [of _ _ _ "n+10" _], assumption, simp)
      subgoal for i3 apply (cases "nth_error l_bin (n+11)"; simp)
        apply (subst add.assoc [of pc n 11])
        apply (frule list_in_list_nth_error [of _ _ _ "n+11" _], assumption, simp)
        done done done done done done done done done done

lemma nth_error_comm: "nth_error l_bin (a + b) = nth_error l_bin (b + a)"
  by (simp add: add.commute)

lemma list_in_list_x64_decode:
  "list_in_list l_bin pc l \<Longrightarrow> x64_decode n l_bin = Some v \<Longrightarrow> x64_decode (pc+n) l = Some v"
  apply (simp add: x64_decode_def)
  apply (cases "nth_error l_bin n"; simp)
  apply (frule list_in_list_nth_error [of _ _ _ n _], assumption, simp)
  subgoal for h
    apply (cases "h = 144"; simp)
    apply (cases "h = 153"; simp)
    apply (cases "h = 195"; simp)
    apply (cases "h = 102"; simp)
    subgoal using list_in_list_x64_decode_op_0x66_prop by blast
    apply (cases "h = 15"; simp)
    subgoal using list_in_list_x64_decode_op_0x0f_prop by blast
    apply (cases "bitfield_extract 4 4 h \<noteq> 4"; simp)
    subgoal using list_in_list_x64_decode_op_not_rex_prop by blast
    apply (cases "bitfield_extract 0 4 h = 0"; simp)
    apply (cases "nth_error l_bin (Suc n)"; simp)
    apply (frule list_in_list_nth_error [of _ _ _ "Suc n" _], assumption, simp)
    subgoal for op
      apply (cases "op = 153"; simp)
      apply (cases "bitfield_extract 3 5 op = 10"; simp)
      apply (cases "bitfield_extract 3 5 op = 11"; simp)
      apply (cases "bitfield_extract 3 5 op = 23"; simp)

      subgoal
        apply (cases "nth_error l_bin (Suc (Suc n))"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ "Suc (Suc n)" _], assumption, simp)
        subgoal for i1 apply (cases "nth_error l_bin (n+3)"; simp)
          apply (subst add.assoc [of pc n 3])
          apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
        subgoal for i2 apply (cases "nth_error l_bin (n+4)"; simp)
          apply (subst add.assoc [of pc n 4])
          apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
        subgoal for i3 apply (cases "nth_error l_bin (n+5)"; simp)
          apply (subst add.assoc [of pc n 5])
          apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption, simp)
        subgoal for i4 apply (cases "nth_error l_bin (n+6)"; simp)
          apply (subst add.assoc [of pc n 6])
          apply (frule list_in_list_nth_error [of _ _ _ "n+6" _], assumption, simp)
        subgoal for i5 apply (cases "nth_error l_bin (n+7)"; simp)
          apply (subst add.assoc [of pc n 7])
          apply (frule list_in_list_nth_error [of _ _ _ "n+7" _], assumption, simp)
        subgoal for i6 apply (cases "nth_error l_bin (n+8)"; simp)
          apply (subst add.assoc [of pc n 8])
          apply (frule list_in_list_nth_error [of _ _ _ "n+8" _], assumption, simp)
        subgoal for i7 apply (cases "nth_error l_bin (n+9)"; simp)
          apply (subst add.assoc [of pc n 9])
          apply (frule list_in_list_nth_error [of _ _ _ "n+9" _], assumption, simp)
          done done done done done done done done

        apply (cases "op = 104"; simp)
        subgoal
          apply (cases "nth_error l_bin (Suc (Suc n))"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ "Suc (Suc n)" _], assumption, simp)
          subgoal for i1 apply (cases "nth_error l_bin (n+3)"; simp)
            apply (subst add.assoc [of pc n 3])
          apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
          subgoal for i2 apply (cases "nth_error l_bin (n+4)"; simp)
            apply (subst add.assoc [of pc n 4])
          apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
          subgoal for i3 apply (cases "nth_error l_bin (n+5)"; simp)
            apply (subst add.assoc [of pc n 5])
          apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption, simp)
          done done done done 

        apply (cases "op = 15"; simp)
        subgoal
          apply (cases "nth_error l_bin (Suc (Suc n))"; simp)
          apply (frule list_in_list_nth_error [of _ _ _ "Suc (Suc n)" _], assumption, simp)
          subgoal for i1 apply (cases "bitfield_extract 3 5 i1 = 25"; simp)
            apply (cases "bitfield_extract 4 4 i1 = 4"; simp)
            apply (cases "nth_error l_bin (n+3)"; simp)
            apply (subst add.assoc [of pc n 3])
            apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
            done done

        apply (cases "nth_error l_bin (Suc (Suc n))"; simp)
        apply (frule list_in_list_nth_error [of _ _ _ "Suc (Suc n)" _], assumption, simp)
        subgoal for reg apply (cases "op = 137"; simp)
          subgoal apply (simp add: Let_def) 
            apply (cases "bitfield_extract 6 2 reg = 3"; simp)
            apply (cases "bitfield_extract 6 2 reg = 1"; simp)
              subgoal
                apply (cases "nth_error l_bin (n+3)"; simp)
                apply (subst add.assoc [of pc n 3])
                apply (subst add.assoc [of pc n 3])
                by (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)

            apply (cases "bitfield_extract 6 2 reg = 2"; simp)
            apply (cases "bitfield_extract 0 3 reg \<noteq> 4"; simp)
              subgoal
                apply (cases "nth_error l_bin (n+3)"; simp)
                apply (subst add.assoc [of pc n 3])
                apply (subst add.assoc [of pc n 3])
                apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
                subgoal for d1 apply (cases "nth_error l_bin (n+4)"; simp)
                  apply (subst add.assoc [of pc n 4])
                  apply (subst add.assoc [of pc n 4])
                apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
                subgoal for d2 apply (cases "nth_error l_bin (n+5)"; simp)
                  apply (subst add.assoc [of pc n 5])
                  apply (subst add.assoc [of pc n 5])
                apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption, simp)
                subgoal for d3 apply (cases "nth_error l_bin (n+6)"; simp)
                  apply (subst add.assoc [of pc n 6])
                  apply (subst add.assoc [of pc n 6])
                apply (frule list_in_list_nth_error [of _ _ _ "n+6" _], assumption, simp)
                subgoal for d4 apply (cases "u32_of_u8_list [d1, d2, d3, d4]"; simp)
                subgoal for dis apply (cases "ireg_of_u8 (bitfield_insert 3 (Suc 0) (bitfield_extract 3 3 reg) (bitfield_extract 2 (Suc 0) h))"; simp)
                subgoal for src apply (cases "ireg_of_u8 (bitfield_insert 3 (Suc 0) (bitfield_extract 0 3 reg) (bitfield_extract 0 (Suc 0) h))"; simp)
                subgoal for rb 
                  by argo
                done done done done done done done
              
              apply (cases "nth_error l_bin (n+3)"; simp)
              apply (subst add.assoc [of pc n 3])
              apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
              subgoal for d1 apply (cases "nth_error l_bin (n+4)"; simp)
                apply (subst add.assoc [of pc n 4])
              apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
              subgoal for d2 apply (cases "nth_error l_bin (n+5)"; simp)
                apply (subst add.assoc [of pc n 5])
              apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption, simp)
              subgoal for d3 apply (cases "nth_error l_bin (n+6)"; simp)
                apply (subst add.assoc [of pc n 6])
              apply (frule list_in_list_nth_error [of _ _ _ "n+6" _], assumption, simp)
              subgoal for d4 apply (cases "nth_error l_bin (n+7)"; simp)
                apply (subst add.assoc [of pc n 7])
              apply (frule list_in_list_nth_error [of _ _ _ "n+7" _], assumption, simp)
              done done done done done

            apply (cases "op = 135"; simp)
            subgoal 
              apply (simp add: Let_def)
              apply (cases "bitfield_extract 6 2 reg = 3"; simp)
              apply (cases "bitfield_extract 6 2 reg = 2"; simp)
              apply (cases " bitfield_extract 0 3 reg = 4"; simp)
              apply (cases "nth_error l_bin (n+3)"; simp)
              apply (subst add.assoc [of pc n 3])
              apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
              subgoal for d1 apply (cases "nth_error l_bin (n+4)"; simp)
                apply (subst add.assoc [of pc n 4])
              apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
              subgoal for d2 apply (cases "nth_error l_bin (n+5)"; simp)
                apply (subst add.assoc [of pc n 5])
              apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption, simp)
              subgoal for d3 apply (cases "nth_error l_bin (n+6)"; simp)
                apply (subst add.assoc [of pc n 6])
              apply (frule list_in_list_nth_error [of _ _ _ "n+6" _], assumption, simp)
              subgoal for d4 apply (cases "nth_error l_bin (n+7)"; simp)
                apply (subst add.assoc [of pc n 7])
              apply (frule list_in_list_nth_error [of _ _ _ "n+7" _], assumption, simp)
              done done done done done

            apply (cases "op = 99"; simp)
            apply (cases "op = 1"; simp)
            apply (cases "op = 41"; simp)
            apply (cases "op = 247"; simp)
            subgoal
              apply (simp add: Let_def)

              apply (cases "bitfield_extract 6 2 reg = 3 \<and> bitfield_extract 3 3 reg = 3"; simp)
              apply (cases "bitfield_extract 6 2 reg = 3 \<and> bitfield_extract 3 3 reg = 4"; simp)
              apply (cases "bitfield_extract 6 2 reg = 3 \<and> bitfield_extract 3 3 reg = 5"; simp)
              apply (cases "bitfield_extract 6 2 reg = 3 \<and> bitfield_extract 3 3 reg = 6"; simp)
              apply (cases "bitfield_extract 6 2 reg = 3 \<and> bitfield_extract 3 3 reg = 7"; simp)
              apply (cases "bitfield_extract 6 2 reg = 3 \<and> bitfield_extract 3 3 reg = 0"; simp)
              apply (cases "nth_error l_bin (n+3)"; simp)
              apply (subst add.assoc [of pc n 3])
              apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
              subgoal for d1 apply (cases "nth_error l_bin (n+4)"; simp)
                apply (subst add.assoc [of pc n 4])
              apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
              subgoal for d2 apply (cases "nth_error l_bin (n+5)"; simp)
                apply (subst add.assoc [of pc n 5])
              apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption, simp)
              subgoal for d3 apply (cases "nth_error l_bin (n+6)"; simp)
                apply (subst add.assoc [of pc n 6])
              apply (frule list_in_list_nth_error [of _ _ _ "n+6" _], assumption, simp)
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

              apply (cases "bitfield_extract 6 2 reg = 3 \<and> bitfield_extract 3 3 reg = 2"; simp)
              apply (cases "bitfield_extract 6 2 reg = 2 \<and> bitfield_extract 0 3 reg = 4"; simp)
              apply (cases "nth_error l_bin (n+3)"; simp)
              apply (subst add.assoc [of pc n 3])
              apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
              subgoal for sib apply (cases "nth_error l_bin (n+4)"; simp)
                apply (subst add.assoc [of pc n 4])
              apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
              subgoal for d1 apply (cases "nth_error l_bin (n+5)"; simp)
                apply (subst add.assoc [of pc n 5])
              apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption, simp)
              subgoal for d2 apply (cases "nth_error l_bin (n+6)"; simp)
                apply (subst add.assoc [of pc n 6])
              apply (frule list_in_list_nth_error [of _ _ _ "n+6" _], assumption, simp)
              subgoal for d3 apply (cases "nth_error l_bin (n+7)"; simp)
                apply (subst add.assoc [of pc n 7])
              apply (frule list_in_list_nth_error [of _ _ _ "n+7" _], assumption, simp)
              done done done done done

            apply (cases "op = 199"; simp)
            subgoal
              apply (simp only: Let_def)

              apply (cases "bitfield_extract 6 2 reg = 1"; simp)
              subgoal
                apply (cases "nth_error l_bin (4+n)"; simp)
                subgoal for i1 apply (frule list_in_list_nth_error [of _ _ _ "4 + n" i1]) apply blast
                  apply (rule subst [of "pc + (4 + n)" "4 + (pc + n)"]; simp)

                  apply (cases "nth_error l_bin (5+n)"; simp)
                  subgoal for i2 apply (frule list_in_list_nth_error [of _ _ _ "5 + n" i2]) apply blast
                  apply (rule subst [of "pc + (5 + n)" "5 + (pc + n)"]; simp)

                  apply (cases "nth_error l_bin (6+n)"; simp)
                  subgoal for i3 apply (frule list_in_list_nth_error [of _ _ _ "6 + n" i3]) apply blast
                  apply (rule subst [of "pc + (6 + n)" "6 + (pc + n)"]; simp)

                  apply (cases "nth_error l_bin (7+n)"; simp)
                  subgoal for i4 apply (frule list_in_list_nth_error [of _ _ _ "7 + n" i4]) apply blast
                  apply (rule subst [of "pc + (7 + n)" "7 + (pc + n)"]; simp)
                  apply (cases "ireg_of_u8 (bitfield_insert 3 (Suc 0) (bitfield_extract 0 3 reg) (bitfield_extract 0 (Suc 0) h))"; simp)
                  subgoal for dst apply (cases "u32_of_u8_list [i1, i2, i3, i4]"; simp)
                  subgoal for imm apply (cases "bitfield_extract 3 3 reg = 0 \<and> bitfield_extract 2 (Suc 0) h = 0  \<and> bitfield_extract (Suc 0) (Suc 0) h = 0"; simp)
                    apply (cases "bitfield_extract 3 (Suc 0) h = 1"; simp)
                    apply (cases "nth_error l_bin (n+3)"; simp)
                    apply (subst add.assoc [of pc n 3])
                    apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
                    done done done done done done done

                  apply (cases "bitfield_extract 6 2 reg = 2"; simp)
                  subgoal
                    apply (cases "nth_error l_bin (7+n)"; simp)
                    apply (frule list_in_list_nth_error [of _ _ _ "7+n" _], assumption)
                    apply (rule subst [of "pc + (7 + n)" "7 + (pc + n)"]; simp)

                    subgoal for i1
                      apply (cases "nth_error l_bin (8+n)"; simp)
                      subgoal for i2 apply (frule list_in_list_nth_error [of _ _ _ "8+n" i2]) apply blast
                        apply (rule subst [of "pc + (8 + n)" "8 + (pc + n)"]; simp)

                      apply (cases "nth_error l_bin (9+n)"; simp)
                      subgoal for i3 apply (frule list_in_list_nth_error [of _ _ _ "9+n" i3]) apply blast
                        apply (rule subst [of "pc + (9 + n)" "9 + (pc + n)"]; simp)

                      apply (cases "nth_error l_bin (10+n)"; simp)
                      subgoal for i4 apply (frule list_in_list_nth_error [of _ _ _ "10+n" i4]) apply blast
                        apply (rule subst [of "pc + (10 + n)" "10 + (pc + n)"]; simp)

                        apply (cases "ireg_of_u8 (bitfield_insert 3 (Suc 0) (bitfield_extract 0 3 reg) (bitfield_extract 0 (Suc 0) h))"; simp)
                        subgoal for dst apply (cases "u32_of_u8_list [i1, i2, i3, i4]"; simp)
                          apply (cases "bitfield_extract 3 3 reg = 0 \<and> bitfield_extract 2 (Suc 0) h = 0  \<and> bitfield_extract (Suc 0) (Suc 0) h = 0"; simp)

                          apply (cases "nth_error l_bin (n+3)"; simp)
                          apply (subst add.assoc [of pc n 3])
                          apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
                          subgoal for sib apply (cases "nth_error l_bin (n+4)"; simp)
                            apply (subst add.assoc [of pc n 4])
                          apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
                          subgoal for d1 apply (cases "nth_error l_bin (n+5)"; simp)
                            apply (subst add.assoc [of pc n 5])
                          apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption, simp)
                          subgoal for d2 apply (cases "nth_error l_bin (n+6)"; simp)
                            apply (subst add.assoc [of pc n 6])
                          apply (frule list_in_list_nth_error [of _ _ _ "n+6" _], assumption, simp)
                            done done done done done done done done done

                  apply (cases "nth_error l_bin (n+3)"; simp)
                  apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption)
                  apply (subst add.assoc [of pc n 3], simp)
                  subgoal for i1 apply (cases "nth_error l_bin (n+4)"; simp)
                  apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption)
                    apply (subst add.assoc [of pc n 4], simp)
                  subgoal for i2 apply (cases "nth_error l_bin (n+5)"; simp)
                  apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption)
                    apply (subst add.assoc [of pc n 5], simp)
                  subgoal for i3 apply (cases "nth_error l_bin (n+6)"; simp)
                  apply (frule list_in_list_nth_error [of _ _ _ "n+6" _], assumption)
                    apply (subst add.assoc [of pc n 6], simp)
                  subgoal for i4 apply (cases "ireg_of_u8 (bitfield_insert 3 (Suc 0) (bitfield_extract 0 3 reg) (bitfield_extract 0 (Suc 0) h))"; simp)
                  subgoal for dst apply (cases "u32_of_u8_list [i1, i2, i3, i4]"; simp)
                  subgoal for imm apply (cases "bitfield_extract 3 3 reg = 0 \<and> bitfield_extract 2 (Suc 0) h = 0  \<and> bitfield_extract (Suc 0) (Suc 0) h = 0"; simp)
                  apply (cases "bitfield_extract 6 2 reg = 3"; simp)
                  apply (cases "bitfield_extract 3 (Suc 0) h = 0"; simp)
                    done done done done done done done

                  apply (cases "op = 129"; simp)
                  subgoal 
                    apply (simp add: Let_def)
                    using list_in_list_x64_decode_op_0x81_prop by blast

                  apply (cases "op = 193"; simp)
                  subgoal
                    apply (cases "nth_error l_bin (n+3)"; simp)
                    apply (subst add.assoc [of pc n 3])
                    apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
                    done

                  apply (cases "op = 136"; simp)
                  subgoal
                    apply (cases "bitfield_extract 6 2 reg = 1 \<and> bitfield_extract (Suc 0) (Suc 0) h = 0 \<and> bitfield_extract 3 (Suc 0) h = 0"; simp)
                    apply (cases "nth_error l_bin (n+3)"; simp)
                    apply (subst add.assoc [of pc n 3])
                    apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
                    done

                  apply (cases "op = 139"; simp)
                  subgoal
                    apply (simp only: Let_def)
                    apply (cases "bitfield_extract 6 2 reg = 1 \<and> bitfield_extract (Suc 0) (Suc 0) h = 0"; simp)
                    subgoal
                      apply (cases "nth_error l_bin (n+3)"; simp)
                      apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption)
                      apply (subst add.assoc [of pc n 3], simp)
                      apply (subst add.assoc [of pc n 3], simp)
                      subgoal for dis apply (cases "ireg_of_u8 (bitfield_insert 3 (Suc 0) (bitfield_extract 3 3 reg) (bitfield_extract 2 (Suc 0) h))"; simp)
                        subgoal for src apply (cases "ireg_of_u8 (bitfield_insert 3 (Suc 0) (bitfield_extract 0 3 reg) (bitfield_extract 0 (Suc 0) h))"; simp)
                          subgoal for dst by force 
                    done done done

                  apply (cases "bitfield_extract 6 2 reg = 2"; simp)
                  apply (cases "bitfield_extract 0 3 reg \<noteq> 4"; simp)
                  subgoal
                    apply (cases "nth_error l_bin (n+3)"; simp)
                    apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption)
                    apply (subst add.assoc [of pc n 3], simp)
                    apply (subst add.assoc [of pc n 3], simp)
                    apply (cases "nth_error l_bin (n+4)"; simp)
                    apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption)
                    apply (subst add.assoc [of pc n 4], simp)
                    apply (subst add.assoc [of pc n 4], simp)
                    apply (cases "nth_error l_bin (n+5)"; simp)
                    apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption)
                    apply (subst add.assoc [of pc n 5], simp)
                    apply (subst add.assoc [of pc n 5], simp)
                    apply (cases "nth_error l_bin (n+6)"; simp)
                    apply (frule list_in_list_nth_error [of _ _ _ "n+6" _], assumption)
                    apply (subst add.assoc [of pc n 6], simp)
                    apply (subst add.assoc [of pc n 6], simp)
                    subgoal for d1 d2 d3 d4 apply (cases "u32_of_u8_list [d1, d2, d3, d4]"; simp)
                    subgoal for dis apply (cases "ireg_of_u8 (bitfield_insert 3 (Suc 0) (bitfield_extract 3 3 reg) (bitfield_extract 2 (Suc 0) h))"; simp)
                    subgoal for src apply (cases "ireg_of_u8 (bitfield_insert 3 (Suc 0) (bitfield_extract 0 3 reg) (bitfield_extract 0 (Suc 0) h))"; simp)
                    subgoal for dst apply (cases "bitfield_extract (Suc 0) (Suc 0) h = 0"; simp)
                      by argo
                    done done done done

                  apply (cases "nth_error l_bin (n+3)"; simp)
                  apply (subst add.assoc [of pc n 3])
                  apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
                  apply (cases "nth_error l_bin (n+4)"; simp)
                  apply (subst add.assoc [of pc n 4])
                  apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
                  apply (cases "nth_error l_bin (n+5)"; simp)
                  apply (subst add.assoc [of pc n 5])
                  apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption, simp)
                  apply (cases "nth_error l_bin (n+6)"; simp)
                  apply (subst add.assoc [of pc n 6])
                  apply (frule list_in_list_nth_error [of _ _ _ "n+6" _], assumption, simp)
                  apply (cases "nth_error l_bin (n+7)"; simp)
                  apply (subst add.assoc [of pc n 7])
                  apply (frule list_in_list_nth_error [of _ _ _ "n+7" _], assumption, simp)
                  done

                apply (cases "op = 141"; simp)
                subgoal
                  apply (simp add: Let_def)
                  apply (cases "bitfield_extract 6 2 reg = 1"; simp)
                  subgoal
                    apply (cases "nth_error l_bin (n+3)"; simp)
                    apply (subst add.assoc [of pc n 3])
                    apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
                    done
                  apply (cases "bitfield_extract 6 2 reg = 2"; simp)
                  subgoal
                    apply (cases "nth_error l_bin (n+3)"; simp)
                    apply (subst add.assoc [of pc n 3])
                    apply (frule list_in_list_nth_error [of _ _ _ "n+3" _], assumption, simp)
                    apply (cases "nth_error l_bin (n+4)"; simp)
                    apply (subst add.assoc [of pc n 4])
                    apply (frule list_in_list_nth_error [of _ _ _ "n+4" _], assumption, simp)
                    apply (cases "nth_error l_bin (n+5)"; simp)
                    apply (subst add.assoc [of pc n 5])
                    apply (frule list_in_list_nth_error [of _ _ _ "n+5" _], assumption, simp)
                    apply (cases "nth_error l_bin (n+6)"; simp)
                    apply (subst add.assoc [of pc n 6])
                    apply (frule list_in_list_nth_error [of _ _ _ "n+6" _], assumption, simp)
                    done done done done

                  done
                done

end