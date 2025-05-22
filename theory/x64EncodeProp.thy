theory x64EncodeProp
imports
  Main
  rBPFCommType
  x64Assembler
begin

lemma x64_encode_length_ge_1: "x64_encode ins = Some l \<Longrightarrow> 1 \<le> length l"
  apply (cases ins; simp add: Let_def if_split_asm)
  subgoal for x1 x2
    by (cases "construct_rex_to_u8 False (and (u8_of_ireg x2) 8 \<noteq> 0) False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; simp; auto)
  subgoal by auto
  subgoal for x1 x2
    by (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; simp; auto)
  subgoal by auto
  subgoal for x1 x2 x3
    apply (cases x2; simp)
    subgoal for a1 a2 a3
      apply (cases a1; simp)
      subgoal for y1
        apply (cases a2; simp add: Let_def)
        subgoal
          apply (cases "a3 \<le> 127 \<or> - 128 \<le> a3"; simp add: Let_def)
          subgoal
            apply (cases "construct_rex_to_u8 (x3 = M64) (and (u8_of_ireg x1) 8 \<noteq> 0) False (and (u8_of_ireg y1) 8 \<noteq> 0) = 64"; cases x3; simp; auto)
            done
          apply (cases "and (u8_of_ireg y1) 7 \<noteq> 4"; simp add: Let_def)
            apply (cases "construct_rex_to_u8 (x3 = M64) (and (u8_of_ireg x1) 8 \<noteq> 0) False (and (u8_of_ireg y1) 8 \<noteq> 0) = 64"; cases x3; simp; auto)
            done
          subgoal for z
            apply (cases z; simp)
            subgoal for z1 z2
              apply (cases "3 < z2 \<or> x3 \<noteq> M64"; simp)
              by auto
            done
          done
        done
      done
  subgoal for x1 x2 x3
    apply (cases x1; simp)
    subgoal for a1 a2 a3
      apply (cases a1; simp)
      subgoal for y1
        apply (cases a2; simp add: Let_def)
        subgoal
          apply (cases "a3 \<le> 127 \<or> - 128 \<le> a3"; simp add: Let_def)
          subgoal
            apply (cases "construct_rex_to_u8 (x3 = M64) (and (u8_of_ireg x2) 8 \<noteq> 0) False (and (u8_of_ireg y1) 8 \<noteq> 0) = 64"; cases x3; simp; auto)
            done
          apply (cases "and (u8_of_ireg y1) 7 \<noteq> 4"; simp add: Let_def)
            apply (cases "construct_rex_to_u8 (x3 = M64) (and (u8_of_ireg x2) 8 \<noteq> 0) False (and (u8_of_ireg y1) 8 \<noteq> 0) = 64"; cases x3; simp; auto)
            done
          subgoal for z
            apply (cases z; simp)
            subgoal for z1 z2
              apply (cases "3 < z2 \<or> x3 \<noteq> M64"; simp)
              by auto
            done
          done
        done
      done
  subgoal for x1 x2 x3
    apply (cases x3; simp)
    apply (cases x1; simp)
      subgoal for y1 y2 y3
        apply (cases y1; simp add: Let_def)
        subgoal for z
          apply (cases y2; simp add: Let_def)
          subgoal
            apply (cases "y3 \<le> 127 \<or> - 128 \<le> y3"; simp; auto)
            done
          done
        done
      done
  subgoal for x1 x2 x3
    by (cases "construct_rex_to_u8 False (and (u8_of_ireg x2) 8 \<noteq> 0) False (and (u8_of_ireg x3) 8 \<noteq> 0) = 64"; simp; auto)
  subgoal by auto
  subgoal by auto
  subgoal for x1 x2 x3
    apply (cases x3; simp)
    apply (cases x2; simp)
    subgoal for y1 y2 y3
      apply (cases y1; simp)
      subgoal for z
        apply (cases y2; simp)
        subgoal for k
          apply (cases k; simp)
          subgoal for k1 k2
            apply (cases "3 < k2"; simp; auto)
            done
          done
        done
      done
    done
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for x1 x2
    apply (cases x2; simp)
    subgoal for y1 y2 y3
      apply (cases y1; simp)
      subgoal for z1
        apply (cases y2; simp add: Let_def)
        apply (cases "y3 \<le> 127 \<or> - 128 \<le> y3"; simp; auto)
        done 
      done
    done
  subgoal for x1
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal by auto
  subgoal by auto
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False (and (u8_of_ireg x2) 8 \<noteq> 0) False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal for x1 x2 x3
    apply (cases x3; auto)
    apply (cases x1; auto)
    subgoal for y1 y2 y3
      apply (cases y1; auto)
      subgoal for z
        apply (cases y2; auto)
        subgoal for k1 k2
          apply (cases "3 < k2"; auto)
          done
        done
      done
    done
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False (and (u8_of_ireg x2) 8 \<noteq> 0) False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False (and (u8_of_ireg x2) 8 \<noteq> 0) False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal for x1
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done

  subgoal by auto
  subgoal for x1
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal by auto
  subgoal for x1
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal by auto
  subgoal for x1
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal by auto
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False (and (u8_of_ireg x2) 8 \<noteq> 0) False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal by auto
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False (and (u8_of_ireg x2) 8 \<noteq> 0) False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal by auto
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False (and (u8_of_ireg x2) 8 \<noteq> 0) False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal by auto
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal by auto
  subgoal for x1
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal by auto
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal by auto
  subgoal for x1
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal by auto
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal by auto
  subgoal for x1
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal by auto
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal for x1
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal by auto
  subgoal for x1
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal by auto
  subgoal for x1 x2
    apply (cases x2; auto)
    apply (cases x1; auto)
    subgoal for y1 y2 y3
      apply (cases y1; auto)
      subgoal for z1
        apply (cases y2; auto)
        subgoal for k1 k2
          apply (cases "3 < k2"; auto)
          done
        done
      done
    done
  subgoal for x1
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False (and (u8_of_ireg x2) 8 \<noteq> 0) False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done

  subgoal by auto
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal by auto
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False (and (u8_of_ireg x1) 8 \<noteq> 0) False (and (u8_of_ireg x2) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal by auto
  subgoal for x1 x2
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for x1
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg x1) 8 \<noteq> 0) = 64"; auto)
    done
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

end