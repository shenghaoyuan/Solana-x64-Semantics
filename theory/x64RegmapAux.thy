theory x64RegmapAux
imports
  Main       
  rBPFCommType Val Mem x64Syntax
  x64Disassembler  
begin

definition intlist_to_reg_ir :: "x64_bin  \<Rightarrow> int list  \<Rightarrow> ireg \<Rightarrow> val" where
" intlist_to_reg_ir lbin lr = ( 
  case (x64_decode 0 lbin) of Some (_, ins) \<Rightarrow> 
    (\<lambda> r.
      case r of RAX \<Rightarrow> Vlong (of_int (lr!0)) |
                RBX \<Rightarrow> Vlong (of_int (lr!1)) |
                RCX \<Rightarrow> (case ins of 
                          Pshrq_r _ \<Rightarrow> Vbyte (of_int (lr!2)) 
                        | Pshlq_r _ \<Rightarrow> Vbyte (of_int (lr!2)) 
                        | Psarq_r _ \<Rightarrow> Vbyte (of_int (lr!2))
                        | _ \<Rightarrow> Vlong (of_int (lr!2))) |
                RDX \<Rightarrow> Vlong (of_int (lr!3)) |
                RSI \<Rightarrow> Vlong (of_int (lr!4)) |
                RDI \<Rightarrow> Vlong (of_int (lr!5)) |
                RBP \<Rightarrow> Vlong (of_int (lr!6)) |
                RSP \<Rightarrow> Vlong (of_int (lr!7)) |
                R8  \<Rightarrow> Vlong (of_int (lr!8)) |
                R9  \<Rightarrow> Vlong (of_int (lr!9)) |
                R10 \<Rightarrow> Vlong (of_int (lr!10)) |
                R11 \<Rightarrow> Vlong (of_int (lr!11)) |
                R12 \<Rightarrow> Vlong (of_int (lr!12)) |
                R13 \<Rightarrow> Vlong (of_int (lr!13)) |
                R14 \<Rightarrow> Vlong (of_int (lr!14)) |
                R15 \<Rightarrow> Vlong (of_int (lr!15)) ) | 
   None \<Rightarrow> 
    (\<lambda> r. Vundef)
)"




definition intlist_to_reg_ir_32 :: "x64_bin  \<Rightarrow> int list  \<Rightarrow> ireg \<Rightarrow> val" where
" intlist_to_reg_ir_32 lbin lr  = ( 
  case (x64_decode 0 lbin) of Some (_, ins) \<Rightarrow> 
    (\<lambda> r.
      case r of RAX \<Rightarrow> Vint (of_int (lr!0)) |
                RBX \<Rightarrow> Vint (of_int (lr!1)) |
                RCX \<Rightarrow> (case ins of 
                          Pshrl_r _ \<Rightarrow> Vbyte (of_int (lr!2)) 
                        | Pshll_r _ \<Rightarrow> Vbyte (of_int (lr!2)) 
                        | Psarl_r _ \<Rightarrow> Vbyte (of_int (lr!2))
                        | _ \<Rightarrow> Vint (of_int (lr!2))) |
                RDX \<Rightarrow> Vint (of_int (lr!3)) |
                RSI \<Rightarrow> Vint (of_int (lr!4)) |
                RDI \<Rightarrow> Vint (of_int (lr!5)) |
                RBP \<Rightarrow> Vint (of_int (lr!6)) |
                RSP \<Rightarrow> Vint (of_int (lr!7)) |
                R8  \<Rightarrow> Vint (of_int (lr!8)) |
                R9  \<Rightarrow> Vint (of_int (lr!9)) |
                R10 \<Rightarrow> Vint (of_int (lr!10)) |
                R11 \<Rightarrow> Vint (of_int (lr!11)) |
                R12 \<Rightarrow> Vint (of_int (lr!12)) |
                R13 \<Rightarrow> Vint (of_int (lr!13)) |
                R14 \<Rightarrow> Vint (of_int (lr!14)) |
                R15 \<Rightarrow> Vint (of_int (lr!15)) ) | 
   None \<Rightarrow> 
    (\<lambda> r. Vundef)
    
)"



definition intlist_to_reg_ir_16 :: "x64_bin  \<Rightarrow> int list  \<Rightarrow> ireg \<Rightarrow> val" where
" intlist_to_reg_ir_16 lbin lr = ( 
  case (x64_decode 0 lbin) of Some (_, ins) \<Rightarrow> 
    (\<lambda> r.
      case r of RAX \<Rightarrow> Vshort (of_int (lr!0)) |
                RBX \<Rightarrow> Vshort (of_int (lr!1)) |
                RCX \<Rightarrow> Vshort (of_int (lr!2)) |
                RDX \<Rightarrow> Vshort (of_int (lr!3)) |
                RSI \<Rightarrow> Vshort (of_int (lr!4)) |
                RDI \<Rightarrow> Vshort (of_int (lr!5)) |
                RBP \<Rightarrow> Vshort (of_int (lr!6)) |
                RSP \<Rightarrow> Vshort (of_int (lr!7)) |
                R8  \<Rightarrow> Vshort (of_int (lr!8)) |
                R9  \<Rightarrow> Vshort (of_int (lr!9)) |
                R10 \<Rightarrow> Vshort (of_int (lr!10)) |
                R11 \<Rightarrow> Vshort (of_int (lr!11)) |
                R12 \<Rightarrow> Vshort (of_int (lr!12)) |
                R13 \<Rightarrow> Vshort (of_int (lr!13)) |
                R14 \<Rightarrow> Vshort (of_int (lr!14)) |
                R15 \<Rightarrow> Vshort (of_int (lr!15)) ) | 
   None \<Rightarrow> 
    (\<lambda> r. Vundef)
    
)"

definition intlist_to_reg_cr :: "int list  \<Rightarrow> crbit \<Rightarrow> val" where
" intlist_to_reg_cr lc =  ( \<lambda> r. 
    case r of ZF \<Rightarrow> Vint (of_int (lc!0)) |
              CF \<Rightarrow> Vint (of_int (lc!1)) |
              PF \<Rightarrow> Vint (of_int (lc!2)) |
              SF \<Rightarrow> Vint (of_int (lc!3)) |
              OF \<Rightarrow> Vint (of_int (lc!4)) )
"


end