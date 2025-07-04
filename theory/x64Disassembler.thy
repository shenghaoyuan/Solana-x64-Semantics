theory x64Disassembler
imports
  Main
  rBPFCommType
  x64Syntax
begin

(*
value "[(1::nat)]!(0::nat)"

value "[(1::nat)]!(1::nat)" returns an error, we should have a nth_error? *)

definition x64_decode_op_0x66 :: "nat \<Rightarrow> x64_bin \<Rightarrow> (nat * instruction) option" where
"x64_decode_op_0x66 pc l_bin = (
  case nth_error l_bin (pc+1) of None \<Rightarrow> None | Some h1 \<Rightarrow>
    if bitfield_extract 4 4 h1 \<noteq> 0b0100 then  
      \<comment> \<open> R7.1 [legacy + opcode + modrm + imm] \<close>
      case nth_error l_bin (pc+2) of None \<Rightarrow> None | Some reg \<Rightarrow>
      let modrm = bitfield_extract 6 2 reg in
      let reg1  = bitfield_extract 3 3 reg in
      let reg2  = bitfield_extract 0 3 reg in
      let src   = bitfield_insert 3 1 reg1 0 in
      let dst   = bitfield_insert 3 1 reg2 0 in
        if h1 = 0xc1 then 
       \<comment> \<open> P2887 `ROL : register by immediate count` -> `0x66 1100 000w : 11 000 reg : imm8` \<close>
          case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some imm \<Rightarrow>
            if modrm = 0b11 \<and> src = 0b000 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                Some (4, Prolw_ri dst imm))
            else None
      else if h1 = 0x81 then
        if modrm = 0b11 then
          case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
            case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some i1 \<Rightarrow> (
            case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some i2 \<Rightarrow> (
              case u16_of_u8_list [i1,i2] of None \<Rightarrow> None |
                Some imm \<Rightarrow> 
                  \<comment> \<open> P2876 `ADD imm16 to reg16` -> ` 0x66 1000 00sw : 11 000 reg : imm16` \<close>
                  if reg1 = 0b000 then
                    Some (5, Paddw_ri dst imm)
                  else None) ))
        else None
      \<comment> \<open> R7.2 [legacy + opcode + modrm + displacement] \<close>
        else if h1 = 0x89 then 
          \<comment> \<open> P2882 ` MOV: reg to memory`  ->  `66H 0100 0RXB : 1000 1001 : mod reg r/m `\<close>
            if modrm = 0b01  then
              case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some dis \<Rightarrow> ( \<comment> \<open> displacement8 \<close> 
                case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
                case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> ( 
                    Some (4, Pmov_mr (Addrmode (Some dst) None (scast dis)) src  M16))))
            else None
        else None
    else  
      let w = bitfield_extract 3 1 h1 in
      let r = bitfield_extract 2 1 h1 in
      let x = bitfield_extract 1 1 h1 in
      let b = bitfield_extract 0 1 h1 in (
        case nth_error l_bin (pc+2) of None \<Rightarrow> None | Some op \<Rightarrow> (
        case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some reg \<Rightarrow> (
        let modrm = bitfield_extract 6 2 reg in
        let reg1  = bitfield_extract 3 3 reg in
        let reg2  = bitfield_extract 0 3 reg in
        let src   = bitfield_insert 3 1 reg1 r in
        let dst   = bitfield_insert 3 1 reg2 b in
          \<comment> \<open> R7.3 [legacy + rex + opcode + modrm + imm] \<close>
          if op = 0xc1 then 
          \<comment> \<open> P2887 `ROL : register by immediate count` -> `0x66 1100 000w : 11 000 reg : imm8` \<close>
            case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some imm \<Rightarrow> (
              if modrm = 0b11 \<and> src = 0b000 then
                case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                  if w = 0 \<and> r = 0 \<and> x = 0 then
                    Some (5, Prolw_ri dst imm)
                  else None)
              else None )
          else if op = 0x81 then
            if modrm = 0b11 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some i1 \<Rightarrow> (
                case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some i2 \<Rightarrow> (
                  case u16_of_u8_list [i1,i2] of None \<Rightarrow> None |
                    Some imm \<Rightarrow> 
                      \<comment> \<open> P2876 `ADD imm16 to reg16` -> ` 0x66 1000 00sw : 11 000 reg : imm16` \<close>
                      if reg1 = 0b000 \<and> w = 0 \<and> r = 0 \<and> x = 0 then
                        Some (6, Paddw_ri dst imm)
                      else None) ))
            else None
          \<comment> \<open> R7.4 [legacy + rex + opcode + modrm + displacement\<close>
          else if op = 0x89 then 
          \<comment> \<open> P2882 ` MOV: reg to memory`  ->  `66H 0100 0RXB : 1000 1001 : mod reg r/m `\<close>
            if modrm = 0b01  then
              case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some dis \<Rightarrow> (  \<comment> \<open> displacement8 \<close>
                  case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
                  case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> ( 
                    if w = 0 \<and> x = 0 then
                      Some (5, Pmov_mr (Addrmode (Some dst) None (scast dis)) src  M16)
                    else None )))
            else None
          else None )))
)"

definition x64_decode_op_0x0f :: "nat \<Rightarrow> x64_bin \<Rightarrow> (nat * instruction) option" where
"x64_decode_op_0x0f pc l_bin = (
  case nth_error l_bin (pc+1) of None \<Rightarrow> None | Some op \<Rightarrow>
    \<comment> \<open> R8.1 [escape + opcode]          
    if op = 0x31 then 
      Some (2, Prdtsc)\<close>
    \<comment> \<open> P2877 `BSWAP: register `   -> `0000 1111 : 1100 1 reg` \<close>
    if bitfield_extract 3 5 op = 0b11001 then
      let reg2 = bitfield_extract 0 3 op in
      let dst  = bitfield_insert 3 1 reg2 0 in
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          Some (2, Pbswapl dst))
    \<comment> \<open> R8.2 [escape + opcode + modrm] \<close>
    \<comment> \<open> P2919 `MOVcc : resgister2  to resgister1 ` -> `0100 0R0B 0000 1111: 0100 tttn : 11 reg1 reg2` \<close>
    else if bitfield_extract 4 4 op = 0b0100 then
      let flag = (bitfield_extract 0 4 op) in 
      case nth_error l_bin (pc+2) of None \<Rightarrow> None | Some reg \<Rightarrow>
      let modrm = bitfield_extract 6 2 reg in
      let reg1  = bitfield_extract 3 3 reg in
      let reg2  = bitfield_extract 0 3 reg in
      let src   = bitfield_insert 3 1 reg1 0 in
      let dst   = bitfield_insert 3 1 reg2 0 in
        if modrm = 0b11 then
          case cond_of_u8 flag of None \<Rightarrow> None | Some t \<Rightarrow>(
          case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
          case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
            Some (3, Pcmovl t src dst))))
        else None
    \<comment> \<open> R8.3 [escape + opcode + displacement] \<close>
    \<comment> \<open> P2880 `JCC: full displacement` -> `0000 1111 : 1000 tttn : full displacement` \<close>
    else if bitfield_extract 4 4 op = 0b1000 then
      let flag = (bitfield_extract 0 4 op) in
      case nth_error l_bin (pc+2) of None \<Rightarrow> None | Some i1 \<Rightarrow> (
      case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some i2 \<Rightarrow> (
      case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some i3 \<Rightarrow> (
      case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some i4 \<Rightarrow> (
        case u32_of_u8_list [i1,i2,i3,i4] of None \<Rightarrow> None | Some d \<Rightarrow>(
        case cond_of_u8 flag of None \<Rightarrow> None | Some t \<Rightarrow>(
          Some(6, Pjcc t d))) ))))
    else None
)"


definition x64_decode_op_not_rex :: "u8 \<Rightarrow> nat \<Rightarrow> x64_bin \<Rightarrow> (nat * instruction) option" where
"x64_decode_op_not_rex h pc l_bin = (
    \<comment> \<open> R1 [opcode] \<close>
    \<comment> \<open> P2885 `PUSH: qwordregister (alternate encoding)`   -> ` 0100 W00BS : 0101 0 reg64` \<close>
  if bitfield_extract 3 5 h = 0b01010 then
    let reg2 = bitfield_extract 0 3 h in
    let dst  = bitfield_insert 3 1 reg2 0 in
    case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
    Some (1, Ppushl_r dst))
    \<comment> \<open> P2885 `POP: qwordregister (alternate encoding)`   -> ` 0100 W00B : 0101 1 reg64 ` \<close>
    else if bitfield_extract 3 5 h = 0b01011 then
    let reg2 = bitfield_extract 0 3 h in
    let dst  = bitfield_insert 3 1 reg2 0 in
    case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
    Some (1, Ppopl dst))
    \<comment> \<open> R4 [opcode + displacement] \<close>
    else if h = 0xe8 then   
    \<comment> \<open> P2878 `CALL: direct`   -> `1110 1000 : displacement32` \<close>
    case nth_error l_bin (pc+1) of None \<Rightarrow> None | Some i1 \<Rightarrow> (
    case nth_error l_bin (pc+2) of None \<Rightarrow> None | Some i2 \<Rightarrow> (
    case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some i3 \<Rightarrow> (
    case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some i4 \<Rightarrow> (
    case u32_of_u8_list [i1,i2,i3,i4] of None \<Rightarrow> None |
      Some d \<Rightarrow> ( Some (5, Pcall_i (scast d))) ))))
    else if h = 0xe9 then
    \<comment> \<open> P2881 `JMP: direct` -> `1110 1001 : displacement32` \<close>
    case nth_error l_bin (pc+1) of None \<Rightarrow> None | Some i1 \<Rightarrow> (
    case nth_error l_bin (pc+2) of None \<Rightarrow> None | Some i2 \<Rightarrow> (
    case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some i3 \<Rightarrow> (
    case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some i4 \<Rightarrow> (
    case u32_of_u8_list [i1,i2,i3,i4] of None \<Rightarrow> None |
      Some d \<Rightarrow> ( Some (5, Pjmp (scast d))) ))))
    else
    case nth_error l_bin (pc+1) of None \<Rightarrow> None | Some reg \<Rightarrow>
    let modrm = bitfield_extract 6 2 reg in
    let reg1  = bitfield_extract 3 3 reg in
    let reg2  = bitfield_extract 0 3 reg in
    let src   = bitfield_insert 3 1 reg1 0 in
    let dst   = bitfield_insert 3 1 reg2 0 in
    \<comment> \<open> R2 [opcode + modrm] \<close>
    if h = 0x89 then 
    \<comment> \<open> P2887 `MOV register1 to register2` -> `0100 0R0B : 1000 1001 : 11 reg1 reg2` \<close>
      if modrm = 0b11 then
        case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          Some (2, Pmovl_rr dst src)))
      else if modrm = 0b01 then
        \<comment> \<open> P2882 ` MOV: reg to memory` ->  `0100 WRXB : 1000 1001 : mod reg r/m` \<close>
        \<comment> \<open> P2882 ` MOV: qwordregister to memory64` ->  `0100 1RXB 1000 1001 : mod qwordreg r/m` \<close>
        case nth_error l_bin (pc+2) of None \<Rightarrow> None | Some dis \<Rightarrow> ( \<comment> \<open> displacement8 \<close>
          case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
          case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> ( 
              Some (3, Pmov_mr (Addrmode (Some dst) None (scast dis)) src M32))))
      else if modrm = 0b10 then 
        case nth_error l_bin (pc+2) of None \<Rightarrow> None | Some d1 \<Rightarrow> (
        case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some d2 \<Rightarrow> (
        case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some d3 \<Rightarrow> (
        case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some d4 \<Rightarrow> (
          case u32_of_u8_list [d1,d2,d3,d4] of None \<Rightarrow> None | Some dis \<Rightarrow>(
          case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
          case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
             Some (6, Pmov_mr (Addrmode (Some dst) None dis) src M32)))) ))))
      else None
    else if h = 0x01 then
    \<comment> \<open> P2876 `ADD register1 to register2` -> `0100 0R0B : 0000 000w : 11 reg1 reg2` \<close>
      if modrm = 0b11 then
        case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          Some (2, Paddl_rr dst src))) 
      else None
    \<comment> \<open> P2884 `NEG  register2`   -> `0100 100B : 1111 0111 : 11011reg` \<close>
    else if h = 0xf7 then
      if modrm = 0b11 \<and> reg1 = 0b011 then 
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          Some (2, Pnegl dst))
    \<comment> \<open> P2884 `MUL  AL, AX, or EAX with register2` -> ` 0100 000B : 1111 011w : 11 100 reg` \<close>
      else if modrm = 0b11 \<and> reg1 = 0b100 then
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          Some (2, Pmull_r dst))
    \<comment> \<open> P2880 `IMUL AL, AX, or EAX with register2` -> ` 0100 000B : 1111 011w : 11 101 reg` \<close>
      else if modrm = 0b11 \<and> reg1 = 0b101 then
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
           Some (2, Pimull_r dst))
      else if modrm = 0b11 \<and> reg1 = 0b110 then
    \<comment> \<open> P2879 `DIV  AL, AX, or EAX by register2`   -> ` 0100 000B : 1111 011w : 11 110 reg` \<close>
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
           Some (2, Pdivl_r dst))
      else if modrm = 0b11 \<and> reg1 = 0b111 then
    \<comment> \<open> P2879 `IDIV AL, AX, or EAX by register2`   -> ` 0100 000B : 1111 011w : 11 111 reg` \<close>
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
           Some (2, Pidivl_r dst))
     \<comment> \<open> P2892 `TEST: immediate and register`   -> `  1111 011w : 11 000 reg : imm ` \<close>
      else if modrm = 0b11 \<and> reg1 = 0b000 then
        case nth_error l_bin (pc+2) of None \<Rightarrow> None | Some i1 \<Rightarrow> (
        case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some i2 \<Rightarrow> (
        case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some i3 \<Rightarrow> (
        case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some i4 \<Rightarrow> (
          case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              case u32_of_u8_list [i1, i2, i3,i4] of None \<Rightarrow> None |
                Some imm \<Rightarrow> 
                    Some (6, Ptestl_ri dst imm)) ))))
      else None
    \<comment> \<open> P2891 `SUB register1 from register2` -> `0100 WR0B : 0010 100w : 11 reg1 reg2` \<close> 
    else if h = 0x29 then
      if modrm = 0b11 then (
        case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          Some (2, Psubl_rr dst src) )))
      else None
    \<comment> \<open> P2876 `AND register1 to register2` -> ` 0010 000w : 11 reg1 reg2 ` \<close>
    else if h = 0x21 then
      if modrm = 0b11 then (
        case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
           Some (2, Pandl_rr dst src))) ) 
      else None
    \<comment> \<open> P2884 `OR register1 to register2` -> ` 0000 100w : 11 reg1 reg2` \<close>
    else if h = 0x09 then
      if modrm = 0b11 then (
        case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          Some (2, Porl_rr dst src) )))
      else None
    \<comment> \<open> P2893 `XOR register1 to register2` -> ` 0011 000w : 11 reg1 reg2` \<close>
    else if h = 0x31 then
      if modrm = 0b11 then (
        case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          Some (2, Pxorl_rr dst src))) ) 
      else None
    else if h = 0xd3 then
      \<comment> \<open> P2889 `SHL register by CL`              -> ` 1100 000w : 11 100 reg ` \<close>
      if modrm = 0b11 \<and> reg1 = 0b100 then 
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          Some (2, Pshll_r dst))
      \<comment> \<open> P2890 `SHR register by CL`              -> ` 1100 000w : 11 101 reg ` \<close>
      else if modrm = 0b11 \<and> reg1 = 0b101 then
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          Some (2, Pshrl_r dst))  
      \<comment> \<open> P2888 `SAR register by CL`              -> ` 1100 000w : 11 111 reg ` \<close>
      else if modrm = 0b11 \<and> reg1 = 0b111 then
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          Some (2, Psarl_r dst))  
    else None
    \<comment> \<open> P2892 `TEST: register1 and register2`   -> ` 1000 010w : 11 reg1 reg2` \<close>
    else if h = 0x85 then
      if modrm = 0b11 then(
        case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          Some(2, Ptestl_rr dst src) )))
      else None
    \<comment> \<open> P2878 `CMP: register1 with register2`   -> ` 0011 100w : 11 reg1 reg2 ` \<close>
    else if h = 0x39 then
      if modrm = 0b11 then(
        case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          Some(2, Pcmpl_rr src dst) )))
      else None
    else if h = 0xff then
    \<comment> \<open> P2878 `CALL: register indirect`   -> `0100 W00Bw 1111 1111 : 11 010 reg ` \<close>
      if modrm = 0b11 \<and> reg1 = 0b010 then
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          Some (2, Pcall_r dst)) 
      else None
    \<comment> \<open> R3 [opcode + modrm + imm] \<close>
    \<comment> \<open> P2882 `MOV immediate to register` -> ` 1100 011w : 11 000 reg : imm` \<close>
    else if h = 0xc7 then
      case nth_error l_bin (pc+2) of None \<Rightarrow> None | Some i1 \<Rightarrow> (
      case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some i2 \<Rightarrow> (
      case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some i3 \<Rightarrow> (
      case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some i4 \<Rightarrow> (
      case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
      case u32_of_u8_list [i1, i2, i3, i4] of None \<Rightarrow> None |
          Some imm \<Rightarrow> 
            if modrm = 0b11 \<and> reg1 = 0b000 then
              Some (6, Pmovl_ri dst imm)
            else None) ))))
    else if h = 0xc1 then
      case nth_error l_bin (pc+2) of None \<Rightarrow> None | Some imm \<Rightarrow> ( 
        \<comment> \<open> P2889 `SHL register by immediate count`      -> `1100 000w : 11 100 reg : imm8 ` \<close>
        if modrm = 0b11 \<and> reg1 = 0b100 then 
          case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
             Some (3, Pshll_ri dst imm))
        \<comment> \<open> P2890 `SHR register by immediate count`      -> ` 1100 000w : 11 101 reg : imm8 ` \<close>
        else if modrm = 0b11 \<and> reg1 = 0b101 then 
          case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
             Some (3, Pshrl_ri dst imm))
        \<comment> \<open> P2890 `SAR register by immediate count`      -> ` 1100 000w : 11 111 reg : imm8 ` \<close>
        else if modrm = 0b11 \<and> reg1 = 0b111 then 
          case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
             Some (3, Psarl_ri dst imm))
        \<comment> \<open> P2888 `ROR register by immediate count`      -> ` 1100 000w : 11 001 reg : imm8 ` \<close>
        else if modrm = 0b11 \<and> reg1 = 0b001 then 
          case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
             Some (3, Prorl_ri dst imm))
         else None)
    else if h = 0x81 then
      if modrm = 0b11 then
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          case nth_error l_bin (pc+2) of None \<Rightarrow> None | Some i1 \<Rightarrow> (
          case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some i2 \<Rightarrow> (
          case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some i3 \<Rightarrow> (
          case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some i4 \<Rightarrow> (
            case u32_of_u8_list [i1,i2,i3,i4] of None \<Rightarrow> None |
              Some imm \<Rightarrow> 
                \<comment> \<open> P2876 `ADD immediate to register` -> ` 1000 00sw : 11 000 reg : immediate data` \<close>
                if reg1 = 0b000 then
                  Some (6, Paddl_ri dst imm)
                \<comment> \<open> P2891 `OR: immediate to register` -> `0100 000B  1000 00sw : 11 001 reg : imm` \<close>
                else if reg1 = 0b001 then
                  Some (6, Porl_ri dst imm)
                \<comment> \<open> P2891 `AND: immediate to register` -> `0100 000B : 1000 00sw : 11 100 reg : immediate` \<close>
                else if reg1 = 0b100 then
                  Some (6, Pandl_ri dst imm)
                \<comment> \<open> P2891 `SUB: immediate from register` -> `0100 000B 1000 00sw : 11 101 reg : imm` \<close>
                else if reg1 = 0b101 then
                  Some (6, Psubl_ri dst imm)
                \<comment> \<open> P2893 `XOR: immediate to register` -> ` 0100 000B 1000 00sw : 11 110 reg : imm` \<close>
                else if reg1 = 0b110 then
                  Some (6, Pxorl_ri dst imm)
                \<comment> \<open> P2878 `CMP: immediate32 with qwordregister`   -> `0100 100B 1000 0001 : 11 111 qwordreg : imm32` \<close>
                else if reg1 = 0b111 then
                  Some (6, Pcmpl_ri dst imm)
                else None) ))))
      else None
    \<comment> \<open> R5 [opcode + modrm + displacement] \<close>
    \<comment> \<open> P2882 ` MOV: memory to reg`   ->  `0100 0RXB : 1000 101w : mod reg r/m`\<close>
    else if h = 0x88 then
      if modrm = 0b01  then
        case nth_error l_bin (pc+2) of None \<Rightarrow> None | Some dis \<Rightarrow> ( \<comment> \<open> displacement8 \<close>
          case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
          case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> ( 
            Some (3, Pmov_mr (Addrmode (Some dst) None (scast dis)) src  M8))) )
      else None
    else if h = 0x8b then 
      if modrm = 0b01 then
        case nth_error l_bin (pc+2) of None \<Rightarrow> None | Some dis \<Rightarrow> ( \<comment> \<open> displacement8 \<close>
            case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              Some (3, Pmov_rm src (Addrmode (Some dst) None (scast dis))  M32))) )
      else if modrm = 0b10 then \<comment> \<open> displacement32 \<close>
        case nth_error l_bin (pc+2) of None \<Rightarrow> None | Some d1 \<Rightarrow> (
        case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some d2 \<Rightarrow> (
        case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some d3 \<Rightarrow> (
        case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some d4 \<Rightarrow> (
          case u32_of_u8_list [d1,d2,d3,d4] of None \<Rightarrow> None | Some dis \<Rightarrow>(
          case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
          case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
             Some (6, Pmov_rm src (Addrmode (Some dst) None dis) M32)))) ))))
      else None
    else None
)"

definition x64_decode_op_0x81 :: "u8 \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow> nat \<Rightarrow> x64_bin \<Rightarrow> (nat * instruction) option" where
"x64_decode_op_0x81 modrm dst reg1 reg2 w r x b pc l_bin = (
  if modrm = 0b11 then
    case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
    case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some i1 \<Rightarrow> (
    case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some i2 \<Rightarrow> (
    case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some i3 \<Rightarrow> (
    case nth_error l_bin (pc+6) of None \<Rightarrow> None | Some i4 \<Rightarrow> (
      case u32_of_u8_list [i1,i2,i3,i4] of None \<Rightarrow> None |
        Some imm \<Rightarrow> (
          \<comment> \<open> P2876 `ADD immediate to register` -> `0100 000B : 1000 00sw : 11 000 reg : immediate data` \<close>
          if reg1 = 0b000 then
            if w = 0 \<and> r = 0 \<and> x = 0 then
              Some (7, Paddl_ri dst imm)
            else None
          \<comment> \<open> P2891 `OR: immediate to register` -> `0100 000B  1000 00sw : 11 001 reg : imm` \<close>
          else if reg1 = 0b001 then
            if w = 0 \<and> r = 0 \<and> x = 0 then
              Some (7, Porl_ri dst imm)
            else None
          \<comment> \<open> P2891 `AND: immediate to register` -> `0100 000B : 1000 00sw : 11 100 reg : immediate` \<close>
          else if reg1 = 0b100 then
            if w = 0 \<and> r = 0 \<and> x = 0 then
              Some (7, Pandl_ri dst imm)
            else None
          \<comment> \<open> P2891 `SUB: immediate from register` -> `0100 000B 1000 00sw : 11 101 reg : imm` \<close>
          else if reg1 = 0b101 then
            if w = 0 \<and> r = 0 \<and> x = 0 then
              Some (7, Psubl_ri dst imm)
            else None
          \<comment> \<open> P2893 `XOR: immediate to register` -> ` 0100 000B 1000 00sw : 11 110 reg : imm` \<close>
          else if reg1 = 0b110 then
            if w = 0 \<and> r = 0 \<and> x = 0 then
              Some (7, Pxorl_ri dst imm)
            else None
          \<comment> \<open> P2878 `CMP: immediate with register`   -> `0100 000B 1000 00sw : 11 111 reg : imm` \<close>
          \<comment> \<open> P2878 `CMP: immediate32 with qwordregister`   -> `0100 100B 1000 0001 : 11 111 qwordreg : imm32` \<close>
          else if reg1 = 0b111 then
            if w = 1 \<and> r = 0 \<and> x = 0 then
              Some (7, Pcmpq_ri dst imm)
            else if w = 0 \<and> r = 0 \<and> x = 0 then
              Some (7, Pcmpl_ri dst imm)
            else None
          else None)) ))))
  else if modrm = 0b10 \<and> reg2 = 0b100 then
    case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some sib \<Rightarrow> (
    let rbase  = bitfield_extract 0 3 sib in
    let rindex = bitfield_extract 3 3 sib in
    let scale  = bitfield_extract 6 2 sib in
    let index  = bitfield_insert 3 1 rindex x in
    let base   = bitfield_insert 3 1 rbase  b in
      case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some d1 \<Rightarrow> (
      case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some d2 \<Rightarrow> (
      case nth_error l_bin (pc+6) of None \<Rightarrow> None | Some d3 \<Rightarrow> (
      case nth_error l_bin (pc+7) of None \<Rightarrow> None | Some d4 \<Rightarrow> (
        case u32_of_u8_list [d1,d2,d3,d4] of None \<Rightarrow> None | Some dis \<Rightarrow>(
        if reg1 = 0b000 then
          case nth_error l_bin (pc+8) of None \<Rightarrow> None | Some i1 \<Rightarrow> (
          case nth_error l_bin (pc+9) of None \<Rightarrow> None | Some i2 \<Rightarrow> (
          case nth_error l_bin (pc+10) of None \<Rightarrow> None | Some i3 \<Rightarrow> (
          case nth_error l_bin (pc+11) of None \<Rightarrow> None | Some i4 \<Rightarrow> (
          case u32_of_u8_list [i1,i2,i3,i4] of None \<Rightarrow> None | Some imm \<Rightarrow> (
          if w = 1 \<and> r = 0 then
            case ireg_of_u8 index of None \<Rightarrow> None | Some ri \<Rightarrow> (
            case ireg_of_u8 base  of None \<Rightarrow> None | Some rb \<Rightarrow> (
              Some (12, Paddq_mi (Addrmode (Some rb) (Some (ri, scale)) (scast dis)) imm M64 )))
          else None) ))))
        else None) )))) )
  else None
)"

definition x64_decode :: "nat \<Rightarrow> x64_bin \<Rightarrow> (nat * instruction) option" where
"x64_decode pc l_bin = (
  case nth_error l_bin pc of None \<Rightarrow> None | Some h \<Rightarrow> \<comment> \<open> R1 [opcode] \<close>
    if h = 0x90 then 
      \<comment> \<open> P2884 `NOP – No Operation` -> `1001 0000` \<close> 
      Some (1, Pnop)
    else if h = 0x99 then
      Some (1, Pcdq)
    else if h = 0xc3 then
      \<comment> \<open> P2887 ` RET near` -> ` 1100 0011` \<close>
      Some (1, Pret)
    \<comment> \<open> R7 legacy \<close>
    else if h = 0x66 then  \<comment> \<open> 16-bit mode \<close>
      x64_decode_op_0x66 pc l_bin
    else if h = 0x0f then \<comment> \<open> R8 escape \<close>
      x64_decode_op_0x0f pc l_bin
    else if bitfield_extract 4 4 h \<noteq> 0b0100 then  \<comment> \<open> h is not rex  \<close>
        x64_decode_op_not_rex h pc l_bin
    else if bitfield_extract 0 4 h = 0 then   \<comment> \<open> h is rex, the low 4-bit must not 0  \<close> 
      None
    else  \<comment> \<open> h is rex  \<close> 
      let w = bitfield_extract 3 1 h in
      let r = bitfield_extract 2 1 h in
      let x = bitfield_extract 1 1 h in
      let b = bitfield_extract 0 1 h in (
      case nth_error l_bin (pc+1) of None \<Rightarrow> None | Some op \<Rightarrow>
      \<comment> \<open> R6.1 [rex + opcode] \<close>
      if op = 0x99 then
        if w = 1 \<and> r = 0 \<and> x = 0 \<and> b = 0 then
          Some (2, Pcqo)
        else None
      \<comment> \<open> P2885 `PUSH: qwordregister (alternate encoding)`   -> ` 0100 W00BS : 0101 0 reg64` \<close>
      else if bitfield_extract 3 5 op = 0b01010 then
        let reg2 = bitfield_extract 0 3 op in
        let dst  = bitfield_insert 3 1 reg2 b in
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          if w = 0 \<and> r = 0 \<and> x = 0 then
            Some (2, Ppushl_r dst)
          else None)
      \<comment> \<open> P2885 `POP: qwordregister (alternate encoding)`   -> ` 0100 W00B : 0101 1 reg64 ` \<close>
      else if bitfield_extract 3 5 op = 0b01011 then
        let reg2 = bitfield_extract 0 3 op in
        let dst  = bitfield_insert 3 1 reg2 b in
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          if w = 0 \<and> r = 0 \<and> x = 0 then
            Some (2, Ppopl dst)
          else None)
      \<comment> \<open> R6.2 [rex + opcode + imm] \<close> 
      \<comment> \<open> P2882 `MOV immediate64 to qwordregister (alternate encoding)` -> `0100 100B 1011 1reg : imm64` \<close>
      else if bitfield_extract 3 5 op = 0b10111 then
        let reg2 = bitfield_extract 0 3 op in
        let dst  = bitfield_insert 3 1 reg2 b in
        case nth_error l_bin (pc+2) of None \<Rightarrow> None | Some i1 \<Rightarrow> (
        case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some i2 \<Rightarrow> (
        case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some i3 \<Rightarrow> (
        case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some i4 \<Rightarrow> (
        case nth_error l_bin (pc+6) of None \<Rightarrow> None | Some i5 \<Rightarrow> (
        case nth_error l_bin (pc+7) of None \<Rightarrow> None | Some i6 \<Rightarrow> (
        case nth_error l_bin (pc+8) of None \<Rightarrow> None | Some i7 \<Rightarrow> (
        case nth_error l_bin (pc+9) of None \<Rightarrow> None | Some i8 \<Rightarrow> (
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
        case u64_of_u8_list [i1, i2, i3, i4, i5, i6, i7, i8] of None \<Rightarrow> None |
            Some imm \<Rightarrow> 
              if w = 1 \<and> r = 0 \<and> x = 0 then
                Some (10, Pmovq_ri dst imm)
          else None) ))))))))
      \<comment> \<open> P2885 `PUSH: imm32`   -> `0100 1000 0110 1000 : imm32 ` \<close>
      else if op = 0x68 then 
        case nth_error l_bin (pc+2) of None \<Rightarrow> None | Some i1 \<Rightarrow> (
        case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some i2 \<Rightarrow> (
        case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some i3 \<Rightarrow> (
        case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some i4 \<Rightarrow> (
          case u32_of_u8_list [i1, i2, i3, i4] of None \<Rightarrow> None |
            Some imm \<Rightarrow> 
              if w = 1 \<and> r = 0 \<and> x = 0 \<and> b = 0 then
                Some (6, Ppushl_i imm)
              else None ))))
      else if op = 0x0f then 
        case nth_error l_bin (pc+2) of None \<Rightarrow> None | Some op1 \<Rightarrow> (
      \<comment> \<open> R8.4 [rex + escape + opcode] \<close>
      \<comment> \<open> P2877 `BSWAP: register `   -> `0000 1111 : 1100 1 reg` \<close>
      \<comment> \<open> P2877 `BSWAP: qwordregister `   -> `0100 100B 0000 1111 : 1100 1 reg` \<close>
      if bitfield_extract 3 5 op1 = 0b11001 then
        let reg2 = bitfield_extract 0 3 op1 in
        let dst  = bitfield_insert 3 1 reg2 b in
          case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
            if w = 1 \<and> x = 0 \<and> r = 0 then
              Some (3, Pbswapq dst)
            else if w = 0 \<and> x = 0 \<and> r = 0 then
              Some (3, Pbswapl dst)
            else None)
      \<comment> \<open> R8.5 [rex + escape + opcode + modrm] \<close>
      \<comment> \<open> P2919 `MOVcc : resgister2  to resgister1 ` -> `0100 0R0B 0000 1111: 0100 tttn : 11 reg1 reg2` \<close>
      \<comment> \<open> P2919 `MOVcc : qwordregister2 to qwordregister1` -> ` 0100 1R0B 0000 1111: 0100 tttn : 11 qwordreg1 qwordreg2` \<close>
        else if bitfield_extract 4 4 op1 = 0b0100 then
          let flag = (bitfield_extract 0 4 op1)  in 
          case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some reg \<Rightarrow>
          let modrm = bitfield_extract 6 2 reg in
          let reg1  = bitfield_extract 3 3 reg in
          let reg2  = bitfield_extract 0 3 reg in
          let src   = bitfield_insert 3 1 reg1 r in
          let dst   = bitfield_insert 3 1 reg2 b in
            if modrm = 0b11 then
              case cond_of_u8 flag of None \<Rightarrow> None | Some t \<Rightarrow>(
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 0 \<and> x = 0 then
                  Some (4, Pcmovl t src dst)
                else if w = 1 \<and> x = 0 then
                  Some (4, Pcmovq t src dst)
                else None)))
            else None
        else None)
      else (
        case nth_error l_bin (pc+2) of None \<Rightarrow> None | Some reg \<Rightarrow>
        let modrm = bitfield_extract 6 2 reg in
        let reg1  = bitfield_extract 3 3 reg in
        let reg2  = bitfield_extract 0 3 reg in
        let src   = bitfield_insert 3 1 reg1 r in
        let dst   = bitfield_insert 3 1 reg2 b in
          \<comment> \<open> R6.3 [rex + opcode + modrm] \<close>
          if op = 0x89 then
            if modrm = 0b11 then (
            \<comment> \<open> P2882 `MOV register1 to register2` -> `0100 WR0B : 1000 100w : 11 reg1 reg2` \<close>
            \<comment> \<open> P2882 `MOV qwordregister1 to qwordregister2` -> `0100 1R0B : 1000 1001 : 11 reg1 reg2` \<close>
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 then   \<comment> \<open> rex should be `W=1` and `X=0`\<close> 
                  Some (3, Pmovq_rr dst src) 
                else if w = 0 \<and> x = 0 then
                  Some (3, Pmovl_rr dst src)
                else None))) 
              \<comment> \<open> R6.5 [rex + opcode + modrm + displacement] \<close>
            else if modrm = 0b01 then
              \<comment> \<open> P2882 ` MOV: reg to memory` ->  `0100 WRXB : 1000 1001 : mod reg r/m` \<close>
              \<comment> \<open> P2882 ` MOV: qwordregister to memory64` ->  `0100 1RXB 1000 1001 : mod qwordreg r/m` \<close>
              case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some dis \<Rightarrow> (  \<comment> \<open> displacement8 \<close>
                case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
                case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> ( 
                  if w = 1 \<and> x = 0 then
                    Some (4, Pmov_mr (Addrmode (Some dst) None (scast dis)) src M64)
                  else if w = 0 \<and> x = 0 then
                    Some (4, Pmov_mr (Addrmode (Some dst) None (scast dis)) src M32)
                  else None)) )
            else if modrm = 0b10 then
              if reg2 \<noteq> 0b100 then 
                case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some d1 \<Rightarrow> (
                case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some d2 \<Rightarrow> (
                case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some d3 \<Rightarrow> (
                case nth_error l_bin (pc+6) of None \<Rightarrow> None | Some d4 \<Rightarrow> (
                  case u32_of_u8_list [d1,d2,d3,d4] of None \<Rightarrow> None | Some dis \<Rightarrow>(
                    case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
                    case ireg_of_u8 dst of None \<Rightarrow> None | Some rb \<Rightarrow> (
                      Some (7, Pmov_mr (Addrmode (Some rb) None dis) src (if w = 1 then M64 else M32))))) ))))
              else 
                case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some sib \<Rightarrow> (
                let rbase  = bitfield_extract 0 3 sib in
                let rindex = bitfield_extract 3 3 sib in
                let scale  = bitfield_extract 6 2 sib in
                let index  = bitfield_insert 3 1 rindex x in
                let base   = bitfield_insert 3 1 rbase  b in
                case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some d1 \<Rightarrow> (
                case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some d2 \<Rightarrow> (
                case nth_error l_bin (pc+6) of None \<Rightarrow> None | Some d3 \<Rightarrow> (
                case nth_error l_bin (pc+7) of None \<Rightarrow> None | Some d4 \<Rightarrow> (
                    case u32_of_u8_list [d1,d2,d3,d4] of None \<Rightarrow> None | Some dis \<Rightarrow>(
                      if w = 1 then
                        case ireg_of_u8 src   of None \<Rightarrow> None | Some src \<Rightarrow> (
                        case ireg_of_u8 index of None \<Rightarrow> None | Some ri \<Rightarrow> (
                        case ireg_of_u8 base  of None \<Rightarrow> None | Some rb \<Rightarrow> (
                          Some (8, Pmov_mr (Addrmode (Some rb) (Some (ri, scale)) (scast dis)) src M64))))
                      else None) )))) )
            else None
          else if op = 0x87 then
          \<comment> \<open> P2893 `XCHG: register1 with register2 `   -> ` 0100 1R0B 1000 011w : 11 reg1 reg2 ` \<close>
            if modrm = 0b11 then (
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 then           
                  Some (3, Pxchgq_rr dst src)
                else None)))
          \<comment> \<open> P2893 `XCHG: memory64 with qwordregister `  -> ` 0100 1RXB 1000 011w : 11 reg1 reg2 ` \<close>
          else if modrm = 0b10 then 
            if reg2 = 0b100 then
              case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some sib \<Rightarrow> (
              let rbase  = bitfield_extract 0 3 sib in
              let rindex = bitfield_extract 3 3 sib in
              let scale  = bitfield_extract 6 2 sib in
              let index  = bitfield_insert 3 1 rindex x in
              let base   = bitfield_insert 3 1 rbase  b in
                case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some d1 \<Rightarrow> (
                case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some d2 \<Rightarrow> (
                case nth_error l_bin (pc+6) of None \<Rightarrow> None | Some d3 \<Rightarrow> (
                case nth_error l_bin (pc+7) of None \<Rightarrow> None | Some d4 \<Rightarrow> (
                  case u32_of_u8_list [d1,d2,d3,d4] of None \<Rightarrow> None | Some dis \<Rightarrow>(
                    if w = 1  then
                      case ireg_of_u8 src   of None \<Rightarrow> None | Some src \<Rightarrow> (
                      case ireg_of_u8 index of None \<Rightarrow> None | Some ri \<Rightarrow> (
                      case ireg_of_u8 base  of None \<Rightarrow> None | Some rb \<Rightarrow> (
                        Some (8, Pxchgq_rm src (Addrmode (Some rb) (Some (ri, scale)) (scast dis)) M64))))
                    else None) ) ))))
            else None
          else None
          else if op = 0x63 then
          \<comment> \<open> P2883 `MOVXD dwordregister2 to qwordregister1` -> ` 0100 1R0B 0110 0011 : 11 quadreg1 dwordreg2` \<close>
            if modrm = 0b11 then (
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 then
                  Some (3, Pmovsl_rr src dst )
                else None)))
            else None
          else if op = 0x01 then
            \<comment> \<open> P2887 `ADD register1 to register2` -> `0100 WR0B : 0000 000w : 11 reg1 reg2` \<close>
            if modrm = 0b11 then (
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 then 
                  Some (3, Paddq_rr dst src)
                else if w = 0 \<and> x = 0 then
                   Some (3, Paddl_rr dst src)
                else None )))
            else None
          else if op = 0x29 then
            \<comment> \<open> P2891 `SUB register1 from register2` -> `0100 WR0B : 0010 100w : 11 reg1 reg2` \<close> 
            if modrm = 0b11 then (
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 then 
                  Some (3, Psubq_rr dst src)
                else if w = 0 \<and> x = 0 then
                  Some (3, Psubl_rr dst src) 
                else None)))
            else None
          else if op = 0xf7 then
            \<comment> \<open> P2884 `NEG  register2`     -> ` 0100 W00B : 1111 011w : 11 011 reg` \<close>
            if modrm = 0b11 \<and> reg1 = 0b011 then 
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> r = 0 \<and> x = 0 then 
                  Some (3, Pnegq dst) 
                else if w = 0 \<and> r = 0 \<and> x = 0 then 
                  Some (3, Pnegl dst)
                else None)
            \<comment> \<open> P2884 `MUL  AL, AX, or EAX with register2`       -> ` 0100 000B : 1111 011w : 11 100 reg` \<close>
            \<comment> \<open> P2884 `MUL  RAX with qwordregister (to RDX:RAX)` -> ` 0100 100B : 1111 011w : 11 100 qowrdreg` \<close>
            else if modrm = 0b11 \<and> reg1 = 0b100 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 \<and> r = 0 \<and> x = 0 then 
                Some (3, Pmulq_r dst) 
              else if w = 0 \<and> r = 0 \<and> x = 0 then 
                Some (3, Pmull_r dst)
              else None)
            \<comment> \<open> P2880 `IMUL AL, AX, or EAX with register2`       -> ` 0100 000B : 1111 011w : 11 101 reg` \<close>
            \<comment> \<open> P2880 `IMUL RAX with qwordregister (to RDX:RAX)` -> ` 0100 100B : 1111 011w : 11 101 qwordreg` \<close>
            else if modrm = 0b11 \<and> reg1 = 0b101 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> r = 0 \<and> x = 0 then 
                  Some (3, Pimulq_r dst) 
                else if w = 0 \<and> r = 0 \<and> x = 0 then 
                  Some (3, Pimull_r dst)
                else None)
            \<comment> \<open> P2879 `DIV AL, AX, or EAX by register2`          -> ` 0100 000B : 1111 011w : 11 110 reg` \<close>
            \<comment> \<open> P2879 `DIV EAX by qwordregister (to RDX:RAX)`    -> ` 0100 100B : 1111 011w : 11 110 qwordreg` \<close>
            else if modrm = 0b11 \<and> reg1 = 0b110 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> r = 0 \<and> x = 0 then 
                  Some (3, Pdivq_r dst) 
                else if w = 0 \<and> r = 0 \<and> x = 0 then 
                  Some (3, Pdivl_r dst)
                else None)
            \<comment> \<open> P2879 `IDIV AL, AX, or EAX by register2`         -> ` 0100 000B : 1111 011w : 11 111 reg` \<close>
            \<comment> \<open> P2879 `IDIV RAX by qwordregister (to RDX:RAX)`   -> ` 0100 100B : 1111 011w : 11 111 qwordreg` \<close>
            else if modrm = 0b11 \<and> reg1 = 0b111 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1  \<and> r = 0 \<and> x = 0 then 
                  Some (3, Pidivq_r dst) 
                else if w = 0 \<and> r = 0 \<and> x = 0 then 
                  Some (3, Pidivl_r dst)
                else None)
            \<comment> \<open> P2892 `TEST: immediate and register`   -> ` 0100 000B 1111 011w : 11 000 reg : imm ` \<close>
            \<comment> \<open> P2892 `TEST: immediate32 and qwordregister `   -> ` 0100 100B 1111 0111 : 11 000 qwordreg : imm32 ` \<close>
            else if modrm = 0b11 \<and> reg1 = 0b000 then
              case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some i1 \<Rightarrow> (
              case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some i2 \<Rightarrow> (
              case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some i3 \<Rightarrow> (
              case nth_error l_bin (pc+6) of None \<Rightarrow> None | Some i4 \<Rightarrow> (
                case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                case u32_of_u8_list [i1, i2, i3, i4] of None \<Rightarrow> None | Some imm \<Rightarrow> (
                    if w = 1 \<and> r = 0 \<and> x = 0 then
                      Some (7, Ptestq_ri dst imm)
                    else if w = 0 \<and> r = 0 \<and> x = 0 then
                      Some (7, Ptestl_ri dst imm)
                    else None)) ))))
            else None
          else if op = 0x09 then
          \<comment> \<open> P2884 `OR register1 to register2` -> ` 0100 WR0B : 0000 100w : 11 reg1 reg2` \<close>
          \<comment> \<open> P2884 `OR qwordregister1 to qwordregister2` -> ` 0100 1R0B : 0000 1001 : 11 reg1 reg2` \<close>
            if modrm = 0b11 then (
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 then 
                  Some (3, Porq_rr dst src) 
                else if w = 0 \<and> x = 0 then
                  Some (3, Porl_rr dst src) 
                else None)))
            else None
          else if op = 0x21 then
          \<comment> \<open> P2876 `AND register1 to register2` -> ` 0100 WR0B : 0010 000w : 11 reg1 reg2` \<close>
          \<comment> \<open> P2876 `AND qwordregister1 to qwordregister2` -> ` 0100 1R0B : 0010 0001 : 11 reg1 reg2` \<close>
            if modrm = 0b11 then (
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 then 
                  Some (3, Pandq_rr dst src)
                else if w = 0 \<and> x = 0 then 
                  Some (3, Pandl_rr dst src)
                else None)) ) 
            else None
          else if op = 0x31 then
          \<comment> \<open> P2893 `XOR register1 to register2` -> ` 0100 WRXB : 0011 000w : 11 reg1 reg2` \<close>
          \<comment> \<open> P2893 `XOR qwordregister1 to qwordregister2` -> ` 0100 1R0B : 0011 0001 : 11 reg1 reg2` \<close>
            if modrm = 0b11 then (
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 then 
                  Some (3, Pxorq_rr dst src)
                else if w = 0 \<and> x = 0 then 
                  Some (3, Pxorl_rr dst src)
                else None)) ) 
            else None
          else if op = 0xd3 then
          \<comment> \<open> P2889 `SHL register by CL`              -> ` 0100 000B 1100 000w : 11 100 reg ` \<close>
          \<comment> \<open> P2889 `SHL qwordregister by CL`         -> ` 0100 100B 1100 000w : 11 100 reg ` \<close>
            if modrm = 0b11 \<and> reg1 = 0b100 then 
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1  \<and> x = 0 \<and> r = 0 then 
                  Some (3, Pshlq_r dst) 
                else if w = 0  \<and> x = 0 \<and> r = 0 then 
                  Some (3, Pshll_r dst)
                else None) 
          \<comment> \<open> P2890 `SHR register by CL`              -> ` 0100 000B 1100 000w : 11 101 reg ` \<close>
          \<comment> \<open> P2890 `SHR qwrodregister by CL`         -> ` 0100 100B 1100 000w : 11 101 reg ` \<close>
            else if modrm = 0b11 \<and> reg1 = 0b101 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1  \<and> x = 0 \<and> r = 0 then 
                  Some (3, Pshrq_r dst) 
                else if w = 0  \<and> x = 0 \<and> r = 0 then
                  Some (3, Pshrl_r dst)
                else None)  
          \<comment> \<open> P2888 `SAR register by CL`              -> ` 0100 000B 1100 000w : 11 111 reg ` \<close>
          \<comment> \<open> P2888 `SAR qwordregister by CL`         -> ` 0100 100B 1100 000w : 11 111 reg ` \<close>
            else if modrm = 0b11 \<and> reg1 = 0b111 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1  \<and> x = 0 \<and> r = 0 then 
                  Some (3, Psarq_r dst) 
                else if w = 0  \<and> x = 0 \<and> r = 0 then
                  Some (3, Psarl_r dst)
                else None)  
          else None
        \<comment> \<open> P2892 `TEST: register1 and register2`   -> ` 0100 0R0B 1000 010w : 11 reg1 reg2` \<close>
        \<comment> \<open> P2892 `TEST:  qwordregister1 and qwordregister2`   -> ` 0100 1R0B 1000 0101 : 11 qwordreg1 qwordreg2` \<close>
        else if op = 0x85 then
          if modrm = 0b11 then(
            case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 \<and> x = 0 then
                Some(3, Ptestq_rr dst src)
              else if w = 0 \<and> x = 0 then
                Some(3, Ptestl_rr dst src)
              else None )))
          else None
        \<comment> \<open> P2878 `CMP: register1 with register2`   -> ` 0100 0R0B 0011 100w : 11 reg1 reg2 ` \<close>
        \<comment> \<open> P2878 `CMP: qwordregister1 with qwordregister2`   -> `0100 1R0B 0011 1001 : 11 qwordreg1 qwordreg2` \<close>
        else if op = 0x39 then
          if modrm = 0b11 then(
            case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 \<and> x = 0 then
                Some(3, Pcmpq_rr src dst)
              else if w = 0 \<and> x = 0 then
                Some(3, Pcmpl_rr src dst)
              else None )))
          else None
        \<comment> \<open> P2878 `CALL: register indirect`   -> `0100 W00Bw 1111 1111 : 11 010 reg ` \<close>
        else if op = 0xff then
          if modrm = 0b11 \<and> reg1 = 0b010 then
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 0 \<and> r = 0 \<and> x = 0 then
                Some (3, Pcall_r dst)
              else None) 
        \<comment> \<open> P2885 `PUSH: memory64`   -> `0100 W00BS : 1111 1111 : mod 110 r/m ` \<close>
          else if modrm = 0b10 \<and> reg2 = 0b100 then                           
            case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some sib \<Rightarrow> (
            let rbase  = bitfield_extract 0 3 sib in
            let rindex = bitfield_extract 3 3 sib in
            let scale  = bitfield_extract 6 2 sib in
            let index  = bitfield_insert 3 1 rindex x in
            let base   = bitfield_insert 3 1 rbase  b in
              case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some d1 \<Rightarrow> (
              case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some d2 \<Rightarrow> (
              case nth_error l_bin (pc+6) of None \<Rightarrow> None | Some d3 \<Rightarrow> (
              case nth_error l_bin (pc+7) of None \<Rightarrow> None | Some d4 \<Rightarrow> (
                case u32_of_u8_list [d1,d2,d3,d4] of None \<Rightarrow> None | Some dis \<Rightarrow>(
                if reg1 = 0b110 then
                  if w = 1 \<and> r = 0 then
                    case ireg_of_u8 index of None \<Rightarrow> None | Some ri \<Rightarrow> (
                    case ireg_of_u8 base  of None \<Rightarrow> None | Some rb \<Rightarrow> (
                      Some (8, Ppushq_m (Addrmode (Some rb) (Some (ri, scale)) (scast dis)) M64 )))
                  else None
                else None) )))) )
          else None
        \<comment> \<open> R6.4 [rex + opcode + modrm + imm] \<close>
        else if op = 0xc7 then
          let n = if modrm = 0b01 then 1 else if modrm = 0b10 then 4 else 0 in
          case nth_error l_bin (pc+3+n) of None \<Rightarrow> None | Some i1 \<Rightarrow> (
          case nth_error l_bin (pc+4+n) of None \<Rightarrow> None | Some i2 \<Rightarrow> (
          case nth_error l_bin (pc+5+n) of None \<Rightarrow> None | Some i3 \<Rightarrow> (
          case nth_error l_bin (pc+6+n) of None \<Rightarrow> None | Some i4 \<Rightarrow> (
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
            case u32_of_u8_list [i1, i2, i3, i4] of None \<Rightarrow> None |
              Some imm \<Rightarrow> 
              if reg1 = 0b000 \<and> r = 0 \<and> x = 0 then
                if modrm = 0b11 then
                \<comment> \<open> P2882 `MOV immediate to register` -> `0100 000B : 1100 011w : 11 000 reg : imm` \<close>
                  if w = 0 then
                    Some (7, Pmovl_ri dst imm)
                  else None
                \<comment> \<open> R6.6 [rex + opcode + modrm + displacement + imm] \<close>
                \<comment> \<open> P2882 `MOV immediate32 to memory64 (zero extend)` -> ` 0100 10XB 1100 0111 : mod 000 r/m : imm32` \<close>
                else if modrm = 0b01 then
                  if w = 1 then
                    case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some dis \<Rightarrow> (
                    Some (8, Pmov_mi (Addrmode (Some dst) None (scast dis)) imm M64) )
                  else None
                else if modrm = 0b10  then
                  case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some d1 \<Rightarrow> (
                  case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some d2 \<Rightarrow> (
                  case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some d3 \<Rightarrow> (
                  case nth_error l_bin (pc+6) of None \<Rightarrow> None | Some d4 \<Rightarrow> (
                    case u32_of_u8_list [d1, d2, d3, d4] of None \<Rightarrow> None |
                      Some dis \<Rightarrow> (
                        if w = 1 then
                          Some (11, Pmov_mi (Addrmode (Some dst) None dis) imm M64)
                        else None) ))))
                else None
              else None) ))))
        else if op = 0x81 then
          x64_decode_op_0x81 modrm dst reg1 reg2 w r x b pc l_bin
        else if op = 0xc1 then
          case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some imm \<Rightarrow> (
        \<comment> \<open> P2889 `SHL register by immediate count`      -> ` 0100 000B 1100 000w : 11 100 reg : imm8 ` \<close>
        \<comment> \<open> P2889 `SHL qwordregister by immediate count` -> ` 0100 100B 1100 000w : 11 100 reg : imm8 ` \<close>
            if modrm = 0b11 \<and> reg1 = 0b100 then 
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 \<and> r = 0 then Some (4, Pshlq_ri dst imm)
                else if w = 0 \<and> x = 0 \<and> r = 0 then Some (4, Pshll_ri dst imm)
                else None)
        \<comment> \<open> P2890 `SHR register by immediate count`      -> ` 0100 000B 1100 000w : 11 101 reg : imm8 ` \<close>
        \<comment> \<open> P2890 `SHR qwordregister by immediate count` -> ` 0100 100B 1100 000w : 11 101 reg : imm8 ` \<close>
            else if modrm = 0b11 \<and> reg1 = 0b101 then 
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 \<and> r = 0 then Some (4, Pshrq_ri dst imm)
                else if w = 0 \<and> x = 0 \<and> r = 0 then Some (4, Pshrl_ri dst imm)
                else None)
        \<comment> \<open> P2888 `SAR register by immediate count`      -> ` 0100 000B 1100 000w : 11 111 reg : imm8 ` \<close>
        \<comment> \<open> P2888 `SAR qwordregister by immediate count` -> ` 0100 100B 1100 000w : 11 111 reg : imm8 ` \<close>
            else if modrm = 0b11 \<and> reg1 = 0b111 then 
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 \<and> r = 0 then Some (4, Psarq_ri dst imm)
                else if w = 0 \<and> x = 0 \<and> r = 0 then Some (4, Psarl_ri dst imm)
                else None)
        \<comment> \<open> P2888 `ROR register by immediate count`      -> ` 0100 000B 1100 000w : 11 001 reg : imm8 ` \<close>
        \<comment> \<open> P2888 `ROR qwordregister by immediate count` -> ` 0100 100B 1100 000w : 11 001 reg : imm8 ` \<close>
            else if modrm = 0b11 \<and> reg1 = 0b001 then 
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 \<and> r = 0 then Some (4, Prorq_ri dst imm)
                else if w = 0 \<and> x = 0 \<and> r = 0 then Some (4, Prorl_ri dst imm)
                else None)
            else None)
    \<comment> \<open> R6.5 [rex + opcode + modrm + displacement] \<close>
        else if op = 0x88 then
          \<comment> \<open> P2882 ` MOV: reg to memory`  ->  `0100 0RXB : 1000 1000 : mod reg r/m `\<close>
          if modrm = 0b01 \<and> x = 0 \<and> w = 0 then
            case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some dis \<Rightarrow> (\<comment> \<open> displacement8 \<close>
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> ( 
                Some (4, Pmov_mr (Addrmode (Some dst) None (scast dis)) src M8))) )
          else None
        else if op = 0x8b then    
          if modrm = 0b01 \<and> x = 0 then
          \<comment> \<open> P2882 ` MOV: memory to reg`             ->  `0100 0RXB : 1000 101w : mod reg r/m`\<close>
          \<comment> \<open> P2882 ` MOV: memory64 to qwordregister` ->  `0100 1RXB : 1000 1011 : mod qwordreg r/m`\<close>
            case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some dis \<Rightarrow> (  \<comment> \<open> displacement8 \<close>
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> ( 
                Some (4, Pmov_rm src (Addrmode (Some dst) None (scast dis))  (if w = 1 then M64 else M32))))  )
          else if modrm = 0b10  then
            if reg2 \<noteq> 0b100 then
              case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some d1 \<Rightarrow> (
              case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some d2 \<Rightarrow> (
              case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some d3 \<Rightarrow> (
              case nth_error l_bin (pc+6) of None \<Rightarrow> None | Some d4 \<Rightarrow> (
              case u32_of_u8_list [d1,d2,d3,d4] of None \<Rightarrow> None | Some dis \<Rightarrow>(
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> ( 
                if x = 0 then
                  Some (7, Pmov_rm src (Addrmode (Some dst) None dis) (if w = 1 then M64 else M32))
                else None)))  ))))
            else \<comment> \<open> sib \<close>
              case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some sib \<Rightarrow> (
              let rbase  = bitfield_extract 0 3 sib in
              let rindex = bitfield_extract 3 3 sib in
              let scale  = bitfield_extract 6 2 sib in
              let index  = bitfield_insert 3 1 rindex x in
              let base   = bitfield_insert 3 1 rbase  b in
                case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some d1 \<Rightarrow> (
                case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some d2 \<Rightarrow> (
                case nth_error l_bin (pc+6) of None \<Rightarrow> None | Some d3 \<Rightarrow> (
                case nth_error l_bin (pc+7) of None \<Rightarrow> None | Some d4 \<Rightarrow> (
                  case u32_of_u8_list [d1,d2,d3,d4] of None \<Rightarrow> None | Some dis \<Rightarrow>(
                    if w = 1  then
                      case ireg_of_u8 src   of None \<Rightarrow> None | Some src \<Rightarrow> (
                      case ireg_of_u8 index of None \<Rightarrow> None | Some ri \<Rightarrow> (
                      case ireg_of_u8 base  of None \<Rightarrow> None | Some rb \<Rightarrow> (
                        Some (8, Pmov_rm src (Addrmode (Some rb) (Some (ri, scale))  dis) M64))))
                    else None) ) ))))
          else None
        \<comment> \<open> P2881 `LEA: Load Effective Address: in qwordregister `  -> `0100 1RXB : 1000 1101 : mod qwordreg r/m` \<close>
        else if op = 0x8d then    
          if modrm = 0b01 then
            case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some dis \<Rightarrow> ( \<comment> \<open> displacement8 \<close>
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> ( 
                if w = 1 \<and> x = 0 then
                  Some (4, Pleaq src (Addrmode (Some dst) None (scast dis)))
                else None))  )
          else if modrm = 0b10  then
            case nth_error l_bin (pc+3) of None \<Rightarrow> None | Some d1 \<Rightarrow> (
            case nth_error l_bin (pc+4) of None \<Rightarrow> None | Some d2 \<Rightarrow> (
            case nth_error l_bin (pc+5) of None \<Rightarrow> None | Some d3 \<Rightarrow> (
            case nth_error l_bin (pc+6) of None \<Rightarrow> None | Some d4 \<Rightarrow> (
              case u32_of_u8_list [d1, d2, d3, d4] of None \<Rightarrow> None | Some dis \<Rightarrow> (
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> ( 
                if w = 1 \<and> x = 0 then
                  Some (7, Pleaq src (Addrmode (Some dst) None dis))
                else None))) ))))
          else None
    \<comment> \<open> R6.6 [rex + opcode + modrm + displacement + imm] \<close>
        else None ))
)"


(*
fun x64_disassemble_aux :: "nat \<Rightarrow> nat \<Rightarrow> x64_bin \<Rightarrow> x64_asm option" where
"x64_disassemble_aux 0 _ _ = Some []" |
"x64_disassemble_aux (Suc n) pc l_bin = (
  case x64_decode pc l_bin of
  None        \<Rightarrow> None \<or>  
  Some (k, l) \<Rightarrow> (
    case x64_disassemble_aux n (pc+k) l_bin of
    None    \<Rightarrow> None |
    Some l1 \<Rightarrow> Some (l#l1))
)"

definition x64_disassemble :: "x64_bin \<Rightarrow> x64_asm option" where
"x64_disassemble l_bin = x64_disassemble_aux (length l_bin) 0 l_bin" *)


(*
(**r 
 [Pmov_rr ireg.R8 ireg.RAX]"
(**r Some [102, 65, 137, 200] 11 001 000 *)
*)
value "x64_disassemble [102, 65, 137, 200]"
value "102 = (0x66::u8)"
value "137 = (0x89::u8)"

value "bitfield_extract 2 1 64" (**r r = 0 *)
value "bitfield_extract 0 1 64" (**r b = 0 *)
value "bitfield_extract 6 2 195" (**r modrm = 3 *)
value "bitfield_extract 3 3 200" (**r reg1 = 0 *)
value "bitfield_extract 0 3 195" (**r reg2 = 3 *)
value "bitfield_insert 3 1 0 0" (**r src = 0 *)
value "bitfield_insert 3 1  3 0" (**r dst = 3 *)
value "ireg_of_u8 0" (**r Some RAX *)
value "ireg_of_u8 3" (**r Some RBX *) *)

end