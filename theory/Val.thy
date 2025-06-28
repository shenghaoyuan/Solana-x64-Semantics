section \<open> CompCert Value Type \<close>

theory Val
  imports
  Main
  rBPFCommType
begin

definition sub_overflowi32 :: "u32 \<Rightarrow> u32 \<Rightarrow> u32 \<Rightarrow> u32" where
"sub_overflowi32 x y bin = (
  let s = (scast x) - (scast y) - (scast bin) in
    if i32_MIN \<le>s s \<and> s \<le>s i32_MAX then 0 else 1
)"

definition sub_overflowi64 :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64" where
"sub_overflowi64 x y bin = (
  let s = (scast x) - (scast y) - (scast bin) in
    if i64_MIN \<le>s s \<and> s \<le>s i64_MAX then 0 else 1
)"


datatype val = Vundef | Vbyte u8 | Vshort u16 | Vint u32 | Vlong u64


definition cl_mask6 :: "u8 \<Rightarrow> nat" 
  where "cl_mask6 w \<equiv> (unat w) mod 64"

definition cl_mask3 :: "u8 \<Rightarrow> nat" 
  where "cl_mask3 w \<equiv> (unat w) mod 32"

subsection \<open> 16-bit Arithmetic operations \<close>

definition rol16 :: "val \<Rightarrow> val \<Rightarrow> val" where \<comment> \<open> bswap 16 \<close>
"rol16 v n = (
  case v of                     
  Vshort v1 \<Rightarrow> (case n of Vbyte n1 \<Rightarrow>
    let n1 = n1 mod 16 in
    Vshort (Bit_Operations.or (v1 << (unat n1)) (v1 >> (unat (16 - n1))))
  | _ \<Rightarrow> Vundef)                                               
 |  _ \<Rightarrow> Vundef
)"

definition add16 :: "val \<Rightarrow> val \<Rightarrow> val" where
"add16 v1 v2 = (
  case v1 of
    Vshort n1 \<Rightarrow> (case v2 of Vshort n2 \<Rightarrow> Vshort (n1 + n2) | _ \<Rightarrow> Vundef) |
    _ \<Rightarrow> Vundef
)"

subsection \<open> 32-bit Arithmetic operations \<close>


definition longofintu :: "val \<Rightarrow> val" where
"longofintu v = (
  case v of
    Vint i \<Rightarrow> Vlong (ucast i) |
    _ \<Rightarrow> Vundef
)"

definition longofints :: "val \<Rightarrow> val" where
"longofints v = (
  case v of
    Vint i \<Rightarrow> Vlong (scast i) |
    _ \<Rightarrow> Vundef
)"

(*value "longofints (Vint 0xa3406d58)"*)

definition intoflongl:: "val \<Rightarrow> val" where
"intoflongl v = (
  case v of
    Vlong i \<Rightarrow> Vint (ucast i) |
    _ \<Rightarrow> Vundef
)"

definition intoflongh :: "val \<Rightarrow> val" where
"intoflongh v = (
  case v of
    Vlong i \<Rightarrow> Vint (ucast(i>>32)) |
    _ \<Rightarrow> Vundef
)"

definition signex32 :: "val \<Rightarrow> val" where
"signex32 v = (
  case v of
    Vint n \<Rightarrow> 
      let i::u64 = scast n in
      let d::u32 = ucast (i >> 32) in
        (Vint d)|
      _ \<Rightarrow> Vundef
)"
 \<comment> \<open> value "signex32 (Vint 0xFFFF8000)" \<close>

definition neg32 :: "val \<Rightarrow> val" where
"neg32 v = (
  case v of
    Vint n \<Rightarrow> Vint (- n) |
    _ => Vundef
)"

definition maketotal :: "val option \<Rightarrow> val" where
"maketotal ov = (case ov of Some v \<Rightarrow> v | None \<Rightarrow> Vundef)"

definition add32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"add32 v1 v2 = (
  case v1 of
    Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (n1 + n2) | _ \<Rightarrow> Vundef) |
    _ \<Rightarrow> Vundef
)"

definition sub32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"sub32 v1 v2 = (
  case v1 of
    Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (n1 - n2) | _ \<Rightarrow> Vundef) |
    _ \<Rightarrow> Vundef
)"

definition mul32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"mul32 v1 v2 = (
  case v1 of
    Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (n1 * n2) | _ \<Rightarrow> Vundef) |
    _ \<Rightarrow> Vundef
)"


definition mulhu32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"mulhu32 v1 v2 = (
  case v1 of Vint w1 \<Rightarrow> ( 
    case v2 of Vint w2 \<Rightarrow> 
      let prod64 = (uint w1) * (uint w2) in     
      let  hi32    = prod64 div (2 ^ 32) in  
      (Vint (word_of_int hi32))
     |
    _ \<Rightarrow>  Vundef)
  | _ \<Rightarrow> Vundef
)"

definition mulhs32 :: "val \<Rightarrow> val \<Rightarrow> val" where
  "mulhs32 v1 v2 = (
     case v1 of Vint w1 \<Rightarrow>
       (case v2 of Vint w2 \<Rightarrow>
          let  w1s64 = scast w1 :: u64 in
          let  w2s64 = scast w2 :: u64 in
          let  prod64 = w1s64 * w2s64    in
          let  hi32_word64 = prod64 >> 32 in
          let  hi32 = ucast hi32_word64 :: u32 in
            (Vint hi32)
       | _ \<Rightarrow> Vundef)
     | _ \<Rightarrow> Vundef )"

(*value "mulhs32 (Vint 0xCAE5CED) (Vint 0x2AD33EBD)"*)

(*
value "mulhu32 (Vint 0xC3BCA93E) (Vint 0x18BD2FEE)"
definition mulhu322 :: "val \<Rightarrow> val \<Rightarrow> val" where
"mulhu322 v1 v2 = (
  case v1 of
    Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint ((n1 * n2) div (2 ^ 32) ) | _ \<Rightarrow> Vundef) |
    _ \<Rightarrow> Vundef
)"

definition mulhs32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"mulhs32 v1 v2 = (
  case v1 of
    Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> 
                Vint ( ((scast n1) * (scast n2)) div (2 ^ 32) )  | _ \<Rightarrow> Vundef) |
    _ \<Rightarrow> Vundef
)"*)

\<comment>\<open> ` x86 style extended division and modulusv` \<close>
definition divmod32u :: "val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (val \<times> val) option" where
"divmod32u v1 v2 v3 = (           
  case v1 of 
    Vint nh \<Rightarrow> (case v2 of 
      Vint nl \<Rightarrow> (case v3 of 
        Vint d \<Rightarrow> if d \<noteq> 0 then
           let
              divisor   ::u64 = ucast d;
              dividend  ::u64 = Bit_Operations.or (((ucast nh)::u64) << 32) (ucast nl);
              quotient  ::u64 = dividend div divisor;
              remainder ::u64 = dividend mod divisor
            in
              if quotient \<le> ucast u32_MAX then
                Some (Vint (ucast quotient), Vint (ucast remainder))
              else
                None
            else
              None
      | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)
  | _ \<Rightarrow> None
)"



definition bswap32 :: "val \<Rightarrow> val" where
"bswap32 v =(
  case v of 
    Vint n \<Rightarrow>( 
      let byte0 = (and n 0xFF) << 24 in
      let byte1 = (and n 0xFF00) << 8 in
      let byte2 = (and n 0xFF0000) >> 8 in                       
      let byte3 = (and n 0xFF000000) >> 24 in
      Vint (or (or (or byte0 byte1) byte2) byte3)
  )
  | _ \<Rightarrow> Vundef
)"

fun sdiv0 :: "int \<Rightarrow> int \<Rightarrow> int"   (infixl "sdiv0" 70) where
  "x sdiv0 y = (if y = 0 then 0        
                else if (x \<ge> 0 \<and> y > 0) \<or> (x \<le> 0 \<and> y < 0)
                     then x div y   
                     else - ( (-x) div y))" 

definition smod0 :: "int \<Rightarrow> int \<Rightarrow> int"   (infixl "smod0" 70) where
  "x smod0 y = x - (x sdiv0 y) * y" 


definition divmod32s :: "val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (val \<times> val) option" where
"divmod32s v1 v2 v3 = (
  case v1 of Vint nh \<Rightarrow> 
    (case v2 of  Vint nl \<Rightarrow> 
      (case v3 of  Vint d \<Rightarrow> if d = 0 then None else
          let dividend  = (((sint nh) :: int)* (2^ 32)) + (uint nl);
               divisor   = sint d;
               q         = dividend sdiv0 divisor;
               r         = dividend smod0 divisor
           in
              if  q \<ge> - (2^31) \<and> q \<le> 2^31 - 1 then
                Some (Vint (word_of_int q), Vint (word_of_int r))
              else
                None
      | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)
  | _ \<Rightarrow> None
)"

(*value "divmod32s (Vint 0xFB46A459) (Vint 0xD84E74A4) (Vint 0xEC818EBA)"
value "divmod32s (Vint 0xDBEDE14D) (Vint 0xC831885A) (Vint 0x57D8BDC3)"*)


definition sub_overflow32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"sub_overflow32 v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (sub_overflowi32 n1 n2 0) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition negative32 :: "val \<Rightarrow> val" where
"negative32 v = (
  case v of
  Vint n \<Rightarrow> Vint (if (scast n) <s (0::i32) then 1 else 0 ) |
  _ \<Rightarrow> Vundef
)"

definition or32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"or32 v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (Bit_Operations.or n1 n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition and32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"and32 v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (Bit_Operations.and n1 n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition xor32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"xor32 v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (Bit_Operations.xor n1 n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"



definition shl32 :: "val \<Rightarrow> val \<Rightarrow> val"  where
"shl32 v1 v2 = (
   case v1 of
     Vint n1 \<Rightarrow> (case v2 of
       Vbyte n2 \<Rightarrow>
         let s = cl_mask3 n2  
         in  Vint (n1 << s)
     | _ \<Rightarrow> Vundef)
   | _ \<Rightarrow> Vundef)"

definition shr32 :: "val \<Rightarrow> val \<Rightarrow> val"  where
"shr32 v1 v2 = (
   case v1 of
     Vint n1 \<Rightarrow> (case v2 of
       Vbyte n2 \<Rightarrow>
         let s = cl_mask3 n2
         in  Vint (n1 >> s)
     | _ \<Rightarrow> Vundef)
   | _ \<Rightarrow> Vundef)"

definition sar32 :: "val \<Rightarrow> val \<Rightarrow> val"  where
"sar32 v1 v2 = (
   case v1 of
     Vint n1 \<Rightarrow> (case v2 of
       Vbyte n2 \<Rightarrow>
         let s = cl_mask3 n2 in
         let res = word_of_int (sint n1 div 2 ^ s)
         in  Vint res
     | _ \<Rightarrow> Vundef)
   | _ \<Rightarrow> Vundef)"

definition ror32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"ror32 v n = (                                                   
  case v of                     
  Vshort v1 \<Rightarrow> (case n of Vbyte n1 \<Rightarrow>
    let  n1 = n1 mod 32 in
     Vshort (Bit_Operations.or (v1 >> (unat n1)) (v1 << (unat (32 - n1))))
  | _ \<Rightarrow> Vundef)  
 |  _ \<Rightarrow> Vundef
)"

subsection \<open> 64-bit Arithmetic operations \<close>

definition signex64 :: "val \<Rightarrow> val" where
"signex64 v = (
  case v of
    Vlong n \<Rightarrow> 
      let i::u128 = scast n in
      let d::u64  = ucast (i >> 64) in
        (Vlong d)|
      _ \<Rightarrow> Vundef
)"

definition neg64 :: "val \<Rightarrow> val" where
"neg64 v = (
  case v of
  Vlong n \<Rightarrow> Vlong (- n) |
  _ => Vundef
)"

definition add64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"add64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vlong (n1 + n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef                           
)"

definition sub64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"sub64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vlong (n1 - n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition mul64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"mul64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vlong (n1 * n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition mulhu64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"mulhu64 v1 v2 = (
  case v1 of Vlong w1 \<Rightarrow> ( 
    case v2 of Vlong w2 \<Rightarrow> 
      let prod128 = (uint w1) * (uint w2) in     
      let  hi64    = prod128 div (2 ^ 64) in  
      (Vlong (word_of_int hi64))|
    _ \<Rightarrow> Vundef
    )
  | _ \<Rightarrow> Vundef
)"

(*value "mulhu64 (Vlong 0x832C6E98D40CF303) (Vlong 0x1AC2B637142DDF17)"*)

definition mulhs64 :: "val \<Rightarrow> val \<Rightarrow> val" where
  "mulhs64 v1 v2 = (
     case v1 of Vlong w1 \<Rightarrow>
       (case v2 of Vlong w2 \<Rightarrow>
          let  w1s128 = scast w1 :: u128 in
          let  w2s128 = scast w2 :: u128 in
          let  prod128 = w1s128 * w2s128    in
          let  hi64_word128 = prod128 >> 64 in
          let  hi64 = ucast hi64_word128 :: u64 in
            (Vlong hi64)
       | _ \<Rightarrow> Vundef)
     | _ \<Rightarrow> Vundef )"


\<comment>\<open> ` x86 style extended division and modulusv` \<close>

definition divmod64u :: "val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (val \<times> val) option" where
"divmod64u v1 v2 v3 = (
   case v1 of Vlong nh \<Rightarrow> (
     case v2 of Vlong nl \<Rightarrow> (
       case v3 of Vlong d \<Rightarrow>(
         if d \<noteq> 0 then
           let  dividend  = Bit_Operations.or (((ucast nh)::u128) << 64)  (ucast nl) in
           let  quotient  = dividend div (ucast d) in
           let  remainder = dividend mod (ucast d)  in
            if quotient \<le> ucast u64_MAX then
             Some (Vlong (ucast quotient), Vlong (ucast remainder))
            else None
         else None )
       | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)
   | _ \<Rightarrow> None)"


definition divmod64s :: "val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (val \<times> val) option" where
"divmod64s v1 v2 v3 = (
  case v1 of Vlong nh \<Rightarrow> 
    (case v2 of Vlong nl \<Rightarrow> 
      (case v3 of Vlong d \<Rightarrow> if d = 0 then None else
          let dividend  = (((sint nh) :: int) * (2^64)) + (uint nl); 
               divisor   = sint d;
               q         = dividend sdiv0 divisor;
               r         = dividend smod0 divisor
           in
              if  q \<ge> - (2^63) \<and> q \<le> 2^63 - 1 then
                Some (Vlong (word_of_int q), Vlong (word_of_int r))
              else
                None
      | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)
  | _ \<Rightarrow> None
)"
(*value "divmod64s (Vlong 0xFB65FEFF6FF47AEE) (Vlong 0x452F0C982D21021A) (Vlong 0x30214063B01654DC)"*)

(*value "divmod64u (Vlong 0x81BE036B5441E8C0) (Vlong 0x162C63C7F93D44BC) (Vlong 0xE880EF4C993CC4F4)"*)

(*definition divmod64s :: "val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (val \<times> val) option" where
"divmod64s v1 v2 v3 = (
  case v1 of  Vlong nh \<Rightarrow> 
    (case v2 of Vlong nl \<Rightarrow> 
      (case v3 of Vlong d \<Rightarrow> if d \<noteq> 0 then
           let
              divisor::i128   = scast d;
              dividend::i128  = Bit_Operations.or (((scast nh)::i128) << 64) (scast nl);
              quotient::i128  = dividend div divisor;
              remainder::i128 = dividend mod divisor
            in
              if quotient \<le>s(scast i64_MAX) \<and> (scast i64_MIN) \<le>s quotient then
                Some (Vlong (ucast quotient), Vlong (ucast remainder))
              else
                None
            else
              None
      | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)
  | _ \<Rightarrow> None
)"*)
(*value "divmod64s  (Vlong 0xE78C3B9597713344)(Vlong 0xF53AA4F3C9761923) (Vlong 0x61C122ABD34AB718)"*)

(*value "divmod64u (Vlong 0x41312DB81DB54480) (Vlong 0x814D1520ED19E70E) (Vlong 0x7A73296A48B0CC01) " *)

(*definition divmod64u :: "val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (val \<times> val) option" where
"divmod64u v1 v2 v3 = (
  case v1 of 
    Vlong nh \<Rightarrow> (case v2 of 
      Vlong nl \<Rightarrow> (case v3 of 
        Vlong d \<Rightarrow> if d \<noteq> 0 then
           let
              divisor::u128   = ucast d;
              dividend::u128  = Bit_Operations.or ((ucast nh) << 64) (ucast nl);
              quotient::u128  = dividend div divisor;
              remainder::u128 = dividend mod divisor
            in
              Some (Vlong (ucast quotient), Vlong (ucast remainder))
              \<comment>\<open> if quotient \<le> ucast u64_MAX then
                Some (Vlong (ucast quotient), Vlong (ucast remainder))
              else
                None \<close>
            else
              None
      | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)
  | _ \<Rightarrow> None
)"
*)


definition sub_overflow64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"sub_overflow64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vint (ucast (sub_overflowi64 n1 n2 0)) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition negative64 :: "val \<Rightarrow> val" where
"negative64 v = (
  case v of
  Vlong n \<Rightarrow> Vlong (if (scast n) <s (0::i64) then 1 else 0 ) |
  _ \<Rightarrow> Vundef
)"

definition or64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"or64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vlong (Bit_Operations.or n1 n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition xor64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"xor64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vlong (Bit_Operations.xor n1 n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition and64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"and64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vlong (Bit_Operations.and n1 n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition shl64_2 :: "val \<Rightarrow> val \<Rightarrow> val" where
"shl64_2 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vbyte n2 \<Rightarrow> Vlong (n1 << (unsigned n2)) | _ \<Rightarrow> Vundef) | \<comment> \<open>`v2 = RCX - CL`\<close>
  _ \<Rightarrow> Vundef
)"


definition shl64 :: "val \<Rightarrow> val \<Rightarrow> val"  where
  "shl64 v1 v2 = (
     case v1 of
       Vlong n1 \<Rightarrow> (case v2 of
         Vbyte n2 \<Rightarrow>
           let s = cl_mask6 n2  
           in  Vlong (n1 << s)
       | _ \<Rightarrow> Vundef)
     | _ \<Rightarrow> Vundef)"

definition shr64 :: "val \<Rightarrow> val \<Rightarrow> val"  where
  "shr64 v1 v2 = (
     case v1 of
       Vlong n1 \<Rightarrow> (case v2 of
         Vbyte n2 \<Rightarrow>
           let s = cl_mask6 n2
           in  Vlong (n1 >> s)
       | _ \<Rightarrow> Vundef)
     | _ \<Rightarrow> Vundef)"

(*value "shr64 (Vlong 0xE9273BF48579EAFC) (Vbyte 0x40)"
value "shl64 (Vlong 0xE9273BF48579EAFC) (Vbyte 0x40)"*)

definition sar64 :: "val \<Rightarrow> val \<Rightarrow> val"  where
  "sar64 v1 v2 = (
     case v1 of
       Vlong n1 \<Rightarrow> (case v2 of
         Vbyte n2 \<Rightarrow>
           let s = cl_mask6 n2 in
           let res = word_of_int (sint n1 div 2 ^ s)
           in  Vlong res
       | _ \<Rightarrow> Vundef)
     | _ \<Rightarrow> Vundef)"

(*value "sar64 (Vlong 0xB1341E1CC2072557) (Vbyte 3)"*)

definition ror64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"ror64 v n = (
  case v of                     
  Vshort v1 \<Rightarrow> (case n of Vbyte n1 \<Rightarrow>
    let  n1 = n1 mod 64 in
     Vshort (Bit_Operations.or (v1 >> (unat n1)) (v1 << (unat (32 - n1))))
  | _ \<Rightarrow> Vundef)  
 |  _ \<Rightarrow> Vundef
)"

definition bswap64 :: "val \<Rightarrow> val" where
"bswap64 v = (
  case v of 
    Vint n \<Rightarrow> (
      let byte0 = (and n 0xFF) << 56 in
      let byte1 = (and n 0xFF00) << 40 in
      let byte2 = (and n 0xFF0000) << 24 in
      let byte3 = (and n 0xFF000000) << 8 in
      let byte4 = (and n 0xFF00000000) >> 8 in
      let byte5 = (and n 0xFF0000000000) >> 24 in
      let byte6 = (and n 0xFF000000000000) >> 40 in
      let byte7 = (and n 0xFF00000000000000) >> 56 in
      Vint (or (or (or (or (or (or (or byte0 byte1) byte2) byte3) byte4) byte5) byte6) byte7)
    )
  | _ \<Rightarrow> Vundef
)"
subsection \<open> Comparisons \<close>

datatype comparison =
    Ceq (* same *)
  | Cne (* different *)
  | Clt (* less than *)
  | Cle (* less than or equal *)
  | Cgt (* greater than *)
  | Cge (* greater than or equal *)


definition cmpi32 :: "comparison \<Rightarrow> i32 \<Rightarrow> i32 \<Rightarrow> bool" where
"cmpi32 c x y = (
  case c of
  Ceq \<Rightarrow> x = y |
  Cne \<Rightarrow> x \<noteq> y |
  Clt \<Rightarrow> x <s y |
  Cle \<Rightarrow> x \<le>s y |
  Cgt \<Rightarrow> y <s x |
  Cge \<Rightarrow> y \<le>s x
)"

definition cmpu32 :: "comparison \<Rightarrow> u32 \<Rightarrow> u32 \<Rightarrow> bool" where
"cmpu32 c x y = (
  case c of
  Ceq \<Rightarrow> x = y |
  Cne \<Rightarrow> x \<noteq> y |
  Clt \<Rightarrow> x < y |
  Cle \<Rightarrow> x \<le> y |
  Cgt \<Rightarrow> y < x |
  Cge \<Rightarrow> y \<le> x
)"


definition cmpi64 :: "comparison \<Rightarrow> i64 \<Rightarrow> i64 \<Rightarrow> bool" where
"cmpi64 c x y = (
  case c of
  Ceq \<Rightarrow> x = y |
  Cne \<Rightarrow> x \<noteq> y |
  Clt \<Rightarrow> x <s y |
  Cle \<Rightarrow> x \<le>s y |
  Cgt \<Rightarrow> y <s x |
  Cge \<Rightarrow> y \<le>s x
)"

definition cmpu64 :: "comparison \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> bool" where
"cmpu64 c x y = (
  case c of
  Ceq \<Rightarrow> x = y |
  Cne \<Rightarrow> x \<noteq> y |
  Clt \<Rightarrow> x < y |
  Cle \<Rightarrow> x \<le> y |
  Cgt \<Rightarrow> y < x |
  Cge \<Rightarrow> y \<le> x
)"

definition cmp_bool :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool option" where
"cmp_bool c v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Some (cmpi32 c (scast n1) (scast n2)) | _ \<Rightarrow> None) |
  _ \<Rightarrow> None
)"

definition cmpu_bool :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool option" where
"cmpu_bool c v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Some (cmpu32 c n1 n2) | _ \<Rightarrow> None) |
  _ \<Rightarrow> None
)"

definition cmpl_bool :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool option" where
"cmpl_bool c v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Some (cmpi64 c (scast n1) (scast n2)) | _ \<Rightarrow> None) |
  _ \<Rightarrow> None
)"

definition cmplu_bool :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool option" where
"cmplu_bool c v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Some (cmpu64 c n1 n2) | _ \<Rightarrow> None) |
  _ \<Rightarrow> None
)"

definition of_optbool :: " bool option \<Rightarrow> val" where
"of_optbool ob = (case ob of None \<Rightarrow> Vundef | Some True \<Rightarrow> Vint 1 | Some False \<Rightarrow> Vint 0)"

definition cmp :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
"cmp c v1 v2 = of_optbool (cmp_bool c v1 v2)"

definition cmpu :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
"cmpu c v1 v2 = of_optbool (cmpu_bool c v1 v2)"

definition cmpl :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
"cmpl c v1 v2 = of_optbool (cmpl_bool c v1 v2)"

definition cmplu :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
"cmplu c v1 v2 = of_optbool (cmplu_bool c v1 v2)"

end