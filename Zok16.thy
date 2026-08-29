theory Zok16
  imports Solidity_Main
begin

abbreviation "IntT     \<equiv> SType.TValue TSint"

abbreviation "ProofT a b c \<equiv> storage_data.Array [a,b,c]"
abbreviation "a \<equiv> 0::nat"
abbreviation "b \<equiv> 1::nat"
abbreviation "c \<equiv> 2::nat"


abbreviation "VerifyingKeyT alpha beta gamma delta gamma_abc \<equiv> storage_data.Array [alpha, beta, gamma, delta, gamma_abc]"
abbreviation "alpha \<equiv> 0::nat"
abbreviation "beta \<equiv> 1::nat"
abbreviation "gamma \<equiv> 2::nat"
abbreviation "delta \<equiv> 3::nat"
abbreviation "gamma_abc \<equiv> 4::nat"

abbreviation  "G1       \<equiv> SType.DArray IntT"
abbreviation  "G2       \<equiv> SType.DArray (SType.DArray IntT)"

abbreviation "snark_scalar_field \<equiv> STR ''snark_scalar_field''"

abbreviation "vk_abc   \<equiv> STR ''vk_abc''" 

abbreviation "vk_x     \<equiv> STR ''vk_x''"
abbreviation "input    \<equiv> STR ''input''"
abbreviation "proof_main \<equiv> STR ''proof_main''"

abbreviation "p1       \<equiv> STR ''p1''"
abbreviation "p2       \<equiv> STR ''p2''"
abbreviation "s        \<equiv> STR ''s''"
abbreviation "p        \<equiv> STR ''p''"

(* Temporary *)
abbreviation "temp0    \<equiv> STR ''temp0''"

contract Verifier
  for vk_x:G1
and vk_abc:"SType.DArray G1"
and  temp0: G1    (* For loading in G1(0,0) *)


constructor
where
  "\<langle>skip\<rangle>"

cfunction test
where
   "\<langle>skip\<rangle>",

cfunction negate
where
   "\<langle>skip\<rangle>",


cfunction addition external
  calldata p1:G1 and p2:G2 
where        
  "\<langle>skip\<rangle>",


cfunction scalar_mul external
  param s:IntT
  calldata p:G1
where
   "\<langle>skip\<rangle>",


cfunction PairingProd4
where
   "\<langle>skip\<rangle>",


cfunction verify external
  calldata input:"SType.DArray IntT" and proof_main:"SType.DArray (SType.DArray IntT)"
where
  "do {
     decl TSint snark_scalar_field;
     \<langle>assert\<rangle> ( (arrayLength (input) []) \<langle>+\<rangle> \<langle>sint\<rangle> 1  \<langle>=\<rangle>  (arrayLength (vk_abc) []) );   
     vk_x [] ::=\<^sub>s temp0 ~\<^sub>s [];
     \<langle>assert\<rangle> ( vk_x ~\<^sub>s [\<langle>sint\<rangle> 0]  \<langle>=\<rangle> \<langle>sint\<rangle> 0);
     \<langle>assert\<rangle> ( vk_x ~\<^sub>s [\<langle>sint\<rangle> 1]  \<langle>=\<rangle> \<langle>sint\<rangle> 0);
     init (Uint 0) (STR ''i'');
     while_monad ( ((STR ''i'') ~ []) \<langle><\<rangle> (storeArrayLength (input) []) )
      (do {
         \<langle>assert\<rangle> (input ~\<^sub>s [(STR ''i'') ~ []] \<langle><\<rangle> snark_scalar_field ~ []);
         (STR ''i'') [] ::= ((STR ''i'') ~ []) \<langle>+\<rangle> \<langle>sint\<rangle> 1
      })
  }"

end
