import Holant.Certificates.AffineEndpoint.SupportEnumeration

namespace Holant.Certificates.AffineEndpoint
open Holant.Tractable.AffinePhase
set_option backward.isDefEq.respectTransparency false

 def wordCode (x : Word 4) : Fin 16 :=
  (if x 0 then 8 else 0)+(if x 1 then 4 else 0)+(if x 2 then 2 else 0)+(if x 3 then 1 else 0)

 def codeWord : Fin 16→Word 4 :=
  ![![false,false,false,false],![false,false,false,true],![false,false,true,false],![false,false,true,true],
    ![false,true,false,false],![false,true,false,true],![false,true,true,false],![false,true,true,true],
    ![true,false,false,false],![true,false,false,true],![true,false,true,false],![true,false,true,true],
    ![true,true,false,false],![true,true,false,true],![true,true,true,false],![true,true,true,true]]

 theorem wordCode_codeWord : ∀i,wordCode (codeWord i)=i := by decide +kernel
 theorem codeWord_wordCode : ∀x,codeWord (wordCode x)=x := by decide +kernel

 def wordEquiv : Fin 16 ≃ Word 4 where
  toFun := codeWord
  invFun := wordCode
  left_inv := wordCode_codeWord
  right_inv := codeWord_wordCode

 theorem codeWord_injective : Function.Injective codeWord := wordEquiv.injective
 theorem wordCode_injective : Function.Injective wordCode := wordEquiv.symm.injective

 def decodeSupport (S : Finset (Fin 16)) : Finset (Word 4) := S.map ⟨codeWord,codeWord_injective⟩
 theorem decodeSupport_injective : Function.Injective decodeSupport := Finset.map_injective _

 theorem decodeSupport_card (S : Finset (Fin 16)) : (decodeSupport S).card=S.card := Finset.card_map _

end Holant.Certificates.AffineEndpoint
