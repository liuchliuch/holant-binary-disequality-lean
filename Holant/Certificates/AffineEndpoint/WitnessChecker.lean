import Holant.Certificates.AffineEndpoint.IntegerTransformData
import Holant.Certificates.AffineEndpoint.References

/-! A small division-free checker. Negative certificates identify one literal
forbidden coefficient; positive certificates give an actual affine reference
and a surviving central coordinate. Completeness is checked separately. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Certificates.OctahedralSeparator IntegerValues
set_option maxRecDepth 100000

 def oddCode : Fin 8 → Fin 16 := ![1,2,4,7,8,11,13,14]
 def centralCode : Fin 6 → Fin 16 := ![3,5,6,9,10,12]
 theorem oddCode_weight : ∀i,Holant.weight (codeWord (oddCode i))%2=1 := by decide +kernel
 theorem centralCode_word : ∀i,codeWord (centralCode i)=centralWord i := by decide +kernel
 theorem zeroCode_word : codeWord 0=zeroWord := by decide
 theorem oneCode_word : codeWord 15=oneWord := by decide

 def WitnessCheck (c : InputCode) (k : Fin 18) (w : ℕ) : Prop :=
  if hw : w<8 then integerOutput c k (oddCode ⟨w,hw⟩)≠zero else
  if w=8 then integerOutput c k 0=zero else
  if w=9 then integerOutput c k 15=zero else
  if w=10 then ∀i : Fin 6,integerOutput c k (centralCode i)=zero else
  let r : Fin 612 := ⟨(w-11)/6%612,Nat.mod_lt _ (by decide)⟩
  let p : Fin 6 := ⟨(w-11)%6,Nat.mod_lt _ (by decide)⟩
  let g := integerOutput c k
  let h := integerInput (referenceInput r)
  g (centralCode p)≠zero ∧ h (centralCode p)≠zero ∧
    (∀i : Fin 6,IntegerCoefficient.mul (g (centralCode i)) (h (centralCode p))=
      IntegerCoefficient.mul (g (centralCode p)) (h (centralCode i))) ∧
    IntegerCoefficient.mul (IntegerCoefficient.mul (g 15) (g 0))
        (IntegerCoefficient.mul (h (centralCode p)) (h (centralCode p)))=
      IntegerCoefficient.mul (IntegerCoefficient.mul (g (centralCode p)) (g (centralCode p))) (h 15)

 instance (c : InputCode) (k : Fin 18) (w : ℕ) : Decidable (WitnessCheck c k w) := by
  unfold WitnessCheck
  infer_instance

end Holant.Certificates.AffineEndpoint
