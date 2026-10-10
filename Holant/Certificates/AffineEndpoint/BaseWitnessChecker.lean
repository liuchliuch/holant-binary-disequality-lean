import Holant.Certificates.AffineEndpoint.BaseTransformData
import Holant.Certificates.AffineEndpoint.WitnessChecker
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Certificates.OctahedralSeparator IntegerValues
 def BaseWitnessCheck (s : SupportCatalog.SupportIndex) (c : Nat) (b : Bool) (w : ℕ) : Prop :=
  if hw : w<8 then baseIntegerOutput s c b (oddCode ⟨w,hw⟩)≠zero else
  if w=8 then baseIntegerOutput s c b 0=zero else
  if w=9 then baseIntegerOutput s c b 15=zero else
  if w=10 then ∀i : Fin 6,baseIntegerOutput s c b (centralCode i)=zero else
  let r : Fin 612 := ⟨(w-11)/6%612,Nat.mod_lt _ (by decide)⟩
  let p : Fin 6 := ⟨(w-11)%6,Nat.mod_lt _ (by decide)⟩
  let g := baseIntegerOutput s c b
  let h := fastIntegerInput (referenceInput r).1 (referenceInput r).2.val
  g (centralCode p)≠zero ∧ h (centralCode p)≠zero ∧
    (∀i : Fin 6,IntegerCoefficient.mul (g (centralCode i)) (h (centralCode p))=
      IntegerCoefficient.mul (g (centralCode p)) (h (centralCode i))) ∧
    IntegerCoefficient.mul (IntegerCoefficient.mul (g 15) (g 0))
        (IntegerCoefficient.mul (h (centralCode p)) (h (centralCode p)))=
      IntegerCoefficient.mul (IntegerCoefficient.mul (g (centralCode p)) (g (centralCode p))) (h 15)

 instance (s : SupportCatalog.SupportIndex) (c : Nat) (b : Bool) (w : Nat) :
    Decidable (BaseWitnessCheck s c b w) := by unfold BaseWitnessCheck; infer_instance
end Holant.Certificates.AffineEndpoint
