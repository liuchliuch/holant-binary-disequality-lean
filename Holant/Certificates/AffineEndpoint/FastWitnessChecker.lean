import Holant.Certificates.AffineEndpoint.FastTransformData
import Holant.Certificates.AffineEndpoint.WitnessChecker
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Certificates.OctahedralSeparator IntegerValues
 def FastWitnessCheck (s : SupportCatalog.SupportIndex) (c : Nat) (k : Fin 18) (w : ℕ) : Prop :=
  if hw : w<8 then fastIntegerOutput s c k (oddCode ⟨w,hw⟩)≠zero else
  if w=8 then fastIntegerOutput s c k 0=zero else
  if w=9 then fastIntegerOutput s c k 15=zero else
  if w=10 then ∀i : Fin 6,fastIntegerOutput s c k (centralCode i)=zero else
  let r : Fin 612 := ⟨(w-11)/6%612,Nat.mod_lt _ (by decide)⟩
  let p : Fin 6 := ⟨(w-11)%6,Nat.mod_lt _ (by decide)⟩
  let g := fastIntegerOutput s c k
  let h := fastIntegerInput (referenceInput r).1 (referenceInput r).2.val
  g (centralCode p)≠zero ∧ h (centralCode p)≠zero ∧
    (∀i : Fin 6,IntegerCoefficient.mul (g (centralCode i)) (h (centralCode p))=
      IntegerCoefficient.mul (g (centralCode p)) (h (centralCode i))) ∧
    IntegerCoefficient.mul (IntegerCoefficient.mul (g 15) (g 0))
        (IntegerCoefficient.mul (h (centralCode p)) (h (centralCode p)))=
      IntegerCoefficient.mul (IntegerCoefficient.mul (g (centralCode p)) (g (centralCode p))) (h 15)

 instance (s : SupportCatalog.SupportIndex) (c : Nat) (k : Fin 18) (w : Nat) :
    Decidable (FastWitnessCheck s c k w) := by unfold FastWitnessCheck; infer_instance
end Holant.Certificates.AffineEndpoint
