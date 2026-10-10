import Holant.Certificates.AffineEndpoint.BaseWitnessChecker

/-! Packet evaluation builds the fixed support descriptor once, outside the
phase-code loop. The descriptor is derived from the actual cached chart data. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Certificates.OctahedralSeparator IntegerValues
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

structure InputDescriptor where
  dimension : Nat
  terms : List (Bool × Fin 16 × Fin 16)

 def supportDescriptor (s : SupportCatalog.SupportIndex) : InputDescriptor where
  dimension := fastSupportDimension s
  terms := List.ofFn fun y : Fin 16 =>
    ((fastSupportMask s).testBit y.val,y,fastSupportCoordinates s y)

 def descriptorTerm (p : InputDescriptor) (c : Nat) (b : Bool) (x : Fin 16)
    (t : Bool × Fin 16 × Fin 16) : Coeff :=
  if t.1 then rotate (baseTensor b x t.2.1)
    ⟨DigitPhaseRuntime.exponent p.dimension c t.2.2.val,DigitPhaseRuntime.exponent_lt _ _ _⟩ else zero

 def descriptorOutput (p : InputDescriptor) (c : Nat) (b : Bool) (x : Fin 16) : Coeff :=
  IntegerValues.sum (p.terms.map (descriptorTerm p c b x))

 theorem descriptorOutput_eq (s : SupportCatalog.SupportIndex) (c : Nat) (b : Bool) (x : Fin 16) :
    descriptorOutput (supportDescriptor s) c b x=baseIntegerOutput s c b x := by
  simp only [descriptorOutput,supportDescriptor,List.map_ofFn]
  rfl

 def DescriptorCheck (D : InputDescriptor) (c : Nat) (b : Bool) (w : ℕ) : Prop :=
  if hw : w<8 then descriptorOutput D c b (oddCode ⟨w,hw⟩)≠zero else
  if w=8 then descriptorOutput D c b 0=zero else
  if w=9 then descriptorOutput D c b 15=zero else
  if w=10 then ∀i : Fin 6,descriptorOutput D c b (centralCode i)=zero else
  let r : Fin 612 := ⟨(w-11)/6%612,Nat.mod_lt _ (by decide)⟩
  let p : Fin 6 := ⟨(w-11)%6,Nat.mod_lt _ (by decide)⟩
  let g := descriptorOutput D c b
  let h := fastIntegerInput (referenceInput r).1 (referenceInput r).2.val
  g (centralCode p)≠zero ∧ h (centralCode p)≠zero ∧
    (∀i : Fin 6,IntegerCoefficient.mul (g (centralCode i)) (h (centralCode p))=
      IntegerCoefficient.mul (g (centralCode p)) (h (centralCode i))) ∧
    IntegerCoefficient.mul (IntegerCoefficient.mul (g 15) (g 0))
        (IntegerCoefficient.mul (h (centralCode p)) (h (centralCode p)))=
      IntegerCoefficient.mul (IntegerCoefficient.mul (g (centralCode p)) (g (centralCode p))) (h 15)

 instance (p : InputDescriptor) (c : Nat) (b : Bool) (w : Nat) : Decidable (DescriptorCheck p c b w) := by
  unfold DescriptorCheck; infer_instance

 theorem descriptorCheck_iff (s : SupportCatalog.SupportIndex) (c : Nat) (b : Bool) (w : Nat) :
    DescriptorCheck (supportDescriptor s) c b w ↔ BaseWitnessCheck s c b w := by
  simp only [DescriptorCheck,BaseWitnessCheck,descriptorOutput_eq]

 def packetCheck (s : SupportCatalog.SupportIndex) (b : Bool) (start : Nat) (ws : Array Nat) : Bool :=
  let p := supportDescriptor s
  (List.range ws.size).all (fun i => decide (DescriptorCheck p (start+i) b (ws.getD i 0)))

 theorem packetCheck_sound (s : SupportCatalog.SupportIndex) (b : Bool) (start : Nat) (ws : Array Nat)
    (h : packetCheck s b start ws=true) (i : Nat) (hi : i<ws.size) :
    BaseWitnessCheck s (start+i) b (ws.getD i 0) := by
  apply (descriptorCheck_iff s (start+i) b (ws.getD i 0)).mp
  exact of_decide_eq_true (List.all_eq_true.mp h i (List.mem_range.mpr hi))

end Holant.Certificates.AffineEndpoint
