import Holant.Proofs.Hardness.GeneralEOPairedFamilyDuplicate
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionOrientation
import Holant.Proofs.Platonic.PhysicalCostComposition

/-! A finite signed palette consists solely of repeated original labels.
Negating compressed arguments is realized by reversing their actual covering
pair directions. All reductions below keep one fixed coefficient field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilySigned
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity BinaryCompose
namespace D
export GeneralEOPairedFamilyDuplicate (arities arity_label signatures query controlled)
end D
namespace O
export GeneralEOPairedFamilyExtractionOrientation (pairing covers compressed_value xorWord)
end O
namespace N
export GeneralEOPairedCSPFamilyNative (totalValue totalControlled)
end N
namespace Pn
export GeneralEOPairedFamilyExtractionPinNative (value controlled)
end Pn
namespace T
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {d s t : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K d) (G : (i : Fin s) → Signature K (arity i.val))
variable (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))
variable (label : Fin t → Fin s)
variable (signs : (i : Fin t) → Fin (P (label i)).count → Bool)

def basePairing (i : Fin t) : OrientedPerfectPairing (D.arities (arity:=arity) label i.val) where
  count := (P (label i)).count
  ports := (P (label i)).ports.trans (finCongr (D.arity_label label i).symm)

def pairing (i : Fin t) : OrientedPerfectPairing (D.arities (arity:=arity) label i.val) :=
  O.pairing (basePairing P label i) (signs i)

omit [Algebra ℚ K] [CharZero K] in
theorem base_covers (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) (i : Fin t) :
    GeneralEOPairedCSPCycles.Covers (basePairing P label i) (D.signatures G label i) := by
  intro x hx j
  have h := hf (label i) (fun k => x (Fin.cast (D.arity_label label i).symm k)) hx j
  exact h

omit [Algebra ℚ K] [CharZero K] in
theorem covers (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) (i : Fin t) :
    GeneralEOPairedCSPCycles.Covers (pairing P label signs i) (D.signatures G label i) :=
  O.covers (basePairing P label i) (signs i) (D.signatures G label i) (base_covers G P label hf i)

omit [Algebra ℚ K] [CharZero K] in
theorem base_compressed (i : Fin t) (z : Fin (P (label i)).count → Bool) :
    GeneralEOPairedCSPCycles.compress (basePairing P label i) (D.signatures G label i) z=
      GeneralEOPairedCSPCycles.compress (P (label i)) (G (label i)) z := by
  unfold GeneralEOPairedCSPCycles.compress D.signatures OrientedPerfectPairing.word basePairing
  simp only [Equiv.symm_trans_apply,finCongr_symm,finCongr_apply]
  congr 1

omit [Algebra ℚ K] [CharZero K] in
theorem signed_compressed (i : Fin t) (z : Fin (P (label i)).count → Bool) :
    GeneralEOPairedCSPCycles.compress (pairing P label signs i) (D.signatures G label i) z=
      GeneralEOPairedCSPCycles.compress (P (label i)) (G (label i))
        (fun j => Bool.xor (signs i j) (z j)) := by
  unfold pairing
  rw [O.compressed_value,base_compressed]
  rfl

abbrev value := N.totalValue (D.signatures G label) (pairing P label signs)
abbrev pinnedValue := Pn.value (D.signatures G label) (pairing P label signs)

/-- Arbitrary signed compressed literals reduce to the literal original
signature dictionary by a real query writer and duplicate-label recoder. -/
def controlled (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction (GeneralEOPairedCSPFamilyRaw.encoding t) F.encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
      (value G P label signs) (GeneralEOPairedCSPNative.targetValue F G) :=
  T.composeControlled
    (N.totalControlled F (D.signatures G label) (pairing P label signs) (covers G P label signs hf))
    (D.controlled F G label)

/-- Reserved constants are eliminated internally before any original-family
query. No pin signature, field equality or supplied reduction is assumed. -/
def pinnedControlled (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction (GeneralEOPairedCSPFamilyRaw.encoding t) F.encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
      (pinnedValue G P label signs) (GeneralEOPairedCSPNative.targetValue F G) :=
  T.composeControlled
    (Pn.controlled F (D.signatures G label) (pairing P label signs) (covers G P label signs hf))
    (controlled F G P label signs hf)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilySigned
