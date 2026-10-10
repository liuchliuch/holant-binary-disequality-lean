import Holant.Proofs.Hardness.GeneralEOPairedFamilyBundleValue
import Holant.Proofs.Hardness.GeneralEOPairedFamilySignedOriginal

/-! Finite signed tensor/minor palettes have a fully executed original-family
backend. The source does not assume a gadget oracle, a pin, or a reduction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler GeneralEOPairedCSPFamilyRaw
namespace W
export GeneralEOPairedFamilyBundleRaw (Recipe query queryComputes)
export GeneralEOPairedFamilyBundleValue (coefficient query_valid query_value)
end W
namespace Pn
export GeneralEOPairedFamilyExtractionPinNative (coefficients value controlled)
export GeneralEOPairedFamilyExtractionPinRaw (free)
end Pn
namespace S
export GeneralEOPairedFamilySigned (pairing signed_compressed pinnedControlled)
end S
namespace T
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end T
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {d s t : ℕ} {a b : ℕ → ℕ}
variable (F : FixedField K d) (G : (j : Fin t) → Signature K (b j.val))
variable (Q : (i : Fin s) → OrientedPerfectPairing (a i.val))
variable (P : (j : Fin t) → OrientedPerfectPairing (b j.val))
variable (recipe : W.Recipe Q P)

def value (r : Raw s) : K := if r.WellFormed Q then
  GeneralEOPairedCSPFamilyRaw.value Q (W.coefficient Q P recipe (Pn.coefficients G P)) r else 0

def rejected : Raw t := ⟨0,[],[0]⟩
theorem rejected_invalid : ¬(Pn.free (rejected (t:=t))).WellFormed P := by
  intro h
  have hh := h.1
  simp [rejected,Pn.free,Raw.edgeCount] at hh

def validatedQuery (r : Raw s) : Raw t :=
  if r.WellFormed Q then W.query Q P recipe r else rejected

def validatedComputes : Computes (encoding s) (encoding t) (validatedQuery Q P recipe) :=
  congrComputes (ifComputes (GeneralEOPairedCSPFamilyValidation.validates Q)
    (W.queryComputes Q P recipe) (constantComputes (encoding s) (encoding t) rejected))
    (fun r => by simp [validatedQuery])

omit [Algebra ℚ K] [CharZero K] in
theorem query_value (r : Raw s) : value G Q P recipe r = Pn.value G P (validatedQuery Q P recipe r) := by
  by_cases hr : r.WellFormed Q
  · simp only [value,validatedQuery,ite_eq_left hr,Pn.value,ite_eq_left (W.query_valid Q P recipe r hr)]
    exact (W.query_value Q P recipe (Pn.coefficients G P) r).symm
  · simp only [value,validatedQuery,ite_eq_right hr,Pn.value,ite_eq_right (rejected_invalid P)]

def toPinnedControlled (hf : ∀ i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction (encoding s) F.encoding (encoding t) F.encoding
      (value G Q P recipe) (Pn.value G P) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq (validatedComputes Q P recipe)
    (identityComputes F.encoding) (Pn.controlled F G P hf).sourceOutputBound
    (value G Q P recipe) (query_value G Q P recipe)

section Signed
variable {u : ℕ} {arity : ℕ → ℕ}
variable (H : (i : Fin u) → Signature K (arity i.val))
variable (R : (i : Fin u) → OrientedPerfectPairing (arity i.val))
variable (label : Fin t → Fin u)
variable (sign : (j : Fin t) → Fin (R (label j)).count → Bool)
variable (rs : W.Recipe Q (S.pairing R label sign))

abbrev signedValue := value (GeneralEOPairedFamilyDuplicate.signatures H label) Q (S.pairing R label sign) rs

omit [Algebra ℚ K] [CharZero K] in
theorem signed_coefficient (i : Fin s) (z : Fin (Q i).count → Bool) :
    W.coefficient Q (S.pairing R label sign) rs
      (Pn.coefficients (GeneralEOPairedFamilyDuplicate.signatures H label) (S.pairing R label sign)) i z =
    ((rs i).map fun node => GeneralEOPairedCSPCycles.compress (R (label node.1)) (H (label node.1))
      (fun j => Bool.xor (sign node.1 j) (Sum.elim id z (node.2 j)))).prod := by
  unfold GeneralEOPairedFamilyBundleValue.coefficient
  congr 1
  apply List.map_congr_left
  intro node _
  exact S.signed_compressed H R label sign node.1 _

/-- Actual fixed-field graph backend for any finite signed parent-factor list. -/
def controlled (hf : ∀ i,GeneralEOPairedCSPCycles.Covers (R i) (H i)) :
    LengthControlledOracleReduction (encoding s) F.encoding
      (RawClosedNetwork.validatedEncoding u 1 arity) F.encoding
      (signedValue Q H R label sign rs) (GeneralEOPairedCSPNative.targetValue F H) :=
  T.composeControlled
    (toPinnedControlled F (GeneralEOPairedFamilyDuplicate.signatures H label) Q
      (S.pairing R label sign) rs (GeneralEOPairedFamilySigned.covers H R label sign hf))
    (S.pinnedControlled F H R label sign hf)
end Signed

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleSource
