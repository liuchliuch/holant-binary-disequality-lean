import Holant.Proofs.Hardness.GeneralOddHigherResidueQuaternaryPinning
import Holant.Proofs.Hardness.GeneralEOTensorPowerRemovalOriginalField

/-! Exact original-field data for removing a scalar macro with a unit entry.
The augmented dictionary keeps its own generated field and codec. Its inclusion
into the old field is proved from the actual coefficient memberships, rather
than identifying presentations. The signed tensor specialization supplies those
memberships using only rational constants. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedTensorRemovalField
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (coefficients originalField originalPresentation originalTables originalValue)
end O
namespace A
export GeneralEOTensorPowerRemovalOriginalField (family family_mem family_old family_new oldLabel newLabel)
end A
namespace P
export GeneralOddHigherResidueQuaternaryPinning (scale scale_ambient lifted_labels)
end P
namespace B
export GeneralEONonARSPinningFieldBridge (lift labels exact native denote_lift)
end B
set_option backward.isDefEq.respectTransparency false
variable {s n : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance baseAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'
variable (f : Signature AlgebraicComplex n) (hf : ∀x,f x∈O.originalField G)

abbrev augmented := A.family G f

def row (x : Fin n→Bool) : O.originalField G := ⟨f x,hf x⟩

include hf in
theorem field_le : O.originalField (augmented G f)≤O.originalField G := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨⟨i,x⟩,rfl⟩
  exact A.family_mem G f (O.originalField G)
    (fun i x => coefficient_mem_familyField (O.coefficients G) ⟨i,x⟩) hf i x

def embedding : O.originalField (augmented G f)→ₐ[ℚ]O.originalField G :=
  IntermediateField.inclusion (field_le G f hf)

@[simp] theorem embedding_coe (x : O.originalField (augmented G f)) :
    (embedding G f hf x).val=x.val := IntermediateField.coe_inclusion _ x

variable (N : Network AlgebraicComplex n) (NL : Labelling N.shape s 1 a)
variable (hN : LabelledNetwork.Exact G N NL) (hn : ∀e,N.edge e=Signature.disequality)
variable (c : AlgebraicComplex) (hc : c≠0) (hvalue : N.denote=c • f)
variable (unit : Fin n→Bool) (hunit : f unit=1)

abbrev scalar : O.originalField G := P.scale G N NL unit

include hN hn hvalue hunit in
theorem scalar_ambient : (scalar G N NL unit : AlgebraicComplex)=c := by
  rw [scalar,P.scale_ambient G N NL hN hn unit,hvalue]
  simp [hunit]

include hN hn hc hvalue hunit in
theorem scalar_nonzero : scalar G N NL unit≠0 := by
  intro hz
  apply hc
  rw [←scalar_ambient G f N NL hN hn c hvalue unit hunit,hz]
  rfl

include hN hn hvalue hunit in
theorem lifted_value : (B.lift G N NL).denote=scalar G N NL unit • row G f hf := by
  funext x
  apply Subtype.ext
  change ((B.lift G N NL).denote x : AlgebraicComplex)=
    (scalar G N NL unit : AlgebraicComplex)*(row G f hf x : AlgebraicComplex)
  rw [B.denote_lift G N NL hN hn x,scalar_ambient G f N NL hN hn c hvalue unit hunit,hvalue]
  rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedTensorRemovalField
