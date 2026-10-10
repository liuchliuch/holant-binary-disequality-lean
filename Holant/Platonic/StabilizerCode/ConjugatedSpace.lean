import Holant.Platonic.StabilizerCode.SupportedSpace

/-! Actual commuting Pauli stabilizers for the Clifford preimage of a supported
space. All operators are literal conjugates; their joint fixed space has the
required Hilbert dimension. No physical Clifford gadget is introduced. -/
namespace Holant.Platonic.StabilizerCode
noncomputable section
open Holant Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.Platonic.StabilizerLine Holant.Platonic.ActiveSupport
open Holant.Certificates.MatchingProductBridge
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

 def codeSpace (C : AnalyticClifford n) (D : BinaryCode n) : Submodule ℂ (Signature ℂ n) :=
  (supportedSpace D).comap C.operator.toLinearMap

@[simp] theorem mem_codeSpace (C : AnalyticClifford n) (D : BinaryCode n)
    (f : Signature ℂ n) : f∈codeSpace C D ↔ C.operator f∈supportedSpace D := Iff.rfl

 def codeSpaceEquiv (C : AnalyticClifford n) (D : BinaryCode n) :
    codeSpace C D ≃ₗ[ℂ] supportedSpace D where
  toFun f := ⟨C.operator f.val,f.property⟩
  invFun g := ⟨C.operator.symm g.val,by simpa using g.property⟩
  left_inv f := by apply Subtype.ext;simp
  right_inv g := by apply Subtype.ext;simp
  map_add' f g := by apply Subtype.ext;simp
  map_smul' c f := by apply Subtype.ext;simp

 theorem codeSpace_finrank (C : AnalyticClifford n) (D : BinaryCode n) :
    Module.finrank ℂ (codeSpace C D)=2^Module.finrank (ZMod 2) D := by
  rw [(codeSpaceEquiv C D).finrank_eq,supportedSpace_finrank]

 def conjugatedZ (C : AnalyticClifford n) (z : BinaryVector n) :
    Signature ℂ n →ₗ[ℂ] Signature ℂ n :=
  C.operator.symm.toLinearMap.comp ((zAction z).comp C.operator.toLinearMap)

@[simp] theorem conjugatedZ_apply (C : AnalyticClifford n) (z : BinaryVector n)
    (f : Signature ℂ n) : conjugatedZ C z f=C.operator.symm (zAction z (C.operator f)) := rfl

 theorem conjugatedZ_is_standardPauli (C : AnalyticClifford n) (z : BinaryVector n) :
    ∃c : ZMod 4,∃a b : BinaryVector n,∀f,conjugatedZ C z f=standardPauli c a b f := by
  obtain ⟨c,a,b,h⟩ := C.standard_inverse_conjugates 0 0 z
  exact ⟨c,a,b,fun f=>by simpa [conjugatedZ_apply,zAction_standard] using h f⟩

 theorem conjugatedZ_commute (C : AnalyticClifford n) (z t : BinaryVector n)
    (f : Signature ℂ n) :
    conjugatedZ C z (conjugatedZ C t f)=conjugatedZ C t (conjugatedZ C z f) := by
  simp only [conjugatedZ_apply,LinearEquiv.apply_symm_apply]
  rw [zAction_commute]

 theorem conjugatedZ_add (C : AnalyticClifford n) (z t : BinaryVector n)
    (f : Signature ℂ n) :
    conjugatedZ C (z+t) f=conjugatedZ C z (conjugatedZ C t f) := by
  simp [zAction_add]

@[simp] theorem conjugatedZ_zero (C : AnalyticClifford n) (f : Signature ℂ n) :
    conjugatedZ C 0 f=f := by simp

 theorem conjugatedZ_involution (C : AnalyticClifford n) (z : BinaryVector n)
    (f : Signature ℂ n) : conjugatedZ C z (conjugatedZ C z f)=f := by
  rw [←conjugatedZ_add]
  have hz : z+z=0 := by
    ext i
    change z i+z i=0
    rcases binary_cases (z i) with h|h <;> rw [h] <;> decide
  rw [hz,conjugatedZ_zero]

 theorem mem_codeSpace_iff_fixed (C : AnalyticClifford n) (D : BinaryCode n)
    (f : Signature ℂ n) :
    f∈codeSpace C D ↔ ∀z∈dualCode D,conjugatedZ C z f=f := by
  rw [mem_codeSpace,supported_iff_z_fixed]
  constructor
  · intro hf z hz
    simp [hf z hz]
  · intro hf z hz
    have he:=congrArg C.operator (hf z hz)
    simpa using he

/-- The original image lies in one literal joint +1 eigenspace of commuting
Paulis, of dimension 2^k with k≤4. This supplies the code interpretation of9.19. -/
 theorem source_common_stabilizer_code (Φ : Binary →ₗ[ℂ] Signature ℂ n)
    (htest : ∀K,tetrahedralBase K → Φ K=0 ∨ ComplexAffine (Φ K)) :
    ∃(C : AnalyticClifford n) (D : BinaryCode n),Module.finrank (ZMod 2) D≤4 ∧
      Module.finrank ℂ (codeSpace C D)=2^Module.finrank (ZMod 2) D ∧
      (∀K,Φ K∈codeSpace C D) ∧
      (∀z∈dualCode D,∃c : ZMod 4,∃a b : BinaryVector n,
        ∀f,conjugatedZ C z f=standardPauli c a b f) ∧
      (∀z t f,conjugatedZ C z (conjugatedZ C t f)=
        conjugatedZ C t (conjugatedZ C z f)) ∧
      (∀f,f∈codeSpace C D ↔ ∀z∈dualCode D,conjugatedZ C z f=f) := by
  obtain ⟨C,D,hD,hs⟩:=source_support_subset Φ htest
  refine ⟨C,D,hD,codeSpace_finrank C D,?_,?_,conjugatedZ_commute C,mem_codeSpace_iff_fixed C D⟩
  · intro K w hw
    by_contra hn
    exact hw (hs K hn)
  · intro z _
    exact conjugatedZ_is_standardPauli C z

end
end Holant.Platonic.StabilizerCode
