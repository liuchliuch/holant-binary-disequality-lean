import Holant.Platonic.StabilizerCode.ConjugatedSpace
import Holant.Platonic.StabilizerErasure.Encoder

/-! The supported-space conclusion is the range of an actual Clifford encoder
with fixed zero ancillas. This makes the stabilizer-code interpretation usable
without assuming an encoding witness. -/
namespace Holant.Platonic.StabilizerCode
noncomputable section
open Holant Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.Platonic.StabilizerLine Holant.Platonic.ActiveSupport
open Holant.Platonic.StabilizerErasure
open Holant.Certificates.MatchingProductBridge
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

 def inverseClifford (C : AnalyticClifford n) : AnalyticClifford n where
  operator := C.operator.symm
  unitary := by
    intro f g
    simpa using (C.unitary (C.operator.symm f) (C.operator.symm g)).symm
  pauli_forward := C.pauli_inverse
  pauli_inverse := C.pauli_forward

 theorem exists_code_encoder (C : AnalyticClifford n) (D : BinaryCode n) :
    ∃V : StabilizerIsometry (Module.finrank (ZMod 2) D) n,
      LinearMap.range V.map=codeSpace C D := by
  obtain ⟨r,s,e,hr,_,he⟩:=exists_adapted_coordinates D
  subst r
  let V : StabilizerIsometry (Module.finrank (ZMod 2) D) n := ⟨s,e,inverseClifford C⟩
  refine ⟨V,?_⟩
  ext f
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨g,rfl⟩
    change C.operator (C.operator.symm (attachZero e g))∈supportedSpace D
    rw [LinearEquiv.apply_symm_apply]
    intro w hw
    have hz : (e (vectorWord w)).2≠0 := fun hz=>hw ((he _).mp hz)
    simp [attachZero,hz]
  · intro hf
    refine ⟨evaluateZero e (C.operator f),?_⟩
    apply C.operator.injective
    change C.operator (C.operator.symm (attachZero e (evaluateZero e (C.operator f))))=C.operator f
    rw [LinearEquiv.apply_symm_apply]
    ext w
    by_cases hw : (e (vectorWord w)).2=0
    · have hh : e.symm ((e (vectorWord w)).1,0)=vectorWord w := by
        apply e.injective
        simp only [LinearEquiv.apply_symm_apply]
        exact Prod.ext rfl hw.symm
      simp [attachZero,evaluateZero,hw,hh]
    · have hn : vectorWord w∉D := fun hn=>hw ((he _).mpr hn)
      have hz := hf w hn
      simpa [attachZero,hw] using hz.symm

/-- Actual factorization through at most four logical qubits, with a proved
isometry and its true adjoint. No encoding or support witness is assumed. -/
 theorem source_encoded_four_active_qubits (Φ : Binary →ₗ[ℂ] Signature ℂ n)
    (htest : ∀K,tetrahedralBase K → Φ K=0 ∨ ComplexAffine (Φ K)) :
    ∃k : ℕ,k≤4 ∧ ∃V : StabilizerIsometry k n,
      ∃Ψ : Binary →ₗ[ℂ] Signature ℂ k,
        Φ=V.map.comp Ψ ∧ Ψ=V.adjoint.comp Φ ∧
        (∀f g,hermitian (V.map f) (V.map g)=hermitian f g) := by
  obtain ⟨C,D,hD,_,hmem,_,_,_⟩:=source_common_stabilizer_code Φ htest
  obtain ⟨V,hV⟩:=exists_code_encoder C D
  refine ⟨_,hD,V,V.adjoint.comp Φ,?_,rfl,V.isometry⟩
  apply LinearMap.ext
  intro K
  have hm : Φ K∈LinearMap.range V.map := by rw [hV];exact hmem K
  obtain ⟨g,hg⟩:=hm
  change Φ K=V.map (V.adjoint (Φ K))
  rw [←hg,V.adjoint_map]

end
end Holant.Platonic.StabilizerCode
