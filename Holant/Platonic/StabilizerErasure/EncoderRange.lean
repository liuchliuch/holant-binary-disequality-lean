import Holant.Platonic.StabilizerCode.EncoderBridge
import Holant.Platonic.StabilizerErasure.PauliCompression

/-! Source-definition verification for every concrete encoder, including
arbitrary invertible binary coordinate splittings. The range is exactly a
joint fixed space of commuting actual Paulis, of dimension 2^k; together
with `logical_representatives`, this proves the source's two defining
stabilizer-isometry properties rather than relying on a definition name. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.Tractable.AffinePhase
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k a : ℕ}

def coordinateCode (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector k × BinaryVector a) :
    BinaryCode n := LinearMap.ker (rightCoordinates e)

@[simp] theorem mem_coordinateCode
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector k × BinaryVector a) (x : BinaryVector n) :
    x∈coordinateCode e ↔ (e x).2=0 := Iff.rfl

def coordinateCodeEquiv
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector k × BinaryVector a) :
    coordinateCode e ≃ₗ[ZMod 2] BinaryVector k where
  toFun x := (e x.val).1
  invFun y := ⟨e.symm (y,0),by simp⟩
  left_inv x := by
    apply Subtype.ext
    apply e.injective
    simp only [LinearEquiv.apply_symm_apply]
    exact Prod.ext rfl x.property.symm
  right_inv y := by simp
  map_add' x y := by simp
  map_smul' c x := by simp

theorem coordinateCode_finrank
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector k × BinaryVector a) :
    Module.finrank (ZMod 2) (coordinateCode e)=k := by
  rw [(coordinateCodeEquiv e).finrank_eq]
  simp [BinaryVector]

theorem range_attachZero
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector k × BinaryVector a) :
    LinearMap.range (attachZero e)=supportedSpace (coordinateCode e) := by
  ext f
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨g,rfl⟩
    intro w hw
    simp only [mem_coordinateCode] at hw
    simp [attachZero,hw]
  · intro hf
    refine ⟨evaluateZero e f,?_⟩
    ext w
    by_cases hw : (e (vectorWord w)).2=0
    · have hh : e.symm ((e (vectorWord w)).1,0)=vectorWord w := by
        apply e.injective
        simp only [LinearEquiv.apply_symm_apply]
        exact Prod.ext rfl hw.symm
      simp [attachZero,evaluateZero,hw,hh]
    · have hz := hf w (by simpa using hw)
      simpa [attachZero,hw] using hz.symm

theorem StabilizerIsometry.range_codeSpace (V : StabilizerIsometry k n) :
    LinearMap.range V.map=
      codeSpace (inverseClifford V.clifford) (coordinateCode V.coordinates) := by
  ext f
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨g,rfl⟩
    change V.clifford.operator.symm (V.clifford.operator (attachZero V.coordinates g))∈
      supportedSpace (coordinateCode V.coordinates)
    rw [LinearEquiv.symm_apply_apply,←range_attachZero]
    exact ⟨g,rfl⟩
  · intro hf
    change V.clifford.operator.symm f∈supportedSpace (coordinateCode V.coordinates) at hf
    rw [←range_attachZero] at hf
    obtain ⟨g,hg⟩ := hf
    refine ⟨g,?_⟩
    change V.clifford.operator (attachZero V.coordinates g)=f
    rw [hg,LinearEquiv.apply_symm_apply]

theorem StabilizerIsometry.range_finrank (V : StabilizerIsometry k n) :
    Module.finrank ℂ (LinearMap.range V.map)=2^k := by
  rw [V.range_codeSpace,codeSpace_finrank,coordinateCode_finrank]

/-- The literal image is the complete common +1 eigenspace, rather than
only a subset of a stabilizer code. -/
theorem StabilizerIsometry.mem_range_iff_pauli_fixed (V : StabilizerIsometry k n)
    (f : Signature ℂ n) :
    f∈LinearMap.range V.map ↔ ∀z∈dualCode (coordinateCode V.coordinates),
      conjugatedZ (inverseClifford V.clifford) z f=f := by
  rw [V.range_codeSpace,mem_codeSpace_iff_fixed]

theorem StabilizerIsometry.stabilizer_code_and_logicals (V : StabilizerIsometry k n) :
    (Module.finrank ℂ (LinearMap.range V.map)=2^k) ∧
    (∀f,f∈LinearMap.range V.map ↔ ∀z∈dualCode (coordinateCode V.coordinates),
      conjugatedZ (inverseClifford V.clifford) z f=f) ∧
    (∀z,∃c : ZMod 4,∃a b : BinaryVector n,∀f,
      conjugatedZ (inverseClifford V.clifford) z f=standardPauli c a b f) ∧
    (∀z t f,conjugatedZ (inverseClifford V.clifford) z
      (conjugatedZ (inverseClifford V.clifford) t f)=
      conjugatedZ (inverseClifford V.clifford) t
        (conjugatedZ (inverseClifford V.clifford) z f)) ∧
    ∀Q : Pauli k,∃P : Pauli n,∀f,P.run (V.map f)=V.map (Q.run f) :=
  ⟨V.range_finrank,V.mem_range_iff_pauli_fixed,
    conjugatedZ_is_standardPauli (inverseClifford V.clifford),
    conjugatedZ_commute (inverseClifford V.clifford),V.logical_representatives⟩

end
end Holant.Platonic.StabilizerErasure
