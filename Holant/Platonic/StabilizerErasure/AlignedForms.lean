import Holant.Platonic.StabilizerErasure.ColumnForms
import Holant.Platonic.StabilizerCode.LocalAxisClifford

/-! Correctability itself gives the pure or mixed analytic isometry form.
The required pure-case coordinate change is an actually constructed local
Clifford. Only the residual isometry's stabilizer-tableau closure remains
outside this theorem. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

def composeClifford (C D : AnalyticClifford n) : AnalyticClifford n where
  operator := D.operator.trans C.operator
  unitary f g := (C.unitary _ _).trans (D.unitary f g)
  pauli_forward := by
    intro P
    obtain ⟨Q,hQ⟩ := D.pauli_forward P
    obtain ⟨R,hR⟩ := C.pauli_forward Q
    exact ⟨R,fun f => by simp [hQ,hR]⟩
  pauli_inverse := by
    intro P
    obtain ⟨Q,hQ⟩ := C.pauli_inverse P
    obtain ⟨R,hR⟩ := D.pauli_inverse Q
    exact ⟨R,fun f => by simp [hQ,hR]⟩

def StabilizerIsometry.postcompose (V : StabilizerIsometry k n) (C : AnalyticClifford n) :
    StabilizerIsometry k n := ⟨V.ancillas,V.coordinates,composeClifford C V.clifford⟩

@[simp] theorem StabilizerIsometry.postcompose_map (V : StabilizerIsometry k n)
    (C : AnalyticClifford n) (f : Signature ℂ k) :
    (V.postcompose C).map f=C.operator (V.map f) := rfl

/-- Full analytic part of the erasure alternative, with no supplied axis
alignment or residual isometry witness. The source additionally calls the
residual W a stabilizer isometry; that stronger property is not claimed. -/
theorem correctable_analytic_forms (V : StabilizerIsometry k (n+1))
    (r : Fin (n+1)) (h : Correctable V r) :
    (∃C : AnalyticClifford (n+1),∃R : Kernel ℂ,∃b : Bool,
      ∃W : Signature ℂ k →ₗ[ℂ] Signature ℂ n,
        (∀f,C.operator f=siteAction r R f) ∧
        (∀f g,hermitian (W f) (W g)=hermitian f g) ∧
        ∀f w,C.operator (V.map f) w=if w r=b then W f (r.removeNth w) else 0) ∨
    (∃W : Signature ℂ (k+1) →ₗ[ℂ] Signature ℂ n,
      (∀f g,hermitian (W f) (W g)=hermitian f g) ∧
      ∀f b w,V.map f (r.insertNth b w)=(sqrtTwo : ℂ)⁻¹*W (auxiliaryKet b f) w) := by
  obtain ⟨a,ha,_,hz|⟨p,hp,hap,ho⟩⟩ := correctable_expectation_dichotomy V r h
  · right
    have he : ∀p : Fin 4,p≠0 → ∀f,V.adjoint (siteAction r (qubitPauli p) (V.map f))=0 := by
      intro p hp f
      rw [ha,hz p hp,zero_smul]
    exact ⟨mixedResidual V r,mixedResidual_isometry V r he,mixed_column_expansion V r⟩
  · left
    obtain ⟨C,R,hR,hC⟩ := exists_local_axis_clifford r p hp
    have han : a p≠0 := by rcases hap with hh|hh <;> rw [hh] <;> norm_num
    have he := V.scalar_nonzero_action (physicalPauli r p) (a p) han
      (by simpa only [physicalPauli_exact] using ha p)
    simp only [physicalPauli_exact] at he
    obtain ⟨b,hb⟩ : ∃b : Bool,a p=(if b then (-1 : ℂ) else 1) := by
      rcases hap with hh|hh
      · exact ⟨false,hh⟩
      · exact ⟨true,hh⟩
    have hZ (f : Signature ℂ k) :
        siteAction r (qubitPauli 3) ((V.postcompose C).map f)=
          (if b then (-1 : ℂ) else 1) • (V.postcompose C).map f := by
      rw [StabilizerIsometry.postcompose_map,←hC,he,map_smul,hb]
    refine ⟨C,R,b,pureResidual (V.postcompose C) r b,hR,
      pureResidual_isometry (V.postcompose C) r b hZ,?_⟩
    intro f w
    exact pure_column_expansion (V.postcompose C) r b hZ f w

end
end Holant.Platonic.StabilizerErasure
