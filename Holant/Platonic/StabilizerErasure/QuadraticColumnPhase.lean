import Holant.Platonic.StabilizerErasure.ColumnPhaseDerivatives

/-! Reconstruct the actual even-mixed Z/4 quadratic from affine Pauli
derivatives, using the proved nowhere-zero third-difference criterion.
This supplies the phase clause for arbitrary analytic Clifford encoders. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.CharacterFlat
open Holant.Platonic.StabilizerLine
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

theorem affine_derivatives_cube (a : BinaryVector k → ℂ)
    (h : ∀u,∃q : ZMod 4,∃ell : BinaryVector k →ₗ[ZMod 2] ZMod 2,
      ∀z,a (z+u)=phaseRoot q*sign (ell z)*a z)
    (z u v w : BinaryVector k) :
    a (z+u+v+w)*a (z+u)*a (z+v)*a (z+w)=
      a (z+u+v)*a (z+u+w)*a (z+v+w)*a z := by
  obtain ⟨q,ell,he⟩ := h w
  rw [he (z+u+v),he z,he (z+u),he (z+v)]
  simp only [map_add,sign_add]
  ring

/-- A nowhere-zero complex table whose translation derivatives are exact
Pauli phases has a genuine stabilizer quadratic phase, with even mixed
coefficients. No quadratic witness is supplied as a premise. -/
theorem quadratic_of_affine_derivatives (a : BinaryVector k → ℂ) (ha : ∀z,a z≠0)
    (h : ∀u,∃q : ZMod 4,∃ell : BinaryVector k →ₗ[ZMod 2] ZMod 2,
      ∀z,a (z+u)=phaseRoot q*sign (ell z)*a z) :
    ∃c : ℂ,c≠0 ∧ ∃Q : QuadraticPhase k,
      ∀z,a z=c*(fourthRootPhase (Q.eval (wordVector z)) : ℂ) := by
  have hr (z : BinaryVector k) : ∃q : ZMod 4,a z=phaseRoot q*a 0 := by
    obtain ⟨q,ell,he⟩ := h z
    exact ⟨q,by simpa using he 0⟩
  choose q hq using hr
  let f : Signature AlgebraicComplex k := fun w => fourthRootPhase (q (vectorWord w))
  have hf (w : Word k) : f w≠0 := fourthRootPhase_ne_zero _
  have hv (w : Word k) : a (vectorWord w)=a 0*(f w : ℂ) := by
    rw [hq]
    simp [f,phaseRoot,mul_comm]
  have ht : ThirdTrivial f := by
    intro z u v w
    apply (thirdRatio_eq_one_iff hf z u v w).mpr
    apply Subtype.ext
    push_cast
    have hc := affine_derivatives_cube a h (vectorWord z) (vectorWord u) (vectorWord v) (vectorWord w)
    simp only [←vector_xor,hv] at hc
    apply mul_left_cancel₀ (pow_ne_zero 4 (ha 0))
    linear_combination hc
  obtain hzero|⟨c,hc,S,Q,hform⟩ := affine_of_thirdTrivial hf ht
  · exact (hf (origin k) (by simp [hzero])).elim
  · have hS (w : Word k) : S.Holds w := by
      by_contra hw
      exact hf w (by simp [hform,affineFormula,hw])
    refine ⟨a 0*(c : ℂ),mul_ne_zero (ha 0) (by exact_mod_cast hc),Q,?_⟩
    intro z
    have hv0 := hv (wordVector z)
    simpa [hform,affineFormula,hS,mul_assoc] using hv0

theorem framed_column_quadratic_phase (V : StabilizerIsometry k n)
    (A : AnalyticClifford n) (B : AnalyticClifford k)
    (c : BinaryVector n) (M : BinaryVector k →ₗ[ZMod 2] BinaryVector n)
    (a : BinaryVector k → ℂ) (ha : ∀z,a z≠0)
    (hcol : ∀z,framedMap V A B (ket (wordVector z))=a z • ket (wordVector (c+M z))) :
    ∃a₀ : ℂ,a₀≠0 ∧ ∃Q : QuadraticPhase k,
      ∀z,a z=a₀*(fourthRootPhase (Q.eval (wordVector z)) : ℂ) :=
  quadratic_of_affine_derivatives a ha (framed_column_phase_derivatives V A B c M a ha hcol)

end
end Holant.Platonic.StabilizerErasure
