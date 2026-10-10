import Holant.Platonic.StabilizerShortening.NoErasureShortening
import Holant.Platonic.StabilizerShortening.CorrectableShortening

/-!
Source Lemma 9.21, stabilizer-code tetrahedral shortening, for an arbitrary
source-primary stabilizer isometry U. The proof constructs all encoder,
frame, residual, rank, and phase data internally. The untouched ports are
the actual identity extension defined by tensorMap and wordTensor.

The first conclusion is a genuine tensor product over a partition of the
original physical ports into two nonempty sets, with both factors nonzero.
The second uses one of the fixed twelve tetrahedral representatives on two
different original physical ports. Its actual residual is nonzero and
nonaffine. The coordinate Cliffords in the proof are analytic changes of
coordinates; none is added to the permitted physical resources.

The proof establishes the same statement for arbitrary k; the source
wrapper retains the manuscript's k≤4 hypothesis. Arbitrary fourth-root
Pauli eigenvalue characters are also accepted directly.
-/
namespace Holant.Platonic.StabilizerShortening
open Holant Holant.Tractable.AffinePhase
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
open Holant.Platonic.StabilizerErasure
open Holant.Certificates.TetrahedralAffine
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {k m n : ℕ}

/-- The actual contraction pair consists of different original ports. -/
theorem physical_pair_distinct (p : (Bool ⊕ Fin n) ≃ Fin m) :
    p (.inl false)≠p (.inl true) := by
  intro h
  have he := p.injective h
  simp at he

theorem actual_card_distinct_witness (f : Signature ℂ m)
    (h : HasNonaffineTetrahedralCard f) :
    ∃n : ℕ,∃p : (Bool ⊕ Fin n) ≃ Fin m,∃r : Representative,
      p (.inl false)≠p (.inl true) ∧
      pairCard p (complexKernel r) f≠0 ∧ ¬ComplexAffine (pairCard p (complexKernel r) f) := by
  obtain ⟨n,p,r,hn,ha⟩ := h
  exact ⟨n,p,r,physical_pair_distinct p,hn,ha⟩

/-- The full shortening alternative, in fact valid without the source's
upper bound on the number of logical qubits. -/
theorem semantic_stabilizer_shortening (t : ℕ)
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) (hU : IsStabilizerIsometry U)
    (ht : 1≤t) (hroom : k+2≤n)
    (f : Signature ℂ (k+t)) (hf : ¬ComplexAffine f) :
    Holant.Pauli.ExoticKlein.Fiber.HasProperTensorFactor (tensorMap t U f) ∨
      HasNonaffineTetrahedralCard (tensorMap t U f) := by
  cases n with
  | zero => omega
  | succ n =>
    by_cases hc : ∃r,CorrectableMap U r
    · exact correctable_shortening U hU t ht f hf hc
    · apply Or.inr
      apply no_correctable_actual_shortening t U hU _ hroom f hf
      intro r hr
      exact hc ⟨r,hr⟩

/-- Lemma 9.21 with precisely the source's primary isometry hypothesis,
k≤4, at least one untouched qubit, and at least two redundant code ports. -/
theorem source_stabilizer_code_tetrahedral_shortening (t : ℕ)
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) (hU : IsStabilizerIsometry U)
    (_hk : k≤4) (ht : 1≤t) (hroom : k+2≤n)
    (f : Signature ℂ (k+t)) (hf : ¬ComplexAffine f) :
    Holant.Pauli.ExoticKlein.Fiber.HasProperTensorFactor (tensorMap t U f) ∨
      HasNonaffineTetrahedralCard (tensorMap t U f) :=
  semantic_stabilizer_shortening t U hU ht hroom f hf

/-- The exact identity-tensor-U formula accompanies the physical conclusion,
including all untouched input bits and the actual output ordering. -/
theorem source_stabilizer_shortening_with_action (t : ℕ)
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) (hU : IsStabilizerIsometry U)
    (hk : k≤4) (ht : 1≤t) (hroom : k+2≤n)
    (f : Signature ℂ (k+t)) (hf : ¬ComplexAffine f) :
    (∀x : Word t,∀y : Word n,
      tensorMap t U f (wordTensor t x y)=U (fun z=>f (wordTensor t x z)) y) ∧
    (Holant.Pauli.ExoticKlein.Fiber.HasProperTensorFactor (tensorMap t U f) ∨
      HasNonaffineTetrahedralCard (tensorMap t U f)) :=
  ⟨tensorMap_wordTensor t U f,
    source_stabilizer_code_tetrahedral_shortening t U hU hk ht hroom f hf⟩

/-- Direct source eigenvalue-character input, with no additional encoder
presentation or restricted choice of Pauli eigenvalues. -/
theorem source_eigenvalue_stabilizer_shortening (t : ℕ)
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (hiso : ∀f g,hermitian (U f) (U g)=hermitian f g)
    (himage : HasPauliEigenspaceImage U)
    (hlogical : ∀Q : Pauli k,∃P : Pauli n,∀f,P.run (U f)=U (Q.run f))
    (hk : k≤4) (ht : 1≤t) (hroom : k+2≤n)
    (f : Signature ℂ (k+t)) (hf : ¬ComplexAffine f) :
    Holant.Pauli.ExoticKlein.Fiber.HasProperTensorFactor (tensorMap t U f) ∨
      HasNonaffineTetrahedralCard (tensorMap t U f) :=
  source_stabilizer_code_tetrahedral_shortening t U
    ⟨hiso,(hasStabilizerImage_iff_eigenvalues U).mpr himage,hlogical⟩ hk ht hroom f hf

end
end Holant.Platonic.StabilizerShortening
