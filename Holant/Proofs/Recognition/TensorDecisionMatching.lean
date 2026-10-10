import Holant.Proofs.Recognition.TensorDecisionStable
import Holant.Tractable.Anchor.MatrixActions

/-!
# Genuine finite structural recognition of the matching tensor alternatives

The generic one-hot checker is executable over a field with exact decidable
entry equality. The original algebraic source alternative is reduced, in both
directions, by the source's fixed inverse K or KX action at every port. The
outer orientation is common to the whole finite family. No decomposition is
an input to any test. Original algebraic descriptor-byte implementation and
physical complexity bounds are separate obligations.
-/

namespace Holant.LocalDrafts.RemoteWork.TractChainV1.TensorDecisionMatching

open Holant.Tractable TensorDecisionNullary

variable {K : Type*} [Field K] {n : ℕ}

theorem oneHot_divisionClosed : DivisionClosed (fun _ (g : Signature K _) => Signature.OneHot g) := by
  intro m g c _ hg x hx
  change g x / c = 0
  rw [hg x hx, zero_div]

section Executable
variable [DecidableEq K]

instance (f : Signature K n) : Decidable (Signature.OneHot f) :=
  inferInstanceAs (Decidable (∀ x, 1 < Holant.weight x → f x = 0))

def recognizeOneHot (f : Signature K n) : Bool :=
  TensorDecisionStable.recognize (fun _ g => Signature.OneHot g) f

theorem recognizeOneHot_eq_true_iff (f : Signature K n) :
    recognizeOneHot f = true ↔ f = 0 ∨ Signature.TensorClosure (fun _ g => Signature.OneHot g) f :=
  TensorDecisionStable.recognize_eq_true_iff _ oneHot_divisionClosed f
end Executable

noncomputable section

/-- Exactly the two fixed source matrices, including the shared orientation. -/
def basis (opposite : Bool) : InvertibleKernel :=
  if opposite then sourceKBasis.comp bitFlipBasis else sourceKBasis

/-- The inverse of KX is XK-inverse: the prescribed K table is read with
all output bits complemented, so no new algebraic constants are needed. -/
theorem inverse_true_apply (f : Signature AlgebraicComplex n) (x : Fin n → Bool) :
    (basis true).symm.action f x = sourceKBasis.symm.action f (fun j => !(x j)) := by
  simp only [basis,ite_true,InvertibleKernel.comp_symm,InvertibleKernel.comp_action,
    bitFlipBasis_symm,bitFlipBasis_action]

theorem inverse_factor (opposite : Bool) (m : ℕ) (f : Signature AlgebraicComplex m)
    (hf : matchingImage opposite m f) :
    Signature.OneHot ((basis opposite).symm.action f) := by
  obtain ⟨g,hg,rfl⟩ := hf
  cases opposite with
  | false =>
    change Signature.OneHot (sourceKBasis.symm.action (sourceKBasis.action g))
    simpa [InvertibleKernel.symm_action_action, Signature.OneHot, AtMostOneSupport,
      Holant.weight, Holant.Tractable.weight] using hg
  | true =>
    change Signature.OneHot ((sourceKBasis.comp bitFlipBasis).symm.action
      ((sourceKBasis.comp bitFlipBasis).action g))
    simpa [InvertibleKernel.symm_action_action, Signature.OneHot, AtMostOneSupport,
      Holant.weight, Holant.Tractable.weight] using hg

theorem forward_factor (opposite : Bool) (m : ℕ) (g : Signature AlgebraicComplex m)
    (hg : Signature.OneHot g) : matchingImage opposite m ((basis opposite).action g) := by
  refine ⟨g,?_,?_⟩
  · simpa only [Signature.OneHot, AtMostOneSupport, Holant.weight, Holant.Tractable.weight] using hg
  · cases opposite <;> rfl

/-- Both directions of the actual source tensor-image reduction. -/
theorem sourceMatching_iff (opposite : Bool) (f : Signature AlgebraicComplex n) :
    SourceTensorClosure (matchingImage opposite) f ↔
      SourceTensorClosure (fun _ g => Signature.OneHot g) ((basis opposite).symm.action f) := by
  constructor
  · rintro (hz | ht)
    · left
      subst f
      funext x
      simp [InvertibleKernel.action, Signature.coordinateAction]
    · right
      exact ht.map_action (basis opposite).inverse (inverse_factor opposite)
  · rintro (hz | ht)
    · left
      have h := congrArg (basis opposite).action hz
      rw [InvertibleKernel.action_symm_action] at h
      refine h.trans ?_
      funext x
      simp [InvertibleKernel.action, Signature.coordinateAction]
    · right
      have h := ht.map_action (basis opposite).matrix (forward_factor opposite)
      change Signature.TensorClosure (matchingImage opposite)
        ((basis opposite).action ((basis opposite).symm.action f)) at h
      simpa only [InvertibleKernel.action_symm_action] using h

/-- Original-table structural test: explicit inverse action followed by finite
port partitions, support pivots, restrictions and row equality. -/
def recognizeMatching (opposite : Bool) (f : Signature AlgebraicComplex n) : Bool := by
  classical
  exact recognizeOneHot ((basis opposite).symm.action f)

theorem recognizeMatching_eq_true_iff (opposite : Bool) (f : Signature AlgebraicComplex n) :
    recognizeMatching opposite f = true ↔ SourceTensorClosure (matchingImage opposite) f := by
  classical
  change recognizeOneHot ((basis opposite).symm.action f) = true ↔ _
  rw [recognizeOneHot_eq_true_iff]
  exact (sourceMatching_iff opposite f).symm

/-- The orientation is outside the family universal, exactly as in source clause (4). -/
def recognizeFamily {s : ℕ} (arity : Fin s → ℕ)
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i)) : Bool :=
  decide ((∀ i, recognizeMatching false (G i) = true) ∨
    (∀ i, recognizeMatching true (G i) = true))

theorem recognizeFamily_eq_true_iff {s : ℕ} (arity : Fin s → ℕ)
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i)) :
    recognizeFamily arity G = true ↔
      (∀ i, SourceTensorClosure (matchingImage false) (G i)) ∨
      (∀ i, SourceTensorClosure (matchingImage true) (G i)) := by
  simp only [recognizeFamily, decide_eq_true_eq, recognizeMatching_eq_true_iff]

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.TensorDecisionMatching
