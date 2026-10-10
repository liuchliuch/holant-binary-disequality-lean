import Holant.Proofs.Closure.ClosureCompatibleAlignmentIncidence
import Holant.Dihedral.TwoCardLocalization.ResidualOrder

/-! An intrinsic factor-line obstruction on any matching ancestor.  Its two
cards may have arbitrary kernels and independently chosen coefficient tables;
the common residual incidence and the at-most-one varying factor are derived
from the literal ancestor itself. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
open Holant Holant.Certificates.MatchingContractionClosure
open Holant.Dihedral.TwoCardLocalization

variable {K E : Type} [Field K] [Fintype E] [DecidableEq E] {n : ℕ}

theorem matching_ancestor_factor_line_bound (M : Presentation K (Fin (n+2)))
    (C₀ C₁ : Binary (K:=K)) (p : (E × Bool) ≃ Fin n)
    (A₀ A₁ : E → Binary (K:=K)) (κ₀ κ₁ : K)
    (nonzero₀ : productValue p A₀ κ₀ ≠ 0) (nonzero₁ : productValue p A₁ κ₁ ≠ 0)
    (nonsingular : ∀ e,Matrix.det (A₀ e) ≠ 0)
    (equation₀ : Signature.contract C₀ M.tensor = productValue p A₀ κ₀)
    (equation₁ : Signature.contract C₁ M.tensor = productValue p A₁ κ₁)
    (e f : E) (different : e ≠ f) :
    (∃ c : K,c ≠ 0 ∧ A₁ e = c • A₀ e) ∨ (∃ c : K,c ≠ 0 ∧ A₁ f = c • A₀ f) := by
  classical
  let R := oneVariableProducts M (0 : Fin (n+2)) 1 Fin.zero_ne_one
  let remaining := (remainingOrder (0 : Fin (n+2)) 1 Fin.zero_ne_one).symm
  let q := R.products.ports.trans remaining
  have orderIdentity : Holant.Dihedral.CompatibleClosure.pairOrder (0 : Fin (n+2)) 1 = Equiv.refl _ := by
    simp [Holant.Dihedral.CompatibleClosure.pairOrder]
  have native (C : Binary (K:=K)) :
      Signature.contract C M.tensor = Tensor.reindex remaining (contractPair 0 1 C M.tensor) := by
    simpa [orderIdentity,Tensor.reindex,remaining] using
      (contractPair_order (0 : Fin (n+2)) 1 Fin.zero_ne_one C M.tensor).symm
  have output (C : Binary (K:=K)) :
      Signature.contract C M.tensor = productValue q (R.products.matrix C) (R.products.scalar C) := by
    rw [native C,R.products.equation C]
    rfl
  have product₀ : productValue p A₀ κ₀ = productValue q (R.products.matrix C₀) (R.products.scalar C₀) :=
    equation₀.symm.trans (output C₀)
  have product₁ : productValue p A₁ κ₁ = productValue q (R.products.matrix C₁) (R.products.scalar C₁) :=
    equation₁.symm.trans (output C₁)
  have sameMatching : ClosureMatchingMinor.mate p = ClosureMatchingMinor.mate q :=
    ClosureMatchingMinor.mate_eq_of_tensor_eq p A₀ κ₀ q (R.products.matrix C₀) (R.products.scalar C₀)
      nonzero₀ nonsingular product₀
  have fixedLine (j : E) (fixed : some (incidenceIndex p q j) ≠ R.exceptional) :
      ∃ c : K,c ≠ 0 ∧ A₁ j = c • A₀ j := by
    obtain ⟨c₀,hc₀,line₀⟩ := equal_tensors_incidence_line p q sameMatching A₀ (R.products.matrix C₀)
      κ₀ (R.products.scalar C₀) nonzero₀ product₀ j
    obtain ⟨c₁,hc₁,line₁⟩ := equal_tensors_incidence_line p q sameMatching A₁ (R.products.matrix C₁)
      κ₁ (R.products.scalar C₁) nonzero₁ product₁ j
    have factor : incidenceFactor p q (R.products.matrix C₀) j =
        incidenceFactor p q (R.products.matrix C₁) j := by
      unfold incidenceFactor
      rw [R.fixed C₀ C₁ (incidenceIndex p q j) fixed]
    refine ⟨c₁/c₀,div_ne_zero hc₁ hc₀,?_⟩
    rw [line₀,line₁,factor,smul_smul,div_mul_cancel₀ c₁ hc₀]
  by_cases firstFixed : some (incidenceIndex p q e) ≠ R.exceptional
  · exact Or.inl (fixedLine e firstFixed)
  · have secondFixed : some (incidenceIndex p q f) ≠ R.exceptional := by
      intro equal
      have he : some (incidenceIndex p q e) = R.exceptional := not_ne_iff.mp firstFixed
      have indices := Option.some.inj (he.trans equal.symm)
      exact different (incidenceIndex_injective p q sameMatching indices)
    exact Or.inr (fixedLine f secondFixed)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
