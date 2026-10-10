import Holant.Proofs.Closure.ClosureMatchingResidual
import Holant.Dihedral.TwoCardLocalization.DistinctCore

/-! A genuine different-matching pair of inherited cards excludes a matching
product on its common ancestor. The obstruction is derived from one common
residual port construction and intrinsic minors, not from a supplied uniqueness
or six-port rigidity certificate. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureLocalizationObstruction
open Holant Holant.Certificates Holant.Certificates.MatchingContractionClosure
open Holant.Dihedral.TwoCardLocalization
variable {K P : Type} [Field K] [DecidableEq P]

private theorem reindexed_equation {u v : P} {f : Tensor K P}
    (R : ClosureMatchingResidual.Products u v f) {n : ℕ}
    (order : Remaining u v ≃ Fin n) (C : Binary (K:=K)) :
    Tensor.reindex order (contractPair u v C f) =
      productValue (R.ports.trans order) (R.matrix C) (R.scalar C) := by
  rw [R.equation C]
  rfl

/-- Nonsingular output factors can be compared to the SAME derived residual
ports, without assuming the derived cycle scalar is nonzero. -/
theorem same_output_mate {u v : P} {f : Tensor K P}
    (R : ClosureMatchingResidual.Products u v f) {n : ℕ}
    (order : Remaining u v ≃ Fin n) (C₀ C₁ : Binary (K:=K))
    (M₀ M₁ : Presentation K (Fin n))
    (h₀ : M₀.tensor ≠ 0) (h₁ : M₁.tensor ≠ 0)
    (det₀ : ∀ e, Matrix.det (M₀.matrix e) ≠ 0)
    (det₁ : ∀ e, Matrix.det (M₁.matrix e) ≠ 0)
    (eq₀ : M₀.tensor = Tensor.reindex order (contractPair u v C₀ f))
    (eq₁ : M₁.tensor = Tensor.reindex order (contractPair u v C₁ f)) :
    ClosureMatchingMinor.mate M₀.ports = ClosureMatchingMinor.mate M₁.ports := by
  have left := ClosureMatchingMinor.mate_eq_of_tensor_eq M₀.ports M₀.matrix M₀.scalar
    (R.ports.trans order) (R.matrix C₀) (R.scalar C₀) h₀ det₀
    (eq₀.trans (reindexed_equation R order C₀))
  have right := ClosureMatchingMinor.mate_eq_of_tensor_eq M₁.ports M₁.matrix M₁.scalar
    (R.ports.trans order) (R.matrix C₁) (R.scalar C₁) h₁ det₁
    (eq₁.trans (reindexed_equation R order C₁))
  exact left.trans right.symm

/-- The actual inherited disagreement cannot come from ANY matching product
on the fixed ancestor. All scalar and orientation changes are included. -/
theorem different_pair_excludes_product {G : Set (Kernel K)}
    (group : ProjectiveMatrixGroup G) (M : Presentation K P)
    (u v : P) (distinct : u ≠ v) {n : ℕ} (order : Remaining u v ≃ Fin n)
    (C₀ C₁ : Kernel K) :
    ¬ DifferentProducts G n
      (Tensor.reindex order (contractPair u v C₀ M.tensor))
      (Tensor.reindex order (contractPair u v C₁ M.tensor)) := by
  rintro ⟨M₀,M₁,valid₀,valid₁,scalar₀,scalar₁,eq₀,eq₁,different⟩
  have mate := same_output_mate (ClosureMatchingResidual.products M u v distinct)
    order C₀ C₁ M₀ M₁
    (productValue_nonzero _ _ _ (fun e => SafeBinary.nonsingular group (valid₀ e)) scalar₀)
    (productValue_nonzero _ _ _ (fun e => SafeBinary.nonsingular group (valid₁ e)) scalar₁)
    (fun e => SafeBinary.nonsingular group (valid₀ e))
    (fun e => SafeBinary.nonsingular group (valid₁ e)) eq₀.symm eq₁.symm
  apply different
  apply Equiv.ext
  intro i
  exact congrFun mate i

/-- Concrete native first-pair version used by the six-port localization
output. The original ordered residual coordinates are not replaced. -/
theorem native_different_cards_not_matching {n : ℕ} {G H : Set (Kernel K)}
    (group : ProjectiveMatrixGroup G) (h : Signature K (n+2)) (A₀ A₁ : Kernel K)
    (different : DifferentProducts G n (Signature.contract A₀ h) (Signature.contract A₁ h)) :
    ¬ MatchingOrZero H h := by
  intro matching
  rcases matching with zero | ⟨M,_valid,_scalar,literal⟩
  · have nonzero := different.nonzero group
    rw [zero,Signature.contract_zero] at nonzero
    exact nonzero.1 rfl
  · subst h
    have orderIdentity : Holant.Dihedral.CompatibleClosure.pairOrder (0 : Fin (n+2)) 1 = Equiv.refl _ := by
      simp [Holant.Dihedral.CompatibleClosure.pairOrder]
    have native (A : Kernel K) :
        Tensor.reindex (remainingOrder (0 : Fin (n+2)) 1 Fin.zero_ne_one).symm
          (contractPair 0 1 A M.tensor) = Signature.contract A M.tensor := by
      simpa [orderIdentity,Tensor.reindex] using
        contractPair_order (0 : Fin (n+2)) 1 Fin.zero_ne_one A M.tensor
    apply different_pair_excludes_product group M (0 : Fin (n+2)) 1 Fin.zero_ne_one
      (remainingOrder (0 : Fin (n+2)) 1 Fin.zero_ne_one).symm A₀ A₁
    simpa only [native] using different

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureLocalizationObstruction
end
