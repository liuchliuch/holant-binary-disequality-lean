import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionChoice
import Holant.Proofs.Hardness.EONegativePairReduction

/-! The original negative EO criterion supplies the two compressed-family
failures needed by the actual closed-support CSP source. No class failure of
a selected singleton or supplied hard binary is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOClosedCriterion
open Holant Holant.Tractable
namespace E
export GeneralEOPairedFamilyExtractionChoice (compressed)
end E
namespace C
export GeneralEOPairedCSPFamilyFieldClosed (class_iff)
end C
namespace R
export EONegativePairReduction (family signature)
end R
set_option backward.isDefEq.respectTransparency false

theorem isEO_of_central_nonzero {n : ℕ} (f : Signature AlgebraicComplex n)
    (he : Signature.CentralSupport f) (hn : f ≠ 0) : IsEO ⟨n,f⟩ := by
  obtain ⟨x,hx⟩ := Function.ne_iff.mp hn
  refine ⟨⟨weight x,?_⟩,he⟩
  by_contra h
  exact hx (he x (Ne.symm h))

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (he : ∀ i, Signature.CentralSupport (G i)) (hn : ∀ i, G i ≠ 0)
variable (closed : ∀ i, GeneralEONegativeClosedSupport.Closed (G i))

theorem class_criterion (chosen : EOClass)
    (hc : ∀ i, chosen.Holds (E.compressed G he hn closed i)) :
    EOTract (preprocess (R.family G)) := by
  refine ⟨(Set.finite_range (R.signature G)).subset (fun _ h => h.1),?_,
    .positive,chosen,?_,?_⟩
  · rintro g ⟨⟨i,rfl⟩,_⟩
    exact isEO_of_central_nonzero (G i) (he i) (hn i)
  · rintro g ⟨⟨i,rfl⟩,_⟩ x y z hx hy hz
    exact Or.inl (closed i x y z hx hy hz)
  · rintro g ⟨⟨i,rfl⟩,_⟩ p
    exact (C.class_iff G he hn closed i chosen).mp (hc i) p

/-- Both failed class choices are derived from the literal preprocessed
root predicate and the internally selected whole-support pairings. -/
theorem closed_negative_failures (negative : ¬EOTract (preprocess (R.family G))) :
    (¬∀ i, Affine (E.compressed G he hn closed i)) ∧
      (¬∀ i, Product (E.compressed G he hn closed i)) := by
  constructor
  · intro all
    exact negative (class_criterion G he hn closed .affine all)
  · intro all
    exact negative (class_criterion G he hn closed .product all)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOClosedCriterion
