import Holant.Proofs.Hardness.EOQuaternarySparseDispatch
import Holant.Proofs.Hardness.ComplexPlaneThreeSupportData

/-! Exhaustive support dispatch in the original algebraic coefficients. The
coefficient-sensitive full plane is retained explicitly for its physical source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternarySupportCases
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace S
export EOQuaternarySparseDispatch (middleSupport support_card sparse_dispatch Plane complex complex_algebraic complex_eo)
end S
namespace T
export EOQuaternarySparseTract (support small_tract)
end T
namespace O
export FiveSupportEOOrdering (middleCoeff middleWord ExactlyFive)
end O
set_option backward.isDefEq.respectTransparency false

private theorem all_middle (M : Signature AlgebraicComplex 4)
    (h : ∀i : Fin 6,O.middleCoeff M i≠0) : DenseEOUnitLocal.NonzeroMiddle M := by
  exact ⟨h 0,h 1,h 2,h 3,h 4,h 5⟩

theorem dense_of_card (M : Signature AlgebraicComplex 4)
    (h : (S.middleSupport M).card=6) : DenseEOUnitLocal.NonzeroMiddle M := by
  classical
  apply all_middle M
  have hu : S.middleSupport M=Finset.univ := Finset.eq_univ_of_card _ (by simpa using h)
  intro i
  have hi : i∈S.middleSupport M := by rw [hu]; exact Finset.mem_univ i
  simpa [EOQuaternarySparseDispatch.middleSupport,EOQuaternarySparseFourLocal.mask] using hi

theorem five_of_card (M : Signature AlgebraicComplex 4)
    (h : (S.middleSupport M).card=5) : O.ExactlyFive M := by
  classical
  simpa [O.ExactlyFive,EOQuaternarySparseDispatch.middleSupport,
    EOQuaternarySparseFourLocal.mask] using h

/-- Every EO support lands in a proved tract region or one of the four concrete
counting-source regions. No hard-or-tract conclusion is assumed here. -/
theorem classified (M : Signature AlgebraicComplex 4) (he : DenseEOUnitLocal.EOSupport M) :
    EOTract {⟨4,M⟩} ∨ DenseEOUnitLocal.NonzeroMiddle M ∨ O.ExactlyFive M ∨
      EOQuaternarySparseFourLocal.Applicable M ∨
      (S.Plane M ∧ (T.support M).card=3) ∨
      (S.Plane M ∧ (T.support M).card=4) := by
  classical
  have hb : (S.middleSupport M).card≤6 := by
    simpa using Finset.card_le_card (Finset.subset_univ (S.middleSupport M))
  by_cases h6 : (S.middleSupport M).card=6
  · exact Or.inr (Or.inl (dense_of_card M h6))
  by_cases h5 : (S.middleSupport M).card=5
  · exact Or.inr (Or.inr (Or.inl (five_of_card M h5)))
  have hs : (T.support M).card≤4 := by rw [S.support_card M he]; omega
  rcases S.sparse_dispatch M he hs with ht|ha|hp
  · exact Or.inl ht
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · by_cases hsmall : (T.support M).card≤2
    · exact Or.inl (T.small_tract M he hsmall)
    · by_cases h3 : (T.support M).card=3
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp,h3⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp,by omega⟩))))

theorem complex_support_card (M : Signature AlgebraicComplex 4) :
    (ComplexPlaneThreeSupportData.support (S.complex M)).card=(T.support M).card := by
  classical
  congr 1
  ext x
  simp [ComplexPlaneThreeSupportData.mem_support,EOQuaternarySparseTract.mem_support,
    EOQuaternarySparseDispatch.complex]

theorem complex_plane (M : Signature AlgebraicComplex 4) (hp : S.Plane M) :
    ComplexPlaneThreeSupportData.Plane (S.complex M) := by
  obtain ⟨i,hi,hj⟩ := hp
  refine ⟨i,?_,?_⟩
  · exact congrArg (fun z : AlgebraicComplex => (z : ℂ)) hi
  · exact congrArg (fun z : AlgebraicComplex => (z : ℂ)) hj

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternarySupportCases
