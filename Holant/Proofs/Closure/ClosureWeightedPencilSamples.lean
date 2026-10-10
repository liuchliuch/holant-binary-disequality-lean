import Holant.Proofs.Closure.ClosureWeightedPencilSource

/-! All actual algebraic root phases give the same four-port source matching.
Complex root phases are lifted inside AlgebraicComplex; all coefficient maps
preserve the literal supplied presentations and analytic endpoint equations.
New proof, awaiting strict kernel validation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
open Holant Holant.Tractable Holant.Projective Holant.Marked Holant.Marked.SupportAtlas
open Holant.Certificates.MatchingContractionClosure
open Holant.Dihedral.TwoCardLocalization
open Holant.LocalDrafts.MainChain
open ClosureRootPencil

def complexTensor (q : Signature Scalar 4) : Signature ℂ 4 := fun x => (q x : ℂ)

def algebraicPencil (U V : Signature Scalar 4) (t : Scalar) : Signature Scalar 4 := U+t • V

def WeightedMatching (m : ℕ) (d : Scalar) (q : Signature Scalar 4) : Prop :=
  ∃ M : Presentation Scalar (Fin 4), M.scalar≠0 ∧
    (∀ e,Kernel.mul (M.matrix e) (ClosureShiftedWeighted.D d) ∈ groupM m) ∧ q=M.tensor

theorem complex_pencil (U V : Signature Scalar 4) (t : Scalar) :
    complexTensor (algebraicPencil U V t)=pencil (complexTensor U) (complexTensor V) (t : ℂ) := by
  funext x
  change CyclicBoundary.AlgebraicRepresentatives.inclusion (U x+t*V x)=
    CyclicBoundary.AlgebraicRepresentatives.inclusion (U x)+
      CyclicBoundary.AlgebraicRepresentatives.inclusion t *
        CyclicBoundary.AlgebraicRepresentatives.inclusion (V x)
  simp only [map_add,map_mul]

/-- The complex phases are genuine algebraic lifts of the same root grid;
no finite sample set or extra matching oracle is supplied. -/
theorem samples_of_algebraic {m : ℕ} (positive : 0<m) (d : Scalar) (hd : d≠0)
    (U V : Signature Scalar 4)
    (samples : ∀ t : Phase m,algebraicPencil U V t.val=0 ∨
      WeightedMatching m d (algebraicPencil U V t.val)) :
    Samples m (complexTensor U) (complexTensor V) := by
  intro z root
  let t : Phase m := CyclicBoundary.AlgebraicRepresentatives.liftRoot positive ⟨z,root⟩
  have value : (t.val : ℂ)=z := rfl
  have same : complexTensor (algebraicPencil U V t.val)=pencil (complexTensor U) (complexTensor V) z := by
    rw [complex_pencil,value]
  rcases samples t with zero | ⟨M,nonzero,weighted,equation⟩
  · left
    rw [←same,zero]
    funext x
    exact map_zero CyclicBoundary.AlgebraicRepresentatives.inclusion
  · right
    have mapped : complexTensor (algebraicPencil U V t.val)=(complexPresentation M).tensor := by
      rw [equation,complexPresentation_tensor]
      rfl
    rw [←same,mapped]
    exact weighted_presentation_monomial positive d hd M nonzero weighted

/-- Internally derived matching equality at the actual four-port residual
boundary. Both source presentations and ordered root phases remain explicit. -/
theorem sampled_presentations_same_mate {m : ℕ} (hm : 4≤m)
    (d : Scalar) (hd : d≠0) (U V : Signature Scalar 4)
    (samples : ∀ t : Phase m,algebraicPencil U V t.val=0 ∨
      WeightedMatching m d (algebraicPencil U V t.val))
    (t0 t1 : Phase m) (M N : Presentation Scalar (Fin 4))
    (nonzeroM : M.scalar≠0) (nonzeroN : N.scalar≠0)
    (weightedM : ∀ e,Kernel.mul (M.matrix e) (ClosureShiftedWeighted.D d) ∈ groupM m)
    (weightedN : ∀ e,Kernel.mul (N.matrix e) (ClosureShiftedWeighted.D d) ∈ groupM m)
    (equationM : algebraicPencil U V t0.val=M.tensor)
    (equationN : algebraicPencil U V t1.val=N.tensor) :
    (presentationMatching M).mate=(presentationMatching N).mate := by
  have positive : 0<m := by omega
  have actual := samples_of_algebraic positive d hd U V samples
  have imageM : (complexPresentation M).tensor=
      pencil (complexTensor U) (complexTensor V) (t0.val : ℂ) := by
    rw [complexPresentation_tensor,←equationM]
    exact complex_pencil U V t0.val
  have imageN : (complexPresentation N).tensor=
      pencil (complexTensor U) (complexTensor V) (t1.val : ℂ) := by
    rw [complexPresentation_tensor,←equationN]
    exact complex_pencil U V t1.val
  obtain ⟨P⟩ := weighted_presentation_monomial positive d hd M nonzeroM weightedM
  obtain ⟨E⟩ := weighted_presentation_monomial positive d hd N nonzeroN weightedN
  have liveM : pencil (complexTensor U) (complexTensor V) (t0.val : ℂ)≠0 :=
    imageM ▸ P.nonzero_tensor
  have liveN : pencil (complexTensor U) (complexTensor V) (t1.val : ℂ)≠0 :=
    imageN ▸ E.nonzero_tensor
  have root0 : (t0.val : ℂ)^m=1 := by exact_mod_cast t0.property
  have root1 : (t1.val : ℂ)^m=1 := by exact_mod_cast t1.property
  apply weighted_presentations_same_mate positive d hd M N nonzeroM nonzeroN weightedM weightedN
  rw [imageM,imageN]
  exact ((sampled_support_exact hm _ _ actual _ root0 liveM).trans
    (sampled_support_exact hm _ _ actual _ root1 liveN).symm).subset

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
