import Holant.Proofs.Tetrahedral.CyclicResource.Source
import Holant.Proofs.FiniteGroups.Stabilization.FullRetainedDeck
import Holant.Proofs.FiniteGroups.Stabilization.BinaryPrimes
import Holant.Proofs.Algorithms.RingHomDescent


namespace Holant.LocalDrafts.TetrahedralCompletion.CyclicResource.PhaseProvenance
open Holant Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open CyclicBoundary CyclicBoundary.PhysicalAttachments CyclicBoundary.ZeroEndpointDressing
open RingHomRealization
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Non-singularity follows from the actual physical action equation. It is
not an extra safe-binary hypothesis on the selected phase representatives. -/
theorem phase_det {F : SignatureFamily ℂ} {N : ℕ} (R : Representatives F N)
    (s : {s : ℂ // s^N=1}) :
    Matrix.det (R.matrix s) = -4 * (R.scalar s)^2 * s.val := by
  have hx : Matrix.det (X : Binary (K := ℂ)) = -1 := by
    rw [binary_det_formula]
    norm_num [X,Signature.disequality]
  have hh : Matrix.det (hadamard : Binary (K := ℂ)) = -2 := by
    rw [binary_det_formula]
    norm_num [hadamard]
  have hp : Matrix.det ((2 * R.scalar s) • phase s.val) =
      4 * (R.scalar s)^2 * s.val := by
    rw [binary_det_formula]
    simp [phase,TwoCopyKernels.diagonal]
    ring
  have hd := congrArg (fun A : Kernel ℂ => Matrix.det A) (R.action s)
  change Matrix.det ((Matrix.of (R.matrix s) * Matrix.of X) * Matrix.of hadamard) =
    Matrix.det (Matrix.of hadamard * Matrix.of ((2 * R.scalar s) • phase s.val)) at hd
  simp only [Matrix.det_mul] at hd
  change Matrix.det (R.matrix s) * Matrix.det X * Matrix.det hadamard =
    Matrix.det hadamard * Matrix.det ((2 * R.scalar s) • phase s.val) at hd
  rw [hx,hh,hp] at hd
  linear_combination hd / 2

theorem phase_nonsingular {F : SignatureFamily ℂ} {N : ℕ} (R : Representatives F N)
    (hN : 0 < N) (s : {s : ℂ // s^N=1}) : Matrix.det (R.matrix s) ≠ 0 := by
  rw [phase_det]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (R.scalar_ne_zero s)))
    (Holant.Projective.CyclicPhasePencil.root_ne_zero hN s.property)

variable {L : Type*} [Field L]

/-- Descent of an arbitrary actual signature, with its value recovered from
the same chosen open graph. No a priori coefficient preimage is required. -/
theorem actual_preimage (φ : L →+* ℂ) {F : SignatureFamily L} {n : ℕ}
    {f : Signature ℂ n} (hf : Gadget.Realizes (mapFamily φ F) .disequality f) :
    ∃ g : Signature L n, Gadget.Realizes F .disequality g ∧
      RingHomRealization.mapSignature φ g = f := by
  obtain ⟨M,hM,hW,he⟩ := hf
  let D := RingHomDescent.descendNetwork φ M hM
  refine ⟨D.tensor,⟨D,RingHomDescent.descend_labels φ M hM,hW,rfl⟩,?_⟩
  exact (RingHomDescent.descend_tensor φ M hM).trans he

def mapMatrix (φ : L →+* ℂ) (B : Binary (K := L)) : Kernel ℂ :=
  fun a b => φ (B a b)

theorem mapMatrix_det (φ : L →+* ℂ) (B : Binary (K := L)) :
    Matrix.det (mapMatrix φ B) = φ (Matrix.det B) := by
  simp only [binary_det_formula,mapMatrix,map_sub,map_mul]

theorem phase_preimage (φ : L →+* ℂ) {F : SignatureFamily L} {N : ℕ}
    (R : Representatives (mapFamily φ F) N) (hN : 0 < N)
    (s : {s : ℂ // s^N=1}) :
    ∃ B : Binary (K := L), ActualNonsingular F B ∧ mapMatrix φ B = R.matrix s := by
  obtain ⟨g,hg,he⟩ := actual_preimage φ (R.actual s)
  have hb : mapMatrix φ (binaryMatrix g) = R.matrix s := by
    funext a b
    exact congrFun he ![a,b]
  refine ⟨binaryMatrix g,⟨?_,?_⟩,hb⟩
  · simpa only [binarySignature_binaryMatrix] using hg
  · intro hz
    have hd := phase_nonsingular R hN s
    rw [←hb,mapMatrix_det,hz,map_zero] at hd
    exact hd rfl

variable [NumberField L]

/-- Here Λ is DEFINED to be the existing fullRetainedDeck output, not a
fresh augmentation of the current node. Completeness and the unchanged-group
test recover a retained literal binary proportional to each chosen phase. -/
theorem phase_has_frozen_source (φ : L →+* ℂ) (F₀ : SignatureFamily L)
    (h₀ : ResidualTorsion F₀) (q₀ : Signature L 4)
    (hΛ : ResidualTorsion (fullRetainedDeck F₀ h₀ q₀))
    (hgroup : completeGroup (fullRetainedDeck F₀ h₀ q₀) hΛ = completeGroup F₀ h₀)
    {N : ℕ} (R : Representatives (mapFamily φ (fullRetainedDeck F₀ h₀ q₀)) N)
    (hN : 0 < N) (s : {s : ℂ // s^N=1}) :
    ∃ g : completeGroup F₀ h₀, ∃ c : L, c ≠ 0 ∧
      R.matrix s = φ c • mapMatrix φ (actualRepresentative F₀ h₀ g) ∧
      (⟨2,binarySignature (actualRepresentative F₀ h₀ g)⟩ : AnySignature L) ∈
        fullRetainedDeck F₀ h₀ q₀ := by
  obtain ⟨B,hB,hmap⟩ := phase_preimage φ R hN s
  obtain ⟨g,c,hc,he⟩ := (frozen_representatives_cover_retained
    (fullRetainedDeck_retains F₀ h₀ q₀) h₀ hΛ hgroup).2 B hB
  refine ⟨g,c,hc,?_,fullRetainedDeck_representative F₀ h₀ q₀ g⟩
  rw [←hmap,he]
  funext a b
  simp [mapMatrix]

end
end Holant.LocalDrafts.TetrahedralCompletion.CyclicResource.PhaseProvenance
