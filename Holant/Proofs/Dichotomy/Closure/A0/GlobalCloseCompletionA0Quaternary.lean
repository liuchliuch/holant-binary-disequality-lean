import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0Workfield
import Holant.Proofs.Closure.HistorySectorNormalizedDeck
import Holant.Proofs.Dichotomy.Retained.StableCurrentEvenEOTransport
import Holant.Certificates.EqualityQuaternary.CoordinatePrimality

/-! Actual A0 prime q4 support from its complete physical CURRENT deck.
The Hadamard edge is exactly 2Z and the weighted-pencil parameter is -1.
This proof does not misuse the shifted A parameter guard at eta=1. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0Quaternary
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.Marked.SupportAtlas Holant.Certificates.EqualityQuaternary
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (stable : ∀ f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)
abbrev basis := GlobalCloseCompletionA0Workfield.basis
abbrev normalized : Signature AlgebraicComplex 4 :=
  basis.symm.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q)

include core literal in
theorem normalized_prime : TensorPrime (normalized G q) :=
  prime_coordinateAction (ClosureSourceRows.core_ambient_prime G P q core literal)
    (fun _ => basis.inverse) (fun _ => basis.matrix) (fun _ => basis.matrix_inverse)

private theorem safe_physical (B : Mat) (hB : B=0 ∨ sectorTransfer basis B∈groupM N.selected.m) :
    SafeWeighted N.selected.m (-1) (complexMatrix (transport basis B)) := by
  rcases hB with rfl | hB
  · left
    funext b c
    simp [complexMatrix,transport,Kernel.mul_apply]
  · right
    have h := groupM_complex_root (by have := N.range; omega) _ hB
    rw [←transport_mul_edge,ClosureMarkedCyclic.same_edge,scale_mul_right,
      complexMatrix_scale,complexMatrix_mul,complexMatrix_diagonal] at h
    have h2 : ((2 : Scalar) : ℂ)≠0 := by norm_num
    simpa using (rootMonomial_smul_iff N.selected.m (2 : ℂ) h2 _).mp h

abbrev representatives := HistorySectorNormalized.representatives G P torsion basis N.selected

theorem card_normalization (e : Equiv.Perm (Fin 4)) (p : Bool) (t : Phase N.selected.m) :
    transport basis (physicalCard
      (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q) e
      ((representatives G P torsion N).matrix p t))=
        scale (2*(representatives G P torsion N).multiplier p t)
          (contract0 (reorder (normalized G q) e)
            (Kernel.mul (diagonalKernel 1 (-1)) (if p then S t.val else R t.val))) := by
  rw [physicalCard_transport,Kernel.mul_assoc,transport_mul_edge,
    (representatives G P torsion N).transfer,ClosureMarkedCyclic.same_edge,scale_mul,contract0_scale]

include core literal stable in
theorem safeDeck : SafeDeck N.selected.m (-1) (complexTensor (normalized G q)) := by
  intro e p t ht
  let z : Phase N.selected.m := ⟨Holant.Projective.CyclicPhasePencil.algebraicRoot
    (by have := N.range; omega) t ht,Holant.Projective.CyclicPhasePencil.algebraicRoot_pow
      (by have := N.range; omega) t ht⟩
  have physical := HistorySectorNormalized.physicalDeck G P torsion basis N.selected q core literal stable e p z
  have h := safe_physical G P torsion N _ physical
  rw [card_normalization G P torsion N q,complexMatrix_scale,complex_weighted_card] at h
  have hn : (↑(2*(representatives G P torsion N).multiplier p z) : ℂ)≠0 := by
    exact_mod_cast mul_ne_zero (by norm_num : (2 : Scalar)≠0)
      ((representatives G P torsion N).multiplier_ne_zero p z)
  exact (safeWeighted_smul_iff N.selected.m (-1)
    (↑(2*(representatives G P torsion N).multiplier p z) : ℂ) hn _).mp h

include N core literal stable in
theorem parity_and_complement :
    ∃p : Bool,(∀x,normalized G q x≠0 → parity x=p) ∧
      (∀x,normalized G q (complement x)=0 ↔ normalized G q x=0) := by
  have deck := deckSupport_of_samples (by have := N.range; omega) (-1) (by norm_num) (by simp)
    (complexTensor (normalized G q)) (safeDeck G P torsion N q core literal stable)
  have nonzero := (normalized_prime G P q core literal).1
  obtain ⟨x,hx⟩ : ∃x,normalized G q x≠0 := by
    by_contra h
    push Not at h
    exact nonzero (funext h)
  have live : nonzeroBit (complexTensor (normalized G q) x)=true := by
    simp [complexTensor,hx]
  obtain ⟨p,hp,hc⟩ := classification deck ⟨x,live⟩
  refine ⟨p,?_,?_⟩
  · intro y hy
    apply hp y
    simp [complexTensor,hy]
  · intro y
    have he : nonzeroBit (complexTensor (normalized G q) (complement y))=false ↔
        nonzeroBit (complexTensor (normalized G q) y)=false := by rw [complement_eq deck y]
    simpa only [nonzeroBit_false,complexTensor,AlgebraicComplex.coe_eq_zero] using he


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0Quaternary
end
