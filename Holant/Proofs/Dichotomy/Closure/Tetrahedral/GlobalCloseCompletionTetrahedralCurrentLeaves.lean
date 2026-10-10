import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralSavedCards
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralSixCurrent
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralAffineDeck
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentReconstruction
import Holant.Proofs.Dichotomy.Retained.StableCurrentEvenRowBasis

/-! Same-palette T closure through the actual saved trees. Every final q4
occurrence is excluded by its own final preparation receipt, including leaves
installed during generation. Hence each six-port raw card has only binary
saved leaves. Above six, exact smaller-leaf reconstruction gives affine cards. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralCurrentLeaves
open Holant Holant.Tractable Holant.Algebraic
open Holant.Projective.BoundedTorsion Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2 Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source ClosureMarkedReversalOvergroup.Ambient
open FrontierCommonPresentation StableHigherCurrentCoverage StableHigherCurrentReconstruction
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable {A : GeneratedGroupWorklist.Active G base}
variable (R : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
abbrev IsAffine := leafPredicate G affineClass InvertibleKernel.identity
variable (semantic : HasModel (overgroup (ClosureSourceRows.embedding G)
  (palette G base R).family R.final.ready.torsion) (.platonic .tetrahedral))

theorem affine_iff (f : AnySignature (OI.K G)) :
    IsAffine G f ↔ Affine (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f.2) := by
  change Affine (InvertibleKernel.identity.symm.action (embed G f).2) ↔ _
  simp only [InvertibleKernel.identity_symm,InvertibleKernel.identity_action] <;> rfl

include semantic in
theorem binary_affine (f : AnySignature (OI.K G))
    (retained : f∈(palette G base R).family) (prime : Prime f) (two : f.1=2) : IsAffine G f := by
  rcases f with ⟨n,f⟩
  dsimp only at two
  subst n
  apply (affine_iff G _).mpr
  apply GlobalCloseCompletionTetrahedralAffineCards.affine_of_complex
  apply GlobalCloseCompletionTetrahedralAffineCards.matching_affine
    (ClosureSourceRows.embedding G) (palette G base R).family R.final.ready.torsion
    (GlobalCloseCompletionTetrahedralMarking.semantic_tetrahedral_literal
      (ClosureSourceRows.embedding G) (palette G base R).family R.final.ready.torsion
      (palette G base R).equality semantic)
  apply FactorTree.matchingOrZero (.leaf ⟨2,f⟩ prime) (palette G base R).family
  · intro g hg
    have he : g=(⟨2,f⟩ : AnySignature (OI.K G)) := by
      simpa only [FactorTree.leaves,Multiset.mem_singleton] using hg
    exact he.symm ▸ retained
  · intro g hg
    have he : g=(⟨2,f⟩ : AnySignature (OI.K G)) := by
      simpa only [FactorTree.leaves,Multiset.mem_singleton] using hg
    exact congrArg Sigma.fst he

include semantic in
private theorem affine_at_six {m : ℕ} (f : Signature (OI.K G) (m+2))
    (six : m+2=6)
    (stable : ∀q∈rawDeck (palette G base R).family R.final.ready.torsion f,
      MatchingOrZero (actualTransfers (palette G base R).family) q)
    (prime : Prime (⟨m+2,f⟩ : AnySignature (OI.K G))) :
    Affine (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f) := by
  have hm : m=4 := by omega
  subst m
  exact GlobalCloseCompletionTetrahedralSixCurrent.semantic_prime_six_affine
    (ClosureSourceRows.embedding G) (palette G base R).family R.final.ready.torsion
    f stable (palette G base R).equality semantic prime

include noPrior semantic in
theorem six_affine (o : CurrentOccurrences.Id G (palette G base R))
    (six : (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1=6) :
    IsAffine G (CurrentOccurrences.savedLeaf G (palette G base R) o).1 := by
  let r := R.preparationReceipt G base noPrior o
  have proper : 4≤(CurrentOccurrences.savedLeaf G (palette G base R) o).1.1 := by omega
  rw [←r.selectedSignatureFinal G base proper]
  apply (affine_iff G _).mpr
  apply affine_at_six G base R semantic (input G base r proper).signature
  · exact (congrArg Sigma.fst (r.selectedSignatureFinal G base proper)).trans six
  · exact six_matching G base R noPrior semantic o proper six
  · rw [r.selectedSignatureFinal G base proper]
    exact CurrentOccurrences.savedLeaf_prime G (palette G base R) o

include noPrior semantic in
theorem reconstruction : AncestorReconstruction G base (IsAffine G) R noPrior := by
  intro o proper higher cards
  by_cases six : (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1=6
  · exact six_affine G base R noPrior semantic o six
  change (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1≠6 at six
  let r := R.preparationReceipt G base noPrior o
  have size := congrArg Sigma.fst (r.selectedSignatureFinal G base proper)
  change (input G base r proper).m+2=_ at size
  have even : Even ((input G base r proper).m+2) :=
    (r.higherData G base proper).input.evenArity
  have above : 4<(input G base r proper).m+2 := by
    rw [size]
    exact higher
  have notsix : (input G base r proper).m+2≠6 := by
    rw [size]
    exact six
  have high : 8≤(input G base r proper).m+2 := by
    obtain ⟨k,hk⟩ := even
    omega
  rw [←r.selectedSignatureFinal G base proper]
  apply (affine_iff G _).mpr
  apply GlobalCloseCompletionTetrahedralAffineDeck.semantic_prime_higher_affine
    (ClosureSourceRows.embedding G) (palette G base R).family R.final.ready.torsion
    (input G base r proper).signature
  · intro q hq
    exact (affine_iff G _).mp (cards q hq)
  · exact (palette G base R).equality
  · exact semantic
  · exact high
  · rw [r.selectedSignatureFinal G base proper]
    exact CurrentOccurrences.savedLeaf_prime G (palette G base R) o

include noPrior semantic in
theorem current_tract : TractX (familyAction sourceKBasis
    (CurrentFrontierClosure.currentFamily G (palette G base R))) := by
  apply native_tractx_of_reconstruction G base R noPrior .affine InvertibleKernel.identity
  · change Affine (kernelSignature (Kernel.pullback Signature.disequality InvertibleKernel.identity.matrix))
    simpa [InvertibleKernel.identity,Kernel.pullback] using StableCurrentEvenRowBasis.native_edge_affine
  · intro o two
    exact binary_affine G base R semantic _
      (CurrentOccurrences.savedLeaf_retained G (palette G base R) o)
      (CurrentOccurrences.savedLeaf_prime G (palette G base R) o) two
  · intro o four
    exact (no_quaternary G base R noPrior semantic o four).elim
  · exact reconstruction G base R noPrior semantic


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralCurrentLeaves
end
