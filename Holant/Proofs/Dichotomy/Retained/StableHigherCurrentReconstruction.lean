import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentCoverage
import Holant.Proofs.Closure.FrontierNativeClosure

/-! The precise remaining ancestor-reconstruction seam, at one fixed class
and basis. Exact final preparation already proves that every proper current
card is assembled from strictly smaller current saved leaves. Strong induction
therefore reduces whole-current closure to binary/q4 membership and a genuine
higher-ancestor theorem. The latter is explicit and is not supplied here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8192
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentReconstruction
open Holant Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open FrontierClosure FrontierCommonPresentation StableHigherCurrentCoverage
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable (C : AnySignature (OI.K G) → Prop)

def ScaleClosed : Prop := ∀ n (f : Signature (OI.K G) n),
  C ⟨n,f⟩ → ∀ c : OI.K G, c ≠ 0 → C ⟨n,c • f⟩

def ZeroClosed : Prop := ∀ n, C ⟨n,(0 : Signature (OI.K G) n)⟩

variable {S T : GeneratedGroupWorklist.Active G base}
variable {h : GeneratedGroupWorklist.Trace G base S T}
variable {o : CurrentOccurrences.Id G T.source.palette}
variable (r : GeneratedGroupWorklist.PreparationReceipt G base h o)
variable (proper : 4 ≤ (CurrentOccurrences.savedLeaf G T.source.palette o).1.1)

/-- Prepared cards have exact smaller-leaf support in the SAME common class.
No independently chosen current factorization or representative is introduced. -/
theorem rawDeck_closed_of_lower_current (splits : SplitClosed G C)
    (scales : ScaleClosed G C) (zeros : ZeroClosed G C)
    (lower : ∀ q : CurrentOccurrences.Id G T.source.palette,
      (CurrentOccurrences.savedLeaf G T.source.palette q).1.1 <
        (CurrentOccurrences.savedLeaf G T.source.palette o).1.1 →
      C (CurrentOccurrences.savedLeaf G T.source.palette q).1) :
    ∀ f ∈ rawDeck T.source.palette.family T.ready.torsion (input G base r proper).signature,
      C ⟨(input G base r proper).m,f⟩ := by
  classical
  intro f member
  rcases member with zero | ⟨key,rfl⟩
  · rw [zero]
    exact zeros _
  · by_cases zero : current G base r proper key = 0
    · change C ⟨(input G base r proper).m,current G base r proper key⟩
      rw [zero]
      exact zeros _
    · have oldClosed : C (oldRoot G base r proper key zero).1 := by
        apply factorTree_closed G C splits (oldRoot G base r proper key zero).2
        intro p
        rw [← cardLeaf_saved G base r proper key zero p]
        exact lower _ (cardLeaf_arity_lt G base r proper key zero p)
      change C ⟨(input G base r proper).m,
        rawCard T.source.palette.family T.ready.torsion (input G base r proper).signature key⟩
      rw [(transport G base r proper key).equation]
      exact scales _ _ oldClosed _ (transport G base r proper key).nonzero

variable {A : GeneratedGroupWorklist.Active G base}
variable (R : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done = ∅)

/-- This is the mathematical higher-ancestor implication still required.
The entire actual current raw deck is in ONE fixed C. It is not a matching
premise and does not allow a separate basis or class for each card. -/
def AncestorReconstruction : Prop :=
  ∀ (o : CurrentOccurrences.Id G R.final.source.palette)
    (proper : 4 ≤ (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1),
    4 < (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1 →
    (∀ f ∈ rawDeck R.final.source.palette.family R.final.ready.torsion
      (input G base (R.preparationReceipt G base noPrior o) proper).signature,
      C ⟨(input G base (R.preparationReceipt G base noPrior o) proper).m,f⟩) →
    C (CurrentOccurrences.savedLeaf G R.final.source.palette o).1

/-- Binary and q4 leaves are the actual induction base; every higher induction
step receives all proper cards from exact final preparation. -/
theorem local_current_of_reconstruction (splits : SplitClosed G C)
    (scales : ScaleClosed G C) (zeros : ZeroClosed G C)
    (binary : ∀ o : CurrentOccurrences.Id G R.final.source.palette,
      (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1 = 2 →
      C (CurrentOccurrences.savedLeaf G R.final.source.palette o).1)
    (quaternary : ∀ o : CurrentOccurrences.Id G R.final.source.palette,
      (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1 = 4 →
      C (CurrentOccurrences.savedLeaf G R.final.source.palette o).1)
    (reconstruct : AncestorReconstruction G base C R noPrior) :
    CurrentFrontierClosure.LocalCurrentTheorems G R.final.source.palette C := by
  have all : ∀ n : ℕ, ∀ o : CurrentOccurrences.Id G R.final.source.palette,
      (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1 = n →
      C (CurrentOccurrences.savedLeaf G R.final.source.palette o).1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro o arity
      have positive := CurrentOccurrences.savedLeaf_positive G R.final.source.palette o
      have noUnary := CurrentFrontierClosure.no_current_unary G R.final.source.palette
        R.final.ready.noUnary o
      by_cases two : n = 2
      · exact binary o (arity.trans two)
      by_cases four : n = 4
      · exact quaternary o (arity.trans four)
      have three : 3 ≤ (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1 := by omega
      have even := R.final.ready.noOdd _ (CurrentOccurrences.savedLeaf_retained G R.final.source.palette o)
        (CurrentOccurrences.savedLeaf_prime G R.final.source.palette o) three
      have higher : 4 < (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1 := by
        obtain ⟨k,hk⟩ := even
        omega
      apply reconstruct o higher.le higher
      apply rawDeck_closed_of_lower_current G base C
        (R.preparationReceipt G base noPrior o) higher.le splits scales zeros
      intro q lower
      exact ih (CurrentOccurrences.savedLeaf G R.final.source.palette q).1.1
        (by simpa only [arity] using lower) q rfl
  exact ⟨fun o _ _ => all _ o rfl,fun o _ _ => all _ o rfl,
    fun o _ _ _ => all _ o rfl,fun o _ _ _ => all _ o rfl⟩

/-- An exact necessary-and-sufficient seam, with no claim that the ancestor
implication is already proved. This rules out a small-witness-only closure. -/
theorem local_current_iff_reconstruction (splits : SplitClosed G C)
    (scales : ScaleClosed G C) (zeros : ZeroClosed G C) :
    CurrentFrontierClosure.LocalCurrentTheorems G R.final.source.palette C ↔
      (∀ o : CurrentOccurrences.Id G R.final.source.palette,
        (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1 = 2 →
          C (CurrentOccurrences.savedLeaf G R.final.source.palette o).1) ∧
      (∀ o : CurrentOccurrences.Id G R.final.source.palette,
        (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1 = 4 →
          C (CurrentOccurrences.savedLeaf G R.final.source.palette o).1) ∧
      AncestorReconstruction G base C R noPrior := by
  constructor
  · intro leaves
    have all := CurrentFrontierClosure.leaf_conclusion G R.final.source.palette C leaves
    exact ⟨fun o _ => all o,fun o _ => all o,fun o _ _ _ => all o⟩
  · rintro ⟨binary,quaternary,reconstruct⟩
    exact local_current_of_reconstruction G base C R noPrior splits scales zeros binary quaternary reconstruct

/-- The scalar rule is established for the three concrete native target
classes after the SAME field embedding and SAME inverse basis action. -/
theorem target_scaleClosed (target : TargetClass) (U : InvertibleKernel) :
    ScaleClosed G (leafPredicate G target.family U) := by
  intro n f member c _nonzero
  have action : U.symm.action (embed G (⟨n,c • f⟩ : AnySignature (OI.K G))).2 =
      fun x => (Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.embedding G) c *
        U.symm.action (embed G (⟨n,f⟩ : AnySignature (OI.K G))).2 x := by
    change Signature.coordinateAction (fun _ => U.symm.matrix)
      (fun x => (Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.embedding G) (c * f x)) = _
    simp_rw [map_mul]
    exact FrontierSplitClosure.action_scale _ _ _
  cases target with
  | affine =>
    change Affine (U.symm.action (embed G (⟨n,c • f⟩ : AnySignature (OI.K G))).2)
    rw [action]
    exact Affine.scale member _
  | product =>
    change Product (U.symm.action (embed G (⟨n,c • f⟩ : AnySignature (OI.K G))).2)
    rw [action]
    exact Product.scale member _
  | localAffine =>
    change LocalAffine (U.symm.action (embed G (⟨n,c • f⟩ : AnySignature (OI.K G))).2)
    rw [action]
    exact LocalAffine.scale member _

theorem target_zeroClosed (target : TargetClass) (U : InvertibleKernel) :
    ZeroClosed G (leafPredicate G target.family U) := by
  intro n
  have zero : U.symm.action (embed G (⟨n,(0 : Signature (OI.K G) n)⟩ : AnySignature (OI.K G))).2 = 0 := by
    change Signature.coordinateAction (fun _ => U.symm.matrix)
      (fun x => (Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.embedding G) 0) = 0
    simp only [map_zero]
    exact Signature.coordinateAction_zero _
  cases target with
  | affine => change Affine _; rw [zero]; exact affine_zero n
  | product => change Product _; rw [zero]; exact product_zero n
  | localAffine => change LocalAffine _; rw [zero]; exact localAffine_zero n

/-- All actual proper current cards are in the fixed target class whenever
its strictly smaller CURRENT saved leaves are; this needs no rigidity oracle. -/
theorem target_rawDeck_closed_of_lower_current (target : TargetClass) (U : InvertibleKernel)
    (lower : ∀ q : CurrentOccurrences.Id G T.source.palette,
      (CurrentOccurrences.savedLeaf G T.source.palette q).1.1 <
        (CurrentOccurrences.savedLeaf G T.source.palette o).1.1 →
      leafPredicate G target.family U (CurrentOccurrences.savedLeaf G T.source.palette q).1) :
    ∀ f ∈ rawDeck T.source.palette.family T.ready.torsion (input G base r proper).signature,
      leafPredicate G target.family U ⟨(input G base r proper).m,f⟩ :=
  rawDeck_closed_of_lower_current G base (leafPredicate G target.family U) r proper
    (FrontierSplitClosure.splitClosed_target G target U)
    (target_scaleClosed G target U) (target_zeroClosed G target U) lower


/-- No class or basis may be selected per occurrence. With a fixed target and
basis, the only remaining nonbinary induction data are q4 and the displayed
higher-ancestor implication. Split, scalar and zero closure are proved above. -/
theorem target_local_current_iff_reconstruction (target : TargetClass) (U : InvertibleKernel) :
    CurrentFrontierClosure.LocalCurrentTheorems G R.final.source.palette
      (leafPredicate G target.family U) ↔
      (∀ o : CurrentOccurrences.Id G R.final.source.palette,
        (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1 = 2 →
          leafPredicate G target.family U (CurrentOccurrences.savedLeaf G R.final.source.palette o).1) ∧
      (∀ o : CurrentOccurrences.Id G R.final.source.palette,
        (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1 = 4 →
          leafPredicate G target.family U (CurrentOccurrences.savedLeaf G R.final.source.palette o).1) ∧
      AncestorReconstruction G base (leafPredicate G target.family U) R noPrior :=
  local_current_iff_reconstruction G base (leafPredicate G target.family U) R noPrior
    (FrontierSplitClosure.splitClosed_target G target U)
    (target_scaleClosed G target U) (target_zeroClosed G target U)

/-- Compatibility is explicit at the physical native edge as well as all
current saved occurrences. This remains conditional on the actual missing
higher reconstruction theorem; it is not an unconditional endpoint. -/
theorem native_tractx_of_reconstruction (target : TargetClass) (U : InvertibleKernel)
    (edge : (⟨2,kernelSignature (Kernel.pullback Signature.disequality U.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ target.family)
    (binary : ∀ o : CurrentOccurrences.Id G R.final.source.palette,
      (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1 = 2 →
      leafPredicate G target.family U (CurrentOccurrences.savedLeaf G R.final.source.palette o).1)
    (quaternary : ∀ o : CurrentOccurrences.Id G R.final.source.palette,
      (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1 = 4 →
      leafPredicate G target.family U (CurrentOccurrences.savedLeaf G R.final.source.palette o).1)
    (reconstruct : AncestorReconstruction G base (leafPredicate G target.family U) R noPrior) :
    TractX (familyAction sourceKBasis (CurrentFrontierClosure.currentFamily G R.final.source.palette)) :=
  FrontierNativeClosure.relative_current_native_tractx G R.final.source.palette target U edge
    ((target_local_current_iff_reconstruction G base R noPrior target U).mpr
      ⟨binary,quaternary,reconstruct⟩)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentReconstruction
end
