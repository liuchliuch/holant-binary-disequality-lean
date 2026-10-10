import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralClassifier
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralMarking
import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicCards
import Holant.Proofs.Closure.GeneratedGroupQ4Consumers

/-! The actual internal tetrahedral branch cannot retain a prepared prime q4.
The finite coefficient classifier is fed from the same current raw deck and
original-field representatives. Higher arities and external T retain their
separate obligations; no full Platonic dichotomy is claimed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralCurrent
open Holant Holant.Tractable Holant.Algebraic
open Holant.Projective.BoundedTorsion Holant.Projective.FiniteGroupFacts
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.LocalDrafts.FinitePGL2 Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source ClosureMarkedReversalOvergroup.Ambient
namespace C
export GlobalCloseCompletionTetrahedralClassifier (literal_factorization matchingFrame)
end C
namespace D
export GlobalCloseCompletionTetrahedralLiteralDeck (LiteralDeck)
end D
namespace Q
export GeneratedGroupQ4Consumers (table minimum minimum_literal matching)
end Q

theorem matching_tensor (r : Fin 3) (U V : Holant.Certificates.MatchingProductBridge.Binary) :
    matchingProduct r U V=Tensor.reindex (finSumFinEquiv.trans (C.matchingFrame r))
      (Tensor.tensor (Holant.Projective.BoundedTorsion.binarySignature U) (Holant.Projective.BoundedTorsion.binarySignature V)) := by
  ext x
  fin_cases r <;>
    simp [matchingProduct,C.matchingFrame,GlobalCloseCompletionTetrahedralClassifier.matchingFrame,
      P0,P1,P2,Tensor.reindex,Tensor.tensor,Holant.Projective.BoundedTorsion.binarySignature,
      Equiv.swap_apply_def,finSumFinEquiv]

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (same : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

include core same stable in
theorem literal_tetrahedral_impossible
    (literal : group (ClosureSourceRows.embedding G) P.family torsion=modelPGL .tetrahedral) : False := by
  have prime : Prime (⟨4,q⟩ : AnySignature (OI.K G)) := same ▸ core.prime
  let phi := complexEmbedding (ClosureSourceRows.embedding G)
  have hp : Prime (⟨4,RingHomRealization.mapSignature phi q⟩ : AnySignature ℂ) :=
    (prime_mapSignature_iff phi (⟨4,q⟩ : AnySignature (OI.K G))).mpr prime
  have deck : D.LiteralDeck (RingHomRealization.mapSignature phi q) :=
    GlobalCloseCompletionPlatonicCards.current_literal_deck .tetrahedral G P torsion literal q core same stable
  obtain ⟨r,U,V,c,_,_,_,he⟩ := C.literal_factorization (RingHomRealization.mapSignature phi q) deck hp.1
  apply hp.2
  refine ⟨⟨2,c • Holant.Projective.BoundedTorsion.binarySignature U⟩,
    ⟨2,Holant.Projective.BoundedTorsion.binarySignature V⟩,⟨{
      left_pos := by change 0<2; decide
      right_pos := by change 0<2; decide
      ports := finSumFinEquiv.trans (C.matchingFrame r)
      scale := 1
      equation := ?_ }⟩⟩
  change RingHomRealization.mapSignature phi q =
    (1 : ℂ) • Tensor.reindex (finSumFinEquiv.trans (C.matchingFrame r))
      (Tensor.tensor (c • Holant.Projective.BoundedTorsion.binarySignature U)
        (Holant.Projective.BoundedTorsion.binarySignature V))
  rw [he,matching_tensor]
  ext x
  simp [RingHomRealization.mapSignature,Tensor.reindex,Tensor.tensor,smul_eq_mul,mul_assoc]

include core same stable in
theorem semantic_tetrahedral_impossible
    (model : HasModel (overgroup (ClosureSourceRows.embedding G) P.family torsion)
      (.platonic .tetrahedral)) : False :=
  literal_tetrahedral_impossible G P torsion q core same stable
    (GlobalCloseCompletionTetrahedralMarking.semantic_tetrahedral_literal
      (ClosureSourceRows.embedding G) P.family torsion P.equality model)

include core same stable in
theorem actual_tetrahedral_external
    (model : HasModel (group (ClosureSourceRows.embedding G) P.family torsion)
      (.platonic .tetrahedral)) : zClass∉group (ClosureSourceRows.embedding G) P.family torsion := by
  intro hz
  exact literal_tetrahedral_impossible G P torsion q core same stable
    (GlobalCloseCompletionTetrahedralMarking.actual_tetrahedral_internal
      (ClosureSourceRows.embedding G) P.family torsion P.equality model hz)

variable (base : Palette G)
variable {S T : GeneratedGroupWorklist.Active G base}
variable {trace : GeneratedGroupWorklist.Trace G base S T}
variable {o : CurrentOccurrences.Id G T.source.palette}
variable (receipt : GeneratedGroupWorklist.PreparationReceipt G base trace o)
variable (four : (CurrentOccurrences.savedLeaf G T.source.palette o).1.1=4)

include receipt four in
theorem prepared_semantic_tetrahedral_impossible
    (model : HasModel (overgroup (ClosureSourceRows.embedding G)
      T.source.palette.family T.ready.torsion) (.platonic .tetrahedral)) : False :=
  semantic_tetrahedral_impossible G T.source.palette T.ready.torsion
    (Q.table G base four) (Q.minimum G base four) (Q.minimum_literal G base four)
    (Q.matching G base receipt four) model

include receipt four in
theorem prepared_actual_tetrahedral_external
    (model : HasModel (group (ClosureSourceRows.embedding G)
      T.source.palette.family T.ready.torsion) (.platonic .tetrahedral)) :
    zClass∉group (ClosureSourceRows.embedding G) T.source.palette.family T.ready.torsion :=
  actual_tetrahedral_external G T.source.palette T.ready.torsion
    (Q.table G base four) (Q.minimum G base four) (Q.minimum_literal G base four)
    (Q.matching G base receipt four) model

/-- Exact current-q4 refinement of the actual returned marking. It retains
all semantic payloads and only rules out the internal tetrahedral placement. -/
def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    T.source.palette.family T.ready.torsion) : Prop := match M with
  | .platonic p _ => p≠.tetrahedral ∧
      (HasModel (group (ClosureSourceRows.embedding G) T.source.palette.family T.ready.torsion)
        (.platonic .tetrahedral) →
        zClass∉group (ClosureSourceRows.embedding G) T.source.palette.family T.ready.torsion)
  | _ => True

include receipt four in
theorem forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    T.source.palette.family T.ready.torsion) : ForMarking G base (T:=T) M := by
  cases M with
  | platonic p model =>
      constructor
      · intro hp
        subst p
        exact prepared_semantic_tetrahedral_impossible G base receipt four model
      · exact prepared_actual_tetrahedral_external G base receipt four
  | smallTwo => trivial
  | smallFour => trivial
  | cyclic => trivial
  | monomial => trivial
  | bilinear => trivial
  | unshifted => trivial
  | shifted => trivial

def ForResult (result : GeneratedGroupWorklist.Result G base) : Prop := match result with
  | .initialStop .. => True
  | .prepared _ _ (.inl _) => True
  | .prepared _ _ (.inr exhausted) =>
      ∀ (o : CurrentOccurrences.Id G exhausted.final.source.palette)
        (_four : (CurrentOccurrences.savedLeaf G exhausted.final.source.palette o).1.1=4),
        ForMarking G base (T:=exhausted.final)
          (ClosureMarkedActualReceipts.produce G exhausted.final.source.palette
            exhausted.final.ready.torsion).physical.marking

theorem forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result := by
  cases result with
  | initialStop => trivial
  | prepared ready trace result =>
    cases result with
    | inl stop => trivial
    | inr exhausted =>
      intro o four
      exact forMarking G base (exhausted.preparationReceipt G base rfl o) four _

theorem original_current_tetrahedral_refinement : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralCurrent
end
