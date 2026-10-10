import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralCurrent
import Holant.Proofs.Dichotomy.Closure.External.GlobalCloseCompletionExternalTetrahedralCards

/-! The external actual-T possibility inside a semantic O marking also
contradicts the same prepared current prime q4. The finite preserver theorem
is fed only the actual raw-deck tests and their original nonzero multipliers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionExternalTetrahedralCurrent
open Holant Holant.Tractable Holant.Algebraic
open Holant.Projective.BoundedTorsion Holant.Projective.FiniteGroupFacts
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open Holant.Certificates Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.LocalDrafts.FinitePGL2 Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source ClosureMarkedReversalOvergroup.Ambient
open scoped Matrix
namespace D
export GlobalCloseCompletionExternalTetrahedralCards (LiteralDeck current_literal_deck)
end D
namespace L
export GlobalCloseCompletionTetrahedralLiteralDeck
  (relabel rawCard blockSwap cardMatrix_action cardMatrix_complement relabel_relabel)
end L
namespace Q
export GeneratedGroupQ4Consumers (table minimum minimum_literal matching)
end Q

private theorem deck_relabel (q : FourTensor) (h : D.LiteralDeck q)
    (e : Equiv.Perm (Fin 4)) : D.LiteralDeck (L.relabel e q) := by
  intro d K hK
  change L.rawCard (L.relabel e q) d K=0 ∨
    RainbowOrbit.External.Direction (L.rawCard (L.relabel e q) d K)
  have he : L.rawCard (L.relabel e q) d K=L.rawCard q (d.trans e) K := by
    unfold GlobalCloseCompletionTetrahedralLiteralDeck.rawCard
    rw [L.relabel_relabel]
  rw [he]
  exact h (d.trans e) K hK

private theorem deck_oneSided (q : FourTensor) (h : D.LiteralDeck q) :
    OneSided TetrahedralPreservers.External (cardMatrix q) := by
  intro v hv
  have hK : RainbowOrbit.External.Direction (assemble v) := (mem_coefficientSet_iff _ v).mp hv
  have he : coordinates (assemble v)=v := coefficient_assemble v
  have ha : cardMatrix q *ᵥ v=coordinates (L.rawCard q (Equiv.refl _) (assemble v)) := by
    simpa only [he] using L.cardMatrix_action q (assemble v)
  rw [ha]
  have hs : L.rawCard q (Equiv.refl _) (assemble v)=0 ∨
      RainbowOrbit.External.Direction (L.rawCard q (Equiv.refl _) (assemble v)) :=
    h (Equiv.refl _) (assemble v) hK
  rcases hs with hz | hs
  · exact Or.inl (by rw [hz,map_zero])
  · exact Or.inr ⟨_,hs,rfl⟩

private theorem deck_twoSided (q : FourTensor) (h : D.LiteralDeck q) :
    TwoSided TetrahedralPreservers.External (cardMatrix q) := by
  refine ⟨deck_oneSided q h,?_⟩
  rw [←L.cardMatrix_complement]
  exact deck_oneSided _ (deck_relabel q h L.blockSwap)

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (same : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

include core same stable in
theorem literal_external_tetrahedral_impossible
    (literal : group (ClosureSourceRows.embedding G) P.family torsion=
      GlobalCloseCompletionExternalTetrahedralDictionary.group) : False := by
  have prime : Prime (⟨4,q⟩ : AnySignature (OI.K G)) := same ▸ core.prime
  let phi := complexEmbedding (ClosureSourceRows.embedding G)
  have hp : Prime (⟨4,RingHomRealization.mapSignature phi q⟩ : AnySignature ℂ) :=
    (prime_mapSignature_iff phi (⟨4,q⟩ : AnySignature (OI.K G))).mpr prime
  have deck : D.LiteralDeck (RingHomRealization.mapSignature phi q) :=
    D.current_literal_deck G P torsion literal q core same stable
  obtain ⟨r,U,V,c,_,_,_,he⟩ := original_tensor_factorization
    (RingHomRealization.mapSignature phi q) (deck_twoSided _ deck) hp.1
  apply hp.2
  refine ⟨⟨2,c • Holant.Projective.BoundedTorsion.binarySignature U⟩,
    ⟨2,Holant.Projective.BoundedTorsion.binarySignature V⟩,⟨{
      left_pos := by change 0<2; decide
      right_pos := by change 0<2; decide
      ports := finSumFinEquiv.trans (GlobalCloseCompletionTetrahedralClassifier.matchingFrame r)
      scale := 1
      equation := ?_ }⟩⟩
  change RingHomRealization.mapSignature phi q =
    (1 : ℂ) • Tensor.reindex (finSumFinEquiv.trans (GlobalCloseCompletionTetrahedralClassifier.matchingFrame r))
      (Tensor.tensor (c • Holant.Projective.BoundedTorsion.binarySignature U)
        (Holant.Projective.BoundedTorsion.binarySignature V))
  rw [he,GlobalCloseCompletionTetrahedralCurrent.matching_tensor]
  ext x
  simp [RingHomRealization.mapSignature,Tensor.reindex,Tensor.tensor,smul_eq_mul,mul_assoc]

include core same stable in
theorem octahedral_actual_tetrahedral_impossible
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G) P.family torsion)
      (.platonic .octahedral))
    (actual : HasModel (group (ClosureSourceRows.embedding G) P.family torsion)
      (.platonic .tetrahedral)) : False := by
  have outside := GlobalCloseCompletionTetrahedralCurrent.actual_tetrahedral_external
    G P torsion q core same stable actual
  exact literal_external_tetrahedral_impossible G P torsion q core same stable
    (GlobalCloseCompletionExternalTetrahedralDictionary.current_group
      (ClosureSourceRows.embedding G) P.family torsion P.equality semantic actual outside)

include core same stable in
theorem platonic_actual_eq_semantic (p : PlatonicModel)
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G) P.family torsion)
      (.platonic p)) :
    group (ClosureSourceRows.embedding G) P.family torsion=
      overgroup (ClosureSourceRows.embedding G) P.family torsion := by
  have hc : Nat.card (overgroup (ClosureSourceRows.embedding G) P.family torsion) ≤
      2*Nat.card (group (ClosureSourceRows.embedding G) P.family torsion) := by
    rw [source_cardinal]
    exact cardinal_original _ _ _
  obtain ⟨t,ht,g,hk,hh⟩ := ClosureMarkedPlatonicSubgroup.actual_model
    (group (ClosureSourceRows.embedding G) P.family torsion)
    (overgroup (ClosureSourceRows.embedding G) P.family torsion)
    (ClosureMarkedReversalOvergroup.actual_le _ _) hc p semantic
  rcases ht with rfl | ⟨rfl,rfl⟩
  · exact Subgroup.map_injective (MulAut.conj g).injective (hh.trans hk.symm)
  · exact (octahedral_actual_tetrahedral_impossible G P torsion q core same stable
      semantic ⟨g,hh⟩).elim

variable (base : Palette G)
variable {S T : GeneratedGroupWorklist.Active G base}
variable {trace : GeneratedGroupWorklist.Trace G base S T}
variable {o : CurrentOccurrences.Id G T.source.palette}
variable (receipt : GeneratedGroupWorklist.PreparationReceipt G base trace o)
variable (four : (CurrentOccurrences.savedLeaf G T.source.palette o).1.1=4)

include receipt four in
theorem prepared_platonic_actual_eq_semantic (p : PlatonicModel)
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G)
      T.source.palette.family T.ready.torsion) (.platonic p)) :
    group (ClosureSourceRows.embedding G) T.source.palette.family T.ready.torsion=
      overgroup (ClosureSourceRows.embedding G) T.source.palette.family T.ready.torsion :=
  platonic_actual_eq_semantic G T.source.palette T.ready.torsion
    (Q.table G base four) (Q.minimum G base four) (Q.minimum_literal G base four)
    (Q.matching G base receipt four) p semantic

/-- At each prepared current q4 the actual Platonic group is the full
semantic marked group, and only O or I remain possible. -/
def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    T.source.palette.family T.ready.torsion) : Prop := match M with
  | .platonic p _ => p≠.tetrahedral ∧
      group (ClosureSourceRows.embedding G) T.source.palette.family T.ready.torsion=
        overgroup (ClosureSourceRows.embedding G) T.source.palette.family T.ready.torsion
  | _ => True

include receipt four in
theorem forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    T.source.palette.family T.ready.torsion) : ForMarking G base (T:=T) M := by
  cases M with
  | platonic p model =>
      constructor
      · intro hp
        subst p
        exact GlobalCloseCompletionTetrahedralCurrent.prepared_semantic_tetrahedral_impossible
          G base receipt four model
      · exact prepared_platonic_actual_eq_semantic G base receipt four p model
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

theorem original_current_platonic_refinement : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionExternalTetrahedralCurrent
end
