import Holant.Proofs.Dichotomy.Closure.Mixed.GlobalCloseCompletionMixedEOSource
import Holant.Proofs.Dichotomy.Closure.Sparse.GlobalCloseCompletionSparseCurrent
import Holant.Proofs.Dichotomy.Closure.Sparse.GlobalCloseCompletionSparseModel
import Holant.Proofs.Dichotomy.Closure.Binary.GlobalCloseCompletionBinaryEO
import Holant.Proofs.Dichotomy.Retained.StablePaletteTractability

/-! One common basis for every current binary and sparse q4 occurrence, with
one joint physical EO source. If these are all current leaves, the genuine
saved factor trees reconstruct the WHOLE current family and install its
original-G evaluator. Only an actual higher leaf or dense q4 remains outside
this completed branch; no ancestor theorem or chosen per-row basis is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionMixedCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open GlobalCloseCompletionMixedEOModel
open FrontierCommonPresentation
namespace S
export GlobalCloseCompletionSparseCurrent (Sparse Index count occurrence four table core literal matching output)
end S
namespace M
export GlobalCloseCompletionMixedEOSource (OriginalHard originalFamily common_basis_or_hard)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable {A : GeneratedGroupWorklist.Active G base}
variable (R : GeneratedGroupWorklist.Exhausted G base A)
abbrev palette := R.final.source.palette
variable (noPrior : A.source.done=∅)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion))

local instance : Fintype (S.Index G base R) := Fintype.ofFinite _

def sparse_model (o : CurrentOccurrences.Id G (palette G base R)) (hs : S.Sparse G base R o) :
    Model G (palette G base R) (embed G (CurrentOccurrences.savedLeaf G (palette G base R) o).1) := by
  let j : Fin (S.count G base R) := Fintype.equivFin (S.Index G base R) ⟨o,hs⟩
  have hj : (S.occurrence G base R j).val=o :=
    congrArg Subtype.val ((Fintype.equivFin (S.Index G base R)).symm_apply_apply ⟨o,hs⟩)
  have sig : (⟨4,S.table G base R j⟩ : AnySignature (OI.K G))=
      (CurrentOccurrences.savedLeaf G (palette G base R) o).1 := by
    exact (FrontierQ4.tableFour_exact _ (S.four G base R j)).trans
      (congrArg (fun k => (CurrentOccurrences.savedLeaf G (palette G base R) k).1) hj)
  have esig := congrArg (embed G) sig
  exact esig ▸ GlobalCloseCompletionSparseModel.model G (palette G base R) R.final.ready.torsion N
    (S.table G base R) (S.core G base R) (S.literal G base R)
    (S.matching G base R noPrior) (S.output G base R noPrior N) j

def Covered (o : CurrentOccurrences.Id G (palette G base R)) : Prop :=
  (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1=2 ∨ S.Sparse G base R o
abbrev Index := {o : CurrentOccurrences.Id G (palette G base R) // Covered G base R o}
local instance : Fintype (Index G base R) := Fintype.ofFinite _
abbrev count := Fintype.card (Index G base R)
def occurrence (i : Fin (count G base R)) : Index G base R := (Fintype.equivFin _).symm i
def row (i : Fin (count G base R)) : AnySignature AlgebraicComplex :=
  embed G (CurrentOccurrences.savedLeaf G (palette G base R) (occurrence G base R i).val).1
abbrev family := M.originalFamily (row G base R)

def models (i : Fin (count G base R)) : Model G (palette G base R) (row G base R i) := by
  classical
  by_cases two : (CurrentOccurrences.savedLeaf G (palette G base R) (occurrence G base R i).val).1.1=2
  · exact GlobalCloseCompletionBinaryEO.saved_model G (palette G base R) R.final.ready.torsion N
      (occurrence G base R i).val two
  · exact sparse_model G base R noPrior N (occurrence G base R i).val
      ((occurrence G base R i).property.resolve_left two)

theorem complete (o : CurrentOccurrences.Id G (palette G base R)) (ho : Covered G base R o) :
    embed G (CurrentOccurrences.savedLeaf G (palette G base R) o).1∈family G base R := by
  let j := Fintype.equivFin (Index G base R) ⟨o,ho⟩
  have hj : (occurrence G base R j).val=o :=
    congrArg Subtype.val ((Fintype.equivFin (Index G base R)).symm_apply_apply ⟨o,ho⟩)
  exact ⟨j,congrArg (fun k => embed G (CurrentOccurrences.savedLeaf G (palette G base R) k).1) hj⟩

include noPrior N in
theorem common_basis_or_hard :
    (IsCommonKBasis affineClass (family G base R) InvertibleKernel.identity ∨
      IsCommonKBasis productClass (family G base R) InvertibleKernel.identity) ∨ M.OriginalHard G :=
  M.common_basis_or_hard G (palette G base R) (row G base R) (models G base R noPrior N)

theorem whole_family_of_covered (target : TargetClass)
    (basis : IsCommonKBasis target.family (family G base R) InvertibleKernel.identity)
    (covered : ∀o : CurrentOccurrences.Id G (palette G base R),Covered G base R o) :
    TractX (familyAction sourceKBasis (CurrentFrontierClosure.currentFamily G (palette G base R))) := by
  have all : ∀o : CurrentOccurrences.Id G (palette G base R),
      leafPredicate G target.family InvertibleKernel.identity
        (CurrentOccurrences.savedLeaf G (palette G base R) o).1 := by
    intro o
    exact basis.2 _ (complete G base R o (covered o))
  exact FrontierNativeClosure.relative_current_native_tractx G (palette G base R) target
    InvertibleKernel.identity basis.1
    ⟨fun o _ _ => all o,fun o _ _ => all o,fun o _ _ _ => all o,fun o _ _ _ => all o⟩

def Higher : Prop := ∃o : CurrentOccurrences.Id G (palette G base R),
  4<(CurrentOccurrences.savedLeaf G (palette G base R) o).1.1

def Dense : Prop := ∃o : CurrentOccurrences.Id G (palette G base R),
  ∃four : (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1=4,
    ∃p : Bool,StableCurrentEvenEOTransport.FullParity G (GeneratedGroupQ4Consumers.table G base four) p

theorem uncovered (o : CurrentOccurrences.Id G (palette G base R)) (hn : ¬Covered G base R o) :
    Higher G base R ∨ Dense G base R := by
  classical
  by_cases high : 4<(CurrentOccurrences.savedLeaf G (palette G base R) o).1.1
  · exact Or.inl ⟨o,high⟩
  have positive := CurrentOccurrences.savedLeaf_positive G (palette G base R) o
  have noUnary := CurrentFrontierClosure.no_current_unary G (palette G base R) R.final.ready.noUnary o
  have noTwo : (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1≠2 := fun h => hn (.inl h)
  have three : 3≤(CurrentOccurrences.savedLeaf G (palette G base R) o).1.1 := by omega
  have even := R.final.ready.noOdd _ (CurrentOccurrences.savedLeaf_retained G (palette G base R) o)
    (CurrentOccurrences.savedLeaf_prime G (palette G base R) o) three
  have four : (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1=4 := by
    obtain ⟨k,hk⟩ := even
    omega
  refine Or.inr ⟨o,four,?_⟩
  by_contra missing
  exact hn (.inr ⟨four,missing⟩)

def Outcome : Prop := M.OriginalHard G ∨
  TractX (familyAction sourceKBasis (CurrentFrontierClosure.currentFamily G (palette G base R))) ∨
  Higher G base R ∨ Dense G base R

include noPrior N in
/-- All binary/sparse-q4 leaves are now CLOSED jointly. The remaining
constructors name an actual higher ancestor or a genuine dense q4 occurrence. -/
theorem outcome : Outcome G base R := by
  classical
  rcases common_basis_or_hard G base R noPrior N with basis|hard
  · by_cases covered : ∀o : CurrentOccurrences.Id G (palette G base R),Covered G base R o
    · right; left
      rcases basis with affine|product
      · exact whole_family_of_covered G base R .affine affine covered
      · exact whole_family_of_covered G base R .product product covered
    · obtain ⟨o,ho⟩ := not_forall.mp covered
      exact Or.inr (Or.inr (uncovered G base R o ho))
  · exact Or.inl hard


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionMixedCurrent
end
