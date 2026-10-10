import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXRegularResidual
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXBadLabels
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseRankTwoThree

/-! Internally selected regularization inputs from the actual ordinary-X
obstruction. No bad label, rank, support chart, pinning, or per-row phase-class
choice is assumed. The alternative is genuine original-G counting hardness. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXMinimalWitnesses
open Computability Holant Holant.Tractable Holant.Complexity
open scoped BigOperators
open Holant.Tractable.AffinePhase Holant.Tractable.SymmetricBinaryPullback
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeSparseMinimalRank OrdinaryNegativeSparseUniformMinimal
open OrdinaryNegativeSparseRankDescent OrdinaryNegativeSparseRankTwoThree
namespace E
export GlobalCloseCompletionEq4FullSource (count arity table family)
export GlobalCloseCompletionEq4CSPSource (field)
end E
namespace F
export OrdinaryNegativeFourthCompatibilitySource (ambient Hard)
end F
namespace C
export OrdinaryNegativeFourthCompatibility (CommonFourth)
end C
namespace U
export OrdinaryNegativeAffineRankOne (uniform)
end U
namespace S
export OrdinaryNegativeXSquares (AllSquaresAffine)
end S
namespace R
export OrdinaryNegativeXRegularResidual (Ready hard_or_ready)
end R
namespace B
export OrdinaryNegativeXBadLabels (exists_affine_bad exists_uniform_bad)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (o : GlobalCloseCompletionEq4Graph.Output G P)
local instance : Algebra ℚ (E.field G P o) := (E.field G P o).algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (E.family G P o)))

/-- A nonaffine original-table pin row in the shared identity class. -/
def IdentityWitness : Prop :=
  ∃j : Fin (E.count G P),∃rank : ℕ,(rank=2 ∨ rank=3) ∧
    ∃W : PinWitness (E.table G P o j) rank,
      ∀S : Finset (Fin rank),S.card<rank → ∀z : Word rank,Affine (minor W.chart S z)

/-- The same actual original-table pin row in the shared uniform class. -/
def UniformWitness : Prop :=
  ∃j : Fin (E.count G P),∃rank : ℕ,(rank=2 ∨ rank=3) ∧
    ∃W : UniformPinWitness (E.table G P o j) rank,
      ∀S : Finset (Fin rank),S.card<rank → ∀z : Word rank,Affine (U.uniform (minor W.chart S z))

/-- The common phase is retained for the entire family alongside the selected
actual minimal rank-two/three witness and all original Affine squares. -/
def MinimalReady : Prop := S.AllSquaresAffine G P o ∧
  (((∀j,C.CommonFourth (F.ambient G P o j)) ∧ IdentityWitness G P o) ∨
   ((∀j,C.CommonFourth (U.uniform (F.ambient G P o j))) ∧ UniformWitness G P o))

include negative in
theorem identity_witness (squares : S.AllSquaresAffine G P o)
    (common : ∀j,C.CommonFourth (F.ambient G P o j)) : IdentityWitness G P o := by
  obtain ⟨j,bad⟩ := B.exists_affine_bad G P o negative
  have hn : E.table G P o j≠0 := by
    intro hz
    apply bad
    left
    funext x
    change (E.table G P o j x : AlgebraicComplex)=0
    rw [hz]
    rfl
  obtain ⟨rank,hr,W,minimal⟩ := exists_minimal_two_three (E.table G P o j)
    (squares j) hn bad (common j)
  exact ⟨j,rank,hr,W,minimal⟩

include negative in
theorem uniform_witness (squares : S.AllSquaresAffine G P o)
    (common : ∀j,C.CommonFourth (U.uniform (F.ambient G P o j))) : UniformWitness G P o := by
  obtain ⟨j,bad⟩ := B.exists_uniform_bad G P o negative
  have hn : E.table G P o j≠0 := by
    intro hz
    apply bad
    left
    funext x
    rw [U.uniform,localTwist_apply]
    change (∏i,if true && x i then zetaEight else 1)*(E.table G P o j x : AlgebraicComplex)=0
    rw [hz]
    simp
  obtain ⟨rank,hr,W,minimal⟩ := exists_uniform_minimal_two_three (E.table G P o j)
    (squares j) hn bad (common j)
  exact ⟨j,rank,hr,W,minimal⟩

include negative in
theorem minimal_ready (ready : R.Ready G P o) : MinimalReady G P o := by
  refine ⟨ready.1,?_⟩
  rcases ready.2 with identity|uniform
  · exact Or.inl ⟨identity,identity_witness G P o negative ready.1 identity⟩
  · exact Or.inr ⟨uniform,uniform_witness G P o negative ready.1 uniform⟩

include negative in
/-- The endpoint starts from the exact obstruction of the actual retained
ordinary table. All rank, label, class, support and pin selections are internal. -/
theorem hard_or_minimal_ready : F.Hard G ∨ MinimalReady G P o := by
  rcases R.hard_or_ready G P o negative with hard|ready
  · exact Or.inl hard
  · exact Or.inr (minimal_ready G P o negative ready)

/-- Both complementary class obstructions are kept simultaneously. Their
labels may differ; each is an actual original table label with its own genuine
pure-pin minimal witness. The single shared fourth-power phase records which
of these witnesses is necessarily rank two or three. -/
def ComplementaryReady : Prop := S.AllSquaresAffine G P o ∧
  ∃j k : Fin (E.count G P),∃r t : ℕ,1≤r ∧ r≤3 ∧ 1≤t ∧ t≤3 ∧
    ∃WA : PinWitness (E.table G P o j) r,
    ∃WU : UniformPinWitness (E.table G P o k) t,
      (∀S : Finset (Fin r),S.card<r → ∀z : Word r,Affine (minor WA.chart S z)) ∧
      (∀S : Finset (Fin t),S.card<t → ∀z : Word t,Affine (U.uniform (minor WU.chart S z))) ∧
      (((∀i,C.CommonFourth (F.ambient G P o i)) ∧ (r=2 ∨ r=3)) ∨
       ((∀i,C.CommonFourth (U.uniform (F.ambient G P o i))) ∧ (t=2 ∨ t=3)))

include negative in
theorem complementary_ready (ready : R.Ready G P o) : ComplementaryReady G P o := by
  obtain ⟨j,badA⟩ := B.exists_affine_bad G P o negative
  obtain ⟨k,badU⟩ := B.exists_uniform_bad G P o negative
  have hnA : E.table G P o j≠0 := by
    intro hz
    apply badA
    left
    funext x
    change (E.table G P o j x : AlgebraicComplex)=0
    rw [hz]
    rfl
  have hnU : E.table G P o k≠0 := by
    intro hz
    apply badU
    left
    funext x
    rw [U.uniform,localTwist_apply]
    change (∏i,if true && x i then zetaEight else 1)*(E.table G P o k x : AlgebraicComplex)=0
    rw [hz]
    simp
  obtain ⟨r,loA,hiA,WA,minA⟩ := exists_minimal (E.table G P o j) (ready.1 j) hnA badA
  obtain ⟨t,loU,hiU,WU,minU⟩ := exists_minimal_uniform (E.table G P o k) (ready.1 k) hnU badU
  refine ⟨ready.1,j,k,r,t,loA,hiA,loU,hiU,WA,WU,minA,minU,?_⟩
  rcases ready.2 with identity|uniform
  · have lower := rank_at_least_two WA (ready.1 j) (identity j)
    exact Or.inl ⟨identity,by omega⟩
  · have lower := uniform_rank_at_least_two WU (ready.1 k) (uniform k)
    exact Or.inr ⟨uniform,by omega⟩

include negative in
/-- The complete internally chosen complementary input for the positive
rank-one/three/seven-resource mixing theorem. -/
theorem hard_or_complementary_ready : F.Hard G ∨ ComplementaryReady G P o := by
  rcases R.hard_or_ready G P o negative with hard|ready
  · exact Or.inl hard
  · exact Or.inr (complementary_ready G P o negative ready)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXMinimalWitnesses
end
