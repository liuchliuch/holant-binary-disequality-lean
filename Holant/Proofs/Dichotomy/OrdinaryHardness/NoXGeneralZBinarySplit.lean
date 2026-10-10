import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralZBinaryBlock
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralThreeSupport
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenAntiResources

/-! An actual Z, a nonproduct binary even block and equal first-row fourth
powers produce a direct three-support hardness source or a full actual even
anti block. The latter consumes any original-family even Affine obstruction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralZBinarySplit
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
export OrdinaryNegativeXUniversalResource (EvenBad)
end B
namespace A
export NoXGeneralZBinaryAlgebra (filtered values cross_nonzero anti_of_zero)
end A
namespace Z
export NoXGeneralZBinaryBlock (block value)
end Z
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (zLabel : Fin src.size)
variable (zLiteral : (⟨src.b zLabel.val,src.H zLabel⟩ : AnySignature src.K)=⟨2,NoXGeneralZSign.signature⟩)
variable (row : B.Block (s:=src.size) (b:=src.b) 2)
variable (ha : row.signature src.H ![false,false]≠0)
variable (fourth : row.signature src.H ![false,false]^4=row.signature src.H ![false,true]^4)
variable (det : row.signature src.H ![false,false]*row.signature src.H ![true,true]≠
  row.signature src.H ![false,true]*row.signature src.H ![true,false])

include zLiteral ha fourth det in
theorem anti_or_hard : NoXWeightedAntiResourcesOriginal.Hard G ∨
    ∃antiRow : B.Block (s:=src.size) (b:=src.b) 2,∃v w : src.K,v≠0 ∧ w≠0 ∧
      antiRow.signature src.H=NoXWeightedAntiSigned.anti v w := by
  classical
  let f:=row.signature src.H
  let q:=Z.block src.H zLabel zLiteral row
  have qvalue : q.signature src.H=A.filtered f := funext (Z.value src.H zLabel zLiteral row)
  have vals:=A.values f
  have cross : A.filtered f ![false,true]≠0 := by
    rw [vals.2.1]
    exact A.cross_nonzero _ _ _ _ ha fourth det
  have top : A.filtered f ![false,false]=0 := by rw [vals.1,fourth,sub_self]
  have other : A.filtered f ![true,false]≠0 := by rw [vals.2.2.1,←vals.2.1];exact cross
  by_cases zero : A.filtered f ![true,true]=0
  · right
    refine ⟨q,A.filtered f ![false,true],A.filtered f ![false,true],cross,cross,?_⟩
    exact qvalue.trans (A.anti_of_zero f fourth zero)
  · left
    apply NoXGeneralThreeSupport.EvenBlock.countingHard G src q.rows q.balanced (false,false)
    · change q.signature src.H ![false,false]=0
      rw [qvalue]
      exact top
    · intro x y ne
      change q.signature src.H ![x,y]≠0
      rw [qvalue]
      cases x <;> cases y
      · exact False.elim (ne rfl)
      · exact cross
      · exact other
      · exact zero

variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (GenericOrdinarySource.family G src)))
include zLiteral ha fourth det negative in
theorem hard_of_even (bad : B.EvenBad src.H) : NoXWeightedAntiResourcesOriginal.Hard G := by
  rcases anti_or_hard G src zLabel zLiteral row ha fourth det with hard|⟨antiRow,v,w,hv,hw,lit⟩
  · exact hard
  · exact NoXGeneralEvenAntiResources.hard_of_even G src antiRow v w hv hw lit negative bad


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralZBinarySplit
end
