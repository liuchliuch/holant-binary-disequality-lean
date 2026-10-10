import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalFilterBlock
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalFilterAlgebra
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralThreeSupport
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralEvenAntiResources
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! The interpolated reciprocal diagonal produces either a full actual even anti block or direct three-support hardness. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXReciprocalFilterSplit
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
export OrdinaryNegativeXUniversalResource (EvenBad)
end B
namespace A
export NoXReciprocalFilterAlgebra (filtered target top cross_nonzero anti symmetric)
end A
namespace Z
export NoXReciprocalFilterBlock (block value)
end Z
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (row : B.Block (s:=src.size) (b:=src.b) 2)
variable (ha : row.signature src.H ![false,false]≠0)
variable (hb : row.signature src.H ![false,true]≠0)
variable (zLabel : Fin src.size)
variable (zLiteral : (⟨src.b zLabel.val,src.H zLabel⟩ : AnySignature src.K)=
  ⟨2,NoXReciprocalUnary.signature (A.target (row.signature src.H))⟩)
variable (det : row.signature src.H ![false,false]*row.signature src.H ![true,true]≠
  row.signature src.H ![false,true]*row.signature src.H ![true,false])

include zLiteral ha hb det in
theorem anti_or_hard : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G ∨
    ∃antiRow : B.Block (s:=src.size) (b:=src.b) 2,∃v w : src.K,v≠0 ∧ w≠0 ∧
      antiRow.signature src.H=NoXWeightedAntiSigned.anti v w := by
  classical
  let f:=row.signature src.H
  let q:=Z.block (A.target f) src.H zLabel zLiteral row
  have qvalue : q.signature src.H=A.filtered f := funext (Z.value (A.target f) src.H zLabel zLiteral row)
  have cross : A.filtered f ![false,true]≠0 := A.cross_nonzero f ha hb det
  have top : A.filtered f ![false,false]=0 := A.top f hb
  have other : A.filtered f ![true,false]≠0 := by rw [A.symmetric];exact cross
  by_cases zero : A.filtered f ![true,true]=0
  · right
    refine ⟨q,A.filtered f ![false,true],A.filtered f ![false,true],cross,cross,?_⟩
    exact qvalue.trans (A.anti f hb zero)
  · left
    apply NoIOrdinaryRaw.NoXGeneralThreeSupport.EvenBlock.countingHard G src q.rows q.balanced (false,false)
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

variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))
include zLiteral ha hb det negative in
theorem hard_of_even (bad : B.EvenBad src.H) : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  rcases anti_or_hard G src row ha hb zLabel zLiteral det with hard|⟨antiRow,v,w,hv,hw,lit⟩
  · exact hard
  · exact NoIOrdinaryRaw.NoXGeneralEvenAntiResources.hard_of_even G src antiRow v w hv hw lit negative bad


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXReciprocalFilterSplit
end
