import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRelabel
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalFilterSplit

/-! The infinite-ratio binary case, once its pinned even unary has been
exposed as an actual ordinary diagonal graph. All interpolation, block
transport and original-oracle composition are internal. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalComplete
open Holant Holant.Tractable Holant.Certificates.MatchingContractionClosure
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
export OrdinaryNegativeXUniversalResource (EvenBad)
end B
namespace A
export NoXReciprocalFilterAlgebra (target)
end A
namespace R
export NoXReciprocalRelabel (block value)
end R
namespace S
export NoXReciprocalSource (data old_literal new_literal old_included)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (row : B.Block (s:=src.size) (b:=src.b) 2)
variable (ha : row.signature src.H ![false,false]≠0) (hb : row.signature src.H ![false,true]≠0)
variable (det : row.signature src.H ![false,false]*row.signature src.H ![true,true]≠
  row.signature src.H ![false,true]*row.signature src.H ![true,false])
variable (graph : NoXOrdinaryGraphAdjoin.Output src.H 2)
variable (denote : graph.network.denote=binarySignature (OrdinaryTargetInterpolationDiagonal.diagonal
  (row.signature src.H ![false,false]) (row.signature src.H ![false,true])))
variable (infinite : ∀k : ℕ,0<k→(row.signature src.H ![false,true]/row.signature src.H ![false,false])^k≠1)
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (GenericOrdinarySource.family G src)))
include ha hb det graph denote infinite negative in
theorem countingHard (bad : B.EvenBad src.H) : NoXWeightedAntiResourcesOriginal.Hard G := by
  let f:=row.signature src.H
  let target:=A.target f
  let ext := S.data G src graph (f ![false,false]) (f ![false,true]) target denote ha hb infinite
  let labels : Fin src.size→Fin ext.size := Fin.castAdd 1
  have literal : ∀i,(⟨ext.b (labels i).val,ext.H (labels i)⟩ : AnySignature src.K)=⟨src.b i.val,src.H i⟩ :=
    S.old_literal G src graph (f ![false,false]) (f ![false,true]) target
  let lifted := R.block src.H ext.H labels literal row
  have value : lifted.signature ext.H=f := R.value src.H ext.H labels literal row
  have extBad : B.EvenBad ext.H := by
    obtain ⟨n,q,hq⟩ := bad
    refine ⟨n,R.block src.H ext.H labels literal q,?_⟩
    have eqn:=R.value src.H ext.H labels literal q
    simpa only [eqn] using hq
  have obstruction : StableHigherCurrentOrdinaryTerminal.Obstruction
      (preprocess (GenericOrdinarySource.family G ext)) := by
    apply (GenericOrdinarySource.rejected_iff G ext).mp
    intro tract
    exact ((GenericOrdinarySource.rejected_iff G src).mpr negative)
      (tract.mono_family (S.old_included G src graph (f ![false,false]) (f ![false,true])
        target denote ha hb infinite))
  let newLabel : Fin ext.size := ⟨src.size,Nat.lt_succ_self _⟩
  have newLiteral : (⟨ext.b newLabel.val,ext.H newLabel⟩ : AnySignature src.K)=
      ⟨2,NoXReciprocalUnary.signature (A.target (lifted.signature ext.H))⟩ := by
    rw [value]
    exact S.new_literal G src graph (f ![false,false]) (f ![false,true]) target denote ha hb infinite
  apply NoXReciprocalFilterSplit.hard_of_even G ext lifted
    (by simpa only [value] using ha) (by simpa only [value] using hb) newLabel newLiteral
    (by simpa only [value] using det) obstruction extBad

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalComplete
end
