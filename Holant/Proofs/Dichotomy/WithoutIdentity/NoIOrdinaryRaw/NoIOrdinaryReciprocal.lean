import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRelabel
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXReciprocalFilterSplit
import Holant.Proofs.Hardness.EOBinaryPlaneClassification
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralEvenAntiResources
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXReciprocalSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Any actual infinite-ratio diagonal can install the cancellation weight
of a retained full bad even binary. This uses only the direct three-support
and even-antidiagonal counted-verifier sources, not a whole-family backend. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryReciprocal
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
end B
namespace R
export NoXReciprocalRelabel (block value)
end R
namespace S
export NoIOrdinaryRaw.NoXReciprocalSource (data old_literal new_literal)
end S
namespace T
export NoXReciprocalFilterAlgebra (target)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (row : B.Block (s:=src.size) (b:=src.b) 2)
variable (full : ∀x,row.signature src.H x≠0)
variable (badA : ¬Affine (fun x=>(row.signature src.H x : AlgebraicComplex)))
variable (badP : ¬Product (fun x=>(row.signature src.H x : AlgebraicComplex)))
variable (graph : NoXOrdinaryGraphAdjoin.Output src.H 2) (c d : src.K)
variable (form : graph.network.denote=Holant.Certificates.MatchingContractionClosure.binarySignature
  (OrdinaryTargetInterpolationDiagonal.diagonal c d))
variable (hc : c≠0) (hd : d≠0) (infinite : ∀k : ℕ,0<k→(d/c)^k≠1)

include full badA badP form hc hd infinite in
theorem countingHard : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  let target:=T.target (row.signature src.H)
  let ext:=S.data G src graph c d target form hc hd infinite
  let labels : Fin src.size→Fin ext.size:=Fin.castAdd 1
  have literal (i : Fin src.size) : (⟨ext.b (labels i).val,ext.H (labels i)⟩ : AnySignature src.K)=⟨src.b i.val,src.H i⟩:=
    S.old_literal G src graph c d target i
  let lifted:=R.block src.H ext.H labels literal row
  have value : lifted.signature ext.H=row.signature src.H:=R.value src.H ext.H labels literal row
  have determinant : row.signature src.H ![false,false]*row.signature src.H ![true,true]≠
      row.signature src.H ![false,true]*row.signature src.H ![true,false] := by
    intro eqn
    apply badP
    apply (Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification.full_product_iff
      (fun x=>(row.signature src.H x : AlgebraicComplex)) (fun x zero=>full x (Subtype.ext zero))).mpr
    exact congrArg (fun z : src.K=>(z : AlgebraicComplex)) eqn
  let j : Fin ext.size:=⟨src.size,Nat.lt_succ_self _⟩
  have newLiteral : (⟨ext.b j.val,ext.H j⟩ : AnySignature src.K)=
      ⟨2,NoXReciprocalUnary.signature (T.target (lifted.signature ext.H))⟩ := by
    rw [value]
    exact S.new_literal G src graph c d target form hc hd infinite
  rcases NoIOrdinaryRaw.NoXReciprocalFilterSplit.anti_or_hard G ext lifted
    (by simpa only [value] using full ![false,false])
    (by simpa only [value] using full ![false,true]) j newLiteral
    (by simpa only [value] using determinant) with hard|⟨anti,v,w,hv,hw,shape⟩
  · exact hard
  · exact NoIOrdinaryRaw.NoXGeneralEvenAntiResources.countingHard G ext lifted lifted anti v w hv hw shape
      (by simpa only [value] using badA) (by simpa only [value] using badP)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryReciprocal
end
