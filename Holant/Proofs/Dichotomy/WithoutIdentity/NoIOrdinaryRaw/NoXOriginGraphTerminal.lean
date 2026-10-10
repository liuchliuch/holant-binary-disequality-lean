import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXOriginGraphClosure
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOriginFiniteSupply
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiBase
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXOrdinaryGraphSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Install the actual bounded-rank graph once, consume its genuine finite
supplier and return counted-verifier hardness for the original oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXOriginGraphTerminal
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeAffineSystematicSupport
namespace C
export NoIOrdinaryRaw.NoXOriginGraphClosure (output extension obstruction antiLabel' anti_literal)
end C
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))
variable (antiLabel : Fin src.size) (v w : src.K) (hv : v≠0) (hw : w≠0)
variable (literal : (⟨src.b antiLabel.val,src.H antiLabel⟩ : AnySignature src.K)=
  ⟨2,NoXWeightedAntiSigned.anti v w⟩)
variable (fourth : (v : AlgebraicComplex)^4= -((w : AlgebraicComplex)^4))
variable {n r : ℕ} (N : M.Macro src.H n)
variable (D : SystematicSupport (fun x=>(N.network.denote x : AlgebraicComplex)) r)
variable (atOrigin : (N.network.denote (origin n) : AlgebraicComplex)≠0)
variable (square : Affine (fun x=>(N.network.denote x : AlgebraicComplex)^2))
variable (bad : ¬Affine (fun x=>(N.network.denote x : AlgebraicComplex)))
include D negative hv hw literal fourth atOrigin square bad in
theorem countingHard (lower : 1≤r) (upper : r≤3) : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  let dst := C.extension G src N
  let al := C.antiLabel' G src N antiLabel
  let j := NoXOrdinaryGraphAdjoin.newLabel src.H
  have ha : (⟨dst.b al.val,dst.H al⟩ : AnySignature src.K)=
      ⟨2,NoXWeightedAntiSigned.anti v w⟩ := C.anti_literal G src N antiLabel v w literal
  let property (f : AnySignature src.K) : Prop :=
    ∀D : SystematicSupport (fun x=>(f.2 x : AlgebraicComplex)) r,
      f.2 (origin f.1)≠0 → Affine (fun x=>(f.2 x : AlgebraicComplex)^2) →
      ¬Affine (fun x=>(f.2 x : AlgebraicComplex)) → OrdinaryNegativeXUniversalResource.EvenBad dst.H
  have consume : property ⟨dst.b j.val,dst.H j⟩ := by
    intro chart nonzero sq failure
    exact NoXOriginFiniteSupply.bounded dst.H j al (dst.p false) (dst.p true) v w ha
      (dst.hp false) (dst.hp true) hv hw fourth nonzero sq chart lower upper failure
  have lit : (⟨dst.b j.val,dst.H j⟩ : AnySignature src.K)=⟨n,N.network.denote⟩ :=
    NoIOrdinaryRaw.NoXOrdinaryGraphSource.new_literal G src (C.output G src N)
  rw [lit] at consume
  have originK : N.network.denote (origin n)≠0 := fun zero=>atOrigin (by rw [zero];rfl)
  exact NoIOrdinaryRaw.NoXWeightedAntiBase.hard_of_even G dst (C.obstruction G src N negative) al v w hv hw ha
    (consume D originK square bad)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXOriginGraphTerminal
end
