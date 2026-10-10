import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankOneLocalHardness
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionClosure

/-! Under failure of original-oracle hardness, every actual rank-one
LocalAffine graph is Affine. Installing the graph preserves all original
labels, the actual Z row and the same whole-family obstruction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralGraphRankOneLocal
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeAffineSystematicSupport
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
end M
namespace C
export NoXReciprocalSelectionClosure (output extension obstruction)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false

def selfWitness {K : IntermediateField ℚ AlgebraicComplex} {n r : ℕ} (f : Signature K n)
    (D : SystematicSupport (fun x=>(f x : AlgebraicComplex)) r)
    (bad : ¬Affine (fun x=>(f x : AlgebraicComplex))) :
    OrdinaryNegativeSparseMinimalRank.PinWitness f r where
  arity:=n
  pins:=Sum.inr
  pure:=by
    intro i
    refine ⟨i,rfl,?_⟩
    intro j he
    exact Sum.inr.inj he
  chart:=D
  bad:=bad

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (zLabel : Fin src.size)
variable (literal : (⟨src.b zLabel.val,src.H zLabel⟩ : AnySignature src.K)=⟨2,NoXGeneralZSign.signature⟩)
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (GenericOrdinarySource.family G src)))

include literal negative in
theorem label_affine (noHard : ¬NoXWeightedAntiResourcesOriginal.Hard G) (j : Fin src.size)
    (D : SystematicSupport (fun x=>(src.H j x : AlgebraicComplex)) 1)
    (square : Affine (fun x=>(src.H j x : AlgebraicComplex)^2))
    (localGood : LocalAffine (fun x=>(src.H j x : AlgebraicComplex))) :
    Affine (fun x=>(src.H j x : AlgebraicComplex)) := by
  by_contra bad
  exact noHard (NoXGeneralRankOneLocalHardness.countingHard G src zLabel literal negative j
    (selfWitness (src.H j) D bad) square localGood)

include literal negative in
theorem affine {n : ℕ} (noHard : ¬NoXWeightedAntiResourcesOriginal.Hard G) (N : M.Macro src.H n)
    (D : SystematicSupport (fun x=>(N.network.denote x : AlgebraicComplex)) 1)
    (localGood : LocalAffine (fun x=>(N.network.denote x : AlgebraicComplex))) :
    Affine (fun x=>(N.network.denote x : AlgebraicComplex)) := by
  let dst:=C.extension G src N
  let zl:=NoXOrdinaryGraphAdjoin.old src.H zLabel
  let j:=NoXOrdinaryGraphAdjoin.newLabel src.H
  have hz : (⟨dst.b zl.val,dst.H zl⟩ : AnySignature src.K)=⟨2,NoXGeneralZSign.signature⟩:=
    (NoXOrdinaryGraphSource.old_literal G src (C.output G src N) zLabel).trans literal
  let property (f : AnySignature src.K) : Prop:=
    ∀D : SystematicSupport (fun x=>(f.2 x : AlgebraicComplex)) 1,
      Affine (fun x=>(f.2 x : AlgebraicComplex)^2)→
      LocalAffine (fun x=>(f.2 x : AlgebraicComplex))→Affine (fun x=>(f.2 x : AlgebraicComplex))
  have consume : property ⟨dst.b j.val,dst.H j⟩:=by
    intro chart square good
    exact label_affine G dst zl hz (C.obstruction G src N negative) noHard j chart square good
  have lit : (⟨dst.b j.val,dst.H j⟩ : AnySignature src.K)=⟨n,N.network.denote⟩:=
    NoXOrdinaryGraphSource.new_literal G src (C.output G src N)
  rw [lit] at consume
  exact consume D (NoXReciprocalSelectionClosure.square G src N negative zLabel literal noHard) localGood


include literal negative in
theorem uniform_affine {n : ℕ} (noHard : ¬NoXWeightedAntiResourcesOriginal.Hard G) (N : M.Macro src.H n)
    (D : SystematicSupport (fun x=>(N.network.denote x : AlgebraicComplex)) 1)
    (localGood : LocalAffine (fun x=>(N.network.denote x : AlgebraicComplex))) :
    Affine (OrdinaryNegativeAffineRankOne.uniform (fun x=>(N.network.denote x : AlgebraicComplex))) := by
  have square:=NoXReciprocalSelectionClosure.square G src N negative zLabel literal noHard
  have even:=(NoXLocalRankOneWeighted.local_iff_even_sign D square).mp localGood |>.1
  exact (OrdinaryNegativeAffineRankOne.SystematicSupport.even_uniform_iff D square even).mpr
    (affine G src zLabel literal negative noHard N D localGood)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralGraphRankOneLocal
end
