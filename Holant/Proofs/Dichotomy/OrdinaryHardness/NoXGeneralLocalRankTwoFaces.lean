import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralGraphRankOneLocal
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralLocalMinimalGraph
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseUniformMinimal

/-! Genuine least-LocalAffine rank two supplies Affine proper faces in
both ordinary and uniform phase classes. The bridge uses actual pin masks
and rank-one hardness, rather than substituting ordinary minimality. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalRankTwoFaces
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
export OrdinaryNegativeCubicGadgets.Macro (row row_denote)
end M
namespace U
export OrdinaryNegativeAffineRankOne (uniform)
export OrdinaryNegativeSparseUniformMinimal (uniformChart uniform_minor_affine_iff)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false

theorem minor_of_mask {n r : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f r)
    (S : Finset (Fin r)) (z : Word r) (i : Fin r) (outside : i∉S)
    (good : Affine (pinMask f (D.ports i) (z i))) : Affine (minor D S z) := by
  have pulled:=good.precompose (fill (remaining D S) (D.encode z)) (fill_affine _ _)
  have absent : D.ports i∉remaining D S:=mt (selected_remaining D S i).mp outside
  convert pulled using 1
  funext x
  simp only [minor,literal,pinMask,fill_outside _ _ _ _ absent,D.free,ite_true]

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (zLabel : Fin src.size)
variable (literalZ : (⟨src.b zLabel.val,src.H zLabel⟩ : AnySignature src.K)=⟨2,NoXGeneralZSign.signature⟩)
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (GenericOrdinarySource.family G src)))
variable {n : ℕ} (N : M.Macro src.H (n+2))
variable (D : SystematicSupport (fun x=>(N.network.denote x : AlgebraicComplex)) 2)
variable (minimal : ¬NoXGeneralLocalMinimalGraph.Witness (n:=n) (H:=src.H) src.K.subtype 1)

include literalZ negative minimal in
theorem masks (noHard : ¬NoXWeightedAntiResourcesOriginal.Hard G) (i : Fin 2) (bit : Bool) :
    Affine (pinMask (fun x=>(N.network.denote x : AlgebraicComplex)) (D.ports i) bit) ∧
    Affine (U.uniform (pinMask (fun x=>(N.network.denote x : AlgebraicComplex)) (D.ports i) bit)) := by
  let P : M.Macro src.H 1:=M.row (src.p bit) (QuaternaryUnaryAccess.pin bit) (src.hp bit)
  have pin : P.network.denote=(fun x=>if x 0=bit then 1 else 0):=by
    rw [M.row_denote]
    rfl
  let Q:=NoXOriginRestrictionGraphs.pinMask N P (D.ports i)
  have value : (fun x=>(Q.network.denote x : AlgebraicComplex))=
      pinMask (fun x=>(N.network.denote x : AlgebraicComplex)) (D.ports i) bit:=by
    funext x
    rw [NoXOriginRestrictionGraphs.pinMask_value N P (D.ports i) bit pin]
    by_cases hx : x (D.ports i)=bit <;> simp [pinMask,hx]
  obtain ⟨chart⟩:=NoXOriginRestrictionSupport.pin_chart D i bit
  have chartQ : SystematicSupport (fun x=>(Q.network.denote x : AlgebraicComplex)) 1:=by
    rw [value]
    exact chart
  have localQ : LocalAffine (fun x=>(Q.network.denote x : AlgebraicComplex)):=by
    by_contra bad
    exact minimal ⟨Q,bad,⟨chartQ⟩⟩
  constructor
  · rw [←value]
    exact NoXGeneralGraphRankOneLocal.affine G src zLabel literalZ negative noHard Q chartQ localQ
  · rw [←value]
    exact NoXGeneralGraphRankOneLocal.uniform_affine G src zLabel literalZ negative noHard Q chartQ localQ

include literalZ negative minimal in
theorem faces (noHard : ¬NoXWeightedAntiResourcesOriginal.Hard G)
    (S : Finset (Fin 2)) (smaller : S.card<2) (z : Word 2) :
    Affine (minor D S z) ∧ Affine (U.uniform (minor D S z)) := by
  have outside : ∃i : Fin 2,i∉S:=by
    by_contra h
    push Not at h
    have all : S=Finset.univ:=Finset.eq_univ_of_forall h
    simp [all] at smaller
  obtain ⟨i,hi⟩:=outside
  obtain ⟨ordinary,uniform⟩:=masks G src zLabel literalZ negative N D minimal noHard i (z i)
  refine ⟨minor_of_mask D S z i hi ordinary,?_⟩
  apply (U.uniform_minor_affine_iff D S z).mp
  apply minor_of_mask (U.uniformChart D) S z i hi
  change Affine (pinMask (U.uniform (fun x=>(N.network.denote x : AlgebraicComplex))) (D.ports i) (z i))
  simpa only [U.uniform,NoXGeneralLocalRestriction.pin_twist] using uniform

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalRankTwoFaces
end
