import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2TensorMatching
import Holant.ReedMuller.LowArity.FlatSignature
import Holant.ReedMuller.FlatNetwork.Parity

/-! A lower flat card of arity at most six is a literal I/X matching in the
original coefficient field. Its complex scalar is recovered from a supported
old-field coefficient; actual retained I supplies the exact current factors. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2FlatMatching
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

theorem shifted_original (a b : ZMod 2) (u v : Bool) : shiftedBinary a b ![u,v]=
    originalC2Binary (L:=ℂ) (decide (a≠b)) u v := by
  fin_cases a <;> fin_cases b <;> cases u <;> cases v <;> rfl

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
variable (F : SignatureFamily K) (torsion : ResidualTorsion F) (hI : RetainsIdentity F)
variable (phi : K→+*ℂ)

include torsion hI in
theorem matching (f : Signature K n) (small : n≤6)
    (flat : FlatOrZero (RingHomRealization.mapSignature phi f)) : MatchingOrZero (actualTransfers F) f := by
  rcases flat with zero|⟨c,a,D,selfdual,equation⟩
  · left
    funext x
    apply phi.injective
    have h := congrFun zero x
    simpa only [RingHomRealization.mapSignature,Pi.zero_apply,map_zero] using h
  obtain ⟨r,hn⟩ := selfDual_arity_even D selfdual
  rw [←two_mul] at hn
  subst n
  obtain ⟨M,hM⟩ := low_arity_matching r (by omega) D selfdual
  let ports : (Fin r×Bool)≃Fin (2*r) :=
    (Equiv.prodCongr (Equiv.refl (Fin r)) Holant.Pauli.ExoticKlein.SixPort.bitEquiv).trans M
  let label : Fin r→Bool := fun i=>decide (a (M (i,0))≠a (M (i,1)))
  let d : K := f (wordVector a)
  have zeros : (fun i=>bit (wordVector a i)-a i)=0 := by
    funext i
    change boolEquiv (boolEquiv.symm (a i))-a i=0
    rw [Equiv.apply_symm_apply,sub_self]
  have scalar : phi d=(c:ℂ) := by
    have h := congrFun equation (wordVector a)
    change phi d=flatSignature c a D (wordVector a) at h
    simpa only [flatSignature,zeros,Submodule.zero_mem,ite_true] using h
  have nonzero : d≠0 := by
    intro h
    apply c.ne_zero
    rw [←scalar,h,map_zero]
  have complexForm : RingHomRealization.mapSignature phi f=
      productValue ports (fun i=>originalC2Binary (L:=ℂ) (label i)) (c:ℂ) := by
    rw [equation,←flatDecomposition_value M c a D hM]
    funext x
    change (c:ℂ)*(∏i,shiftedBinary (a (M (i,0))) (a (M (i,1))) (fun j=>x (M (i,j))))=_
    change _=(c:ℂ)*(∏i,originalC2Binary (L:=ℂ) (label i) (x (M (i,0))) (x (M (i,1))))
    apply congrArg ((c:ℂ)*·)
    apply Finset.prod_congr rfl
    intro i _
    exact shifted_original _ _ _ _
  right
  refine ⟨⟨r,ports,fun i=>originalC2Binary (L:=K) (label i),d⟩,?_,nonzero,?_⟩
  · intro i
    change transfer (originalC2Binary (L:=K) (label i))∈actualTransfers F
    have h := GlobalCloseCompletionC2CurrentComplement.kernel_member F torsion hI (!(label i))
    cases hi : label i <;> simpa [hi,transfer,originalC2Binary,X_mul_X] using h
  · funext x
    apply phi.injective
    have h := congrFun complexForm x
    simpa only [RingHomRealization.mapSignature,Presentation.tensor,productValue,map_mul,map_prod,
      GlobalCloseCompletionC2TensorMatching.map_c2_binary,scalar] using h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2FlatMatching
end
