import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZCapGraph
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZInverseFinite

/-! Exact literal-row extraction through an injective coefficient embedding,
and actual ordinary series composition in the ambient GHZ coordinates. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZRows
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Certificates.MatchingContractionClosure OrdinaryNegativeCubicGadgets
namespace O
export Holant.LocalDrafts.BinaryInterpolation.OriginalTables (castSignature castSignature_any)
end O
namespace C
export GlobalCloseCompletionSymmetricGHZCapGraph (symmetric)
end C
namespace S
export GlobalCloseCompletionSymmetricGHZInverseFinite (series series_value)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable {K : Type} [Field K] {r n : ℕ} {a : ℕ→ℕ}
variable (phi : K→+*AlgebraicComplex) (H : (i : Fin r)→Signature K (a i.val))
variable (j : Fin r) (f : Signature AlgebraicComplex n)
variable (literal : RingHomRealization.mapAny phi (⟨a j.val,H j⟩ : AnySignature K)=⟨n,f⟩)

def row : Macro H n:=Macro.row j (O.castSignature (congrArg Sigma.fst literal) (H j))
  (O.castSignature_any (congrArg Sigma.fst literal) (H j)).symm

theorem value : RingHomRealization.mapSignature phi (row phi H j f literal).network.denote=f := by
  rw [row,Macro.row_denote]
  have h:=congrArg (RingHomRealization.mapAny phi) (O.castSignature_any (congrArg Sigma.fst literal) (H j))
  exact eq_of_heq (Sigma.mk.inj_iff.mp (h.trans literal)).2

theorem weighted (N : Macro H 3) (p q : AlgebraicComplex) (hp : p≠0) (hq : q≠0)
    (form : RingHomRealization.mapSignature phi N.network.denote=C.symmetric p 0 0 q) :
    ∃u v : K,u≠0 ∧ v≠0 ∧ N.network.denote=C.symmetric u 0 0 v := by
  let u:=N.network.denote ![false,false,false]
  let v:=N.network.denote ![true,true,true]
  have hu : phi u=p := by simpa [u,RingHomRealization.mapSignature,C.symmetric] using congrFun form ![false,false,false]
  have hv : phi v=q := by simpa [v,RingHomRealization.mapSignature,C.symmetric] using congrFun form ![true,true,true]
  refine ⟨u,v,?_,?_,?_⟩
  · intro zero;apply hp;rw [←hu,zero,map_zero]
  · intro zero;apply hq;rw [←hv,zero,map_zero]
  · funext x
    apply phi.injective
    have h:=congrFun form x
    change phi (N.network.denote x)=_ at h
    rw [h]
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> simp [C.symmetric,h0,h1,h2,hu,hv]

theorem series_mapped (N Q : Macro H 2) (A B : Kernel AlgebraicComplex)
    (hn : RingHomRealization.mapSignature phi N.network.denote=kernelSignature A)
    (hq : RingHomRealization.mapSignature phi Q.network.denote=kernelSignature B) :
    RingHomRealization.mapSignature phi (S.series H N Q).network.denote=kernelSignature (Kernel.mul A B) := by
  rw [S.series_value H N Q (binaryMatrix N.network.denote) (binaryMatrix Q.network.denote)
    (binarySignature_binaryMatrix _).symm (binarySignature_binaryMatrix _).symm]
  funext x
  change phi (∑v : Bool,N.network.denote ![x 0,v]*Q.network.denote ![v,x 1])=
    ∑v : Bool,A (x 0) v*B v (x 1)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [map_mul]
  exact congrArg₂ (fun p q : AlgebraicComplex=>p*q) (congrFun hn ![x 0,v]) (congrFun hq ![v,x 1])


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZRows
end
