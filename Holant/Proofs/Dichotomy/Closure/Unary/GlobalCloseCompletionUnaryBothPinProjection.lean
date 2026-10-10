import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinMinimal
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBitFlipPins
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryZeroCapTrees

/-! Literal zero/one caps supply the exact smaller graphs used by the
minimal-prime argument. Dummy variables only enter analytic tensor splits.
Supported-word XOR masks are transported semantically and never installed as
vertices or edges. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinProjection
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
open GeneralOddNonisotropicFrame
namespace B
export GlobalCloseCompletionUnaryBitFlipPins (cap project project_flip cap_small_iff)
export GlobalCloseCompletionUnaryBitFlip (value prime_iff)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {K : Type} [Field K] {r n : ℕ} {a : ℕ→ℕ}

private def packed {f : AnySignature K} (D : TensorDecomposition K f.1) (eqn : D.value=f.2) :
    ClosureSmallArity.Packed f where
  Index:=Fin D.count
  finite:=inferInstance
  arity:=D.arity
  factor:=D.factor
  ports:=D.ports
  scale:=D.scale
  equation:=eqn.symm

theorem small_join {f u v : AnySignature K} (s : ProperSplit f u v)
    (left : Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) u.2)
    (right : Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) v.2) :
    Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) f.2 := by
  obtain ⟨D,hd,ed⟩:=left
  obtain ⟨E,he,ee⟩:=right
  let P:=ClosureSmallArity.Packed.join s (packed D ed) (packed E ee)
  refine ⟨P.decomposition,?_,P.decomposition_value⟩
  intro i
  change Sum.elim D.arity E.arity ((Fintype.equivFin (Fin D.count⊕Fin E.count)).symm i)≤2
  cases (Fintype.equivFin (Fin D.count⊕Fin E.count)).symm i with
  | inl j=>exact hd j
  | inr j=>exact he j

variable (H : (j : Fin r)→Signature K (a j.val))
variable (pins : Bool→NoXOrdinaryGraphAdjoin.Output H 1)
variable (pinsForm : ∀v,(pins v).network.denote=QuaternaryUnaryAccess.pin v)
variable (N : NoXOrdinaryGraphAdjoin.Output H (n+1))

def network (i : Fin (n+1)) (bit : Bool) : Network K n :=
  capHead (pins bit).network (reboundary N.network (Equiv.swap 0 i))

def labels (i : Fin (n+1)) (bit : Bool) : Labelling (network H pins N i bit).shape r 1 a :=
  let h:=capHead_uses (Set.range fun j : Fin r=>(⟨a j.val,H j⟩ : AnySignature K))
    (pins bit).network (reboundary N.network (Equiv.swap 0 i))
    (fun v=>⟨(pins bit).labels.vertex v,(pins bit).exact v⟩) (fun v=>⟨N.labels.vertex v,N.exact v⟩)
  {vertex v:=Classical.choose (h v)
   vertex_arity v:=congrArg Sigma.fst (Classical.choose_spec (h v))
   edge _:=0}

def output (i : Fin (n+1)) (bit : Bool) : NoXOrdinaryGraphAdjoin.Output H n where
  network:=network H pins N i bit
  labels:=labels H pins N i bit
  exact v:=Classical.choose_spec (capHead_uses (Set.range fun j : Fin r=>(⟨a j.val,H j⟩ : AnySignature K))
    (pins bit).network (reboundary N.network (Equiv.swap 0 i))
    (fun v=>⟨(pins bit).labels.vertex v,(pins bit).exact v⟩) (fun v=>⟨N.labels.vertex v,N.exact v⟩) v)
  ordinary:=capHead_ordinary _ _ (pins bit).ordinary N.ordinary

include pinsForm in
theorem denote (i : Fin (n+1)) (bit : Bool) : (output H pins N i bit).network.denote=B.project i bit N.network.denote := by
  funext x
  change (network H pins N i bit).denote x=_
  rw [network,capHead_denote,pinsForm]
  simp only [reboundary_denote]
  cases bit <;>simp [QuaternaryUnaryAccess.pin,B.project,Tensor.reindex]

include pinsForm in
def split (positive : 0<n) (i : Fin (n+1)) (bit : Bool) : ProperSplit
    (⟨n+1,B.cap i bit N.network.denote⟩ : AnySignature K)
    ⟨1,fun _=>1⟩ ⟨n,(output H pins N i bit).network.denote⟩ where
  left_pos:=by change 0<1;decide
  right_pos:=positive
  ports:=(GlobalCloseCompletionUnaryZeroCapTrees.headPorts n).trans (Equiv.swap 0 i)
  scale:=1
  equation:=by
    funext x
    dsimp only
    rw [denote H pins pinsForm N i bit]
    change B.cap i bit N.network.denote x=1*(1*B.project i bit N.network.denote
      (fun j=>x (Equiv.swap 0 i j.succ)))
    simp only [one_mul,B.cap,B.project,Tensor.reindex]
    congr 1
    funext j
    obtain ⟨k,rfl⟩:=(Equiv.swap 0 i).surjective j
    refine Fin.cases ?_ (fun k=>?_) k
    · simp
    · have ne : Equiv.swap (0 : Fin (n+1)) i k.succ≠i := by
        rw [show i=Equiv.swap (0 : Fin (n+1)) i 0 by simp]
        exact (Equiv.swap 0 i).injective.ne (Fin.succ_ne_zero k)
      simp [Function.update_of_ne ne]

include pinsForm in
theorem dummy_small (positive : 0<n) (i : Fin (n+1)) (bit : Bool)
    (small : Signature.TensorClosure (fun k (_ : Signature K k)=>k≤2) (output H pins N i bit).network.denote) :
    Signature.TensorClosure (fun k (_ : Signature K k)=>k≤2) (B.cap i bit N.network.denote) := by
  apply small_join (split H pins pinsForm N positive i bit) _ small
  let D:=ClosureSmallArity.Packed.single (⟨1,fun _=>1⟩ : AnySignature K)
  exact ⟨D.decomposition,(fun _=>by change 1≤2;decide),D.decomposition_value⟩

include pinsForm in
theorem signed_denote (mask : Fin (n+1)→Bool) (i : Fin (n+1)) (bit : Bool) :
    B.project i bit (B.value mask N.network.denote)=
      B.value (fun j=>mask (Equiv.swap 0 i j.succ))
        (output H pins N i (bit^^mask i)).network.denote := by
  rw [denote H pins pinsForm N i (bit^^mask i)]
  exact B.project_flip mask N.network.denote i bit

include pinsForm in
theorem signed_prime (mask : Fin (n+1)→Bool) (i : Fin (n+1)) (bit : Bool)
    (prime : Prime (⟨n,B.project i bit (B.value mask N.network.denote)⟩ : AnySignature K)) :
    Prime (⟨n,(output H pins N i (bit^^mask i)).network.denote⟩ : AnySignature K) := by
  rw [signed_denote H pins pinsForm N mask i bit] at prime
  exact (B.prime_iff _ _).mp prime


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinProjection
end
