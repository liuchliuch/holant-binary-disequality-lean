import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePinSignature
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureTwoColorFace
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Templates
import Holant.Proofs.Hardness.GeneralOddUnaryEscape

/-! Exact literal caps by supplied native pins. Agreement ports can be
removed while retaining the two selected coefficients and their pin face. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePinProjection
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.GeneralExtraction
open NamedContraction SupportDescent
open scoped BigOperators
namespace C
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddUnaryEscape
  (capHead capHead_denote capHead_uses capHead_native)
end C
namespace O
export NativeAntiTargetSource (Output)
end O
namespace D
export NoIPureTwoColorFace (distance Face)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s n : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (arity i.val))


def tail (i : Fin (n+1)) (x : Fin (n+1)→Bool) : Fin n→Bool:=
  fun j=>x (Equiv.swap 0 i j.succ)
def insert (i : Fin (n+1)) (bit : Bool) (z : Fin n→Bool) : Fin (n+1)→Bool:=
  fun j=>(Fin.cons bit z : Fin (n+1)→Bool) (Equiv.swap 0 i j)

theorem insert_tail (i : Fin (n+1)) (x : Fin (n+1)→Bool) : insert i (x i) (tail i x)=x := by
  funext j
  obtain ⟨k,rfl⟩:=(Equiv.swap 0 i).surjective j
  simp only [insert,Equiv.swap_apply_self]
  refine Fin.cases ?_ (fun k=>?_) k
  · simp
  · rfl

theorem tail_insert (i : Fin (n+1)) (bit : Bool) (z : Fin n→Bool) :
    tail i (insert i bit z)=z := by
  funext j
  simp [tail,insert]

theorem distance_tail (i : Fin (n+1)) (x y : Fin (n+1)→Bool) (agree : x i=y i) :
    D.distance (tail i x) (tail i y)=D.distance x y := by
  have h:=(Equiv.sum_comp (Equiv.swap (0 : Fin (n+1)) i)
    (fun j=>if x j=y j then (0 : ℕ) else 1))
  simp only [Fin.sum_univ_succ,Equiv.swap_apply_left,agree,ite_true,zero_add] at h
  simpa only [NoIPureTwoColorFace.distance,
    Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance.distance,
    tail,Fin.sum_univ_succ] using h

theorem weight_tail (i : Fin (n+1)) (x : Fin (n+1)→Bool) :
    weight x=(if x i then 1 else 0)+weight (tail i x) := by
  have h:=Equiv.sum_comp (Equiv.swap (0 : Fin (n+1)) i)
    (fun j=>if x j then (1 : ℕ) else 0)
  simpa only [weight,tail,Fin.sum_univ_succ,Equiv.swap_apply_left] using h.symm

theorem difference_tail (i : Fin (n+1)) (x y : Fin (n+1)→Bool) (agree : x i=y i) :
    (weight (tail i x) : ℤ)-weight (tail i y)=(weight x : ℤ)-weight y := by
  have hx:=weight_tail i x
  have hy:=weight_tail i y
  rw [←agree] at hy
  omega

theorem face_insert (i : Fin (n+1)) (x y : Fin (n+1)→Bool) (agree : x i=y i)
    (z : Fin n→Bool) (face : D.Face (tail i x) (tail i y) z) :
    D.Face x y (insert i (x i) z) := by
  intro j same
  obtain ⟨k,rfl⟩:=(Equiv.swap 0 i).surjective j
  simp only [insert,Equiv.swap_apply_self]
  revert same
  refine Fin.cases ?_ (fun k=>?_) k
  · intro _;simp
  · intro same;exact face k same

variable (pins : Bool→O.Output H 1)
variable (pinsForm : ∀bit,(pins bit).network.denote=pin bit)
variable (N : O.Output H (n+1))

def network (i : Fin (n+1)) (bit : Bool) : Network K n:=
  C.capHead (pins (!bit)).network (reboundary N.network (Equiv.swap 0 i))

theorem uses (i : Fin (n+1)) (bit : Bool) : Uses (network H pins N i bit)
    (Set.range fun j : Fin s=>(⟨arity j.val,H j⟩ : AnySignature K)):=
  C.capHead_uses _ _ _ (fun v=>⟨(pins (!bit)).labels.vertex v,(pins (!bit)).exact v⟩)
    (fun v=>⟨N.labels.vertex v,N.exact v⟩)

def labels (i : Fin (n+1)) (bit : Bool) : Labelling (network H pins N i bit).shape s 1 arity where
  vertex v:=Classical.choose (uses H pins N i bit v)
  vertex_arity v:=congrArg Sigma.fst (Classical.choose_spec (uses H pins N i bit v))
  edge _:=0

def output (i : Fin (n+1)) (bit : Bool) : O.Output H n where
  network:=network H pins N i bit
  labels:=labels H pins N i bit
  exact v:=Classical.choose_spec (uses H pins N i bit v)
  native:=C.capHead_native _ _ (pins (!bit)).native N.native

include pinsForm in
theorem value (i : Fin (n+1)) (bit : Bool) :
    (output H pins N i bit).network.denote=fun z=>N.network.denote (insert i bit z) := by
  funext z
  change (network H pins N i bit).denote z=_
  rw [network,C.capHead_denote,pinsForm]
  simp only [reboundary_denote]
  cases bit <;>simp [pin,insert,Tensor.reindex] <;>rfl

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePinProjection
end
