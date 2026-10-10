import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryProductTopTransport

/-! Two actual copies of the prime row complete the nonzero-coordinate
all-unary branch, including original arity four. One copy is zero-capped to
its selected unary marginal; that marginal caps the corresponding port of
the other copy. The result is a smaller prime or an opposite-pin power. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryProductTopMarginal
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
open GeneralOddNonisotropicFrame
namespace T
export GlobalCloseCompletionUnaryProductTopPrime (value prime)
end T
namespace C
export GlobalCloseCompletionUnaryZeroCaps (graph uses ordinary productTop_entry)
end C
namespace M
export GlobalCloseCompletionUnaryProductTopTransport (reboundary attach)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}
variable (U : Network K 1) (N : Network K (n+1))
variable (w : Fin (n+1)→K) (c d scalar : K) (i : Fin (n+1))

def lastPerm : Equiv.Perm (Fin (n+1)) := Equiv.swap (Fin.last n) i
def firstPerm : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 i
def atLast : Network K (n+1) := reboundary N (lastPerm i)
def atFirst : Network K (n+1) := reboundary N (firstPerm i)
def marginal : Network K 1 := C.graph U n (atLast N i)
def graph : Network K n := capHead (marginal U N i) (atFirst N i)
def multiplier : K := scalar^n*c
def left : K := multiplier (n:=n) c scalar*c*(1+w i*w i)
def right : K := multiplier (n:=n) c scalar*d*w i

variable (positive : 0<n) (pin0 : U.denote (fun _=>false)=scalar)
variable (pin1 : U.denote (fun _=>true)=0) (form : N.denote=T.value w c d)

include positive pin0 pin1 form in
theorem marginal_value : (marginal U N i).denote=
    fun x=>multiplier (n:=n) c scalar*(if x 0 then w i else 1) := by
  have h:=C.productTop_entry U scalar pin0 pin1 n positive (atLast N i)
    (fun j=>w ((lastPerm i).symm j)) c d (M.reboundary N w c d form (lastPerm i))
  simpa [marginal,multiplier,lastPerm] using h

include positive pin0 pin1 form in
theorem denote : (graph U N i).denote=
    T.value (fun j=>w ((firstPerm i).symm j.succ))
      (left w c scalar i) (right w c d scalar i) := by
  have h:=M.attach (marginal U N i) (atFirst N i)
    (fun j=>w ((firstPerm i).symm j)) c d (multiplier (n:=n) c scalar) (w i)
    (marginal_value U N w c d scalar i positive pin0 pin1 form)
    (M.reboundary N w c d form (firstPerm i))
  simpa [graph,left,right,firstPerm] using h

variable (nonzeroScalar : scalar≠0) (hc : c≠0) (hd : d≠0) (hi : w i≠0)
include nonzeroScalar hc hd hi in
theorem right_nonzero : right w c d scalar i≠0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero n nonzeroScalar) hc) hd) hi

def pin : Bool→K := fun b=>if b then 1 else 0

include positive pin0 pin1 form nonzeroScalar hc hd hi in
theorem smaller_or_power : Prime (⟨n,(graph U N i).denote⟩ : AnySignature K) ∨
    (graph U N i).denote=(fun x=>right w c d scalar i*Signature.unaryPower (pin (K:=K)) n x) := by
  classical
  by_cases zero : left w c scalar i=0
  · right
    rw [denote U N w c d scalar i positive pin0 pin1 form]
    funext x
    simp only [T.value,zero,zero_mul,zero_add,Signature.unaryPower,pin]
    rw [Fintype.prod_boole]
    simp only [←funext_iff]
    split_ifs <;> simp
  · left
    rw [denote U N w c d scalar i positive pin0 pin1 form]
    exact T.prime _ _ _ positive zero (right_nonzero w c d scalar i nonzeroScalar hc hd hi)

variable (F : SignatureFamily K) (uUses : Uses U F) (nUses : Uses N F)
include uUses nUses in
theorem uses : Uses (graph U N i) F :=
  capHead_uses F (marginal U N i) (atFirst N i)
    (C.uses F U uUses n (atLast N i) nUses) nUses

variable (uEdges : Ordinary U) (nEdges : Ordinary N)
include uEdges nEdges in
theorem ordinary : Ordinary (graph U N i) :=
  capHead_ordinary (marginal U N i) (atFirst N i)
    (C.ordinary U uEdges n (atLast N i) nEdges) nEdges

variable {r : ℕ} {a : ℕ→ℕ} (H : (j : Fin r)→Signature K (a j.val))
variable (UL : Labelling U.shape r 1 a) (NL : Labelling N.shape r 1 a)
variable (uExact : LabelledNetwork.Exact H U UL) (nExact : LabelledNetwork.Exact H N NL)

def labels : Labelling (graph U N i).shape r 1 a :=
  let hf:=uses U N i (Set.range fun j : Fin r=>(⟨a j.val,H j⟩ : AnySignature K))
    (fun v=>⟨UL.vertex v,uExact v⟩) (fun v=>⟨NL.vertex v,nExact v⟩)
  {vertex v:=Classical.choose (hf v)
   vertex_arity v:=congrArg Sigma.fst (Classical.choose_spec (hf v))
   edge _:=0}

theorem exact : LabelledNetwork.Exact H (graph U N i) (labels U N i H UL NL uExact nExact) := by
  intro v
  exact Classical.choose_spec (uses U N i (Set.range fun j : Fin r=>(⟨a j.val,H j⟩ : AnySignature K))
    (fun v=>⟨UL.vertex v,uExact v⟩) (fun v=>⟨NL.vertex v,nExact v⟩) v)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryProductTopMarginal
end
