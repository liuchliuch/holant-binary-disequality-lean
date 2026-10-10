import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffinePhasePorts

/-! The nonaffine full-parity phase witness in physical H6 gate coordinates,
with the original coefficient-field scale and all four actual face values. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffinePhaseFaceSource
open Holant Holant.Tractable Holant.Algebraic Holant.Tractable.AffinePhase
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open scoped BigOperators
open GlobalCloseCompletionKleinHigherNonaffinePhasePorts
namespace P
export GlobalCloseCompletionKleinHigherNonaffinePhaseParity (encode parity_encode positive_face)
end P
namespace W
export GlobalCloseCompletionKleinHigherNonaffineWalsh (triple sign)
end W
namespace N
export GlobalCloseCompletionKleinHigherNonaffineFullParity (Normal)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {n : ℕ}

def pull (p : Equiv.Perm (Fin n)) (x : Word n) : Word n := fun i=>x (p i)
def reorder {K : Type*} (p : Equiv.Perm (Fin n)) (f : Signature K n) : Signature K n :=
  fun x=>f (pull p.symm x)

@[simp] theorem reorder_pull {K : Type*} (p : Equiv.Perm (Fin n)) (f : Signature K n) (x : Word n) :
    reorder p f (pull p x)=f x := by
  change f (fun i=>x (p (p.symm i)))=f x
  simp only [Equiv.apply_symm_apply]

theorem parity_pull (p : Equiv.Perm (Fin n)) (x : Word n) :
    ClosureSixPort.parity (pull p x)=ClosureSixPort.parity x :=
  Equiv.sum_comp p (fun i=>ClosureSixPort.bit (x i))

theorem parity_triple (d a b : Bool) (z : Word n) :
    ClosureSixPort.parity (append (W.triple d a b) z)=boolEquiv d+ClosureSixPort.parity z := by
  cases d <;> cases a <;> cases b <;>
    simp [append,W.triple,GlobalCloseCompletionKleinHigherNonaffinePhaseParity.parity_cons,boolEquiv] <;>
    norm_num [←add_assoc] <;> decide

theorem face_order {K : Type*} [CommRing K] (f : Signature K (n+3))
    (parity : ZMod 2) (z : Word (n+2)) (j k : Fin (n+2)) (different : j≠k)
    (face : f (P.encode parity (AffinePhase.xor (AffinePhase.xor z (basis j)) (basis k))) *
      f (P.encode parity z) = f (P.encode parity (AffinePhase.xor z (basis j))) *
      f (P.encode parity (AffinePhase.xor z (basis k)))) :
    ∃p : Equiv.Perm (Fin (n+3)),∃d : Bool,∃rest : Word n,
      boolEquiv d+ClosureSixPort.parity rest=parity ∧
      reorder p f (append (W.triple d false false) rest)*
        reorder p f (append (W.triple d true true) rest)=
      reorder p f (append (W.triple d false true) rest)*
        reorder p f (append (W.triple d true false) rest) := by
  obtain ⟨p,hj,hk,hz⟩ := order_exists j k different
  let x := pull p (P.encode parity z)
  let d := x 2^^x 0^^x 1
  let rest := tail x
  have base : pull p (P.encode parity z)=append (W.triple d (x 0) (x 1)) rest := by
    rw [triple_front]
    exact (append_tail x).symm
  have left : pull p (P.encode parity (AffinePhase.xor z (basis j)))=
      append (W.triple d (!(x 0)) (x 1)) rest := by
    rw [show pull p (P.encode parity (AffinePhase.xor z (basis j)))=
      AffinePhase.xor (pull p (P.encode parity z)) (AffinePhase.xor (basis 2) (basis 0)) from
      ordered_toggle p z parity j 0 hj hz,base,toggle_first]
  have right : pull p (P.encode parity (AffinePhase.xor z (basis k)))=
      append (W.triple d (x 0) (!(x 1))) rest := by
    rw [show pull p (P.encode parity (AffinePhase.xor z (basis k)))=
      AffinePhase.xor (pull p (P.encode parity z)) (AffinePhase.xor (basis 2) (basis 1)) from
      ordered_toggle p z parity k 1 hk hz,base,toggle_second]
  have both : pull p (P.encode parity (AffinePhase.xor (AffinePhase.xor z (basis j)) (basis k)))=
      append (W.triple d (!(x 0)) (!(x 1))) rest := by
    rw [show pull p (P.encode parity (AffinePhase.xor (AffinePhase.xor z (basis j)) (basis k)))=
      AffinePhase.xor (pull p (P.encode parity (AffinePhase.xor z (basis j))))
        (AffinePhase.xor (basis 2) (basis 1)) from
      ordered_toggle p (AffinePhase.xor z (basis j)) parity k 1 hk hz,left,toggle_second]
  have parityEq : boolEquiv d+ClosureSixPort.parity rest=parity := by
    rw [←parity_triple d (x 0) (x 1) rest,←base,parity_pull,P.parity_encode]
  refine ⟨p,d,rest,parityEq,?_⟩
  apply face_corner (fun a b=>reorder p f (append (W.triple d a b) rest)) (x 0) (x 1)
  simp only [←base,←left,←right,←both,reorder_pull]
  exact face

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

theorem source (f : Signature (OI.K G) (n+3)) (normal : N.Normal G f)
    (bad : ¬GlobalCloseCompletionKleinAffineLeaf.IsAffine G ⟨n+3,f⟩) :
    ∃p : Equiv.Perm (Fin (n+3)),∃d : Bool,∃rest : Word n,∃signs : Bool→Bool→Bool,
      (∀a b,reorder p f (append (W.triple d a b) rest)=normal.scalar*W.sign (signs a b)) ∧
      W.sign (K:=OI.K G) (signs false false)*W.sign (signs true true)=
        W.sign (signs false true)*W.sign (signs true false) := by
  obtain ⟨z,j,k,different,face⟩ := P.positive_face G f normal bad
  obtain ⟨p,d,rest,parityEq,even⟩ := face_order f normal.parity z j k different face
  let signs : Bool→Bool→Bool := fun a b=>normal.phase (pull p.symm (append (W.triple d a b) rest))
  have value (a b : Bool) : reorder p f (append (W.triple d a b) rest)=normal.scalar*W.sign (signs a b) := by
    change f _=_
    rw [normal.value,if_pos]
    rfl
    rw [parity_pull,parity_triple,parityEq]
  refine ⟨p,d,rest,signs,value,?_⟩
  simp only [value] at even
  apply (mul_left_cancel₀ (pow_ne_zero 2 normal.nonzero))
  linear_combination even

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffinePhaseFaceSource
end
