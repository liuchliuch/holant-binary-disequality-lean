import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffinePhaseFaces
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineFullParity

/-! Full parity support is an affine Boolean cube with one dependent physical
port. A nonaffine row therefore has an actual two-coordinate even-phase face. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffinePhaseParity
open Holant Holant.Tractable Holant.Algebraic
open Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
namespace N
export GlobalCloseCompletionKleinHigherNonaffineFullParity (Normal support_iff)
end N
variable {n : ℕ}

def encode (p : ZMod 2) (y : Word n) : Word (n+1) :=
  Fin.cons (boolEquiv.symm (p-ClosureSixPort.parity y)) y

theorem bit_equiv (b : Bool) : ClosureSixPort.bit b = boolEquiv b := by cases b <;> rfl

theorem parity_cons (b : Bool) (y : Word n) :
    ClosureSixPort.parity (Fin.cons b y) = boolEquiv b + ClosureSixPort.parity y := by
  simp [ClosureSixPort.parity,Fin.sum_univ_succ,bit_equiv]

@[simp] theorem parity_encode (p : ZMod 2) (y : Word n) :
    ClosureSixPort.parity (encode p y)=p := by
  rw [encode,parity_cons,boolEquiv.apply_symm_apply]
  exact sub_add_cancel _ _

theorem encode_tail (x : Word (n+1)) (p : ZMod 2)
    (h : ClosureSixPort.parity x=p) : encode p (fun i=>x i.succ)=x := by
  have hx : x=Fin.cons (x 0) (fun i=>x i.succ) := (Fin.cons_self_tail x).symm
  have hp : boolEquiv (x 0)+ClosureSixPort.parity (fun i=>x i.succ)=p := by
    conv_lhs => rw [←parity_cons,←hx]
    exact h
  have first : boolEquiv.symm (p-ClosureSixPort.parity (fun i=>x i.succ))=x 0 := by
    apply boolEquiv.injective
    rw [boolEquiv.apply_symm_apply]
    exact (eq_sub_iff_add_eq.mpr hp).symm
  rw [encode,first]
  exact hx.symm

def paritySystem (n : ℕ) (p : ZMod 2) : AffineSystem n :=
  ⟨1,fun _ _=>1,fun _=>p⟩

theorem paritySystem_holds (p : ZMod 2) (x : Word n) :
    (paritySystem n p).Holds x ↔ ClosureSixPort.parity x=p := by
  simp only [AffineSystem.Holds,paritySystem,one_mul]
  have bits : (∑j,bitValue (ZMod 2) (x j))=ClosureSixPort.parity x := by
    apply Finset.sum_congr rfl
    intro j _
    cases x j <;> rfl
  simp [bits]

theorem affine_lift {f : Signature AlgebraicComplex (n+1)} (p : ZMod 2)
    (outside : ∀x, ClosureSixPort.parity x≠p → f x=0)
    (hf : Affine (fun y=>f (encode p y))) : Affine f := by
  have h := (hf.precompose (fun x i=>x i.succ) (coordinates_isAffineMap Fin.succ)).restrict
    (paritySystem (n+1) p)
  convert h using 1
  funext x
  by_cases same : ClosureSixPort.parity x=p
  · simp only [paritySystem_holds,same,ite_true]
    exact (congrArg f (encode_tail x p same)).symm
  · simp only [paritySystem_holds,same,ite_false]
    exact outside x same

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

/-- The witness uses two distinct free physical coordinates; its first port is
fixed by the actual support parity, so no independent pinning resource enters. -/
theorem positive_face (f : Signature (OI.K G) (n+1)) (normal : N.Normal G f)
    (bad : ¬ GlobalCloseCompletionKleinAffineLeaf.IsAffine G ⟨n+1,f⟩) :
    ∃ z j k, j≠k ∧
      f (encode normal.parity (AffinePhase.xor (AffinePhase.xor z (basis j)) (basis k))) *
        f (encode normal.parity z) =
      f (encode normal.parity (AffinePhase.xor z (basis j))) *
        f (encode normal.parity (AffinePhase.xor z (basis k))) := by
  classical
  let phi := ClosureSourceRows.embedding G
  let g : Signature AlgebraicComplex n := fun y=>phi (f (encode normal.parity y))
  have live : ∀y,g y≠0 := by
    intro y
    intro zero
    apply ((N.support_iff G f normal _).mpr (parity_encode _ _))
    apply phi.injective
    simpa only [map_zero] using zero
  have squared (y : Word n) : f (encode normal.parity y)^2=normal.scalar^2 := by
    rw [normal.value,if_pos (parity_encode _ _)]
    split_ifs <;> ring
  have squares : ∀x y,g x^2=g y^2 := by
    intro x y
    change (phi (f (encode normal.parity x)))^2=(phi (f (encode normal.parity y)))^2
    rw [←map_pow,←map_pow,squared,squared]
  have nonaffine : ¬ Affine g := by
    intro affine
    apply bad
    apply affine_lift normal.parity _ affine
    intro x outside
    change phi (f x)=0
    rw [normal.value,if_neg outside,map_zero]
  obtain ⟨z,j,k,distinct,face⟩ :=
    GlobalCloseCompletionKleinHigherNonaffinePhaseFaces.positive_face live squares nonaffine
  refine ⟨z,j,k,distinct,?_⟩
  apply phi.injective
  simpa only [g,map_mul] using face

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffinePhaseParity
end
