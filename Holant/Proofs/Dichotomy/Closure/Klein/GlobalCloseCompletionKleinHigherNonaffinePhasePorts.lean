import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffinePhaseParity
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineWalsh
import Mathlib.Logic.Equiv.Fintype

/-! Port orders for the actual H6 phase probe. The two free face coordinates
come first and their dependent parity coordinate comes third. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffinePhasePorts
open Holant Holant.Tractable Holant.Algebraic Holant.Tractable.AffinePhase
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open scoped BigOperators
namespace P
export GlobalCloseCompletionKleinHigherNonaffinePhaseParity (encode parity_encode bit_equiv parity_cons)
end P
namespace W
export GlobalCloseCompletionKleinHigherNonaffineWalsh (triple)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {n : ℕ}

def append (u : Word 3) (z : Word n) : Word (n+3) :=
  Fin.cons (u 0) (Fin.cons (u 1) (Fin.cons (u 2) z))
def tail (x : Word (n+3)) : Word n := fun i=>x i.succ.succ.succ

theorem append_tail (x : Word (n+3)) : append ![x 0,x 1,x 2] (tail x)=x := by
  funext i
  refine Fin.cases (by rfl) (fun i=>?_) i
  refine Fin.cases (by rfl) (fun i=>?_) i
  refine Fin.cases (by rfl) (fun i=>?_) i
  rfl

 theorem parity_xor (x y : Word n) :
    ClosureSixPort.parity (AffinePhase.xor x y)=ClosureSixPort.parity x+ClosureSixPort.parity y := by
  simp only [ClosureSixPort.parity,AffinePhase.xor,←ClosureSixPort.bit_xor,Finset.sum_add_distrib]

 theorem parity_basis (j : Fin n) : ClosureSixPort.parity (basis j)=1 := by
  simp [ClosureSixPort.parity,basis,ClosureSixPort.bit]

 theorem encode_toggle (p : ZMod 2) (z : Word n) (j : Fin n) :
    P.encode p (AffinePhase.xor z (basis j))=
      AffinePhase.xor (P.encode p z) (AffinePhase.xor (basis (0 : Fin (n+1))) (basis j.succ)) := by
  funext i
  refine Fin.cases ?_ (fun k=>?_) i
  · have first : ∀a : ZMod 2,boolEquiv.symm (a-1)=!(boolEquiv.symm a) := by decide
    simp only [P.encode,Fin.cons_zero,parity_xor,parity_basis]
    rw [sub_add_eq_sub_sub,first]
    simp [AffinePhase.xor,basis,Fin.succ_ne_zero,Ne.symm (Fin.succ_ne_zero j)]
  · simp [P.encode,AffinePhase.xor,basis]

 theorem order_exists (j k : Fin (n+2)) (different : j≠k) :
    ∃p : Equiv.Perm (Fin (n+3)), p 0=j.succ ∧ p 1=k.succ ∧ p 2=0 := by
  let start : Fin 3→Fin (n+3) := fun i=>⟨i.val,by omega⟩
  let target : Fin 3→Fin (n+3) := ![j.succ,k.succ,0]
  have hs : Function.Injective start := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin (n+3)=>x.val) h
  have ht : Function.Injective target := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [target,Fin.succ_ne_zero,Ne.symm,Fin.succ_inj]
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair start target hs ht
  exact ⟨p,hp 0,hp 1,hp 2⟩

 theorem tail_toggle (p : Equiv.Perm (Fin (n+3))) (x : Word (n+3))
    (a : Fin (n+3)) (i : Fin 3) (ha : p ⟨i.val,by omega⟩=a) :
    tail (fun q=>(AffinePhase.xor x (basis a)) (p q))=tail (fun q=>x (p q)) := by
  funext k
  have ne : p k.succ.succ.succ≠a := by
    intro same
    have h := p.injective (same.trans ha.symm)
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ] at hv
    omega
  simp [tail,AffinePhase.xor,basis,ne]

theorem toggle_first (d a b : Bool) (z : Word n) :
    AffinePhase.xor (append (W.triple d a b) z)
      (AffinePhase.xor (basis (2 : Fin (n+3))) (basis 0)) =
      append (W.triple d (!a) b) z := by
  funext i
  refine Fin.cases ?_ (fun i=>?_) i
  · cases d <;> cases a <;> cases b <;> rfl
  refine Fin.cases ?_ (fun i=>?_) i
  · cases d <;> cases a <;> cases b <;> rfl
  refine Fin.cases ?_ (fun i=>?_) i
  · cases d <;> cases a <;> cases b <;> rfl
  · have ne2 : i.succ.succ.succ≠(2 : Fin (n+3)) := by
      intro h
      have hv := congrArg (fun q : Fin (n+3)=>q.val) h
      simp only [Fin.val_succ,Fin.val_ofNat] at hv
      norm_num [Nat.mod_eq_of_lt (show 2<n+3 by omega)] at hv <;> omega
    have ne1 : i.succ.succ.succ≠(1 : Fin (n+3)) := by
      intro h
      have hv := congrArg (fun q : Fin (n+3)=>q.val) h
      simp only [Fin.val_succ,Fin.val_ofNat] at hv
      norm_num [Nat.mod_eq_of_lt (show 2<n+3 by omega)] at hv <;> omega
    simp [AffinePhase.xor,basis,append,ne2,ne1]

theorem toggle_second (d a b : Bool) (z : Word n) :
    AffinePhase.xor (append (W.triple d a b) z)
      (AffinePhase.xor (basis (2 : Fin (n+3))) (basis 1)) =
      append (W.triple d a (!b)) z := by
  funext i
  refine Fin.cases ?_ (fun i=>?_) i
  · cases d <;> cases a <;> cases b <;> rfl
  refine Fin.cases ?_ (fun i=>?_) i
  · cases d <;> cases a <;> cases b <;> rfl
  refine Fin.cases ?_ (fun i=>?_) i
  · cases d <;> cases a <;> cases b <;> rfl
  · have ne2 : i.succ.succ.succ≠(2 : Fin (n+3)) := by
      intro h
      have hv := congrArg (fun q : Fin (n+3)=>q.val) h
      simp only [Fin.val_succ,Fin.val_ofNat] at hv
      norm_num [Nat.mod_eq_of_lt (show 2<n+3 by omega)] at hv <;> omega
    have ne1 : i.succ.succ.succ≠(1 : Fin (n+3)) := by
      intro h
      have hv := congrArg (fun q : Fin (n+3)=>q.val) h
      simp only [Fin.val_succ,Fin.val_ofNat] at hv
      norm_num [Nat.mod_eq_of_lt (show 2<n+3 by omega)] at hv <;> omega
    simp [AffinePhase.xor,basis,append,ne2,ne1]

theorem triple_front (x : Word (n+3)) :
    W.triple (x 2^^x 0^^x 1) (x 0) (x 1)=![x 0,x 1,x 2] := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> rfl

theorem ordered_toggle (p : Equiv.Perm (Fin (n+3))) (y : Word (n+2))
    (parity : ZMod 2) (j : Fin (n+2)) (i : Fin (n+3))
    (hj : p i=j.succ) (hz : p 2=0) :
    (fun q=>P.encode parity (AffinePhase.xor y (basis j)) (p q))=
      AffinePhase.xor (fun q=>P.encode parity y (p q))
        (AffinePhase.xor (basis 2) (basis i)) := by
  rw [encode_toggle]
  funext q
  simp only [AffinePhase.xor,basis]
  rw [←hj,←hz]
  simp only [p.injective.eq_iff]

/-- Every ordered even face retains its determinant equality when its base
corner is changed. -/
theorem face_corner {K : Type*} [CommRing K] (f : Bool→Bool→K) (a b : Bool)
    (h : f (!a) (!b)*f a b=f (!a) b*f a (!b)) :
    f false false*f true true=f false true*f true false := by
  cases a <;> cases b <;> first
    | simpa only [Bool.not_false,Bool.not_true,mul_comm] using h
    | simpa only [Bool.not_false,Bool.not_true,mul_comm] using h.symm


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffinePhasePorts
end
