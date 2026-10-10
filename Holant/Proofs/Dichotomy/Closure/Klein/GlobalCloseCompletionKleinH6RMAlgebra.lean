import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6RMBell

/-! Exact finite-sum semantics of the manuscript's four-copy H6 cycle.
The two first joins consume the B blocks; the four final joins connect the
C blocks cyclically. No analytic operator is declared as a source resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6RMAlgebra
open Holant Holant.Tractable
open scoped BigOperators
namespace B
export GlobalCloseCompletionKleinH6RMBell (core E theta core_inner pair_inner four_bells)
end B
namespace R
export GlobalCloseCompletionC2RMActual (rm)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K]

def firstOrder : Equiv.Perm (Fin 12) where
  toFun := ![4,5,0,2,6,7,8,9,1,3,10,11]
  invFun := ![2,8,3,9,0,1,4,5,6,7,10,11]
  left_inv := by decide
  right_inv := by decide

def secondOrder : Equiv.Perm (Fin 16) where
  toFun := ![8,9,0,2,10,11,4,6,12,13,5,7,14,15,1,3]
  invFun := ![2,14,3,15,6,10,7,11,0,1,4,5,8,9,12,13]
  left_inv := by decide
  right_inv := by decide

def joinB (f g : Signature K 6) : Signature K 8 :=
  Signature.contract Signature.equality (Signature.contract Signature.equality
    (Tensor.reindex firstOrder (Signature.tensor f g)))

def joinC (f g : Signature K 8) : Signature K 8 :=
  Signature.contract Signature.equality (Signature.contract Signature.equality
    (Signature.contract Signature.equality (Signature.contract Signature.equality
      (Tensor.reindex secondOrder (Signature.tensor f g)))))

def cycle (f : Signature K 6) : Signature K 8 := joinC (joinB f f) (joinB f f)

theorem first_input (f g : Signature K 6) (x : Fin 8→Bool) (a b c d : Bool) :
    Tensor.reindex firstOrder (Signature.tensor f g) (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d x))))=
      f ![x 0,x 1,a,c,x 2,x 3]*g ![x 4,x 5,b,d,x 6,x 7] := by
  simp only [Tensor.reindex_apply,Signature.tensor_apply]
  congr 1
  · apply congrArg f
    funext i
    fin_cases i <;> rfl
  · apply congrArg g
    funext i
    fin_cases i <;> rfl

theorem second_input (f g : Signature K 8) (x : Fin 8→Bool) (a b c d e h i j : Bool) :
    Tensor.reindex secondOrder (Signature.tensor f g)
      (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d (Fin.cons e (Fin.cons h (Fin.cons i (Fin.cons j x))))))))=
      f ![x 0,x 1,a,c,x 2,x 3,e,i]*g ![x 4,x 5,h,j,x 6,x 7,b,d] := by
  simp only [Tensor.reindex_apply,Signature.tensor_apply]
  congr 1
  · apply congrArg f
    funext k
    fin_cases k <;> rfl
  · apply congrArg g
    funext k
    fin_cases k <;> rfl

theorem joinB_value (f g : Signature K 6) (x : Fin 8→Bool) :
    joinB f g x=∑v : Bool,∑u : Bool,f ![x 0,x 1,u,v,x 2,x 3]*g ![x 4,x 5,u,v,x 6,x 7] := by
  simp only [joinB,Signature.contract_equality]
  rw [first_input f g x false false false false,
    first_input f g x false false true true,
    first_input f g x true true false false,
    first_input f g x true true true true]
  simp only [Fintype.sum_bool]
  ac_rfl

theorem joinC_value (f g : Signature K 8) (x : Fin 8→Bool) :
    joinC f g x=∑z : Bool,∑w : Bool,∑v : Bool,∑u : Bool,
      f ![x 0,x 1,u,v,x 2,x 3,w,z]*g ![x 4,x 5,w,z,x 6,x 7,u,v] := by
  simp only [joinC,Signature.contract_equality]
  rw [second_input f g x false false false false false false false false,
    second_input f g x false false false false false false true true,
    second_input f g x false false false false true true false false,
    second_input f g x false false false false true true true true,
    second_input f g x false false true true false false false false,
    second_input f g x false false true true false false true true,
    second_input f g x false false true true true true false false,
    second_input f g x false false true true true true true true,
    second_input f g x true true false false false false false false,
    second_input f g x true true false false false false true true,
    second_input f g x true true false false true true false false,
    second_input f g x true true false false true true true true,
    second_input f g x true true true true false false false false,
    second_input f g x true true true true false false true true,
    second_input f g x true true true true true true false false,
    second_input f g x true true true true true true true true]
  simp only [Fintype.sum_bool]
  ac_rfl

def pairValue (a : Fin 4→K) (u v w z : Bool) : K :=
  ∑k : Fin 4,a k*B.E (B.theta (B.theta k)) u v*B.E (B.theta (B.theta k)) w z

theorem pairValue_swap (a : Fin 4→K) (u v w z : Bool) : pairValue a w z u v=pairValue a u v w z := by
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem pairValue_inner (a b : Fin 4→K) :
    (∑z : Bool,∑w : Bool,∑v : Bool,∑u : Bool,pairValue a u v w z*pairValue b u v w z)=
      4*∑k : Fin 4,a k*b k := by
  have h := B.pair_inner a b
  have reorder : (∑z : Bool,∑w : Bool,∑v : Bool,∑u : Bool,pairValue a u v w z*pairValue b u v w z)=
      ∑u : Bool,∑v : Bool,∑w : Bool,∑z : Bool,pairValue a u v w z*pairValue b u v w z := by
    simp only [Fintype.sum_bool]
    ac_rfl
  exact reorder.trans h

theorem joinB_core (x : Fin 8→Bool) : joinB (B.core (K:=K)) B.core x=
    2*pairValue (fun k=>B.E k (x 0) (x 1)*B.E k (x 4) (x 5)) (x 2) (x 3) (x 6) (x 7) := by
  rw [joinB_value,Finset.sum_comm]
  exact B.core_inner ![x 0,x 1] ![x 4,x 5] ![x 2,x 3] ![x 6,x 7]

theorem cycle_core (x : Fin 8→Bool) : cycle (B.core (K:=K)) x=32*R.rm x := by
  let a : Fin 4→K := fun k=>B.E k (x 0) (x 1)*B.E k (x 2) (x 3)
  let b : Fin 4→K := fun k=>B.E k (x 4) (x 5)*B.E k (x 6) (x 7)
  rw [cycle,joinC_value]
  simp_rw [joinB_core]
  change (∑z : Bool,∑w : Bool,∑v : Bool,∑u : Bool,
    (2*pairValue a u v w z)*(2*pairValue b w z u v))=32*R.rm x
  have scaled : (∑z : Bool,∑w : Bool,∑v : Bool,∑u : Bool,
      (2*pairValue a u v w z)*(2*pairValue b w z u v))=
      4*(∑z : Bool,∑w : Bool,∑v : Bool,∑u : Bool,pairValue a u v w z*pairValue b u v w z) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro u _
    rw [pairValue_swap b w z u v]
    ring
  rw [scaled,pairValue_inner]
  have product : (∑k : Fin 4,a k*b k)=
      ∑k : Fin 4,B.E k (x 0) (x 1)*B.E k (x 2) (x 3)*B.E k (x 4) (x 5)*B.E k (x 6) (x 7) := by
    apply Finset.sum_congr rfl
    intro k _
    dsimp [a,b]
    ring
  rw [product,B.four_bells]
  ring

theorem joinB_scale (f g : Signature K 6) (c d : K) :
    joinB (c • f) (d • g)=(c*d) • joinB f g := by
  funext x
  simp only [joinB_value,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem joinC_scale (f g : Signature K 8) (c d : K) :
    joinC (c • f) (d • g)=(c*d) • joinC f g := by
  funext x
  simp only [joinC_value,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem cycle_scale (c : K) : cycle (c • (B.core (K:=K)))=(32*c^4) • R.rm := by
  unfold cycle
  simp only [joinB_scale,joinC_scale]
  funext x
  change ((c*c)*(c*c))*cycle B.core x=(32*c^4)*R.rm x
  rw [cycle_core]
  ring


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6RMAlgebra
end
