import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2RMActual
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinStandardCoreAffine

/-! The literal four-copy H6-to-RM8 circuit's finite Bell algebra. All
coefficients and the RM code use the original ordered ports. This module
contains algebraic identities only; physical source access is supplied by a
separate actual-network consumer. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6RMBell
open Holant Holant.Tractable Holant.Algebraic
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.CoefficientAtlas
open scoped BigOperators
namespace R
export GlobalCloseCompletionC2RMActual (rm)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K]

def bell (d l : Bool) : Kernel K := fun a b=>
  if Bool.xor a b=d then (if l && a then -1 else 1) else 0

def E : Fin 4→Kernel K := ![bell false false,bell true false,bell false true,bell true true]
def theta : Equiv.Perm (Fin 4) where
  toFun := ![0,2,3,1]
  invFun := ![0,3,1,2]
  left_inv := by decide
  right_inv := by decide

def core : Signature K 6 := fun x=>∑k : Fin 4,
  E k (x 0) (x 1)*E (theta k) (x 2) (x 3)*E (theta (theta k)) (x 4) (x 5)

theorem core_algebraic : core (K:=AlgebraicComplex)=GlobalCloseCompletionKleinStandardCoreAffine.core := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    cases h3 : x 3 <;> cases h4 : x 4 <;> cases h5 : x 5 <;>
    norm_num [core,Fin.sum_univ_succ,E,theta,bell,
      GlobalCloseCompletionKleinStandardCoreAffine.core,
      GlobalCloseCompletionKleinStandardCoreAffine.bell,h0,h1,h2,h3,h4,h5]

/-- Orthogonality of the four literal ordered Bell matrices. -/
theorem inner (a b : Fin 4→K) :
    (∑u : Bool,∑v : Bool,(∑k : Fin 4,a k*E k u v)*(∑k : Fin 4,b k*E k u v))=
      2*∑k : Fin 4,a k*b k := by
  simp [Fintype.sum_bool,Fin.sum_univ_succ,E,bell]
  ring

/-- Same-label Bell pairs have squared norm four. -/
theorem pair_inner (a b : Fin 4→K) :
    (∑u : Bool,∑v : Bool,∑w : Bool,∑z : Bool,
      (∑k : Fin 4,a k*E (theta (theta k)) u v*E (theta (theta k)) w z)*
      (∑k : Fin 4,b k*E (theta (theta k)) u v*E (theta (theta k)) w z))=
      4*∑k : Fin 4,a k*b k := by
  simp [Fintype.sum_bool,Fin.sum_univ_succ,E,bell,theta]
  ring

theorem theta_inner (a b : Fin 4→K) :
    (∑u : Bool,∑v : Bool,(∑k : Fin 4,a k*E (theta k) u v)*(∑k : Fin 4,b k*E (theta k) u v))=
      2*∑k : Fin 4,a k*b k := by
  simp [Fintype.sum_bool,Fin.sum_univ_succ,E,bell,theta]
  ring

theorem core_block (a c : Fin 2→Bool) (u v : Bool) :
    core (K:=K) ![a 0,a 1,u,v,c 0,c 1]=
      ∑k : Fin 4,(E k (a 0) (a 1)*E (theta (theta k)) (c 0) (c 1))*E (theta k) u v := by
  change (∑k : Fin 4,E k (a 0) (a 1)*E (theta k) u v*E (theta (theta k)) (c 0) (c 1))=_
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Exact contraction of the second two-port block of two H6 copies. -/
theorem core_inner (a b c d : Fin 2→Bool) :
    (∑u : Bool,∑v : Bool,
      core (K:=K) ![a 0,a 1,u,v,c 0,c 1]*core ![b 0,b 1,u,v,d 0,d 1])=
      2*∑k : Fin 4,(E k (a 0) (a 1)*E k (b 0) (b 1))*
        E (theta (theta k)) (c 0) (c 1)*E (theta (theta k)) (d 0) (d 1) := by
  simp_rw [core_block]
  rw [theta_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

def rmCheck (x : Fin 8→Bool) : Bool :=
  ((x 0 ^^ x 1)==(x 2 ^^ x 3)) && ((x 0 ^^ x 1)==(x 4 ^^ x 5)) &&
    ((x 0 ^^ x 1)==(x 6 ^^ x 7)) && (!(x 0 ^^ x 2 ^^ x 4 ^^ x 6))

theorem code_iff_check (x : Fin 8→Bool) :
    (fun p=>boolEquiv (x p))∈code ↔ rmCheck x=true := by
  change (∃a : Param,evaluate a=(fun p=>boolEquiv (x p))) ↔ _
  revert x
  decide +kernel

theorem rm_check (x : Fin 8→Bool) : R.rm (K:=K) x=if rmCheck x then 1 else 0 := by
  simp only [R.rm,code_iff_check]

/-- The four equal-label Bell products are exactly twice literal RM8. -/
theorem four_bells (x : Fin 8→Bool) :
    (∑k : Fin 4,E (K:=K) k (x 0) (x 1)*E k (x 2) (x 3)*E k (x 4) (x 5)*E k (x 6) (x 7))=
      2*R.rm x := by
  rw [rm_check]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    cases h4 : x 4 <;> cases h5 : x 5 <;> cases h6 : x 6 <;> cases h7 : x 7 <;>
    norm_num [Fin.sum_univ_succ,E,bell,rmCheck,h0,h1,h2,h3,h4,h5,h6,h7]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6RMBell
end
