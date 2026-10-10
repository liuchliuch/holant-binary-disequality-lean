import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6RMBell

/-! The literal real h8 phase exception: RM8 support with the complete cubic
sign on original ports 0,1,2,4. The finite integer contraction certificate is
then transported to the original coefficient field. This is not a universal
producer or a claim that arbitrary real signatures already have this form. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH8Table
open Holant Holant.Tractable
open scoped BigOperators
namespace B
export GlobalCloseCompletionKleinH6RMBell (rmCheck rm_check)
end B
namespace R
export GlobalCloseCompletionC2RMActual (rm)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def phase (x : Fin 8→Bool) : Bool :=
  (x 0 && x 1 && x 2) ^^ (x 0 && x 1 && x 4) ^^
    (x 0 && x 2 && x 4) ^^ (x 1 && x 2 && x 4)

variable {K L : Type*} [CommRing K] [CommRing L]

def h8 : Signature K 8 := fun x=>if B.rmCheck x then (if phase x then -1 else 1) else 0

def raw : Signature K 4 := fun x=>
  if x 0=x 3 ∧ x 1=x 2 then (if !(x 0) && x 1 then -2 else 2) else 0

/-- Six equality joins, in the exact source port order found below. -/
def joined (f g : Signature K 8) : Signature K 4 := fun x=>
  ∑u : Bool,∑v : Bool,∑w : Bool,∑z : Bool,∑a : Bool,∑b : Bool,
    f ![x 0,x 1,u,v,w,z,a,b]*g ![v,a,x 2,w,u,x 3,b,z]

theorem map_h8 (phi : K→+*L) (x : Fin 8→Bool) : phi (h8 (K:=K) x)=h8 (K:=L) x := by
  unfold h8
  split_ifs <;> norm_num

theorem map_raw (phi : K→+*L) (x : Fin 4→Bool) : phi (raw (K:=K) x)=raw (K:=L) x := by
  unfold raw
  split_ifs <;> norm_num
  all_goals
    have h : phi (1+1)=(1 : L)+1 := by rw [map_add,map_one]
    norm_num at h
    exact h

/-- A kernel-evaluated finite integer identity, not a numerical experiment. -/
theorem integer_join : ∀x : Fin 4→Bool,joined (h8 (K:=ℤ)) h8 x=raw x := by
  decide +kernel

theorem joined_h8 (x : Fin 4→Bool) : joined (h8 (K:=K)) h8 x=raw x := by
  have h := congrArg (Int.castRingHom K) (integer_join x)
  simpa only [joined,map_sum,map_mul,map_h8,map_raw] using h

theorem joined_scale (f g : Signature K 8) (c d : K) : joined (c • f) (d • g)=(c*d) • joined f g := by
  funext x
  simp only [joined,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem h8_as_rm {F : Type*} [Field F] (x : Fin 8→Bool) :
    h8 (K:=F) x=R.rm x*(if phase x then -1 else 1) := by
  rw [B.rm_check]
  unfold h8
  split_ifs <;> simp


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH8Table
end
