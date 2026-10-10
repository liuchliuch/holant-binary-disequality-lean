import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalMixedProjectionCore

/-! Exact summation of the private sign groups. Every unused group supplies
one factor two; used groups have one forced value. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalMixedProjectionSum
open Holant
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace C
export NoXReciprocalMixedProjectionCore (selected active Allowed logical value)
end C
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {K : Type} [Field K] {n m : ℕ}
variable (p : Fin n→Port m) (sign : Fin m→Bool)
def factor (z : Fin m→Bool) (j : Fin m) (b : Bool) : K :=
  if C.active p sign j then (if b=!(z j) then 1 else 0) else 1
def scale : K := ∏j : Fin m,if C.active p sign j then 1 else 2

theorem indicator (z y : Fin m→Bool) :
    (if C.Allowed p sign z y then (1 : K) else 0)=∏j : Fin m,factor p sign z j (y j) := by
  by_cases allowed:C.Allowed p sign z y
  · rw [if_pos allowed]
    symm
    apply Finset.prod_eq_one
    intro j _
    by_cases active:C.active p sign j
    · simp [factor,active,allowed j active]
    · simp [factor,active]
  · rw [if_neg allowed]
    obtain ⟨j,hj⟩ := not_forall.mp allowed
    have active:C.active p sign j := Classical.byContradiction (fun h=>hj (fun ha=>False.elim (h ha)))
    have neq:y j≠!(z j) := fun he=>hj (fun _=>he)
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [factor,active,neq]

theorem sum_indicator (z : Fin m→Bool) :
    (∑y : Fin m→Bool,if C.Allowed p sign z y then (1 : K) else 0)=scale (K:=K) p sign := by
  simp_rw [indicator]
  rw [←Fintype.prod_sum]
  apply Finset.prod_congr rfl
  intro j _
  by_cases active:C.active p sign j
  · cases h:z j <;> simp [factor,active,Fintype.sum_bool,h]
  · simp [factor,active,Fintype.sum_bool]

theorem scale_ne_zero [CharZero K] : scale (K:=K) p sign≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  split <;> norm_num

variable (present : ∀j,∃i,p i=.inr (j,sign j)) (f : Signature K n)
variable (cover : ∀u,f u≠0→∃w,word p w=u)
include present cover in
theorem value (z : Fin m→Bool) :
    (∑y : Fin m→Bool,f (C.selected p sign z y))=
      scale (K:=K) p sign*f (word p (C.logical sign z)) := by
  simp_rw [C.value p sign present f cover z]
  have eqn (y : Fin m→Bool) :
      (if C.Allowed p sign z y then f (word p (C.logical sign z)) else 0)=
      (if C.Allowed p sign z y then (1 : K) else 0)*f (word p (C.logical sign z)) := by
    split <;> simp
  simp_rw [eqn]
  rw [←Finset.sum_mul,sum_indicator]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalMixedProjectionSum
end
