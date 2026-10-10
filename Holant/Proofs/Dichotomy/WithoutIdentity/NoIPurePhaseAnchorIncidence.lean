import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseIncidenceRegularization

/-! One fixed odd seven-character anchor neutralizes every admissible
rank-at-most-three signed incidence vector. Its phase class is never chosen
again for the tested row. There are at most three full copies and exactly
two proper-coordinate-face slots, with unused slots pinned to the supported
origin. This is an exact finite charge calculation, not a hardness premise. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseAnchorIncidence
open Holant
open scoped BigOperators
namespace R
export NoIPurePhaseIncidenceRegularization (pattern contribution zeroSchedule)
end R
namespace P
export NoIPurePhaseIncidenceRegularization.P (Transform)
end P
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option Elab.async false

/-- Odd residues are their own inverses in Z/4. -/
def copies (a t : ZMod 4) : ℕ := (-(t*a)).val

theorem copies_le (a t : ZMod 4) : copies a t≤3 := by
  have h:=(-(t*a)).val_lt
  unfold copies
  omega

theorem copy_charge (a t : ZMod 4) (odd : a=1 ∨ a=3) :
    t+(copies a t : ZMod 4)*a=0 := by
  rcases odd with rfl|rfl
  all_goals revert t;decide

/-- The two face slots generate the even character part of the tested
kernel, using copies of the fixed anchor rather than copies of the witness. -/
theorem face_charge (a : ZMod 4) (odd : a=1 ∨ a=3) (u : Fin 3→Bool) :
    ∀j,(∑i : Fin 2,R.contribution (fun _=>a) (R.zeroSchedule u i) j)=R.pattern 0 u j := by
  have hu : u=![u 0,u 1,u 2] := by funext i;fin_cases i <;> rfl
  rw [hu]
  rcases odd with rfl|rfl
  all_goals cases h0 : u 0 <;> cases h1 : u 1 <;> cases h2 : u 2 <;> decide

theorem neutralizes (a t : ZMod 4) (odd : a=1 ∨ a=3) (u : Fin 3→Bool) (j : Fin 7) :
    R.pattern t u j+(copies a t : ZMod 4)*a+
      (∑i : Fin 2,R.contribution (fun _=>a) (R.zeroSchedule u i) j)=0 := by
  rw [face_charge a odd u]
  have hc:=copy_charge a t odd
  unfold R.pattern
  cases NoIPurePhaseIncidenceCore.C.codeSeven u j
  · change t+0+(copies a t : ZMod 4)*a+(0+0)=0
    simpa using hc
  · change t+2+(copies a t : ZMod 4)*a+(0+2)=0
    calc
      _=(t+(copies a t : ZMod 4)*a)+4 := by ring
      _=0 := by rw [hc];decide

/-- One option denotes a full anchor copy; every other option denotes one
of the actual proper-coordinate-face substitutions. -/
def schedule (a t : ZMod 4) (u : Fin 3→Bool) : Fin 5→Option P.Transform :=
  ![if 0<copies a t then none else some ⟨0,0,0⟩,
    if 1<copies a t then none else some ⟨0,0,0⟩,
    if 2<copies a t then none else some ⟨0,0,0⟩,
    some (R.zeroSchedule u 0),some (R.zeroSchedule u 1)]

def charge (a : ZMod 4) (o : Option P.Transform) (j : Fin 7) : ZMod 4 :=
  match o with
  | none=>a
  | some t=>R.contribution (fun _=>a) t j

theorem schedule_certificate (a t : ZMod 4) (odd : a=1 ∨ a=3)
    (u : Fin 3→Bool) (j : Fin 7) :
    R.pattern t u j+∑i : Fin 5,charge a (schedule a t u i) j=0 := by
  have hu : u=![u 0,u 1,u 2] := by funext i;fin_cases i <;> rfl
  rw [hu]
  have ht : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by exact (by decide : ∀v : ZMod 4,v=0 ∨ v=1 ∨ v=2 ∨ v=3) t
  rcases odd with rfl|rfl
  all_goals rcases ht with rfl|rfl|rfl|rfl
  all_goals cases h0 : u 0 <;> cases h1 : u 1 <;> cases h2 : u 2 <;> revert j <;> decide


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseAnchorIncidence
