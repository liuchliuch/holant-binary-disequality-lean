import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXSeparateSignedProjection

/-! A sign-separated mixed-parity projection. A live row fixes every used
private orientation from the chosen boundary orientation; absent groups remain
free. Complementation occurs only in this semantic identity. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalMixedProjectionCore
open Holant
open OrdinaryNegativeSignedPortsCore (Port word)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {n m : ℕ}
def selected (p : Fin n→Port m) (sign : Fin m→Bool) (z y : Fin m→Bool) (i : Fin n) : Bool :=
  match p i with
  | .inl b=>b
  | .inr (j,b)=>if b=sign j then z j else y j

def active (p : Fin n→Port m) (sign : Fin m→Bool) (j : Fin m) : Prop :=
  ∃i,p i=.inr (j,!(sign j))
def logical (sign z : Fin m→Bool) : Fin m→Bool := fun j=>sign j ^^ z j
def Allowed (p : Fin n→Port m) (sign z y : Fin m→Bool) : Prop :=
  ∀j,active p sign j→y j=!(z j)

variable (p : Fin n→Port m) (sign : Fin m→Bool)
variable (present : ∀j,∃i,p i=.inr (j,sign j))

theorem ideal (z y : Fin m→Bool) (allowed : Allowed p sign z y) :
    selected p sign z y=word p (logical sign z) := by
  funext i
  cases hi:p i with
  | inl b=>simp [selected,word,hi]
  | inr q=>
    rcases q with ⟨j,b⟩
    by_cases hb:b=sign j
    · simp [selected,word,logical,hi,hb]
    · have flip:b=!(sign j) := by cases hbv:b <;> cases hsv:sign j <;> simp_all
      have hy:=allowed j ⟨i,by simpa only [flip] using hi⟩
      cases hs:sign j <;> cases hz:z j <;> simp_all [selected,word,logical]

variable {K : Type} [Zero K] (f : Signature K n)
variable (cover : ∀u,f u≠0→∃w,word p w=u)
include present cover in
theorem live_allowed (z y : Fin m→Bool) (live : f (selected p sign z y)≠0) :
    Allowed p sign z y := by
  obtain ⟨w,hw⟩ := cover _ live
  have wl : w=logical sign z := by
    funext j
    obtain ⟨i,hi⟩ := present j
    have h:=congrFun hw i
    simp only [word,selected,hi,if_pos rfl] at h
    cases hs:sign j <;> cases hz:z j <;> cases hu:w j <;> simp_all [logical]
  intro j active
  obtain ⟨i,hi⟩ := active
  have h:=congrFun hw i
  rw [wl] at h
  cases hs:sign j <;> cases hz:z j <;> simp_all [word,selected,logical]

include present cover in
theorem value (z y : Fin m→Bool) :
    f (selected p sign z y)=if Allowed p sign z y then f (word p (logical sign z)) else 0 := by
  classical
  by_cases h:Allowed p sign z y
  · rw [if_pos h,ideal p sign z y h]
  · rw [if_neg h]
    by_contra live
    exact h (live_allowed p sign present f cover z y live)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalMixedProjectionCore
end
