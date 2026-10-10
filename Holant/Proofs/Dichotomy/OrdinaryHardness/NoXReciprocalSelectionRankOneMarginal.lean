import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionRankOne

/-! Summing the even orientation of a two-point support preserves its two
weights. An unused orientation contributes exactly the harmless factor two. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOneMarginal
open Holant
namespace R
export NoXReciprocalSelectionRankOne (ports projected anti)
end R
namespace P
export NoXSeparateSignedProjection (rowPort)
end P
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}
variable (x y : Fin n→Bool)
def hasNegative : Prop := ∃i,x i=true ∧ y i=false

def scale : K := by
  classical
  exact if hasNegative x y then 1 else 2

include x y in
theorem monotone_word (none : ¬hasNegative x y) (u v : Bool) :
    T.substitute (P.rowPort (R.ports x y)) ![u,v]=if u then y else x := by
  funext i
  have hi : ¬(x i=true ∧ y i=false) := fun h=>none ⟨i,h⟩
  cases hx:x i <;> cases hy:y i <;> cases u <;>
    simp [T.substitute,P.rowPort,R.ports,hx,hy] at hi ⊢

variable (f : Signature K n) (support : ∀z,f z≠0→z=x ∨ z=y)
variable (positive : Fin n) (hp : x positive=false ∧ y positive=true)
include support hp in
theorem value (u : Bool) : (∑v : Bool,R.projected f x y ![u,v])=
    scale (K:=K) x y*(if u then f y else f x) := by
  classical
  by_cases neg : hasNegative x y
  · obtain ⟨negative,hn⟩ := neg
    rw [R.anti f x y support positive negative hp hn]
    cases u <;> simp [NoXWeightedAntiSigned.anti,Fintype.sum_bool,scale,hasNegative,show ∃i,x i=true ∧ y i=false from ⟨negative,hn⟩]
  · have eqn (v : Bool) : R.projected f x y ![u,v]=if u then f y else f x := by
      unfold R.projected
      rw [monotone_word x y neg]
      cases u <;> rfl
    simp only [eqn,Fintype.sum_bool,scale,if_neg neg]
    ring

theorem scale_ne_zero [CharZero K] : scale (K:=K) x y≠0 := by
  classical
  unfold scale
  split <;> norm_num

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOneMarginal
end
