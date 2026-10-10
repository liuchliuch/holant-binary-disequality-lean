import Holant.Proofs.Hardness.GeneralEOPhaseExtractionDistance

/-! A minimal pair in different support colors exposes exactly two live
corners in its coordinate face. The coloring is arbitrary and may encode
parity or the two surviving classes modulo four. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureTwoColorFace
open Holant
open scoped BigOperators
abbrev distance := @Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance.distance
variable {n : ℕ}

def Face (x y z : Fin n→Bool) : Prop := ∀i,x i=y i → z i=x i

theorem distance_add (x y z : Fin n→Bool) (face : Face x y z) :
    distance x z+distance z y=distance x y := by
  unfold distance Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance.distance
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h:=face i
  cases hx:x i <;> cases hy:y i <;> cases hz:z i <;> simp_all

theorem shorter (x y z : Fin n→Bool) (face : Face x y z) (zx : z≠x) (zy : z≠y) :
    distance x z<distance x y ∧ distance z y<distance x y := by
  have add:=distance_add x y z face
  have a:=Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance.distance_pos zx.symm
  have b:=Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance.distance_pos zy
  change 0<distance x z at a
  change 0<distance z y at b
  omega

variable {K : Type*} [Zero K]

theorem source (f : Signature K n) (color : (Fin n→Bool)→Bool)
    (available : ∃x y,f x≠0 ∧ f y≠0 ∧ color x≠color y) :
    ∃x y,f x≠0 ∧ f y≠0 ∧ color x≠color y ∧
      ∀z,Face x y z → f z≠0 → z=x ∨ z=y := by
  classical
  have exist : ∃d,∃x y,f x≠0 ∧ f y≠0 ∧ color x≠color y ∧ distance x y=d := by
    obtain ⟨x,y,hx,hy,hc⟩:=available
    exact ⟨distance x y,x,y,hx,hy,hc,rfl⟩
  obtain ⟨x,y,hx,hy,hc,hd⟩:=Nat.find_spec exist
  refine ⟨x,y,hx,hy,hc,?_⟩
  intro z face hz
  by_cases zx:z=x
  · exact Or.inl zx
  by_cases zy:z=y
  · exact Or.inr zy
  have lt:=shorter x y z face zx zy
  by_cases cx:color x=color z
  · have cy:color z≠color y:=by simpa only [←cx] using hc
    have lower:=Nat.find_min exist (show distance z y<Nat.find exist by omega)
    exact False.elim (lower ⟨z,y,hz,hy,cy,rfl⟩)
  · have lower:=Nat.find_min exist (show distance x z<Nat.find exist by omega)
    exact False.elim (lower ⟨x,z,hx,hz,cx,rfl⟩)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureTwoColorFace
end
