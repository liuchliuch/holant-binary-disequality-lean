import Holant.ReedMuller.TwoChart.Relation

/-! The exact finite fibers of the genuine localizer relation. Every retained
output has one S-coordinate and precisely the original J-translation fiber. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n m : ℕ}

 theorem relation_coset_iff (S J : BinaryCode n) (phi : S ≃ₗ[ZMod 2] BinaryVector m)
    (p x : BinaryVector n) (y : BinaryVector m) :
    joinVector x y-joinVector p 0∈relationCode S J phi ↔
      x-p-(phi.symm y).val∈J := by
  rw [←join_sub,sub_zero]
  constructor
  · rintro ⟨⟨s,j⟩,he⟩
    have hR := congrArg rightVector he
    have hs : s=phi.symm y := by
      apply phi.injective
      simpa only [relationMap,LinearMap.coe_mk,AddHom.coe_mk,right_join,
        LinearEquiv.apply_symm_apply] using hR
    have hL := congrArg leftVector he
    simp only [relationMap,LinearMap.coe_mk,AddHom.coe_mk,left_join] at hL
    have hj : x-p-(phi.symm y).val=j.val := by rw [←hL,hs];abel
    rw [hj]
    exact j.property
  · intro hx
    refine ⟨⟨phi.symm y,⟨x-p-(phi.symm y).val,hx⟩⟩,?_⟩
    change joinVector ((phi.symm y).val+(x-p-(phi.symm y).val)) (phi (phi.symm y))=joinVector (x-p) y
    rw [LinearEquiv.apply_symm_apply]
    congr 1
    abel

 def relationFiberEquiv (S J : BinaryCode n) (phi : S ≃ₗ[ZMod 2] BinaryVector m)
    (p : BinaryVector n) (y : BinaryVector m) :
    J ≃ {x : BinaryVector n // joinVector x y-joinVector p 0∈relationCode S J phi} where
  toFun j := ⟨p+(phi.symm y).val+j.val,by
    apply (relation_coset_iff S J phi p _ y).mpr
    have h : p+(phi.symm y).val+j.val-p-(phi.symm y).val=j.val := by abel
    rw [h]
    exact j.property⟩
  invFun x := ⟨x.val-p-(phi.symm y).val,(relation_coset_iff S J phi p x.val y).mp x.property⟩
  left_inv j := by apply Subtype.ext;dsimp;abel
  right_inv x := by apply Subtype.ext;dsimp;abel

 theorem relation_fiber_sum {K : Type*} [AddCommMonoid K]
    (S J : BinaryCode n) (phi : S ≃ₗ[ZMod 2] BinaryVector m)
    (p : BinaryVector n) (y : BinaryVector m) (f : BinaryVector n → K) :
    (∑ x : BinaryVector n,if joinVector x y-joinVector p 0∈relationCode S J phi then f x else 0)=
      ∑ j : J,f (p+(phi.symm y).val+j.val) := by
  rw [←Finset.sum_filter]
  rw [Finset.sum_subtype (p:=fun x => joinVector x y-joinVector p 0∈relationCode S J phi)
    _ (by intro x;simp) f]
  exact (Fintype.sum_equiv (relationFiberEquiv S J phi p y).symm _ _ (by
    intro x
    dsimp [relationFiberEquiv]
    congr 1
    abel))

end
end Holant.ReedMuller.TwoChart
