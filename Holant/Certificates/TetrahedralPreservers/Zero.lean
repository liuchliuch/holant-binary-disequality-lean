import Holant.Certificates.TetrahedralPreservers.RankOneCount

noncomputable section
namespace Holant.Certificates.TetrahedralPreservers
open scoped Matrix

theorem rank_zero_iff (A : End) : A.rank = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hr : LinearMap.range A.mulVecLin = ⊥ :=
      Submodule.finrank_eq_zero.mp h
    have hL : A.mulVecLin = 0 := LinearMap.range_eq_bot.mp hr
    ext i j
    have hv := LinearMap.congr_fun hL (Pi.single j 1)
    have hi := congrFun hv i
    simpa using hi
  · rintro rfl
    exact Matrix.rank_zero

def ZeroPreserver (S : Set V) := {A : End // TwoSided S A ∧ A.rank = 0}

theorem zero_preserver_count (S : Set V) : Nat.card (ZeroPreserver S) = 1 := by
  let e : ZeroPreserver S ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => ⟨0,twoSided_zero S,Matrix.rank_zero⟩
    left_inv := fun A => Subtype.ext ((rank_zero_iff A.val).mp A.property.2).symm
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  simp

theorem external_zero_count : Nat.card (ZeroPreserver External) = 1 := zero_preserver_count External

end Holant.Certificates.TetrahedralPreservers
