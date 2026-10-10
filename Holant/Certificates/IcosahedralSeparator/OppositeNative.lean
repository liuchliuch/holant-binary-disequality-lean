import Holant.Certificates.IcosahedralSeparator.Opposite

/-! Actual native-X networks in the opposite display. Their resource family
contains the original ancestor and actual safe opposite-group binary vertices. -/
namespace Holant.Certificates.IcosahedralSeparator.Opposite
open Holant Holant.Certificates.MatchingProductBridge
open Holant.Certificates.OppositeIcosahedral
open Holant.Certificates.OctahedralSeparator.Native (binarySignature pairVertex legVertex dressed_realizes sparse_realizes)
noncomputable section
set_option backward.isDefEq.respectTransparency false

def resources (h : Signature ℂ 6) : SignatureFamily ℂ :=
  {s | s = ⟨6,h⟩ ∨ ∃ U : Matrix Bool Bool ℂ,
    Direction (U*OppositeIcosahedral.X) ∧ s = ⟨2,binarySignature U⟩}

theorem pair_available (K : Matrix Bool Bool ℂ) (hK : Direction K) :
    Direction (Matrix.of (pairVertex K)*OppositeIcosahedral.X) := by
  have he : Matrix.of (pairVertex K)*OppositeIcosahedral.X = OppositeIcosahedral.X*K := by
    ext a b
    cases a <;> cases b <;> simp [pairVertex,OppositeIcosahedral.X,Matrix.mul_apply,Signature.disequality]
  rw [he]
  exact OppositeIcosahedral.direction_X.mul hK

theorem leg_equality_available :
    Direction (Matrix.of (legVertex Signature.equality)*OppositeIcosahedral.X) := by
  have he : Matrix.of (legVertex Signature.equality)*OppositeIcosahedral.X = Matrix.of Q0 := by
    ext a b
    cases a <;> cases b <;> simp [legVertex,Kernel.mul,OppositeIcosahedral.X,Q0,
      Matrix.mul_apply,Signature.equality,Signature.disequality]
  rw [he]
  exact Direction.of_tetrahedral (quaternion_axis_direction .tetrahedral 0)

theorem first_realizes (h : Signature ℂ 6) (K : Matrix Bool Bool ℂ) (hK : Direction K) :
    Gadget.Realizes (resources h) .disequality (Signature.contract K h) := by
  have hr := dressed_realizes h K (fun _ => Signature.equality)
  rw [Signature.coordinateAction_equality] at hr
  apply hr.mono
  rintro s (rfl | rfl | ⟨j,rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨_,pair_available K hK,rfl⟩
  · exact Or.inr ⟨_,leg_equality_available,rfl⟩

theorem sequential_realizes (h : Signature ℂ 6) (K L : Matrix Bool Bool ℂ)
    (hK : Direction K) (hL : Direction L) :
    Gadget.Realizes (resources h) .disequality (Signature.contract L (Signature.contract K h)) := by
  have hid : (![Signature.equality,Signature.equality,Signature.equality,Signature.equality] : Fin 4 → Binary) =
      fun _ => Signature.equality := by funext j; fin_cases j <;> rfl
  have hr := sparse_realizes h K Signature.equality Signature.equality L
  rw [hid,Signature.coordinateAction_equality] at hr
  apply hr.mono
  rintro s (rfl | rfl | rfl | rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr ⟨_,pair_available K hK,rfl⟩
  · exact Or.inr ⟨_,leg_equality_available,rfl⟩
  · exact Or.inr ⟨_,leg_equality_available,rfl⟩
  · exact Or.inr ⟨_,pair_available L hL,rfl⟩

end
end Holant.Certificates.IcosahedralSeparator.Opposite
