import Holant.Certificates.IcosahedralSeparator.Counts
import Holant.Certificates.OctahedralSeparator.NativeSparse

/-! The normalized maps are literal contractions of reconstructed six-port
tensors. The two-step exit has a native-X network with one original ancestor. -/
namespace Holant.Certificates.IcosahedralSeparator
open Holant Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit
namespace Native
open Holant.Certificates.OctahedralSeparator.Native (binarySignature pairVertex legVertex dressed_realizes sparse_realizes)
noncomputable section
set_option backward.isDefEq.respectTransparency false

def resources (h : Signature ℂ 6) : SignatureFamily ℂ :=
  {s | s = ⟨6,h⟩ ∨ ∃ U : Binary, groupDirection .icosahedral (multiply U X) ∧ s = ⟨2,binarySignature U⟩}

theorem direction_X : groupDirection .icosahedral X := by
  have he : multiply Q0 X = X := by
    funext a b
    cases a <;> cases b <;> simp [multiply,Q0,X,Signature.equality,Signature.disequality]
  simpa only [quaternionBasis,Matrix.cons_val_zero,he] using
    groupDirection_right_X .icosahedral (quaternion_axis_direction .icosahedral 0)

theorem pair_available {K : Binary} (hK : groupDirection .icosahedral K) :
    groupDirection .icosahedral (multiply (pairVertex K) X) := by
  have he : pairVertex K = multiply (multiply X K) X := by
    funext a b
    cases a <;> cases b <;> simp [pairVertex,multiply,X,Signature.disequality]
  rw [he,multiply_X_twice]
  have hm : multiply X K = Matrix.of X * Matrix.of K := multiply_eq_matrix_mul X K
  rw [hm]
  exact groupDirection_mul .icosahedral (U := Matrix.of X) (V := Matrix.of K) direction_X hK

theorem leg_equality_available : groupDirection .icosahedral (multiply (legVertex Signature.equality) X) := by
  have he : multiply (legVertex Signature.equality) X = Q0 := by
    funext a b
    cases a <;> cases b <;> simp [legVertex,Kernel.mul,multiply,X,Q0,Signature.equality,Signature.disequality]
  rw [he]
  exact quaternion_axis_direction .icosahedral 0

theorem first_realizes (h : Signature ℂ 6) (K : Binary) (hK : groupDirection .icosahedral K) :
    Gadget.Realizes (resources h) .disequality (Signature.contract K h) := by
  have hr := dressed_realizes h K (fun _ => Signature.equality)
  rw [Signature.coordinateAction_equality] at hr
  apply hr.mono
  rintro s (rfl | rfl | ⟨j,rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨_,pair_available hK,rfl⟩
  · exact Or.inr ⟨_,leg_equality_available,rfl⟩

theorem sequential_realizes (h : Signature ℂ 6) (K L : Binary)
    (hK : groupDirection .icosahedral K) (hL : groupDirection .icosahedral L) :
    Gadget.Realizes (resources h) .disequality (Signature.contract L (Signature.contract K h)) := by
  have hid : (![Signature.equality,Signature.equality,Signature.equality,Signature.equality] : Fin 4 → Binary) =
      fun _ => Signature.equality := by funext j; fin_cases j <;> rfl
  have hr := sparse_realizes h K Signature.equality Signature.equality L
  rw [hid,Signature.coordinateAction_equality] at hr
  apply hr.mono
  rintro s (rfl | rfl | rfl | rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr ⟨_,pair_available hK,rfl⟩
  · exact Or.inr ⟨_,leg_equality_available,rfl⟩
  · exact Or.inr ⟨_,leg_equality_available,rfl⟩
  · exact Or.inr ⟨_,pair_available hL,rfl⟩

end
end Native

noncomputable section
set_option backward.isDefEq.respectTransparency false

def ancestor (i : Fin 36) : Signature ℂ 6 := TetrahedralBridge.reconstruct (sourceImages i)

theorem uniformOutput_map (i : Fin 30) : sourceMap (i.natAdd 6) uniformKernel = uniformOutput i := by
  simp only [uniformKernel,map_add,map_sub,map_smul,uniformOutput]
  change (goldenRatio : ℂ) • sourceMap (i.natAdd 6) (quaternionBasis (0 : Fin 3).succ) -
    (goldenReciprocal : ℂ) • sourceMap (i.natAdd 6) (quaternionBasis (1 : Fin 3).succ) +
    sourceMap (i.natAdd 6) (quaternionBasis (2 : Fin 3).succ) = _
  simp only [sourceMap_next,high_orderedTuple]

theorem uniformOutput_contract (i : Fin 30) :
    uniformOutput i = Signature.contract uniformKernel (ancestor (i.natAdd 6)) := by
  rw [←uniformOutput_map,sourceMap_contract]
  rfl

end
end Holant.Certificates.IcosahedralSeparator
