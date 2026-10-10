import Holant.Certificates.PlatonicQuaternaryExits.Interface

/-! A direct rendering of the three terminal alternatives in Proposition A.26.
The generalized-equality branch records both nonzero endpoint coefficients
and exact vanishing at every other word. -/
namespace Holant.Certificates.PlatonicQuaternaryExits
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section

/-- Pure generalized equality in the literal four-port order. -/
def PureGeneralizedEquality4 (t : Signature ℂ 4) : Prop :=
  t (fun _ => false)≠0 ∧ t (fun _ => true)≠0 ∧
    ∀ x, x≠(fun _ => false) → x≠(fun _ => true) → t x=0

theorem scalar_equality_pure (c : ℂ) (hc : c≠0) :
    PureGeneralizedEquality4 (c • OctahedralSeparator.complexEq4) := by
  refine ⟨?_,?_,?_⟩
  · simpa [OctahedralSeparator.complexEq4] using hc
  · simpa [OctahedralSeparator.complexEq4] using hc
  · intro x h0 h1
    simp [OctahedralSeparator.complexEq4,h0,h1]

/-- Source proposition A.26, with the exact literal q families, the source's
three semantic alternatives, and a bounded actual native network in each branch. -/
theorem all_platonic_quaternary_exits (s : SourceCase) :
    (∃ t : Signature ℂ 4, BoundedRealization s.group s.signature t ∧
      TetrahedralOrientation.EndpointNondegenerateEightVertex t ∧
      ∀ r : Fin 3, (flatten r t).rank=2) ∨
    (∃ t : Signature ℂ 4, BoundedRealization s.group s.signature t ∧
      PureGeneralizedEquality4 t) ∨
    ∃ B : Kernel ℂ, BoundedRealization s.group s.signature
      (OctahedralSeparator.Native.binarySignature B) ∧ Matrix.det (Matrix.of B)≠0 ∧
      ¬s.group (OctahedralSeparator.nativeTransfer B) := by
  rcases platonic_quaternary_exit_certificate s with ⟨t,h,he,hr⟩ | ⟨c,hc,h⟩ | ⟨B,h,hd,ho⟩
  · exact Or.inl ⟨t,h,he,hr⟩
  · exact Or.inr (Or.inl ⟨_,h,scalar_equality_pure c hc⟩)
  · exact Or.inr (Or.inr ⟨B,h,hd,ho⟩)

end
end Holant.Certificates.PlatonicQuaternaryExits
