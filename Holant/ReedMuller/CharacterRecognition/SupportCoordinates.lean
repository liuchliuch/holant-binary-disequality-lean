import Holant.ReedMuller.CharacterRecognition.SupportSelfDual

/-! Logical coordinates remain embedded in the actual self-dual ambient
support. The all-one word is preserved; no freely available basis gadget
or orthogonal change of the actual input tensor is postulated. -/
namespace Holant.ReedMuller.CharacterRecognition
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.AffineRadon
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem exists_automorphism_map_nonzero
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (u v : V) (hu : u≠0) (hv : v≠0) :
    ∃ e : V ≃ₗ[K] V,e u=v := by
  let eu := LinearEquiv.toSpanNonzeroSingleton K V u hu
  let ev := LinearEquiv.toSpanNonzeroSingleton K V v hv
  obtain ⟨e,he⟩ := Submodule.exists_linearEquiv_restrict_eq (eu.symm.trans ev)
  refine ⟨e,?_⟩
  have hh := he (eu 1)
  change ((ev (eu.symm (eu 1))) : V)=e (eu 1 : V) at hh
  rw [eu.symm_apply_apply] at hh
  simpa only [eu,ev,LinearEquiv.toSpanNonzeroSingleton_apply,one_smul] using hh.symm

/-- A literal coordinate equivalence onto the original support direction
which takes the logical all-one word to the physical all-one word. -/
theorem exists_support_coordinates {r : ℕ} (hr : 0<r)
    (U : BinaryCode (2*r)) (hU : SelfDual U) :
    ∃ e : BinaryVector r ≃ₗ[ZMod 2] U,
      (e (ones r) : BinaryVector (2*r))=ones (2*r) := by
  have hRank : Module.finrank (ZMod 2) U=r := by
    have hh := selfDual_half_dimension U hU
    omega
  let e0 : BinaryVector r ≃ₗ[ZMod 2] U :=
    LinearEquiv.ofFinrankEq _ _ (by simp [BinaryVector,hRank])
  let u : U := e0 (ones r)
  let v : U := ⟨ones (2*r),selfDual_ones U hU⟩
  have hu : u≠0 := by
    intro hz
    apply ones_ne_zero hr
    exact e0.injective (by simpa [u] using hz)
  have hv : v≠0 := by
    intro hz
    exact ones_ne_zero (by omega : 0<2*r) (congrArg Subtype.val hz)
  obtain ⟨e,he⟩ := exists_automorphism_map_nonzero (K:=ZMod 2) u v hu hv
  refine ⟨e0.trans e,?_⟩
  exact congrArg Subtype.val he

/-- Every nonzero, non-all-one logical vector gives an actual accessible
physical vector under these coordinates. -/
theorem support_coordinates_accessible {r : ℕ}
    (U : BinaryCode (2*r)) (hU : SelfDual U)
    (e : BinaryVector r ≃ₗ[ZMod 2] U)
    (he : (e (ones r) : BinaryVector (2*r))=ones (2*r))
    (t : BinaryVector r) (ht0 : t≠0) (ht1 : t≠ones r) :
    Accessible (e t : BinaryVector (2*r)) := by
  refine ⟨?_,?_,?_⟩
  · exact (hU (ones (2*r))).mp (selfDual_ones U hU) _ (e t).property
  · intro hz
    apply ht0
    exact e.injective (by apply Subtype.ext;simpa using hz)
  · intro hz
    apply ht1
    exact e.injective (Subtype.ext (hz.trans he.symm))

/-- In particular every single logical coordinate is a physical accessible
direction when there is at least one other coordinate. -/
theorem support_coordinate_basis_accessible {r : ℕ} (hr : 2≤r)
    (U : BinaryCode (2*r)) (hU : SelfDual U)
    (e : BinaryVector r ≃ₗ[ZMod 2] U)
    (he : (e (ones r) : BinaryVector (2*r))=ones (2*r)) (j : Fin r) :
    Accessible (e (unitWord j) : BinaryVector (2*r)) := by
  apply support_coordinates_accessible U hU e he
  · intro hz
    have hh := congrFun hz j
    simp [unitWord_apply] at hh
  · intro hz
    have hw : binaryWeight (unitWord j)=1 := by
      simp [binaryWeight,unitWord_apply,Finset.filter_eq']
    rw [hz] at hw
    have ho : binaryWeight (ones r)=r := by simp [binaryWeight,ones]
    omega

/-- Every two-coordinate sum is also accessible when a third coordinate
exists; the ambient vector is the actual embedded sum. -/
theorem support_coordinate_pair_accessible {r : ℕ} (hr : 3≤r)
    (U : BinaryCode (2*r)) (hU : SelfDual U)
    (e : BinaryVector r ≃ₗ[ZMod 2] U)
    (he : (e (ones r) : BinaryVector (2*r))=ones (2*r))
    (j k : Fin r) (hjk : j≠k) :
    Accessible (e (unitWord j+unitWord k) : BinaryVector (2*r)) := by
  apply support_coordinates_accessible U hU e he
  · intro hz
    have hw := weight_pair j k hjk
    rw [hz] at hw
    simp [binaryWeight] at hw
  · intro hz
    have hw := weight_pair j k hjk
    rw [hz] at hw
    have ho : binaryWeight (ones r)=r := by simp [binaryWeight,ones]
    omega

end
end Holant.ReedMuller.CharacterRecognition
