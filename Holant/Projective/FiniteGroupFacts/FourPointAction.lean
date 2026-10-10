import Holant.Certificates.RainbowOrbit.GroupRepresentatives
import Holant.Projective.FiniteGroupFacts.PlatonicOrders

/-! A faithful four-coset action of the actual octahedral multiplication table.
The table's multiplication is already tied to the literal complex matrices;
`fourPermutation_product` supplies the remaining group-law semantics. -/
namespace Holant.Projective.FiniteGroupFacts
open Holant.Certificates.RainbowOrbit
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 100000

def fourAction : Fin 24 → Fin 4 → Fin 4 :=
  ![![0,1,2,3],![1,0,3,2],![2,3,0,1],![3,2,1,0],![0,3,1,2],![2,0,1,3],![1,3,2,0],![2,1,3,0],![3,1,0,2],![3,0,2,1],![1,2,0,3],![0,2,3,1],![3,2,0,1],![2,3,1,0],![1,2,3,0],![3,0,1,2],![2,0,3,1],![1,3,0,2],![3,1,2,0],![0,2,1,3],![2,1,0,3],![0,3,2,1],![1,0,2,3],![0,1,3,2]]

def fourInverse : Fin 24 → Fin 4 → Fin 4 :=
  ![![0,1,2,3],![1,0,3,2],![2,3,0,1],![3,2,1,0],![0,2,3,1],![1,2,0,3],![3,0,2,1],![3,1,0,2],![2,1,3,0],![1,3,2,0],![2,0,1,3],![0,3,1,2],![2,3,1,0],![3,2,0,1],![3,0,1,2],![1,2,3,0],![1,3,0,2],![2,0,3,1],![3,1,2,0],![0,2,1,3],![2,1,0,3],![0,3,2,1],![1,0,2,3],![0,1,3,2]]

theorem four_inverse_left : ∀ g x, fourInverse g (fourAction g x) = x := by decide +kernel
theorem four_inverse_right : ∀ g x, fourAction g (fourInverse g x) = x := by decide +kernel

def fourPermutation (g : Fin 24) : Equiv.Perm (Fin 4) where
  toFun := fourAction g
  invFun := fourInverse g
  left_inv := four_inverse_left g
  right_inv := four_inverse_right g

theorem four_action_faithful : ∀ g h, (∀ x, fourAction g x = fourAction h x) → g = h := by
  decide +kernel

theorem four_action_product : ∀ g h x,
    fourAction (octahedralProductIndex g h) x = fourAction g (fourAction h x) := by
  decide +kernel

theorem four_action_even : ∀ g : Fin 24,
    (fourPermutation g).sign = 1 ↔ g.val < 12 := by decide +kernel

theorem fourPermutation_injective : Function.Injective fourPermutation := by
  intro g h he
  exact four_action_faithful g h (fun x => congrArg (fun p : Equiv.Perm (Fin 4) => p x) he)

theorem fourPermutation_product (g h : Fin 24) :
    fourPermutation (octahedralProductIndex g h) = fourPermutation g * fourPermutation h := by
  apply Equiv.ext
  intro x
  exact four_action_product g h x

theorem fourPermutation_bijective : Function.Bijective fourPermutation := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨fourPermutation_injective, by simp [Fintype.card_perm, Nat.factorial]⟩

noncomputable def indexSymmetricEquiv : Fin 24 ≃ S4 :=
  Equiv.ofBijective fourPermutation fourPermutation_bijective

def tetrahedralAlternatingAction (g : Fin 12) : A4 :=
  ⟨fourPermutation (g.castAdd 12), (four_action_even _).mpr g.isLt⟩

theorem tetrahedralAlternatingAction_injective : Function.Injective tetrahedralAlternatingAction := by
  intro g h he
  have hp := fourPermutation_injective (congrArg Subtype.val he)
  exact Fin.ext (congrArg (fun k : Fin 24 => k.val) hp)

theorem tetrahedralAlternatingAction_bijective : Function.Bijective tetrahedralAlternatingAction := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨tetrahedralAlternatingAction_injective, by rw [card_alternatingGroup]; decide⟩

noncomputable def indexTetrahedralEquiv : Fin 12 ≃ A4 :=
  Equiv.ofBijective tetrahedralAlternatingAction tetrahedralAlternatingAction_bijective

theorem tetrahedralAlternatingAction_product (g h : Fin 12) :
    tetrahedralAlternatingAction (tetrahedralProductIndex g h) =
      tetrahedralAlternatingAction g * tetrahedralAlternatingAction h := by
  apply Subtype.ext
  change fourPermutation (Fin.castAdd 12 (tetrahedralProductIndex g h)) = _
  have he : ∀ g h : Fin 12,
      Fin.castAdd 12 (tetrahedralProductIndex g h) =
        octahedralProductIndex (Fin.castAdd 12 g) (Fin.castAdd 12 h) := by decide +kernel
  rw [he]
  exact fourPermutation_product _ _

end Holant.Projective.FiniteGroupFacts
