import Holant.Proofs.Closure.ClosureMarkedShiftConjugator

/-! NEW POST-RECOVERY SOURCE; fresh strict verification is required.
The shifted A parameters are derived from the ACTUAL original-field branch:
retained equality, native-X centralizer, noncyclicity, nonsmall group and actual
native-Z absence. No phase, square root, conjugator or desired model is input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedShiftParameters
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open ClosureMarkedDihedral.Source
open ClosureMarkedShiftReflection
open ClosureMarkedShiftConjugator.Reflection
variable {L : Type*} [Field L] [NumberField L]

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedShiftParameters

namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedShiftReflection.Reflection
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open ClosureMarkedDihedral.Source
variable {L : Type*} [Field L] [NumberField L]
variable {φ : L →+* Scalar} {F : SignatureFamily L} {hτ : ResidualTorsion F}
variable (R : ClosureMarkedShiftReflection.Reflection φ F hτ)

theorem rotation_even
    (hI : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F) :
    Even (Nat.card R.rotations) := by
  let H := group φ F hτ
  let H0 := ClosureMarkedCyclic.normalized H
  letI : Finite H := ClosureFieldBridgeGroups.actualFiniteGroup (complexEmbedding φ) F hτ
  let e := H.equivMapOfInjective ClosureMarkedCyclic.normalize.toMonoidHom
    ClosureMarkedCyclic.normalize.injective
  letI : Finite H0 := Finite.of_equiv H e.toEquiv
  letI : Finite R.rotations := Finite.of_injective
    (Subgroup.inclusion (show R.rotations ≤ H0 from inf_le_left))
    (Subgroup.inclusion_injective _)
  have hz : zClass ∈ R.rotations :=
    ⟨⟨xClass,nativeX_mem φ F hτ hI,ClosureMarkedCyclic.nativeX_to_Z⟩,
      by rw [← Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers.torus_neg_one]; exact ⟨-1,rfl⟩⟩
  have h := orderOf_dvd_natCard (⟨zClass,hz⟩ : R.rotations)
  rw [Subgroup.orderOf_mk,zClass_involution] at h
  exact even_iff_two_dvd.mpr h


theorem selected_even
    (hI : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F)
    (hX : group φ F hτ ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (h2 : Nat.card (group φ F hτ) ≠ 2) (h4 : Nat.card (group φ F hτ) ≠ 4) :
    Even (R.selected hX h2 h4).m := by
  rw [R.selected_rotation_card]
  exact R.rotation_even hI

theorem selected_range
    (hI : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F)
    (hX : group φ F hτ ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (h2 : Nat.card (group φ F hτ) ≠ 2) (h4 : Nat.card (group φ F hτ) ≠ 4) :
    4 ≤ (R.selected hX h2 h4).m := by
  have hr := (R.selected hX h2 h4).range
  obtain ⟨k,hk⟩ := R.selected_even hI hX h2 h4
  omega

theorem eta_root
    (hX : group φ F hτ ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (h2 : Nat.card (group φ F hτ) ≠ 2) (h4 : Nat.card (group φ F hτ) ≠ 4) :
    Roots (2*(R.selected hX h2 h4).m) R.eta := by
  rw [R.selected_rotation_card]
  unfold Roots ClosureMarkedShiftConjugator.Reflection.eta
  rw [← map_pow,R.phase_twice_rotation_card,map_one]

theorem eta_not_root
    (hX : group φ F hτ ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (h2 : Nat.card (group φ F hτ) ≠ 2) (h4 : Nat.card (group φ F hτ) ≠ 4)
    (hZ : zClass ∉ group φ F hτ) : ¬ Roots (R.selected hX h2 h4).m R.eta := by
  rw [R.selected_rotation_card]
  intro he
  apply R.phase_not_rotation_root hZ
  apply φ.injective
  rw [map_pow,map_one]
  exact he

def parameters
    (hI : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F)
    (hX : group φ F hτ ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (h2 : Nat.card (group φ F hτ) ≠ 2) (h4 : Nat.card (group φ F hτ) ≠ 4)
    (hZ : zClass ∉ group φ F hτ) : Parameters (R.selected hX h2 h4).m :=
  .A (R.selected_range hI hX h2 h4) (R.selected_even hI hX h2 h4) R.eta R.square
    (R.eta_root hX h2 h4) (R.eta_not_root hX h2 h4 hZ) R.square_eq

@[simp] theorem parameters_basis
    (hI : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F)
    (hX : group φ F hτ ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (h2 : Nat.card (group φ F hτ) ≠ 2) (h4 : Nat.card (group φ F hτ) ≠ 4)
    (hZ : zClass ∉ group φ F hτ) : (R.parameters hI hX h2 h4 hZ).basis = R.basis := rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedShiftReflection.Reflection

namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedShiftParameters.Reflection
export Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedShiftReflection.Reflection
  (rotation_even selected_even selected_range eta_root eta_not_root parameters parameters_basis)
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedShiftParameters.Reflection

namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedShiftParameters
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open ClosureMarkedDihedral.Source
variable {L : Type*} [Field L] [NumberField L]

/-- Closed branch producer: select the source reflection first, then derive
all marked parameters. The input consists only of genuine actual source guards. -/
def selectedReflection (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hX : group φ F hτ ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (hnc : ¬ IsCyclic (group φ F hτ)) := ClosureMarkedShiftReflection.select φ F hτ hX hnc

def selectedParameters (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hI : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F)
    (hX : group φ F hτ ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (hnc : ¬ IsCyclic (group φ F hτ))
    (h2 : Nat.card (group φ F hτ) ≠ 2) (h4 : Nat.card (group φ F hτ) ≠ 4)
    (hZ : zClass ∉ group φ F hτ) :=
  Reflection.parameters (selectedReflection φ F hτ hX hnc) hI hX h2 h4 hZ

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedShiftParameters
end
