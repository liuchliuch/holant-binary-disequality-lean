import Holant.Proofs.Closure.ClosureSourceRowsC2GroupFacts
import Holant.Proofs.Closure.ClosureSourceRowsMatching

/-! The genuine literal order-two complete-group branch. Retained I supplies
the distinguished nonidentity X transfer; finite cardinality two therefore
forces every actual source binary onto the literal I/native-X lines.
No row classifier or row-card condition is an input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open Holant Holant.Algebraic Holant.Tractable
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.OpenNetworkComposition
variable {L : Type*} [Field L]

variable [NumberField L]

/-- This cardinality branch is a finite test of the actual complete group.
It cannot mistake another group's row label for the current source group. -/
theorem c2_key_cases (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) (hcard : Nat.card (completeGroup F torsion) = 2)
    (j : completeGroup F torsion) : j = 1 ∨ j = markedKey F torsion hI := by
  classical
  letI := completeGroup_finite F torsion
  letI := Fintype.ofFinite (completeGroup F torsion)
  by_cases hj : j = 1
  · exact Or.inl hj
  by_cases hk : j = markedKey F torsion hI
  · exact Or.inr hk
  have hmark := markedKey_ne_one F torsion hI
  have hthree : ({1,markedKey F torsion hI,j} : Finset (completeGroup F torsion)).card = 3 := by
    simp [hj,hk,hmark,Ne.symm hj,Ne.symm hk,Ne.symm hmark]
  have hbound := Finset.card_le_univ ({1,markedKey F torsion hI,j} : Finset (completeGroup F torsion))
  rw [hthree] at hbound
  rw [Nat.card_eq_fintype_card] at hcard
  omega

def originalC2Binary (p : Bool) : Binary (K:=L) := if p then X else 1

/-- Every actual nonsingular source binary is covered, with its exact unit
in the ORIGINAL field. This conclusion is not a row membership hypothesis. -/
theorem c2_actual_binary (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) (hcard : Nat.card (completeGroup F torsion) = 2)
    (B : Binary (K:=L)) (hB : ActualNonsingular F B) :
    ∃ p : Bool, ∃ c : L, c ≠ 0 ∧ B = c • originalC2Binary p := by
  obtain ⟨j,c,hc,he⟩ := actual_binary_eq_representative F torsion B hB
  rcases c2_key_cases F torsion hI hcard j with hj | hj
  · refine ⟨true,c,hc,?_⟩
    rw [he,hj,actualRepresentative_one]
    rfl
  · obtain ⟨d,hd,hm⟩ := representative_marked F torsion hI
    refine ⟨false,c*d,mul_ne_zero hc hd,?_⟩
    rw [he,hj,hm,smul_smul]
    rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
