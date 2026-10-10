import Holant.Proofs.Closure.ClosureMarkedDihedral
import Holant.Proofs.Closure.ClosureMarkedReversal

/-! Finite SEMANTIC marked overgroup. The actual group is normalized by Z,
so adjoining that coordinate mark needs at most its two cosets. This is not
an augmented gadget palette: Z obtains no label, access programme or oracle.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedReversalOvergroup
open Holant
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosureMarkedReversal

namespace Involution
variable {Γ : Type*} [Group Γ]
variable (H : Subgroup Γ) (z : Γ) (hz : z*z=1)
variable (hc : ∀ q ∈ H, z*q*z ∈ H)

/-- The two actual cosets; they may coincide when the mark is already actual. -/
def adjoin : Subgroup Γ where
  carrier := {q | q ∈ H ∨ ∃ r ∈ H, q=z*r}
  one_mem' := Or.inl H.one_mem
  mul_mem' := by
    rintro p q (hp | ⟨r,hr,rfl⟩) (hq | ⟨s,hs,rfl⟩)
    · exact Or.inl (H.mul_mem hp hq)
    · right
      refine ⟨(z*p*z)*s,H.mul_mem (hc p hp) hs,?_⟩
      calc p*(z*s) = (z*z)*p*(z*s) := by rw [hz,one_mul]
           _ = z*((z*p*z)*s) := by group
    · exact Or.inr ⟨r*q,H.mul_mem hr hq,mul_assoc _ _ _⟩
    · left
      change (z*r)*(z*s) ∈ H
      have he : (z*r)*(z*s) = (z*r*z)*s := by group
      rw [he]
      exact H.mul_mem (hc r hr) hs
  inv_mem' := by
    rintro p (hp | ⟨r,hr,rfl⟩)
    · exact Or.inl (H.inv_mem hp)
    · right
      have hzi : z⁻¹=z := inv_eq_of_mul_eq_one_right hz
      refine ⟨z*r⁻¹*z,hc r⁻¹ (H.inv_mem hr),?_⟩
      rw [mul_inv_rev,hzi]
      calc r⁻¹*z = (z*z)*(r⁻¹*z) := by rw [hz,one_mul]
           _ = z*(z*r⁻¹*z) := by group

theorem contains_actual : H ≤ adjoin H z hz hc := fun _ h => Or.inl h

theorem contains_mark : z ∈ adjoin H z hz hc := Or.inr ⟨1,H.one_mem,(mul_one z).symm⟩

/-- Smallest semantic group containing the actual group and the coordinate mark. -/
theorem generated : adjoin H z hz hc = Subgroup.closure (insert z (H : Set Γ)) := by
  apply le_antisymm
  · rintro q (hq | ⟨r,hr,rfl⟩)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem z hq)
    · exact (Subgroup.closure _).mul_mem (Subgroup.subset_closure (Set.mem_insert z _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem z hr))
  · rw [Subgroup.closure_le]
    intro q hq
    rcases hq with he | hq
    · rw [he]
      exact contains_mark H z hz hc
    · exact contains_actual H z hz hc hq

def cover : Bool × H → adjoin H z hz hc := fun p => if p.1 then
  ⟨z*p.2,Or.inr ⟨p.2,p.2.property,rfl⟩⟩ else ⟨p.2,Or.inl p.2.property⟩

theorem cover_surjective : Function.Surjective (cover H z hz hc) := by
  rintro ⟨q,hq | ⟨r,hr,rfl⟩⟩
  · exact ⟨(false,⟨q,hq⟩),rfl⟩
  · exact ⟨(true,⟨r,hr⟩),rfl⟩

theorem finite [Finite H] : Finite (adjoin H z hz hc) :=
  Finite.of_surjective (cover H z hz hc) (cover_surjective H z hz hc)

theorem cardinal [Finite H] : Nat.card (adjoin H z hz hc) ≤ 2*Nat.card H := by
  have h := Nat.card_le_card_of_surjective (cover H z hz hc) (cover_surjective H z hz hc)
  simpa only [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_bool] using h

end Involution
variable {L : Type*} [Field L]

/-- Constructed semantic extension of the real current complete group. -/
def semanticOvergroup (F : SignatureFamily L) (hτ : ResidualTorsion F) : Subgroup (PGL2 L) :=
  Involution.adjoin (completeGroup F hτ) nativeZClass
    (by simpa only [pow_two] using (nativeZClass_square (L:=L)))
    (fun _ h => completeGroup_conjugateZ F hτ h)

theorem actual_le (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    completeGroup F hτ ≤ semanticOvergroup F hτ := Involution.contains_actual _ _ _ _

theorem mark_mem (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    nativeZClass ∈ semanticOvergroup F hτ := Involution.contains_mark _ _ _ _

theorem semantic_generated (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    semanticOvergroup F hτ = Subgroup.closure (insert nativeZClass (completeGroup F hτ : Set (PGL2 L))) :=
  Involution.generated _ _ _ _

theorem semantic_finite (F : SignatureFamily L) (hτ : ResidualTorsion F) [Finite (completeGroup F hτ)] :
    Finite (semanticOvergroup F hτ) := Involution.finite _ _ _ _

theorem semantic_cardinal (F : SignatureFamily L) (hτ : ResidualTorsion F) [Finite (completeGroup F hτ)] :
    Nat.card (semanticOvergroup F hτ) ≤ 2*Nat.card (completeGroup F hτ) :=
  Involution.cardinal _ _ _ _

namespace Ambient
open Holant.Tractable Holant.Marked
open Holant.LocalDrafts.MainChain.RingHomRealization
open ClosureMarkedDihedral.Source
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
variable [NumberField L]

theorem native_mark : (ClosureMarkedReversal.nativeZClass (L:=ℂ)) = zClass := by
  apply congrArg (pglMk ℂ)
  apply Units.ext
  ext a b
  cases a <;> cases b <;> simp [nativeZGL,nativeZ,zGL,diagonalGL,diagonal]

def overgroup (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F) : Subgroup (PGL2 ℂ) :=
  semanticOvergroup (mapFamily (complexEmbedding φ) F)
    (ClosureFieldBridgeGroups.mappedTorsion (complexEmbedding φ) F hτ)

/-- The ambient actual group retains the universal mark-normalizer invariant. -/
theorem actual_normalizedZ (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    zClass ∈ Subgroup.normalizer (group φ F hτ : Set (PGL2 ℂ)) := by
  rw [← native_mark]
  exact completeGroup_normalizedZ _ _

/-- The semantic overgroup contains Pauli X,Z, with ONLY X's actuality
obtained from retained I. Z is still only an adjoined semantic mark. -/
theorem pauli_le (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hI : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F) :
    pauliSubgroup ≤ overgroup φ F hτ := by
  change Subgroup.closure ({xClass,zClass} : Set (PGL2 ℂ)) ≤ overgroup φ F hτ
  rw [Subgroup.closure_le]
  rintro q (rfl | hq)
  · exact actual_le _ _ (nativeX_mem φ F hτ hI)
  · have he : q = zClass := Set.mem_singleton_iff.mp hq
    subst q
    rw [← native_mark]
    exact mark_mem _ _

theorem finite (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    Finite (overgroup φ F hτ) := by
  letI := ClosureFieldBridgeGroups.actualFiniteGroup (complexEmbedding φ) F hτ
  exact semantic_finite _ _

/-- Original-field cardinal accounting survives the semantic extension. -/
theorem cardinal_original (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    Nat.card (overgroup φ F hτ) ≤ 2*Nat.card (completeGroup F hτ) := by
  letI := ClosureFieldBridgeGroups.actualFiniteGroup (complexEmbedding φ) F hτ
  have h := semantic_cardinal (mapFamily (complexEmbedding φ) F)
    (ClosureFieldBridgeGroups.mappedTorsion (complexEmbedding φ) F hτ)
  rw [ClosureFieldBridgeGroups.completeGroup_card (complexEmbedding φ) F hτ] at h
  exact h

theorem cardinal_source_bound (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    Nat.card (overgroup φ F hτ) ≤ 2*sourceGroupBound (Module.finrank ℚ L) :=
  (cardinal_original φ F hτ).trans
    (Nat.mul_le_mul_left 2 (completeGroup_card_le_sourceBound F hτ))

/-- The semantic marked overgroup cannot be routed to a cyclic model because
it contains the genuine frozen Pauli Klein-four subgroup. -/
theorem noncyclic (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hI : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F) :
    ¬ IsCyclic (overgroup φ F hτ) := by
  intro hc
  letI := hc
  have hp : IsCyclic pauliSubgroup := Subgroup.isCyclic_of_le (pauli_le φ F hτ hI)
  exact IsKleinFour.not_isCyclic hp

end Ambient
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedReversalOvergroup
end
