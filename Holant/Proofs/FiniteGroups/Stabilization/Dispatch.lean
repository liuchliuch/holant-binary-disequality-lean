import Holant.Proofs.FiniteGroups.Stabilization.Termination
import Holant.Proofs.FiniteGroups.Stabilization.QueueExhaustion
import Holant.Proofs.FiniteGroups.Stabilization.RetainedBatch
import Holant.Tractable.Downward


namespace Holant.LocalDrafts.FinitePGL2.Stabilization

open Holant.Tractable
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
noncomputable section
variable {L : Type*} [Field L]

theorem residualTorsion_mono {F G : SignatureFamily L} (hFG : F ⊆ G)
    (hG : ResidualTorsion G) : ResidualTorsion F := by
  intro B hB
  exact hG B ⟨hB.1.mono hFG, hB.2⟩

/-- This witness includes an actual nonsingular binary gadget; no abstract
matrix counterexample or hardness-completeness assumption is substituted. -/
theorem residual_or_actual_infinite (F : SignatureFamily L) :
    ResidualTorsion F ∨
      ∃ B, ActualNonsingular F B ∧ ¬ ProjectivelyFinite (transfer B) := by
  classical
  by_cases h : ResidualTorsion F
  · exact Or.inl h
  · right
    unfold ResidualTorsion at h
    push_neg at h
    exact h

namespace Node

variable {κ : Type*} [NumberField L] [DecidableEq κ]

/-- The two outer exits are derived from retention.  The third branch is
explicitly a same-stratum result; it does not assert unproved token coverage. -/
theorem retained_transition_dispatch (s t : Node L κ) (hret : s.family ⊆ t.family) :
    completeGroup s.family s.torsion < completeGroup t.family t.torsion ∨
    (completeGroup t.family t.torsion = completeGroup s.family s.torsion ∧
      t.core.signature.1 < s.core.signature.1) ∨
    (completeGroup t.family t.torsion = completeGroup s.family s.torsion ∧
      t.core.signature.1 = s.core.signature.1) := by
  have ha := MinimumCore.arity_nonincrease hret s.core t.core
  rcases completeGroup_eq_or_lt hret s.torsion t.torsion with he | hs
  · rcases lt_or_eq_of_le ha with hlt | heq
    · exact Or.inr (Or.inl ⟨he.symm, hlt⟩)
    · exact Or.inr (Or.inr ⟨he.symm, heq⟩)
  · exact Or.inl hs

theorem retained_step_or_same_stratum (s t : Node L κ) (hret : s.family ⊆ t.family) :
    Step t s ∨
      (completeGroup t.family t.torsion = completeGroup s.family s.torsion ∧
        t.core.signature.1 = s.core.signature.1) := by
  rcases retained_transition_dispatch s t hret with hg | ⟨hg, ha⟩ | he
  · exact Or.inl (.group s t hret hg)
  · exact Or.inl (.arity s t hret hg ha)
  · exact Or.inr he

abbrev Runs (s t : Node L κ) : Prop := Relation.ReflTransGen (fun a b => Step b a) s t

theorem lift_queue_run (s : Node L κ) {q q' : FrozenQueue L s.frozen}
    (h : FrozenQueue.Runs q q') : Runs (s.withQueue q) (s.withQueue q') := by
  induction h with
  | refl => exact .refl
  | @tail q' q'' hrun hstep ih =>
      exact ih.tail (Step.local (s.withQueue q') q'' hstep)

/-- Mathematical local progress and termination are both supplied, rather
than requiring a continuation/progress oracle as a premise. -/
theorem local_exhaustion (s : Node L κ) (hv : s.queue.Valid) :
    ∃ t : Node L κ, Runs s t ∧ t.family = s.family ∧
      t.core.signature = s.core.signature ∧ t.queue.todo = ∅ := by
  obtain ⟨q, hrun, he⟩ := FrozenQueue.exists_exhausted s.queue hv
  exact ⟨s.withQueue q, lift_queue_run s hrun, rfl, rfl, he⟩

end Node

/-- A literal retained equality supplies both charge signs over the whole
retained family.  This does not supply the missing factor-extraction cap. -/
theorem equality_excludes_commonOneSided (F : SignatureFamily AlgebraicComplex)
    (hI : (⟨2, binarySignature Signature.equality⟩ : AnySignature AlgebraicComplex) ∈ F) :
    ¬ Holant.Tractable.CommonOneSided F := by
  rintro (hp | hn)
  · have hx : binarySignature (Signature.equality : Bool → Bool → AlgebraicComplex)
        (fun _ => false) ≠ 0 := by simp [binarySignature, Signature.equality]
    have hc := hp ⟨2, binarySignature Signature.equality⟩ hI (fun _ => false) hx
    norm_num [Holant.charge, Holant.weight] at hc
  · have hx : binarySignature (Signature.equality : Bool → Bool → AlgebraicComplex)
        (fun _ => true) ≠ 0 := by simp [binarySignature, Signature.equality]
    have hc := hn ⟨2, binarySignature Signature.equality⟩ hI (fun _ => true) hx
    norm_num [Holant.charge, Holant.weight] at hc

/-- A proved whole-family structural Tract result on a retained successor
pulls back in the same common basis.  No FP or hardness assertion is made. -/
theorem retained_tract_pullback {F G : SignatureFamily AlgebraicComplex}
    (hret : F ⊆ G) (B : InvertibleKernel)
    (hG : Holant.Tractable.Tract (Holant.Tractable.familyAction B G)) :
    Holant.Tractable.Tract (Holant.Tractable.familyAction B F) :=
  hG.mono_family (Holant.Tractable.familyAction_mono B hret)

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
