import Holant.Proofs.Reductions.EightVertexNonexception.NativeChain
import Holant.Proofs.Hardness.FiveSupportEOOrdering

/-! A genuinely eight-vertex cancellation branch. The two original copies are
joined by two native X edges. Cancellation of b+y removes both corner outputs;
four mandatory nonzero entries and at least one further entry yield a five-
or six-supported EO tensor. Every hypothesis is a literal original coefficient
condition. In particular no generated hardness or gadget-access premise occurs. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexCancellationLocal
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.EightVertexNonexception
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K]

/-- This condition includes fully eight-supported tensors; original corners
need not vanish, and no relation between their two individual values is imposed. -/
structure Applicable (M : Signature K 4) : Prop where
  even : EvenSupport M
  cancel : (entries M).b + (entries M).y = 0
  outer : (entries M).a * (entries M).x + (entries M).b^2 ≠ 0
  c : (entries M).c ≠ 0
  z : (entries M).z ≠ 0
  sum : (entries M).w + (entries M).d ≠ 0
  additional : (entries M).c * (entries M).z + (entries M).d^2 ≠ 0 ∨
    (entries M).c * (entries M).z + (entries M).w^2 ≠ 0

def output (M : Signature K 4) : Signature K 4 := table (chainEntries (entries M))

/-- The original a*x is retained: there is no corner normalization. -/
theorem output_entries (M : Signature K 4) (h : (entries M).b+(entries M).y=0) :
    entries (output M) =
      ⟨0,(entries M).a*(entries M).x+(entries M).b^2,
        (entries M).c*((entries M).w+(entries M).d),
        (entries M).c*(entries M).z+(entries M).d^2,
        (entries M).c*(entries M).z+(entries M).w^2,
        (entries M).z*((entries M).w+(entries M).d),
        (entries M).a*(entries M).x+(entries M).b^2,0⟩ := by
  have hy : (entries M).y = -(entries M).b := by linear_combination h
  change chainEntries (entries M) = _
  apply Entries.ext <;> simp only [chainEntries,hy] <;> ring

theorem output_eo (M : Signature K 4) (h : (entries M).b+(entries M).y=0) :
    DenseEOUnitLocal.EOSupport (output M) := by
  intro x hx
  rw [Holant.EightVertex.ProductAnchor.weight_four] at hx
  have h' : (entries M).y+(entries M).b=0 := by simpa only [add_comm] using h
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals try norm_num [h0,h1,h2,h3] at hx
  all_goals simp [output,table,chainEntries,h0,h1,h2,h3,h,h']

/-- The finite branch is derived from the original coefficients. Both optional
entries may individually cancel, but they are not both zero in this region. -/
theorem output_middle_or_five (M : Signature K 4) (h : Applicable M) :
    DenseEOUnitLocal.NonzeroMiddle (output M) ∨
      FiveSupportEOOrdering.ExactlyFive (output M) := by
  classical
  have hc := mul_ne_zero h.c h.sum
  have hz := mul_ne_zero h.z h.sum
  by_cases hd : (entries M).c*(entries M).z+(entries M).d^2=0
  · right
    have hw : (entries M).c*(entries M).z+(entries M).w^2≠0 := h.additional.resolve_left (not_not_intro hd)
    apply (FiveSupportEOOrdering.exactlyFive_iff _).mpr
    right; right; left
    rw [output_entries M h.cancel]
    exact ⟨h.outer,hc,hd,hw,hz,h.outer⟩
  · by_cases hw : (entries M).c*(entries M).z+(entries M).w^2=0
    · right
      apply (FiveSupportEOOrdering.exactlyFive_iff _).mpr
      right; right; right; left
      rw [output_entries M h.cancel]
      exact ⟨h.outer,hc,hd,hw,hz,h.outer⟩
    · left
      unfold DenseEOUnitLocal.NonzeroMiddle
      rw [output_entries M h.cancel]
      exact ⟨h.outer,hc,hd,hw,hz,h.outer⟩

abbrev template : Template := chainTemplate

theorem valid : template.WellFormed 1 1 (fun _=>4) := chainTemplate_wellFormed

theorem counts : template.vertices.length=2 ∧ template.edges.length=2 :=
  ⟨chainTemplate_vertices,chainTemplate_edges⟩

theorem template_denote (M : Signature K 4) (he : EvenSupport M) :
    (template.network valid (fun _ : Fin 1=>M)
      (fun _ : Fin 1=>Signature.disequality)).denote=output M := by
  rw [chainTemplate_denote,nativeChain_entries M he]
  rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexCancellationLocal
