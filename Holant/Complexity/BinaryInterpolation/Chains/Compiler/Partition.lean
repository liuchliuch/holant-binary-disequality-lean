import Holant.Complexity.BinaryInterpolation.Chains.Compiler.Validated
import Holant.Complexity.FixedGadgetSubstitution.Partition

/-! Partition-function semantics of the actual variable-length machine output.
The source family is evaluated on the original encoded graph. The local
template identities are supplied by explicitTemplate_denote/scaled and the
original-label corolla identity, with no extra graph correctness hypothesis.
-/
namespace Holant.Complexity.BinaryInterpolation.Chains.Compiler.Validated
open FixedGadgetSubstitution RawClosedNetwork
set_option backward.isDefEq.respectTransparency false

theorem sourceArity_eq {s b : ℕ} (arity : ℕ → ℕ) (label : Fin s) (edge : Fin b) (k : ℕ) :
    sourceArity (Occurrence.templates (extendedArity s arity) s label.val edge.val k) =
      extendedArity s arity := by
  funext i
  by_cases h : i = s <;>
    simp [sourceArity,Occurrence.templates,h,explicitTemplate,identityTemplate,extendedArity]

theorem raw_denote_congr {K : Type} [CommSemiring K] {s b : ℕ} {arity : ℕ → ℕ}
    (r q : RawClosedNetwork) (hr : r.WellFormed s b arity) (hq : q.WellFormed s b arity)
    (he : r = q) (signatures : (i : Fin s) → Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) :
    (r.realize hr signatures kernels).denote Fin.elim0 =
      (q.realize hq signatures kernels).denote Fin.elim0 := by
  cases he
  rfl

variable {K : Type} [Field K] {s b : ℕ} (arity : ℕ → ℕ)
variable (label : Fin s) (hlabel : arity label.val = 2) (edge : Fin b)

theorem source_valid (x : Occurrence.Input (s + 1) b (extendedArity s arity)) :
    x.2.val.WellFormed (s + 1) b
      (sourceArity (Occurrence.templates (extendedArity s arity) s label.val edge.val x.1)) := by
  rw [sourceArity_eq]
  exact x.2.property

theorem partition (x : Occurrence.Input (s + 1) b (extendedArity s arity))
    (source : (i : Fin (s + 1)) → Signature K
      (sourceArity (Occurrence.templates (extendedArity s arity) s label.val edge.val x.1) i.val))
    (signatures : (i : Fin s) → Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) (scale : K)
    (hdenote : ∀ i : Fin (s + 1),
      ((Occurrence.templates (extendedArity s arity) s label.val edge.val x.1 i.val).network
        (template_hypotheses arity label hlabel edge x.1 i.val i.isLt).1 signatures kernels).denote =
      (if i.val = s then scale else 1) • source i) :
    ((value arity label hlabel edge x).val.realize (value arity label hlabel edge x).property
      signatures kernels).denote Fin.elim0 =
      scale ^ occurrences s x.2.val *
        (x.2.val.realize (source_valid arity label edge x) source kernels).denote Fin.elim0 := by
  let ts := Occurrence.templates (extendedArity s arity) s label.val edge.val x.1
  have hr := source_valid arity label edge x
  have hg : ∀ i < s + 1, (ts i).WellFormed s b arity :=
    fun i hi => (template_hypotheses arity label hlabel edge x.1 i hi).1
  have he := Occurrence.raw_eq_replace (s + 1) b (extendedArity s arity) s label.val edge.val x
  exact (raw_denote_congr _ _ (value arity label hlabel edge x).property
    (query_wellFormed ts x.2.val hr hg) he signatures kernels).trans
      (replacement_scale_power ts x.2.val hr hg source signatures kernels s scale hdenote)

theorem projective_partition (x : Occurrence.Input (s + 1) b (extendedArity s arity))
    (source : (i : Fin (s + 1)) → Signature K
      (sourceArity (Occurrence.templates (extendedArity s arity) s label.val edge.val x.1) i.val))
    (signatures : (i : Fin s) → Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) (c : K)
    (hdenote : ∀ i : Fin (s + 1),
      ((Occurrence.templates (extendedArity s arity) s label.val edge.val x.1 i.val).network
        (template_hypotheses arity label hlabel edge x.1 i.val i.isLt).1 signatures kernels).denote =
      (if i.val = s then c ^ (x.1 + 1) else 1) • source i) :
    ((value arity label hlabel edge x).val.realize (value arity label hlabel edge x).property
      signatures kernels).denote Fin.elim0 =
      c ^ ((x.1 + 1) * occurrences s x.2.val) *
        (x.2.val.realize (source_valid arity label edge x) source kernels).denote Fin.elim0 := by
  simpa only [pow_mul] using
    partition arity label hlabel edge x source signatures kernels (c ^ (x.1 + 1)) hdenote

end Holant.Complexity.BinaryInterpolation.Chains.Compiler.Validated
