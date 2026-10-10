import Holant.Complexity.FixedGadgetSubstitution.RawSemantics
import Holant.Complexity.FixedGadgetSubstitution.Scalar

/-! Exact partition identity for the compiler's literal query bytes, including
the power of a distinguished fixed gadget's nonzero projective normalization. -/
noncomputable section
namespace Holant.Complexity.FixedGadgetSubstitution
open RawClosedNetwork
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [CommSemiring K]
variable {sourceCount s b : ℕ} {arity : ℕ → ℕ}
variable (templates : ℕ → Template) (r : RawClosedNetwork)
variable (hr : r.WellFormed sourceCount b (sourceArity templates))
variable (hg : ∀ label < sourceCount, (templates label).WellFormed s b arity)
variable (source : (i : Fin sourceCount) → Signature K (sourceArity templates i.val))
variable (signatures : (i : Fin s) → Signature K (arity i.val))
variable (kernels : Fin b → Bool → Bool → K)

/-- Every local scale comes from the fixed template's actual denotation. -/
 theorem replacement_partition (scales : Fin sourceCount → K)
    (hdenote : ∀ label : Fin sourceCount,
      ((templates label.val).network (hg label.val label.isLt) signatures kernels).denote =
        scales label • source label) :
    ((replace templates r).realize (query_wellFormed templates r hr hg)
      signatures kernels).denote Fin.elim0 =
      (∏v,scales (r.signatureLabel hr v)) * (r.realize hr source kernels).denote Fin.elim0 := by
  rw [RawSemantics.denote_query templates r hr hg source signatures kernels]
  apply Finite.denote_scaled
  intro v
  exact hdenote (r.signatureLabel hr v)

/-- The exponent is computed from the original raw label stream. It is neither
an input certificate nor a count extracted from the already-replaced query. -/
 theorem replacement_scale_power (label : ℕ) (scale : K)
    (hdenote : ∀ i : Fin sourceCount,
      ((templates i.val).network (hg i.val i.isLt) signatures kernels).denote =
        (if i.val=label then scale else 1) • source i) :
    ((replace templates r).realize (query_wellFormed templates r hr hg)
      signatures kernels).denote Fin.elim0 =
      scale ^ occurrences label r * (r.realize hr source kernels).denote Fin.elim0 := by
  rw [replacement_partition templates r hr hg source signatures kernels
    (fun i => if i.val=label then scale else 1) hdenote]
  exact congrArg (fun c : K => c*(r.realize hr source kernels).denote Fin.elim0)
    (scale_product label scale r)

end Holant.Complexity.FixedGadgetSubstitution
