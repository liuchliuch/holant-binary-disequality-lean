import Holant.Proofs.BinaryInterpolation.SingularExtraction.PowerGadgets
import Holant.Complexity.BinaryInterpolation.Chains.DirectMacro
import Holant.Tractable.Downward


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open Holant Holant.Tractable Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.BinaryInterpolation.Chains

variable {K : Type*} [Field K] {s : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false

/-- A real ordinary Γ macro, with original labels and exact scale. -/
structure PowerMacro (G : (i : Fin s) → Signature K (arity i.val)) (u : Bool → K) where
  exponent : ℕ
  positive : 0 < exponent
  scale : K
  scale_ne_zero : scale ≠ 0
  network : Network K exponent
  labels : Labelling network.shape s 1 arity
  value : (labels.template.network labels.wellFormed G (fun _ => Signature.disequality)).denote =
    fun x => scale * Signature.unaryPower u exponent x

theorem labelled_powers (G : (i : Fin s) → Signature K (arity i.val))
    (htwo : (2 : K) ≠ 0)
    (hs : BothSigns (Set.range (fun i => (⟨arity i.val, G i⟩ : AnySignature K))))
    (u v : Bool → K) (hu : u ≠ 0) (hv : v ≠ 0)
    (hB : Gadget.RealizesUpTo (Set.range (fun i => (⟨arity i.val, G i⟩ : AnySignature K)))
      .disequality (outerSignature u v)) :
    Nonempty (PowerMacro G u × PowerMacro G v) := by
  obtain ⟨k, l, hk, hl, ⟨a, ha, U, hU, hUX, hUd⟩, ⟨b, hb, V, hV, hVX, hVd⟩⟩ :=
    two_ordinary_powers _ htwo hs u v hu hv hB
  let LU := labellingOfUses arity G U hU (0 : Fin 1)
  let LV := labellingOfUses arity G V hV (0 : Fin 1)
  refine ⟨⟨⟨k, hk, a, ha, U, LU, ?_⟩, ⟨l, hl, b, hb, V, LV, ?_⟩⟩⟩
  · exact (labellingOfUses_denote arity G U hU hUX (0 : Fin 1)
      (fun _ => Signature.disequality) rfl).trans hUd
  · exact (labellingOfUses_denote arity G V hV hVX (0 : Fin 1)
      (fun _ => Signature.disequality) rfl).trans hVd

/-- The manuscript's retained/two-sided setting implies this statement;
retention is not needed for this particular construction. Coefficients are
algebraic because this boundary is over AlgebraicComplex itself. -/
theorem source_labelled_powers
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
    (hs : ¬ Holant.Tractable.CommonOneSided
      (Set.range (fun i => (⟨arity i.val, G i⟩ : AnySignature AlgebraicComplex))))
    (u v : Bool → AlgebraicComplex) (hu : u ≠ 0) (hv : v ≠ 0)
    (hB : Gadget.Realizes (Set.range (fun i => (⟨arity i.val, G i⟩ : AnySignature AlgebraicComplex)))
      .disequality (outerSignature u v)) :
    Nonempty (PowerMacro G u × PowerMacro G v) := by
  have hsign := (Holant.Tractable.commonOneSided_or_bothChargeSigns _).resolve_left hs
  exact labelled_powers G (by norm_num) (bothSigns_of_source hsign) u v hu hv
    ⟨1, one_ne_zero, by simpa using hB⟩

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
