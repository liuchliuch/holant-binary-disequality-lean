import Holant.Complexity.BinaryInterpolation.Chains.Compiler.Counts
import Holant.Complexity.BinaryInterpolation.Chains.Compiler.LabelCounts
import Holant.Complexity.FixedGadgetSubstitution.Adjoin

/-! Compose the variable positive-chain program with the actual fixed-gadget
compiler back to Γ. Source label s is the interpolated binary H; the same
numeric slot in the intermediate graph denotes B. It is then eliminated using
the original-Γ macro. No extra B slot is needed in the original input and no
literal-I signature is assumed. DirectMacro derives the required fixed macro.
-/
namespace Holant.Complexity.BinaryInterpolation.Chains.Compiler.OriginalFamily
open Turing Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution RawClosedNetwork
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

variable {s b : ℕ} (arity : ℕ → ℕ) (g : Template) (hg : g.WellFormed s b arity)
variable (hbinary : g.boundary = 2) (edge : Fin b)

abbrev macroArity := sourceArity (Adjoin.templates s arity g)
abbrev Input := BoundedQueries.Input (s + 1) b (macroArity (s:=s) arity g) s
abbrev inputEncoding := BoundedQueries.inputEncoding (s + 1) b (macroArity (s:=s) arity g) s

include hbinary in
theorem chain_hypotheses (k : ℕ) : ∀ i < s + 1,
    (Occurrence.templates (macroArity (s:=s) arity g) s s edge.val k i).WellFormed (s + 1) b (macroArity (s:=s) arity g) ∧
    (Occurrence.templates (macroArity (s:=s) arity g) s s edge.val k i).boundary = macroArity (s:=s) arity g i := by
  intro i hi
  by_cases h : i = s
  · subst i
    simp only [Occurrence.templates,ite_true]
    refine ⟨explicitTemplate_wellFormed (macroArity (s:=s) arity g)
      (⟨s,Nat.lt_succ_self s⟩ : Fin (s + 1)) ?_ edge k,?_⟩
    · exact (Adjoin.new_boundary g).trans hbinary
    · exact hbinary.symm.trans (Adjoin.new_boundary g).symm
  · simp only [Occurrence.templates,h,ite_false]
    exact ⟨identityTemplate_wellFormed (macroArity (s:=s) arity g) (⟨i,hi⟩ : Fin (s + 1)),rfl⟩

def intermediate (x : Input (s:=s) (b:=b) arity g) :
    FixedGadgetSubstitution.Compiler.Input (s + 1) b (macroArity (s:=s) arity g) :=
  ⟨Occurrence.raw (s + 1) b (macroArity (s:=s) arity g) s s edge.val (x.2.val,x.1),by
    rw [Occurrence.raw_eq_replace]
    exact replace_wellFormed _ _ x.1.property (chain_hypotheses arity g hbinary edge x.2.val)⟩

noncomputable def chainComputes : Computes (inputEncoding (s:=s) (b:=b) arity g)
    (validatedEncoding (s + 1) b (macroArity (s:=s) arity g)) (intermediate arity g hbinary edge) :=
  recode (BoundedQueries.computes (s + 1) b (macroArity (s:=s) arity g) s s edge.val)
    id (fun _ => rfl) (fun _ => rfl)

include hg in
theorem fixed_hypotheses : ∀ i < s + 1,
    (Adjoin.templates s arity g i).WellFormed s b arity ∧
    (Adjoin.templates s arity g i).boundary = macroArity (s:=s) arity g i :=
  fun i hi => ⟨Adjoin.wellFormed g hg i hi,rfl⟩

def value (x : Input (s:=s) (b:=b) arity g) : FixedGadgetSubstitution.Compiler.Input s b arity :=
  FixedGadgetSubstitution.Compiler.value (s + 1) b (macroArity (s:=s) arity g)
    (Adjoin.templates s arity g) s arity (fixed_hypotheses arity g hg)
      (intermediate arity g hbinary edge x)

/-- One actual finite Boolean program compiles every sample directly to Γ. -/
noncomputable def computes : Computes (inputEncoding (s:=s) (b:=b) arity g)
    (validatedEncoding s b arity) (value arity g hg hbinary edge) :=
  (chainComputes arity g hbinary edge).andThen
    (FixedGadgetSubstitution.Compiler.computes (s + 1) b (macroArity (s:=s) arity g)
      (Adjoin.templates s arity g) s arity (fixed_hypotheses arity g hg))

/-- The exact exponent for the fixed macro's projective correction is produced
from the actually emitted intermediate B-label stream by an actual counter. -/
noncomputable def withExponentComputes : Computes (inputEncoding (s:=s) (b:=b) arity g)
    (pairEncoding (validatedEncoding s b arity) UnaryBinary.unaryEncoding)
    (fun x => (value arity g hg hbinary edge x,
      occurrences s (intermediate arity g hbinary edge x).val)) :=
  (chainComputes arity g hbinary edge).andThen
    (FixedGadgetSubstitution.Compiler.withOccurrencesComputes (s + 1) b (macroArity (s:=s) arity g)
      (Adjoin.templates s arity g) s arity (fixed_hypotheses arity g hg) s)

theorem exponent_exact (x : Input (s:=s) (b:=b) arity g) :
    occurrences s (intermediate arity g hbinary edge x).val =
      (x.2.val + 1) * occurrences s x.1.val :=
  Occurrence.raw_label_count (s + 1) b (macroArity (s:=s) arity g) s edge.val (x.2.val,x.1)

/-- The final Γ-query has precisely the fixed macro scale c^((k+1)m).
The intermediate problem has the original Γ labels and the actual B table. -/
theorem value_partition {K : Type} [Field K] (x : Input (s:=s) (b:=b) arity g)
    (source : (i : Fin (s + 1)) → Signature K (macroArity (s:=s) arity g i.val))
    (signatures : (i : Fin s) → Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) (c : K)
    (hdenote : ∀ i : Fin (s + 1),
      ((Adjoin.templates s arity g i.val).network (Adjoin.wellFormed g hg i.val i.isLt)
        signatures kernels).denote = (if i.val = s then c else 1) • source i) :
    ((value arity g hg hbinary edge x).val.realize (value arity g hg hbinary edge x).property
      signatures kernels).denote Fin.elim0 =
      c ^ ((x.2.val + 1) * occurrences s x.1.val) *
        ((intermediate arity g hbinary edge x).val.realize
          (intermediate arity g hbinary edge x).property source kernels).denote Fin.elim0 := by
  have h := replacement_scale_power (Adjoin.templates s arity g)
    (intermediate arity g hbinary edge x).val (intermediate arity g hbinary edge x).property
    (Adjoin.wellFormed g hg) source signatures kernels s c hdenote
  rw [exponent_exact arity g hbinary edge x] at h
  exact h

/-- Fixed macro and spectral normalizations multiply at every physical B
occurrence; the final normalization uses γ=c·β with exponent t·m. -/
theorem value_partition_normalized {K : Type} [Field K]
    (x : Input (s:=s) (b:=b) arity g)
    (source : (i : Fin (s + 1)) → Signature K (macroArity (s:=s) arity g i.val))
    (signatures : (i : Fin s) → Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) (c β z : K)
    (hdenote : ∀ i : Fin (s + 1),
      ((Adjoin.templates s arity g i.val).network (Adjoin.wellFormed g hg i.val i.isLt)
        signatures kernels).denote = (if i.val = s then c else 1) • source i)
    (hspectral : ((intermediate arity g hbinary edge x).val.realize
      (intermediate arity g hbinary edge x).property source kernels).denote Fin.elim0 =
        β ^ ((x.2.val + 1) * occurrences s x.1.val) * z) :
    ((value arity g hg hbinary edge x).val.realize (value arity g hg hbinary edge x).property
      signatures kernels).denote Fin.elim0 =
      (c * β) ^ ((x.2.val + 1) * occurrences s x.1.val) * z := by
  rw [value_partition arity g hg hbinary edge x source signatures kernels c hdenote,hspectral,
    mul_pow,mul_assoc]

theorem normalization_nonzero {K : Type*} [Field K] (c β : K) (hc : c ≠ 0) (hβ : β ≠ 0)
    (t m : ℕ) : (c * β) ^ (t * m) ≠ 0 := pow_ne_zero _ (mul_ne_zero hc hβ)

noncomputable def originalTimePolynomial : Polynomial ℕ :=
  (computes arity g hg hbinary edge).time.comp (3 * Polynomial.X + 1)

theorem original_time_bound (x : Input (s:=s) (b:=b) arity g) :
    ((computes arity g hg hbinary edge).outputs x).steps ≤
      (originalTimePolynomial arity g hg hbinary edge).eval
        ((validatedEncoding (s + 1) b (macroArity (s:=s) arity g)).encode x.1).length := by
  have ht := (computes arity g hg hbinary edge).outputs x |>.steps_le_m
  have hm := natPolynomial_eval_mono (computes arity g hg hbinary edge).time
    (BoundedQueries.input_length_bound _ _ _ _ x)
  simpa [originalTimePolynomial] using ht.trans hm

noncomputable def originalPrimitivePolynomial : Polynomial ℕ :=
  (primitivePolynomial (computes arity g hg hbinary edge)).comp (3 * Polynomial.X + 1)

theorem original_primitive_bound (x : Input (s:=s) (b:=b) arity g) :
    primitiveCost (computes arity g hg hbinary edge).machine
      ((computes arity g hg hbinary edge).outputs x).steps
      (some (initList (computes arity g hg hbinary edge).machine.computer
        ((inputEncoding (s:=s) (b:=b) arity g).encode x))) ≤
      (originalPrimitivePolynomial arity g hg hbinary edge).eval
        ((validatedEncoding (s + 1) b (macroArity (s:=s) arity g)).encode x.1).length := by
  have ht := computes_primitive_cost (computes arity g hg hbinary edge) x
  have hm := natPolynomial_eval_mono (primitivePolynomial (computes arity g hg hbinary edge))
    (BoundedQueries.input_length_bound _ _ _ _ x)
  simpa [originalPrimitivePolynomial] using ht.trans hm

end Holant.Complexity.BinaryInterpolation.Chains.Compiler.OriginalFamily
