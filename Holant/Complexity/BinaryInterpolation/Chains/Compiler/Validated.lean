import Holant.Complexity.BinaryInterpolation.Chains.Compiler.RawCorrectness
import Holant.Complexity.BinaryInterpolation.Chains.Compiler.BoundedQueries
import Holant.Complexity.BinaryInterpolation.Chains.RecordCorrespondence

/-! The variable-length machine produces a validated original-family oracle
input. The extra source label s is replaced by a positive chain of the actual
retained B label. All old signatures, nullary vertices and ordered ports remain.
-/
namespace Holant.Complexity.BinaryInterpolation.Chains.Compiler.Validated
open Turing Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution RawClosedNetwork
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096
set_option Elab.async false

def extendedArity (s : ℕ) (arity : ℕ → ℕ) (i : ℕ) : ℕ := if i = s then 2 else arity i

theorem template_hypotheses {s b : ℕ} (arity : ℕ → ℕ)
    (label : Fin s) (hlabel : arity label.val = 2) (edge : Fin b) (k : ℕ) :
    ∀ i < s + 1,
      (Occurrence.templates (extendedArity s arity) s label.val edge.val k i).WellFormed s b arity ∧
      (Occurrence.templates (extendedArity s arity) s label.val edge.val k i).boundary =
        extendedArity s arity i := by
  intro i hi
  by_cases h : i = s
  · subst i
    simp only [Occurrence.templates,ite_true,extendedArity]
    exact ⟨explicitTemplate_wellFormed arity label hlabel edge k,rfl⟩
  · have hil : i < s := by omega
    have hid : identityTemplate (extendedArity s arity) i = identityTemplate arity i := by
      simp [identityTemplate,extendedArity,h]
    simp only [Occurrence.templates,h,ite_false,hid]
    refine ⟨identityTemplate_wellFormed arity (⟨i,hil⟩ : Fin s),?_⟩
    simp [identityTemplate,extendedArity,h]

variable {s b : ℕ} (arity : ℕ → ℕ)
variable (label : Fin s) (hlabel : arity label.val = 2) (edge : Fin b)
include hlabel

theorem raw_wellFormed (x : Occurrence.Input (s + 1) b (extendedArity s arity)) :
    (Occurrence.raw (s + 1) b (extendedArity s arity) s label.val edge.val x).WellFormed s b arity := by
  rw [Occurrence.raw_eq_replace]
  exact replace_wellFormed _ _ x.2.property (template_hypotheses arity label hlabel edge x.1)

def value (x : Occurrence.Input (s + 1) b (extendedArity s arity)) :
    FixedGadgetSubstitution.Compiler.Input s b arity :=
  ⟨Occurrence.raw (s + 1) b (extendedArity s arity) s label.val edge.val x,
    raw_wellFormed arity label hlabel edge x⟩

/-- Refinement to the target validator changes no byte and has no runtime test
or witness input. Validity follows from the exact emitted physical records. -/
noncomputable def computes :
    Computes (Occurrence.inputEncoding (s + 1) b (extendedArity s arity))
      (validatedEncoding s b arity) (value arity label hlabel edge) :=
  recode (Occurrence.rawComputes (s + 1) b (extendedArity s arity) s label.val edge.val)
    id (fun _ => rfl) (fun _ => rfl)

def boundedValue (x : BoundedQueries.Input (s + 1) b (extendedArity s arity) s) :
    FixedGadgetSubstitution.Compiler.Input s b arity := value arity label hlabel edge (x.2.val,x.1)

/-- All m+1 positive queries, under the faithful original and target encodings. -/
noncomputable def boundedComputes :
    Computes (BoundedQueries.inputEncoding (s + 1) b (extendedArity s arity) s)
      (validatedEncoding s b arity) (boundedValue arity label hlabel edge) :=
  recode (BoundedQueries.computes (s + 1) b (extendedArity s arity) s label.val edge.val)
    id (fun _ => rfl) (fun _ => rfl)

theorem bounded_inFP :
    InFP (BoundedQueries.inputEncoding (s + 1) b (extendedArity s arity) s)
      (validatedEncoding s b arity) (boundedValue arity label hlabel edge) :=
  (boundedComputes arity label hlabel edge).inFP

noncomputable def originalTimePolynomial : Polynomial ℕ :=
  (boundedComputes arity label hlabel edge).time.comp (3 * Polynomial.X + 1)

theorem original_time_bound (x : BoundedQueries.Input (s + 1) b (extendedArity s arity) s) :
    ((boundedComputes arity label hlabel edge).outputs x).steps ≤
      (originalTimePolynomial arity label hlabel edge).eval
        ((validatedEncoding (s + 1) b (extendedArity s arity)).encode x.1).length := by
  have ht := (boundedComputes arity label hlabel edge).outputs x |>.steps_le_m
  have hm := natPolynomial_eval_mono (boundedComputes arity label hlabel edge).time
    (BoundedQueries.input_length_bound _ _ _ _ x)
  simpa [originalTimePolynomial] using ht.trans hm

noncomputable def originalPrimitivePolynomial : Polynomial ℕ :=
  (primitivePolynomial (boundedComputes arity label hlabel edge)).comp (3 * Polynomial.X + 1)

theorem original_primitive_bound (x : BoundedQueries.Input (s + 1) b (extendedArity s arity) s) :
    primitiveCost (boundedComputes arity label hlabel edge).machine
      ((boundedComputes arity label hlabel edge).outputs x).steps
      (some (initList (boundedComputes arity label hlabel edge).machine.computer
        ((BoundedQueries.inputEncoding (s + 1) b (extendedArity s arity) s).encode x))) ≤
      (originalPrimitivePolynomial arity label hlabel edge).eval
        ((validatedEncoding (s + 1) b (extendedArity s arity)).encode x.1).length := by
  have ht := computes_primitive_cost (boundedComputes arity label hlabel edge) x
  have hm := natPolynomial_eval_mono (primitivePolynomial (boundedComputes arity label hlabel edge))
    (BoundedQueries.input_length_bound _ _ _ _ x)
  simpa [originalPrimitivePolynomial] using ht.trans hm

end Holant.Complexity.BinaryInterpolation.Chains.Compiler.Validated
