import Holant.Complexity.FixedFieldMachines.PrimitiveCost
import Holant.Proofs.Recognition.PhysicalFolds
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansionUniqueness

/-! Observers for one already constructed graph evaluator. These lemmas do not
produce an evaluator; producer entries below instantiate them with their sole
installed programme. Every prefix counts all physical stacks of that programme. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.InstalledResources
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
variable {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool} {f : A → B}

noncomputable def storagePolynomial (M : Computes ea eb f) : Polynomial ℕ :=
  Polynomial.X + primitivePolynomial M

theorem prefix_bound (M : Computes ea eb f) (a : A) (j : ℕ)
    (hj : j≤M.time.eval (ea.encode a).length) (cfg : M.machine.Config)
    (hc : (fun z => z.bind M.machine.computer.step)^[j]
      (some (initList M.machine.computer (ea.encode a)))=some cfg) :
    stackSize cfg.stk≤(storagePolynomial M).eval (ea.encode a).length := by
  have hs := M.machine.run_size_le _ cfg j hc
  rw [Machine.size_init] at hs
  have hb := Nat.mul_le_mul_right M.machine.primitiveBudget hj
  apply hs.trans
  simpa only [storagePolynomial,primitivePolynomial,Polynomial.eval_add,Polynomial.eval_X,
    Polynomial.eval_mul,Polynomial.eval_C] using Nat.add_le_add_left hb (ea.encode a).length

/-- One output witness, primitive/answer length bounds, and all prefixes refer
to the same M; there is no oracle query or supplied storage bound. -/
def Contract (M : Computes ea eb f) (a : A) : Prop :=
    Nonempty (TM2OutputsInTime M.machine.computer (ea.encode a)
      (some (eb.encode (f a))) (M.time.eval (ea.encode a).length)) ∧
    primitiveCost M.machine (M.outputs a).steps
      (some (initList M.machine.computer (ea.encode a)))≤
        (primitivePolynomial M).eval (ea.encode a).length ∧
    (eb.encode (f a)).length≤M.outputBound.bound.eval (ea.encode a).length ∧
    ∀j, j≤M.time.eval (ea.encode a).length → ∀cfg : M.machine.Config,
      (fun z => z.bind M.machine.computer.step)^[j]
        (some (initList M.machine.computer (ea.encode a)))=some cfg →
      stackSize cfg.stk≤(storagePolynomial M).eval (ea.encode a).length

theorem receipt (M : Computes ea eb f) (a : A) : Contract M a :=
  ⟨⟨M.outputs a⟩,computes_primitive_cost M a,M.outputBound.length_le a,prefix_bound M a⟩

/-- Keep determinism abstract in the programme, avoiding expansion of the
finite control of a large constructed recognizer. -/
theorem observed_decoded {D : Type} {input : D → A} {output : D → B}
    (M : PhysicalFolds.Runs ea eb input output) (d : D) (word : List Bool) (ticks : ℕ)
    (out : TM2OutputsInTime M.machine.computer (ea.encode (input d)) (some word) ticks) :
    eb.decode word=some (output d) := by
  have known := M.outputs d
  have hw := GraphPreprocessing.OriginalCoefficient.ResidualExpansion.machine_output_unique
    M.machine _ _ _ out.steps known.steps out.evals_in_steps known.evals_in_steps
  rw [hw]
  exact eb.decode_encode _

end Holant.LocalDrafts.RemoteWork.TractChainV1.InstalledResources
