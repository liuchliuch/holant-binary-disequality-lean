import Holant.Proofs.Traversal.MatchingExpansion.Backend
import Holant.Proofs.Algorithms.FamilyAnswerTransport


namespace Holant.LocalDrafts.TraversalCompletion.MatchingExpansion.Evaluator
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain
noncomputable section

variable {s : ℕ} {a : ℕ → ℕ} (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
def edges (_ : Fin 1) : Kernel AlgebraicComplex := Signature.equality
abbrev presentation := OriginalFamily.presentation G edges
abbrev answer := OriginalFamily.value G edges

variable (opposite : Bool) (hf : ∀ i, SourceTensorClosure (matchingImage opposite) (G i))

theorem compiled_value (r : Compiler.Input (s:=s) (a:=a)) :
    (Backend.value G opposite hf (Compiler.value G opposite hf r) : AlgebraicComplex) =
      (answer G r : AlgebraicComplex) := by
  rw [Backend.value_exact, OriginalFamily.value_exact]
  exact Compiler.denote G opposite hf r

/-- Its input type and bytes are the original arity function, without an
expanded-graph, correct-code, field-membership or cost certificate at runtime. -/
def equalityComputes : Computes (RawClosedNetwork.validatedEncoding s 1 a)
    (presentation G).encoding (answer G) := by
  let convert := FamilyAnswerTransport.computes (OriginalFamily.coefficient G edges)
    (Backend.coefficient G opposite hf) (OriginalFamily.coefficient_algebraic G edges)
    (Backend.algebraic G opposite hf)
  apply congrComputes (((Compiler.computes G opposite hf).andThen
    (Backend.computes G opposite hf)).andThen convert)
  intro r
  exact FamilyAnswerTransport.recover_exact (OriginalFamily.coefficient G edges)
    (Backend.coefficient G opposite hf) (answer G r)
    (Backend.value G opposite hf (Compiler.value G opposite hf r))
    (compiled_value G opposite hf r)

include opposite hf in
theorem inFP : InFP (RawClosedNetwork.validatedEncoding s 1 a) (presentation G).encoding (answer G) :=
  (equalityComputes G opposite hf).inFP

def timePolynomial : Polynomial ℕ := (equalityComputes G opposite hf).time
def outputPolynomial : Polynomial ℕ := (equalityComputes G opposite hf).outputBound.bound
def primitivePolynomial : Polynomial ℕ := FixedFieldMachines.primitivePolynomial (equalityComputes G opposite hf)

theorem output_length (r : Compiler.Input (s:=s) (a:=a)) :
    ((presentation G).encoding.encode (answer G r)).length ≤
      (outputPolynomial G opposite hf).eval (RawClosedNetwork.encoding.encode r.val).length :=
  (equalityComputes G opposite hf).outputBound.length_le r

theorem execution (r : Compiler.Input (s:=s) (a:=a)) :
    ∃ t, t ≤ (timePolynomial G opposite hf).eval (RawClosedNetwork.encoding.encode r.val).length ∧
      StackProtocol.RunsExactly (equalityComputes G opposite hf).machine.computer.step
        (Turing.initList (equalityComputes G opposite hf).machine.computer (RawClosedNetwork.encoding.encode r.val))
        (Turing.haltList (equalityComputes G opposite hf).machine.computer
          ((presentation G).encoding.encode (answer G r))) t :=
  ⟨((equalityComputes G opposite hf).outputs r).steps,
    ((equalityComputes G opposite hf).outputs r).steps_le_m,
    ((equalityComputes G opposite hf).outputs r).evals_in_steps⟩

theorem primitive_bound (r : Compiler.Input (s:=s) (a:=a)) :
    let w := equalityComputes G opposite hf
    primitiveCost w.machine (w.outputs r).steps
      (some (Turing.initList w.machine.computer (RawClosedNetwork.encoding.encode r.val))) ≤
        (primitivePolynomial G opposite hf).eval (RawClosedNetwork.encoding.encode r.val).length :=
  computes_primitive_cost (equalityComputes G opposite hf) r

end
end Holant.LocalDrafts.TraversalCompletion.MatchingExpansion.Evaluator
