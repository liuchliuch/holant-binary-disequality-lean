import Holant.Proofs.Tractability.ProductMachine.Loop
import Holant.Proofs.Tractability.ProductMachine.RawCompiler


namespace Holant.LocalDrafts.Tractability.ProductMachine.Compilation

open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Templates (Record recordEncoding LocalFactor)

def scalar (r : Record) : Expr ℕ := if r.1 = 0 then .literal r.2.1 else .zero
def finish (s : Round.State) : Expr ℕ := .mul s.2.2 (Expr.product (s.2.1.map scalar))

noncomputable def scalarEmits : Bytecode.Emits recordEncoding encodingNatBool scalar :=
  congrComputes (ifComputes (PivotScan.equal 0 0)
    ((Rewrite.getComputes 1).andThen (Bytecode.literal encodingNatBool))
    (Bytecode.constant recordEncoding encodingNatBool .zero))
    (fun r => by by_cases h : r.1 = 0 <;> simp [scalar, Rewrite.get, h])

noncomputable def finishComputes : Computes Round.encoding (Expr.encoding encodingNatBool) finish :=
  Bytecode.finish (Bytecode.binary Round.encoding encodingNatBool true _ _
    (Round.accumulator.andThen (Bytecode.unfinish encodingNatBool))
    (Round.factors.andThen (Bytecode.product recordEncoding encodingNatBool scalar scalarEmits)))

def stateExpression (s : Round.State) := finish (Loop.value s)

noncomputable def stateComputes : Computes Round.encoding (Expr.encoding encodingNatBool) stateExpression :=
  Loop.fromState.andThen finishComputes

variable (s b : ℕ) (arity : ℕ → ℕ)
variable (vertices : Fin s → List LocalFactor) (edges : Fin b → List LocalFactor)

def initial (r : Input s b arity) : Round.State :=
  (2 * r.val.edges.length, RawCompiler.factors s b arity vertices edges r, .one)

/-- The number of variable tokens is exactly twice the original edge count.
Concatenating two computed unary words physically creates this counter. -/
noncomputable def initialComputes :
    Computes (RawClosedNetwork.validatedEncoding s b arity) Round.encoding
      (initial s b arity vertices edges) := by
  let edgeCount := edgeCountComputes s b arity
  let count : Computes (RawClosedNetwork.validatedEncoding s b arity) UnaryBinary.unaryEncoding
      (fun r => 2 * r.val.edges.length) :=
    recode (joinComputes (edgeCount.andThen (encodeComputes UnaryBinary.unaryEncoding))
      (edgeCount.andThen (encodeComputes UnaryBinary.unaryEncoding))) id (fun _ => rfl)
      (fun r => by
        change List.replicate r.val.edges.length true ++ List.replicate r.val.edges.length true =
          List.replicate (2 * r.val.edges.length) true
        rw [two_mul, List.replicate_add])
  exact pairComputes count (pairComputes (RawCompiler.computes s b arity vertices edges)
    (constantComputes (RawClosedNetwork.validatedEncoding s b arity) (Expr.encoding encodingNatBool) .one))

def expression (r : Input s b arity) := stateExpression (initial s b arity vertices edges r)

/-- An actual composed finite Boolean-stack program, with no supplied compiler
correctness field. Its result at this interface is syntax, not yet Holant's value. -/
noncomputable def computes :
    Computes (RawClosedNetwork.validatedEncoding s b arity) (Expr.encoding encodingNatBool)
      (expression s b arity vertices edges) :=
  (initialComputes s b arity vertices edges).andThen stateComputes

theorem primitive_bound (r : Input s b arity) :
    let w := computes s b arity vertices edges
    primitiveCost w.machine (w.outputs r).steps
      (some (Turing.initList w.machine.computer (RawClosedNetwork.encoding.encode r.val))) ≤
      (primitivePolynomial w).eval (RawClosedNetwork.encoding.encode r.val).length :=
  computes_primitive_cost (computes s b arity vertices edges) r

end Holant.LocalDrafts.Tractability.ProductMachine.Compilation
