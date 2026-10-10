import Holant.Complexity.FixedFieldMachines.RawGraphEvaluator.Source
import Holant.Proofs.Algorithms.HolographicTransport


namespace Holant.LocalDrafts.MainChain.OneHotSource
open Computability Holant.Algebraic Holant.Complexity
open Holant.Complexity.BinaryCompose Holant.Complexity.FixedFieldMachines
open Holant.OneHot.StackProgram.Machine
noncomputable section

variable {K : Type} [Field K] [Algebra ℚ K] {d s b : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K d) (T : ExactSignatureTables d s b arity)

theorem valid (hvertex : ∀ i, Signature.OneHot (fun x => F.decode (T.vertex i x)))
    (hedge : ∀ i u v, F.decode (T.edge i u v)=Signature.disequality u v)
    (r : ExactSignatureTables.Input s b arity) : RawGraphEvaluator.Valid F T.coefficient r := by
  constructor
  · intro v
    exact hvertex (r.val.signatureLabel r.property v)
  · intro e
    funext u v
    exact hedge (r.val.edgeLabel r.property e) u v

/-- The algorithm accepts the original raw graph bytes, with no descriptor,
traversal witness, one-hot proof, instruction list or size certificate input. -/
def computes (hvertex : ∀ i, Signature.OneHot (fun x => F.decode (T.vertex i x)))
    (hedge : ∀ i u v, F.decode (T.edge i u v)=Signature.disequality u v) :
    Computes (RawClosedNetwork.validatedEncoding s b arity) F.encoding (T.evaluate F) where
  machine := RawGraphEvaluator.machine F T.coefficient
  time := RawGraphEvaluator.timePolynomial F T.coefficient
  outputs r := by
    let run := RawGraphEvaluator.raw_graph_execute F T.coefficient r
      (valid F T hvertex hedge r)
    exact { steps := run.choose, steps_le_m := run.choose_spec.1, evals_in_steps := run.choose_spec.2.1 }

theorem inFP (hvertex : ∀ i, Signature.OneHot (fun x => F.decode (T.vertex i x)))
    (hedge : ∀ i u v, F.decode (T.edge i u v)=Signature.disequality u v) :
    InFP (RawClosedNetwork.validatedEncoding s b arity) F.encoding (T.evaluate F) :=
  (computes F T hvertex hedge).inFP

theorem primitive_bound
    (hvertex : ∀ i, Signature.OneHot (fun x => F.decode (T.vertex i x)))
    (hedge : ∀ i u v, F.decode (T.edge i u v)=Signature.disequality u v)
    (r : ExactSignatureTables.Input s b arity) :
    ∃ time, time ≤ (RawGraphEvaluator.timePolynomial F T.coefficient).eval
        ((RawClosedNetwork.validatedEncoding s b arity).encode r).length ∧
      Kernels.Executes (RawGraphEvaluator.machine F T.coefficient)
        ((RawClosedNetwork.validatedEncoding s b arity).encode r)
        (F.encoding.encode (T.evaluate F r)) time ∧
      primitiveCost (RawGraphEvaluator.machine F T.coefficient) time
        (some (Turing.initList (RawGraphEvaluator.machine F T.coefficient).computer
          ((RawClosedNetwork.validatedEncoding s b arity).encode r))) ≤
        (RawGraphEvaluator.primitivePolynomial F T.coefficient).eval
          ((RawClosedNetwork.validatedEncoding s b arity).encode r).length :=
  RawGraphEvaluator.raw_graph_execute F T.coefficient r (valid F T hvertex hedge r)

/-- A fixed whole-family basis with native transformed edges gives an
implemented evaluator directly. The basis condition is literal matrix/table
data; no runtime family-recognition or unprovided solver is assumed. -/
def transformedComputes (M N : Kernel K) (hMN : Kernel.mul M N=Signature.equality)
    (hvertex : ∀ i, Signature.OneHot
      (Signature.coordinateAction (fun _ => N) (fun x => F.decode (T.vertex i x))))
    (hedge : ∀ i u v,
      Kernel.pullback (fun x y => F.decode (T.edge i x y)) M u v=Signature.disequality u v) :
    Computes (RawClosedNetwork.validatedEncoding s b arity) F.encoding (T.evaluate F) := by
  apply HolographicTransport.computes F T M N hMN
  apply computes
  · intro i
    simpa only [HolographicTransport.tables,LinearEquiv.apply_symm_apply] using hvertex i
  · intro i u v
    simpa only [HolographicTransport.tables,LinearEquiv.apply_symm_apply] using hedge i u v

end
end Holant.LocalDrafts.MainChain.OneHotSource
