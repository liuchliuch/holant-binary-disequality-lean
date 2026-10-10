import Holant.Proofs.Reductions.CyclicPowerConsumer.Reduction
import Holant.Complexity.FixedFieldMachines.PrimitiveCost


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.CyclicPowerConsumer.Machine
open Holant.Tractable
open scoped BigOperators
open Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain RingHomRealization
open CyclicBoundary CyclicBoundary.AlgebraicRepresentatives
open Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
open GeneralExtraction

variable {s N : ℕ} {arity : ℕ → ℕ} {F : SignatureFamily ℂ}
variable {R : PhysicalAttachments.Representatives F N} {q : Signature ℂ 4}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (d : CountedDoubled R q)
variable (hl : ∀ v, (⟨d.certificate.circuit.network.shape.arity v,
  d.certificate.circuit.network.vertex v⟩ : AnySignature ℂ) ∈ mapFamily inclusion (family G))
variable (hN : 0 < N) (ha : arity s = 2)

theorem query_bound (r : GeneralOriginalQuery.Input (s:=s) (arity:=arity)) :
    ((queryEncoding (s:=s) (arity:=arity)).encode (query G d hl hN ha r)).length ≤
      (queryComputes G d hl hN ha).outputBound.bound.eval
        ((inputEncoding (s:=s) (arity:=arity)).encode r).length :=
  (queryComputes G d hl hN ha).outputBound.length_le r

theorem answer_bound (r : GeneralOriginalQuery.Input (s:=s) (arity:=arity)) :
    ((targetPresentation G).encoding.encode (targetValue G (query G d hl hN ha r))).length ≤
      (((GeneralOriginalTarget.originalTables G).outputBound (targetPresentation G)).bound.comp
        (queryComputes G d hl hN ha).outputBound.bound).eval
          ((inputEncoding (s:=s) (arity:=arity)).encode r).length := by
  have h := ((GeneralOriginalTarget.originalTables G).outputBound (targetPresentation G)).length_le
    (query G d hl hN ha r)
  exact h.trans (by
    simpa only [Polynomial.eval_comp] using
      (natPolynomial_eval_mono
        ((GeneralOriginalTarget.originalTables G).outputBound (targetPresentation G)).bound
        (query_bound G d hl hN ha r)))

theorem converted_answer_bound (y : GeneralOriginalTarget.originalField G) :
    ((presentation G d hl hN ha).encoding.encode (embedding G d hl hN ha y)).length ≤
      (answerComputes G d hl hN ha).outputBound.bound.eval
        ((targetPresentation G).encoding.encode y).length :=
  (answerComputes G d hl hN ha).outputBound.length_le y

theorem pre_primitive (r : GeneralOriginalQuery.Input (s:=s) (arity:=arity)) :
    primitiveCost (preComputes G d hl hN ha).machine ((preComputes G d hl hN ha).outputs r).steps
      (some (Turing.initList (preComputes G d hl hN ha).machine.computer
        ((inputEncoding (s:=s) (arity:=arity)).encode r))) ≤
      (primitivePolynomial (preComputes G d hl hN ha)).eval
        ((inputEncoding (s:=s) (arity:=arity)).encode r).length :=
  computes_primitive_cost (preComputes G d hl hN ha) r

theorem post_primitive (p : List (GeneralOriginalTarget.originalField G) ×
    GeneralFieldReduction.Context (field G d hl hN ha)) :
    primitiveCost (postComputes G d hl hN ha).machine ((postComputes G d hl hN ha).outputs p).steps
      (some (Turing.initList (postComputes G d hl hN ha).machine.computer
        ((OracleBatch.contextEncoding (targetPresentation G).encoding
          (contextEncoding G d hl hN ha)).encode p))) ≤
      (primitivePolynomial (postComputes G d hl hN ha)).eval
        ((OracleBatch.contextEncoding (targetPresentation G).encoding
          (contextEncoding G d hl hN ha)).encode p).length :=
  computes_primitive_cost (postComputes G d hl hN ha) p

theorem query_dead (r : GeneralOriginalQuery.Input (s:=s) (arity:=arity))
    (h : ¬ GeneralOriginalQuery.IsLive (original G d hl hN ha) (factor G d hl hN ha)
      (commonMacro G d hl hN ha) r) : (query G d hl hN ha r).val = ⟨[],[]⟩ :=
  GeneralFieldReduction.query_dead (original G d hl hN ha) (factor G d hl hN ha)
    (commonMacro G d hl hN ha) r h

theorem run_trace (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity))
      (targetPresentation G).encoding (targetValue G) oracle)
    (r : GeneralOriginalQuery.Input (s:=s) (arity:=arity)) :
    let M := reduction G d hl hN ha
    ∃ t ≤ M.time.eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length,
      OracleBatch.RunsTrace M.machine oracle
        (M.machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r))
        (M.machine.output ((presentation G d hl hN ha).encoding.encode (sourceValue G d hl hN ha r)))
        t [(queryEncoding (s:=s) (arity:=arity)).encode (query G d hl hN ha r)] := by
  simpa only [reduction, GeneralFieldReduction.pre, List.map_cons, List.map_nil] using
    OracleBatch.of_eq_run_trace (preComputes G d hl hN ha) (postComputes G d hl hN ha)
      ((GeneralOriginalTarget.originalTables G).outputBound (targetPresentation G))
      (sourceValue G d hl hN ha) (recovery G d hl hN ha) oracle ho r

theorem run_cost (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity))
      (targetPresentation G).encoding (targetValue G) oracle)
    (r : GeneralOriginalQuery.Input (s:=s) (arity:=arity)) :
    let M := reduction G d hl hN ha
    ∃ t ≤ M.time.eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length,
      (fun c => c.bind (M.machine.step oracle))^[t]
        (some (M.machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r))) =
        some (M.machine.output ((presentation G d hl hN ha).encoding.encode (sourceValue G d hl hN ha r))) ∧
      OracleBatch.primitiveCount M.machine oracle
        (M.machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t ≤
        M.machine.primitiveBudget * M.time.eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length := by
  let M := reduction G d hl hN ha
  let run := M.correct oracle ho r
  refine ⟨run.steps,run.steps_le_m,run.evals_in_steps,?_⟩
  exact (OracleBatch.primitiveCount_le M.machine oracle
    (M.machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) run.steps).trans
      (Nat.mul_le_mul_left M.machine.primitiveBudget run.steps_le_m)

theorem every_prefix_queries_at_most_one (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity))
      (targetPresentation G).encoding (targetValue G) oracle)
    (r : GeneralOriginalQuery.Input (s:=s) (arity:=arity)) (n : ℕ) :
    let M := reduction G d hl hN ha
    Holant.Complexity.UniversalPairReduction.ThreeQuery.queryCount M.machine oracle
      (M.machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) n ≤ 1 := by
  obtain ⟨t,ht,hr⟩ := run_trace G d hl hN ha oracle ho r
  simpa only [List.length_singleton] using hr.prefix_count_le n

end Holant.LocalDrafts.Hardness.CyclicPowerConsumer.Machine
