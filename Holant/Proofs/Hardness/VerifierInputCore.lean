import Holant.Proofs.Counting.RawGraphMachine.NaturalProblem
import Holant.Proofs.Counting.RawGraphMachine.Access
import Holant.Proofs.Tractability.AffineMachine.AccessPrograms
import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.DualRail.Paired
import Mathlib.Data.Finset.Card


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.DualRail.VerifierInput

open Turing Computability Holant Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.CountingHardness
open VerifierCompiler.Stateful VerifierCompiler.Stateful.CapacityFrontend
open scoped BigOperators

abbrev Literal := ℕ × Bool
abbrev Clause := List Literal
abbrev Formula := List Clause

/-- The variable count is serialized explicitly, including ignored inputs.
This is an OR-CNF input, deliberately distinct from the old raw DualRail.Input. -/
abbrev Input := ℕ × Formula
abbrev literalEncoding := RawClosedNetwork.endpointEncoding
abbrev clauseEncoding := framedListEncoding literalEncoding
abbrev formulaEncoding := framedListEncoding clauseEncoding
def encoding : Encoding Input Bool := pairEncoding RawGraphMachine.Access.unary formulaEncoding

def literalEval (ρ : ℕ → Bool) (l : Literal) : Bool := ρ l.1 == l.2
def clauseEval (c : Clause) (ρ : ℕ → Bool) : Bool := c.any (literalEval ρ)
def formulaEval (f : Formula) (ρ : ℕ → Bool) : Bool := f.all (fun c => clauseEval c ρ)

def pinClauses (a : ℕ) (b : Bool) : Formula := [[(a,b)]]
def copyClauses (a b c : ℕ) : Formula :=
  [[(a,false),(b,true)],[(a,true),(b,false)],
   [(b,false),(c,true)],[(b,true),(c,false)]]
def nandClauses (a b z : ℕ) : Formula :=
  [[(a,true),(z,true)],[(b,true),(z,true)],[(a,false),(b,false),(z,false)]]

/-- These are all three actual clauses for z ↔ ¬(a ∧ b), with no supplied
CNF-correctness premise and no distinctness requirement on the input addresses. -/
theorem nand_clauses_exact (a b z : ℕ) (ρ : ℕ → Bool) :
    formulaEval (nandClauses a b z) ρ = decide (ρ z = !(ρ a && ρ b)) := by
  cases ha : ρ a <;> cases hb : ρ b <;> cases hz : ρ z <;>
    simp [nandClauses,formulaEval,clauseEval,literalEval,ha,hb,hz]

theorem copy_clauses_exact (a b c : ℕ) (ρ : ℕ → Bool) :
    formulaEval (copyClauses a b c) ρ = decide (ρ a = ρ b ∧ ρ b = ρ c) := by
  cases ha : ρ a <;> cases hb : ρ b <;> cases hc : ρ c <;>
    simp [copyClauses,formulaEval,clauseEval,literalEval,ha,hb,hc]

def address (r : RawVertex) (i : ℕ) : ℕ := (r.2.getD i (0,false)).1
def rowFormula (r : RawVertex) : Formula :=
  match r.1 with
  | 0 => []
  | 1 => pinClauses (address r 0) false
  | 2 => pinClauses (address r 0) true
  | 3 => copyClauses (address r 0) (address r 1) (address r 2)
  | 4 => nandClauses (address r 0) (address r 1) (address r 2)
  | _ => [[]]

theorem row_indicator (r : RawVertex) (ρ : ℕ → Bool) :
    (if formulaEval (rowFormula r) ρ then 1 else 0) =
      (CircuitSemantics.rowWeight r ρ : ℕ) := by
  rcases r with ⟨tag,ports⟩
  rcases tag with _ | (_ | (_ | (_ | (_ | tag))))
  all_goals
    cases h₀ : ρ (ports.getD 0 (0,false)).1 <;>
      cases h₁ : ρ (ports.getD 1 (0,false)).1 <;>
      cases h₂ : ρ (ports.getD 2 (0,false)).1 <;>
      simp_all [rowFormula,address,pinClauses,copyClauses,nandClauses,
        formulaEval,clauseEval,literalEval,CircuitSemantics.rowWeight,
        GateAlphabet.pin,GateAlphabet.copy,GateAlphabet.nand,h₀,h₁,h₂]

theorem formulaEval_append (f g : Formula) (ρ : ℕ → Bool) :
    formulaEval (f ++ g) ρ = (formulaEval f ρ && formulaEval g ρ) := by
  simp [formulaEval]

/-- The complete conjunction is the indicator of the complete original row
product, including every COPY row and every input/output cap. -/
theorem rows_indicator (rs : List RawVertex) (ρ : ℕ → Bool) :
    (if formulaEval (rs.flatMap rowFormula) ρ then 1 else 0) =
      (CircuitSemantics.rowsWeight rs ρ : ℕ) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [List.flatMap_cons,formulaEval_append]
    change (if formulaEval (rowFormula r) ρ && formulaEval (rs.flatMap rowFormula) ρ
      then 1 else 0) = CircuitSemantics.rowWeight r ρ * CircuitSemantics.rowsWeight rs ρ
    rw [← row_indicator,← ih]
    cases formulaEval (rowFormula r) ρ <;>
      cases formulaEval (rs.flatMap rowFormula) ρ <;> rfl

def graphInput (r : RawClosedNetwork) : Input := (r.edges.length,r.vertices.flatMap rowFormula)
def Bounded (q : Input) : Prop := ∀ c ∈ q.2, ∀ l ∈ c, l.1 < q.1

private theorem row_formula_bounded (r : RawVertex) (n : ℕ)
    (htag : r.1 < 5) (hlen : r.2.length = GateAlphabet.arity r.1)
    (hp : ∀ p ∈ r.2, p.1 < n) :
    ∀ c ∈ rowFormula r, ∀ l ∈ c, l.1 < n := by
  rcases r with ⟨tag,ports⟩
  have hr (i : ℕ) (hi : i < ports.length) : address (tag,ports) i < n := by
    apply hp (ports.getD i (0,false))
    change ports.getD i (0,false) ∈ ports
    rw [List.getD_eq_get ports (0,false) ⟨i,hi⟩]
    exact List.get_mem _ _
  interval_cases tag
  · simp [rowFormula]
  · have hl : ports.length = 1 := by simpa [GateAlphabet.arity] using hlen
    have h₀ := hr 0 (by omega)
    simp [rowFormula,pinClauses,h₀]
  · have hl : ports.length = 1 := by simpa [GateAlphabet.arity] using hlen
    have h₀ := hr 0 (by omega)
    simp [rowFormula,pinClauses,h₀]
  · have hl : ports.length = 3 := by simpa [GateAlphabet.arity] using hlen
    have h₀ := hr 0 (by omega)
    have h₁ := hr 1 (by omega)
    have h₂ := hr 2 (by omega)
    simp [rowFormula,copyClauses,forall_and,h₀,h₁,h₂]
  · have hl : ports.length = 3 := by simpa [GateAlphabet.arity] using hlen
    have h₀ := hr 0 (by omega)
    have h₁ := hr 1 (by omega)
    have h₂ := hr 2 (by omega)
    simp [rowFormula,nandClauses,h₀,h₁,h₂]

/-- Every generated literal addresses one of the original physical edges.
The actual permutation validator supplies this fact, not a caller layout. -/
theorem graph_bounded (r : RawGraphMachine.NaturalProblem.Input) : Bounded (graphInput r.val) := by
  intro c hc l hl
  obtain ⟨row,hrow,hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨v,rfl⟩ := List.mem_iff_get.mp hrow
  have hports : ∀ p ∈ (r.val.vertices.get v).2, p.1 < r.val.edges.length := by
    intro p hp
    apply (r.val.mem_expectedEndpoints_iff p).mp
    apply r.property.2.2.mem_iff.mp
    exact List.mem_flatten.mpr ⟨(r.val.vertices.get v).2,
      List.mem_map.mpr ⟨r.val.vertices.get v,List.get_mem _ v,rfl⟩,hp⟩
  exact row_formula_bounded (r.val.vertices.get v) r.val.edges.length
    (r.property.1 v).1 (r.property.1 v).2 hports c hc l hl

def accepts (q : Input) (z : Fin q.1 → Bool) : Bool :=
  formulaEval q.2 (NetworkSemantics.extend z)
def value (q : Input) : ℕ := countAccepted (accepts q)

theorem value_bound (q : Input) : value q ≤ 2 ^ q.1 := by
  simpa [value] using countAccepted_le (accepts q)

/-- The explicit unary variable declaration bounds the actual natural answer
bytes; this does not identify an arbitrary field answer with a natural value. -/
theorem answer_bytes (q : Input) :
    (encodingNatBool.encode (value q)).length ≤ (encoding.encode q).length + 1 := by
  have hb : (encodingNatBool.encode (value q)).length ≤ q.1 + 1 := by
    change (encodeNat (value q)).length ≤ _
    rw [Holant.Algebraic.encodeNat_length]
    exact (Nat.size_le_size (value_bound q)).trans Nat.size_pow.le
  have hv : q.1 ≤ (encoding.encode q).length := by
    rw [encoding,pairEncoding_length]
    change q.1 ≤ 2 * (List.replicate q.1 true).length + 1 + (formulaEncoding.encode q.2).length
    rw [List.length_replicate]
    omega
  omega

def outputBound : PolynomialOutputBound encoding encodingNatBool value where
  bound := Polynomial.X + 1
  length_le q := by simpa using answer_bytes q

theorem graph_count (r : RawGraphMachine.NaturalProblem.Input) :
    value (graphInput r.val) = RawGraphMachine.NaturalProblem.value r := by
  rw [RawGraphMachine.NaturalProblem.value_eq_rows]
  unfold value countAccepted accepts graphInput
  apply Finset.sum_congr rfl
  intro z _
  exact rows_indicator r.val.vertices (NetworkSemantics.extend z)

namespace Source

/-- Sole actual circuit frontend. It consumes the original ordered graph,
not an arbitrary formula alleged to represent the circuit. -/
def input (c : CircuitInstance) : Input := graphInput (RawCompiler.compile c)

theorem count (c : CircuitInstance) : value (input c) = c.value :=
  (graph_count (RawCompiler.validated c)).trans
    (RawGraphMachine.NaturalProblem.compiled_value c)

theorem «variables» (c : CircuitInstance) :
    (input c).1 = c.inputs + RawCompiler.freshEdges c.circuit := by
  simp [input,graphInput,RawCompiler.compile]

theorem bounded (c : CircuitInstance) : Bounded (input c) :=
  graph_bounded (RawCompiler.validated c)

/-- Original input bits are the first block; all five physical edges per NAND
and one per constant remain in the second block. -/
def auxiliaryAccepts (c : CircuitInstance) (x : Fin c.inputs → Bool)
    (z : Fin (RawCompiler.freshEdges c.circuit) → Bool) : Bool :=
  formulaEval (input c).2 (NetworkSemantics.extend (Fin.addCases x z))

theorem auxiliary_indicator (c : CircuitInstance) (x : Fin c.inputs → Bool)
    (z : Fin (RawCompiler.freshEdges c.circuit) → Bool) :
    (if auxiliaryAccepts c x z then 1 else 0) =
      (CircuitSemantics.weight c.circuit x z : ℕ) := by
  change (if formulaEval ((RawCompiler.compile c).vertices.flatMap rowFormula)
    (NetworkSemantics.extend (Fin.addCases x z)) then 1 else 0) = _
  rw [rows_indicator,NetworkSemantics.compiled_rowsWeight]
  simp only [Fin.addCases_left,Fin.addCases_right]

/-- The existing five-edge contraction supplies both existence and absence of
multiplicity. It also covers repeated NAND references and ignored inputs. -/
theorem auxiliary_count (c : CircuitInstance) (x : Fin c.inputs → Bool) :
    countAccepted (auxiliaryAccepts c x) = if c.circuit.eval x then 1 else 0 := by
  unfold countAccepted
  simp_rw [auxiliary_indicator]
  exact CircuitSemantics.sum_weight c.circuit x

private theorem count_eq_filter_card {W : Type} [Fintype W] (f : W → Bool) :
    countAccepted f = (Finset.univ.filter (fun z => f z = true)).card := by
  classical
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  unfold countAccepted
  apply Finset.sum_congr rfl
  intro z _
  cases f z <;> rfl

theorem unique_extension (c : CircuitInstance) (x : Fin c.inputs → Bool)
    (hx : c.circuit.eval x = true) :
    ∃! z : Fin (RawCompiler.freshEdges c.circuit) → Bool,
      auxiliaryAccepts c x z = true := by
  classical
  have hc : (Finset.univ.filter (fun z => auxiliaryAccepts c x z = true)).card = 1 := by
    rw [← count_eq_filter_card,auxiliary_count,hx]
    rfl
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using
    Finset.card_eq_one_iff_existsUnique.mp hc

theorem no_extension (c : CircuitInstance) (x : Fin c.inputs → Bool)
    (hx : c.circuit.eval x = false) :
    ∀ z : Fin (RawCompiler.freshEdges c.circuit) → Bool,
      auxiliaryAccepts c x z = false := by
  classical
  have hc : (Finset.univ.filter (fun z => auxiliaryAccepts c x z = true)).card = 0 := by
    rw [← count_eq_filter_card,auxiliary_count,hx]
    rfl
  have he := Finset.card_eq_zero.mp hc
  intro z
  cases hz : auxiliaryAccepts c x z with
  | false => rfl
  | true =>
    have hm : z ∈ Finset.univ.filter (fun z => auxiliaryAccepts c x z = true) := by
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,hz]
    rw [he] at hm
    exact False.elim (Finset.notMem_empty z hm)

theorem extension_exists_iff (c : CircuitInstance) (x : Fin c.inputs → Bool) :
    (∃ z : Fin (RawCompiler.freshEdges c.circuit) → Bool,
      auxiliaryAccepts c x z = true) ↔ c.circuit.eval x = true := by
  constructor
  · rintro ⟨z,hz⟩
    cases hx : c.circuit.eval x with
    | false =>
      have hn := no_extension c x hx z
      rw [hz] at hn
      contradiction
    | true => rfl
  · intro hx
    obtain ⟨z,hz,_⟩ := unique_extension c x hx
    exact ⟨z,hz⟩

end Source

namespace Program

private def list₂ {A B : Type} {ea : Encoding A Bool} (eb : Encoding B Bool)
    {f g : A → B} (wf : Computes ea eb f) (wg : Computes ea eb g) :
    Computes ea (framedListEncoding eb) (fun a => [f a,g a]) :=
  (pairComputes wf (RawGraphMachine.Access.list₁ eb wg)).andThen (RawGraphMachine.Access.cons eb)

private def list₄ {A B : Type} {ea : Encoding A Bool} (eb : Encoding B Bool)
    {f g h j : A → B} (wf : Computes ea eb f) (wg : Computes ea eb g)
    (wh : Computes ea eb h) (wj : Computes ea eb j) :
    Computes ea (framedListEncoding eb) (fun a => [f a,g a,h a,j a]) :=
  (pairComputes wf (RawGraphMachine.Access.list₃ eb wg wh wj)).andThen (RawGraphMachine.Access.cons eb)

/-- These transports preserve literal framed bytes and the same programs. -/
def rowFields : Computes RawClosedNetwork.vertexEncoding
    (pairEncoding encodingNatBool (framedListEncoding literalEncoding)) (fun r => r) :=
  recode (identityComputes (pairEncoding encodingNatBool (framedListEncoding literalEncoding)))
    id (fun _ => rfl) (fun _ => rfl)
def ports := rowFields.andThen (Wiring.secondComputes encodingNatBool (framedListEncoding literalEncoding))
def tag := rowFields.andThen (Wiring.firstComputes encodingNatBool (framedListEncoding literalEncoding))
def literalAddress : Computes literalEncoding encodingNatBool Prod.fst :=
  recode (Wiring.firstComputes encodingNatBool encodingBoolBool) id (fun _ => rfl) (fun _ => rfl)

def addressComputes (i : ℕ) : Computes RawClosedNetwork.vertexEncoding encodingNatBool
    (fun r => address r i) :=
  ((pairComputes ports (constantComputes RawClosedNetwork.vertexEncoding RawGraphMachine.Access.unary i)).andThen
    (ListAccess.getDComputes literalEncoding (0,false))).andThen literalAddress

def literalComputes (i : ℕ) (b : Bool) : Computes RawClosedNetwork.vertexEncoding literalEncoding
    (fun r => (address r i,b)) :=
  recode (pairComputes (addressComputes i)
    (constantComputes RawClosedNetwork.vertexEncoding encodingBoolBool b))
    id (fun _ => rfl) (fun _ => rfl)

def pinComputes (b : Bool) : Computes RawClosedNetwork.vertexEncoding formulaEncoding
    (fun r => pinClauses (address r 0) b) :=
  RawGraphMachine.Access.list₁ clauseEncoding
    (RawGraphMachine.Access.list₁ literalEncoding (literalComputes 0 b))
def copyComputes : Computes RawClosedNetwork.vertexEncoding formulaEncoding
    (fun r => copyClauses (address r 0) (address r 1) (address r 2)) :=
  list₄ clauseEncoding
    (list₂ literalEncoding (literalComputes 0 false) (literalComputes 1 true))
    (list₂ literalEncoding (literalComputes 0 true) (literalComputes 1 false))
    (list₂ literalEncoding (literalComputes 1 false) (literalComputes 2 true))
    (list₂ literalEncoding (literalComputes 1 true) (literalComputes 2 false))
def nandComputes : Computes RawClosedNetwork.vertexEncoding formulaEncoding
    (fun r => nandClauses (address r 0) (address r 1) (address r 2)) :=
  RawGraphMachine.Access.list₃ clauseEncoding
    (list₂ literalEncoding (literalComputes 0 true) (literalComputes 2 true))
    (list₂ literalEncoding (literalComputes 1 true) (literalComputes 2 true))
    (RawGraphMachine.Access.list₃ literalEncoding
      (literalComputes 0 false) (literalComputes 1 false) (literalComputes 2 false))

/-- A fixed five-way opcode test, followed by actual framed-list writers.
An invalid raw tag writes an empty, hence false, clause. -/
def rowComputes : Computes RawClosedNetwork.vertexEncoding formulaEncoding rowFormula := by
  let test (i : ℕ) := (pairComputes tag
    (constantComputes RawClosedNetwork.vertexEncoding encodingNatBool i)).andThen Endpoints.equalComputes
  let program := ifComputes (test 0)
    (constantComputes RawClosedNetwork.vertexEncoding formulaEncoding [])
    (ifComputes (test 1) (pinComputes false)
      (ifComputes (test 2) (pinComputes true)
        (ifComputes (test 3) copyComputes
          (ifComputes (test 4) nandComputes
            (constantComputes RawClosedNetwork.vertexEncoding formulaEncoding [[]])))))
  refine congrComputes program ?_
  intro r
  change (if decide (r.1 = 0) then [] else
    if decide (r.1 = 1) then pinClauses (address r 0) false else
    if decide (r.1 = 2) then pinClauses (address r 0) true else
    if decide (r.1 = 3) then copyClauses (address r 0) (address r 1) (address r 2) else
    if decide (r.1 = 4) then nandClauses (address r 0) (address r 1) (address r 2) else [[]]) = rowFormula r
  rcases r with ⟨k,ps⟩
  rcases k with _ | (_ | (_ | (_ | (_ | k)))) <;> simp [rowFormula]

def graphFields : Computes RawClosedNetwork.encoding
    (pairEncoding (framedListEncoding RawClosedNetwork.vertexEncoding)
      (framedListEncoding encodingNatBool)) (fun r => (r.vertices,r.edges)) :=
  recode (identityComputes (pairEncoding (framedListEncoding RawClosedNetwork.vertexEncoding)
    (framedListEncoding encodingNatBool))) (fun r : RawClosedNetwork => (r.vertices,r.edges))
    (fun _ => rfl) (fun _ => rfl)

/-- The physical variable-list traversal reuses the delivered map/flatten
machines. The declared variable count is physically counted from all edges. -/
def rawComputes : Computes RawClosedNetwork.encoding encoding graphInput := by
  let vs := graphFields.andThen (Wiring.firstComputes
    (framedListEncoding RawClosedNetwork.vertexEncoding) (framedListEncoding encodingNatBool))
  let es := graphFields.andThen (Wiring.secondComputes
    (framedListEncoding RawClosedNetwork.vertexEncoding) (framedListEncoding encodingNatBool))
  let count := es.andThen (Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Indexed.countComputes encodingNatBool)
  let formula := vs.andThen
    (Holant.LocalDrafts.Tractability.AffineMachine.AccessPrograms.flatMap
      RawClosedNetwork.vertexEncoding clauseEncoding rowFormula rowComputes)
  exact pairComputes count formula

def graphComputes : Computes RawGraphMachine.NaturalProblem.encoding encoding
    (fun r => graphInput r.val) :=
  recode rawComputes Subtype.val (fun _ => rfl) (fun _ => rfl)

end Program

namespace Source

/-- Physical original-circuit bytes → original graph bytes → actual OR-CNF
bytes. No finite enumeration is used as a substitute for a program. -/
def computes : Computes CircuitInstance.encoding encoding input :=
  RawGraphMachine.computes.andThen Program.graphComputes

abbrev machine := computes.machine
def time : Polynomial ℕ := computes.time
def storagePolynomial : Polynomial ℕ := Polynomial.X + time * Polynomial.C machine.primitiveBudget

def execution (c : CircuitInstance) :
    TM2OutputsInTime machine.computer (CircuitInstance.encoding.encode c)
      (some (encoding.encode (input c))) (time.eval (CircuitInstance.encoding.encode c).length) :=
  computes.outputs c

theorem exact_run (c : CircuitInstance) :
    (fun q => q.bind machine.computer.step)^[(execution c).steps]
      (some (initList machine.computer (CircuitInstance.encoding.encode c))) =
      some (haltList machine.computer (encoding.encode (input c))) :=
  (execution c).evals_in_steps

theorem primitive_bound (c : CircuitInstance) :
    FixedFieldMachines.primitiveCost machine (execution c).steps
      (some (initList machine.computer (CircuitInstance.encoding.encode c))) ≤
      (FixedFieldMachines.primitivePolynomial computes).eval (CircuitInstance.encoding.encode c).length :=
  FixedFieldMachines.computes_primitive_cost computes c

theorem bytes (c : CircuitInstance) :
    (encoding.encode (input c)).length ≤
      computes.outputBound.bound.eval (CircuitInstance.encoding.encode c).length :=
  computes.outputBound.length_le c

/-- A real prefix of the same finite program has storage bounded by its real
number of transitions. The output receipt above supplies the final clock. -/
theorem storage (c : CircuitInstance) (t : ℕ) (cfg : machine.Config)
    (hr : (fun q => q.bind machine.computer.step)^[t]
      (some (Turing.initList machine.computer (CircuitInstance.encoding.encode c))) = some cfg)
    (ht : t ≤ time.eval (CircuitInstance.encoding.encode c).length) :
    stackSize cfg.stk ≤ storagePolynomial.eval (CircuitInstance.encoding.encode c).length := by
  have h := machine.run_size_le
    (Turing.initList machine.computer (CircuitInstance.encoding.encode c)) cfg t hr
  rw [Machine.size_init] at h
  simp only [storagePolynomial,Polynomial.eval_add,Polynomial.eval_X,
    Polynomial.eval_mul,Polynomial.eval_C]
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ ht) _)

end Source
end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.DualRail.VerifierInput
