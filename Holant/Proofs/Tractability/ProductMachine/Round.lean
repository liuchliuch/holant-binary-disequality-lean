import Holant.Proofs.Tractability.ProductMachine.Isolated


namespace Holant.LocalDrafts.Tractability.ProductMachine.Round

open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Templates (Record recordEncoding)

abbrev State := ℕ × (List Record × Expr ℕ)
def encoding := pairEncoding UnaryBinary.unaryEncoding
  (pairEncoding (framedListEncoding recordEncoding) (Expr.encoding encodingNatBool))

def step (s : State) : State :=
  if s.1 = 0 then s
  else if (PivotScan.selected s.2.1).1 = 0 then
    (s.1 - 1, Isolated.tail s.2.1, .mul s.2.2 (Isolated.multiplier s.2.1))
  else (s.1 - 1, s.2.1.map (Rewrite.record (PivotScan.selected s.2.1)), s.2.2)

noncomputable def count : Computes encoding UnaryBinary.unaryEncoding Prod.fst :=
  Wiring.firstComputes _ _
noncomputable def rest := Wiring.secondComputes UnaryBinary.unaryEncoding
  (pairEncoding (framedListEncoding recordEncoding) (Expr.encoding encodingNatBool))
noncomputable def factors : Computes encoding (framedListEncoding recordEncoding) (fun s => s.2.1) :=
  rest.andThen (Wiring.firstComputes _ _)
noncomputable def accumulator : Computes encoding (Expr.encoding encodingNatBool) (fun s => s.2.2) :=
  rest.andThen (Wiring.secondComputes _ _)
noncomputable def pivot := factors.andThen PivotScan.computes

noncomputable def computes : Computes encoding encoding step := by
  let stopped := (pairComputes count (constantComputes encoding UnaryBinary.unaryEncoding 0)).andThen
    (UniversalPairReduction.SmoothingCompiler.equalComputes UnaryBinary.unaryEncoding)
  let noPivot := (pairComputes (pivot.andThen Endpoint.edgeComputes)
    (constantComputes encoding encodingNatBool 0)).andThen Endpoints.equalComputes
  let smaller := count.andThen Endpoints.unaryPredecessorComputes
  let newExpression := Bytecode.finish (Bytecode.binary encoding encodingNatBool true
    (fun s => s.2.2) (fun s => Isolated.multiplier s.2.1)
    (accumulator.andThen (Bytecode.unfinish encodingNatBool))
    ((factors.andThen Isolated.multiplierComputes).andThen (Bytecode.unfinish encodingNatBool)))
  let isolated := pairComputes smaller
    (pairComputes (factors.andThen Isolated.tailComputes) newExpression)
  let linked := pairComputes smaller
    (pairComputes ((pairComputes pivot factors).andThen Rewrite.listComputes) accumulator)
  exact congrComputes (ifComputes stopped (identityComputes encoding)
    (ifComputes noPivot isolated linked)) (fun s => by simp [step])

@[simp] theorem count_step (s : State) : (step s).1 = s.1 - 1 := by
  simp only [step]
  split_ifs <;> simp_all

theorem factors_step (s : State) : (step s).2.1.length ≤ s.2.1.length := by
  unfold step
  split_ifs
  · exact le_rfl
  · exact Isolated.tail_length _
  · simp

theorem expression_step (s : State) :
    (step s).2.2.size ≤ s.2.2.size + 4 * s.2.1.length + 4 := by
  have h := Isolated.multiplier_size s.2.1
  unfold step
  split_ifs <;> (try simp only [Expr.size]) <;> omega

theorem factors_iterate (s : State) (k : ℕ) :
    ((step^[k]) s).2.1.length ≤ s.2.1.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (factors_step _).trans ih

theorem expression_iterate (s : State) (k : ℕ) :
    ((step^[k]) s).2.2.size ≤ s.2.2.size + k * (4 * s.2.1.length + 4) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := expression_step ((step^[k]) s)
    have hf := factors_iterate s k
    nlinarith

theorem count_iterate (s : State) (k : ℕ) : ((step^[k]) s).1 = s.1 - k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', count_step, ih]; omega

theorem stable (s : State) (h : s.1 = 0) : step s = s := by simp [step, h]

theorem padded (s : State) (k : ℕ) (h : s.1 ≤ k) : (step^[k]) s = (step^[s.1]) s := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  have hz : ((step^[s.1]) s).1 = 0 := by simp [count_iterate]
  have fixed : ∀ j, (step^[j]) ((step^[s.1]) s) = (step^[s.1]) s := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, stable _ hz]
  rw [Nat.add_comm s.1 j, Function.iterate_add_apply]
  exact fixed j

theorem primitive_bound (s : State) :
    primitiveCost computes.machine (computes.outputs s).steps
      (some (Turing.initList computes.machine.computer (encoding.encode s))) ≤
      (primitivePolynomial computes).eval (encoding.encode s).length := computes_primitive_cost computes s

end Holant.LocalDrafts.Tractability.ProductMachine.Round
