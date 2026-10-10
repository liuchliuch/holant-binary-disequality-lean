import Holant.Proofs.Tractability.AffineMachine.Assembly
import Holant.Proofs.Tractability.AffineMachine.FiniteCore


namespace Holant.LocalDrafts.Tractability.AffineMachine.RawCode

open Holant.Tractable AffinePhase TwoTranslate Holant.Complexity ProductMachine
open FixedGadgetSubstitution.Compiler
open scoped BigOperators
noncomputable section

variable {s b : ℕ} {arity : ℕ → ℕ} (D : Assembly.Family s b arity)

abbrev ScaleLabel := Fin s ⊕ Fin b
abbrev Label := ScalarCode.Atom (ScaleLabel (s := s) (b := b))

def scale : ScaleLabel (s := s) (b := b) → AlgebraicComplex
  | .inl i => (Assembly.vertex D i).scale
  | .inr i => (Assembly.edge D i).scale

def labels (r : Input s b arity) : List (ScaleLabel (s := s) (b := b)) :=
  List.ofFn (fun v => .inl (r.val.signatureLabel r.property v)) ++
    List.ofFn (fun e => .inr (r.val.edgeLabel r.property e))

def accumulator (r : Input s b arity) : Expr (Label (s := s) (b := b)) :=
  Expr.product ((labels r).map (fun a => .literal (.inl a)))

theorem accumulator_value (r : Input s b arity) :
    (accumulator r).eval (ScalarCode.coefficient (scale D)) = (Assembly.global D r).scale := by
  simp [accumulator, Expr.eval_product, Expr.eval, ScalarCode.coefficient, labels,
    Assembly.global, Assembly.collect_scale, Assembly.blocks, Assembly.vertexBlock,
    Assembly.edgeBlock, Assembly.place, scale, List.map_map, Function.comp_def]

def table (r : Input s b arity) : Dense.Table (2 * r.val.edges.length) :=
  Dense.snapshot (Assembly.global D r).support (Assembly.global D r).phase

def expression (r : Input s b arity) : Expr (Label (s := s) (b := b)) :=
  FiniteCore.compile (table D r) (accumulator r)

theorem expression_value (r : Input s b arity) :
    (expression D r).eval (ScalarCode.coefficient (scale D)) =
      (r.val.realize r.property D.signatures D.kernels).denote Fin.elim0 := by
  rw [expression, FiniteCore.compile_correct, accumulator_value]
  have he : (table D r).state (Assembly.global D r).scale = Assembly.global D r := by
    simp [table, Dense.Table.state]
  rw [he, Assembly.global_partition]

theorem accumulator_size (r : Input s b arity) :
    (accumulator r).size ≤ 2 * (r.val.vertices.length + r.val.edges.length) + 1 := by
  have h := Expr.size_product_le ((labels r).map
    (fun a => (Expr.literal (.inl a) : Expr (Label (s := s) (b := b)))))
    (by intro e he; obtain ⟨a, _, rfl⟩ := List.mem_map.mp he; rfl)
  simpa [accumulator, labels] using h

def codeBudget (V E : ℕ) : ℕ := 2 * V + 6 * E + 3

theorem expression_size (r : Input s b arity) :
    (expression D r).size ≤ codeBudget r.val.vertices.length r.val.edges.length := by
  have h := FiniteCore.compile_size (table D r) (accumulator r)
  have ha := accumulator_size r
  dsimp only [expression, codeBudget]
  omega

theorem bytecode_length (r : Input s b arity) :
    (expression D r).code.length ≤ codeBudget r.val.vertices.length r.val.edges.length := by
  rw [Expr.code_length]
  exact expression_size D r

theorem expression_size_input (r : Input s b arity) :
    (expression D r).size ≤ 6 * (RawClosedNetwork.encoding.encode r.val).length + 3 := by
  have h := expression_size D r
  have hinput := RawClosedNetwork.counts_le_encoded_length r.val
  unfold codeBudget at h
  omega

/-- A raw-input bound for every intermediate residue table. Only coefficient
payload is counted here; WireSize/FamilySolver separately charge the actual
framed table codec and physical loop. -/
theorem intermediate_payload_input {n : ℕ} (r : Input s b arity) (U : Dense.Table n)
    (h : Dense.Reachable (table D r) U) :
    Dense.payload n U.rows ≤
      Dense.payload (2 * (RawClosedNetwork.encoding.encode r.val).length)
        ((RawClosedNetwork.encoding.encode r.val).length * Assembly.rowBudget D + 1) := by
  have hinput := RawClosedNetwork.counts_le_encoded_length r.val
  have hrows := Assembly.global_rows_le D r
  have hm : max (table D r).rows 1 ≤
      (RawClosedNetwork.encoding.encode r.val).length * Assembly.rowBudget D + 1 := by
    apply max_le
    · change (Assembly.global D r).support.rows ≤ _
      exact hrows.trans ((Nat.mul_le_mul_right (Assembly.rowBudget D) hinput).trans (Nat.le_add_right _ _))
    · omega
  exact (Dense.reachable_payload h).trans (Dense.payload_mono (by omega) hm)

theorem encoded_length_input (labels : Computability.Encoding (Label (s := s) (b := b)) Bool)
    (C : ℕ) (hc : ∀ a, (labels.encode a).length ≤ C) (r : Input s b arity) :
    ((Expr.encoding labels).encode (expression D r)).length ≤
      (2 * C + 14) * (6 * (RawClosedNetwork.encoding.encode r.val).length + 3) + 1 := by
  have h := Holant.OneHot.StackProgram.codeEncoding_length_le labels C hc (expression D r).code
  rw [Expr.code_length] at h
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (expression_size_input D r)) 1)

/-- The structural proof covers every actually interpreted arithmetic operand.
The only algebraic literals are fixed local scales and eight phase constants. -/
theorem scalar_trace_bound {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
    (F : Holant.Algebraic.FixedField K d) (coeff : Label (s := s) (b := b) → Fin d → ℚ)
    (r : Input s b arity) :
    ∀ x ∈ (expression D r).trace (FieldInterpreter.coefficients F coeff), ∀ i,
      Holant.Algebraic.rationalBitHeight (F.decode.symm x i) ≤
        FieldInterpreter.width F coeff (codeBudget r.val.vertices.length r.val.edges.length) :=
  (FieldInterpreter.coordinate_trace_bound F coeff _ _ (expression_size D r)).2

theorem scalar_trace_input_bound {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
    (F : Holant.Algebraic.FixedField K d) (coeff : Label (s := s) (b := b) → Fin d → ℚ)
    (r : Input s b arity) :
    ∀ x ∈ (expression D r).trace (FieldInterpreter.coefficients F coeff), ∀ i,
      Holant.Algebraic.rationalBitHeight (F.decode.symm x i) ≤
        FieldInterpreter.width F coeff (6 * (RawClosedNetwork.encoding.encode r.val).length + 3) :=
  (FieldInterpreter.coordinate_trace_bound F coeff _ _ (expression_size_input D r)).2

end
end Holant.LocalDrafts.Tractability.AffineMachine.RawCode
