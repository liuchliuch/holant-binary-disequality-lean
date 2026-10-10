import Holant.Complexity.FixedFieldMachines.ArithmeticSyntax

/-! End-to-end primitive instruction accounting. This observer is used only in
cost theorems. It charges every executed push/pop/peek/load/branch/goto/halt,
including fixed-constant push sequences and all inlined scalar machine syntax. -/
namespace Holant.Complexity.FixedFieldMachines
open Turing Computability BinaryCompose

/-- Number of actual primitive instructions in the first `fuel` transitions. -/
def primitiveCost (m : Machine) : ℕ → Option m.Config → ℕ
  | 0, _ => 0
  | _ + 1, none => 0
  | fuel + 1, some c => match c.l with
    | none => 0
    | some label => (TM2Cost.primitiveRun (m.program label) c.var c.stk).1 +
      primitiveCost m fuel (m.computer.step c)

theorem primitiveCost_le (m : Machine) (fuel : ℕ) (c : Option m.Config) :
    primitiveCost m fuel c ≤ fuel * m.primitiveBudget := by
  induction fuel generalizing c with
  | zero => simp [primitiveCost]
  | succ fuel ih =>
    cases c with
    | none => simp [primitiveCost]
    | some c =>
      cases hl : c.l with
      | none => simp [primitiveCost, hl]
      | some label =>
        have hc := le_trans (TM2Cost.primitiveRun_cost_le (m.program label) c.var c.stk)
          (m.program_budget_le label)
        have hr := ih (m.computer.step c)
        simp only [primitiveCost, hl]
        simpa [Nat.add_mul, Nat.add_comm] using Nat.add_le_add hc hr

/-- Every uniform polynomial-time witness also has a polynomial bound on the
actual elementary instructions, with no unit-cost coefficient operation. -/
noncomputable def primitivePolynomial {α β : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
    {f : α → β} (w : Computes ea eb f) : Polynomial ℕ :=
  w.time * Polynomial.C w.machine.primitiveBudget

theorem computes_primitive_cost {α β : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
    {f : α → β} (w : Computes ea eb f) (a : α) :
    primitiveCost w.machine (w.outputs a).steps (some (initList w.machine.computer (ea.encode a))) ≤
      (primitivePolynomial w).eval (ea.encode a).length := by
  have h := primitiveCost_le w.machine (w.outputs a).steps
    (some (initList w.machine.computer (ea.encode a)))
  exact le_trans h (by simpa [primitivePolynomial] using
    Nat.mul_le_mul_right w.machine.primitiveBudget (w.outputs a).steps_le_m)

theorem addition_primitive_cost (R : RationalProvider) (n : ℕ) (p : (Fin n → ℚ) × (Fin n → ℚ)) :
    primitiveCost (additionComputes R n).machine ((additionComputes R n).outputs p).steps
      (some (initList (additionComputes R n).machine.computer ((vectorPairEncoding n).encode p))) ≤
      (primitivePolynomial (additionComputes R n)).eval ((vectorPairEncoding n).encode p).length :=
  computes_primitive_cost (additionComputes R n) p

theorem multiplication_primitive_cost (R : RationalProvider) {n : ℕ}
    (D : Holant.Algebraic.ArithmeticData n) (p : (Fin n → ℚ) × (Fin n → ℚ)) :
    primitiveCost (multiplicationComputes R D).machine ((multiplicationComputes R D).outputs p).steps
      (some (initList (multiplicationComputes R D).machine.computer ((vectorPairEncoding n).encode p))) ≤
      (primitivePolynomial (multiplicationComputes R D)).eval ((vectorPairEncoding n).encode p).length :=
  computes_primitive_cost (multiplicationComputes R D) p

end Holant.Complexity.FixedFieldMachines
