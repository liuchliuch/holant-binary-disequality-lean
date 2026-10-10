import Holant.OneHot.StackProgram.GraphCodeMachine.Components.Evaluation.Trace
import Holant.OneHot.ArithmeticSizeEncoding

namespace Holant.OneHot.StackProgram.GraphCodeMachine.Components.Evaluation
open Computability Holant.Complexity ArithmeticSize
variable {A K B : Type} [CommSemiring K]

/-- A closed root contributes its two actual arithmetic operations. -/
def closedBudget (ts : Forest A) : ℕ := 2 * (ts.vertices + ts.edges) + 2

def componentBudget : Descriptor A → ℕ
  | .dense => 0
  | .tree _ ts => closedBudget ts
  | .unicycle _ ts _ us => closedBudget ts + closedBudget us + 1

def productBudget (ds : List (Descriptor A)) : ℕ := (ds.map componentBudget).sum

variable (coeff : A → K) (family : B → K) (unit : B) (hunit : family unit = 1)
variable (hcoeff : ∀ a, Bound family 1 (coeff a))
include hunit hcoeff

theorem closed_bound (a : A) (ts : Forest A) :
    Bound family (closedBudget ts) ((interpretForest coeff ts).closedProgram (coeff a)).run.1 ∧
    Arithmetic.Safe (Bound family (closedBudget ts)) ((interpretForest coeff ts).closedProgram (coeff a)) := by
  have h := ArithmeticSize.closed_program_bound unit hunit (interpretForest coeff ts) (coeff a)
    (forest_all coeff _ hcoeff ts) (hcoeff a)
  simpa only [closedBudget, forestBudget, interpretForest_vertices, interpretForest_edges] using h

/-- Both unicycle residuals are evaluated once, then their actual addition is bounded. -/
theorem component_bound (d : Descriptor A) :
    Bound family (componentBudget d) (componentProgram coeff d).run.1 ∧
    Arithmetic.Safe (Bound family (componentBudget d)) (componentProgram coeff d) := by
  cases d with
  | dense => exact ⟨Bound.zero unit 0, Arithmetic.safe_pure _ _⟩
  | tree a ts => exact closed_bound coeff family unit hunit hcoeff a ts
  | unicycle a ts b us =>
    rcases closed_bound coeff family unit hunit hcoeff a ts with ⟨hx, hpx⟩
    rcases closed_bound coeff family unit hunit hcoeff b us with ⟨hy, hpy⟩
    have hx' := hx.mono unit hunit (Nat.le_add_right (closedBudget ts) (closedBudget us))
    have hy' := hy.mono unit hunit (Nat.le_add_left (closedBudget us) (closedBudget ts))
    have hz := hx'.add unit hunit hy'
    refine ⟨?_, ?_⟩
    · simpa only [componentProgram, componentBudget, bind, Arithmetic.run_bind, Arithmetic.run_addOp] using hz
    · apply Arithmetic.safe_bind (hpx.mono (fun _ h => h.mono unit hunit (by dsimp [componentBudget]; omega)))
      apply Arithmetic.safe_bind (hpy.mono (fun _ h => h.mono unit hunit (by dsimp [componentBudget]; omega)))
      exact Arithmetic.safe_addOp (hx.mono unit hunit (by dsimp [componentBudget]; omega))
        (hy.mono unit hunit (by dsimp [componentBudget]; omega)) hz

/-- Products combine disjoint descriptor budgets, including every partial product. -/
theorem product_bound (ds : List (Descriptor A)) :
    Bound family (productBudget ds) (productProgram coeff ds).run.1 ∧
    Arithmetic.Safe (Bound family (productBudget ds)) (productProgram coeff ds) := by
  induction ds with
  | nil => exact ⟨Bound.one, Arithmetic.safe_pure _ _⟩
  | cons d ds ih =>
    rcases component_bound coeff family unit hunit hcoeff d with ⟨hx, hpx⟩
    rcases ih with ⟨hy, hpy⟩
    have hz := hx.mul hy
    have he : productBudget (d :: ds) = componentBudget d + productBudget ds := rfl
    rw [he]
    refine ⟨?_, ?_⟩
    · simpa only [productProgram, bind, Arithmetic.run_bind, Arithmetic.run_mulOp] using hz
    · apply Arithmetic.safe_bind (hpx.mono (fun _ h => h.mono unit hunit (Nat.le_add_right _ _)))
      apply Arithmetic.safe_bind (hpy.mono (fun _ h => h.mono unit hunit (Nat.le_add_left _ _)))
      exact Arithmetic.safe_mulOp (hx.mono unit hunit (Nat.le_add_right _ _))
        (hy.mono unit hunit (Nat.le_add_left _ _)) hz

omit hunit hcoeff in
/-- The size budget is derived from the real closed-prefix word itself. -/
theorem closedBudget_le (e : Encoding A Bool) (a : A) (ts : Forest A) :
    closedBudget ts ≤ 2 * ((closedEncoding e).encode (a, ts)).length := by
  have h := forest_size_le_input e ts
  simp only [closedEncoding, FixedFieldMachines.pairEncoding, List.length_append,
    Holant.Algebraic.frame_length, TreeEncoding.forestEncoding]
  unfold closedBudget
  omega

omit hunit hcoeff in
theorem componentBudget_le (e : Encoding A Bool) (d : Descriptor A) :
    componentBudget d ≤ (encode e d).length := by
  cases d with
  | dense => simp [componentBudget]
  | tree a ts =>
    have h := closedBudget_le e a ts
    simp only [componentBudget, encode, List.length_append, List.length_cons, List.length_nil,
      Holant.Algebraic.frame_length]
    omega
  | unicycle a ts b us =>
    have ht := closedBudget_le e a ts
    have hu := closedBudget_le e b us
    simp only [componentBudget, encode, List.length_append, List.length_cons, List.length_nil,
      Holant.Algebraic.frame_length]
    omega

omit hunit hcoeff in
theorem productBudget_le (e : Encoding A Bool) (ds : List (Descriptor A)) :
    productBudget ds ≤ ((listEncoding e).encode ds).length := by
  have h : productBudget ds ≤ Components.payloadSize e ds := by
    induction ds with
    | nil => rfl
    | cons d ds ih =>
      have hd := componentBudget_le e d
      simpa only [productBudget, Components.payloadSize, List.map_cons, List.sum_cons] using Nat.add_le_add hd ih
  rw [Components.input_length]
  omega

end Holant.OneHot.StackProgram.GraphCodeMachine.Components.Evaluation
