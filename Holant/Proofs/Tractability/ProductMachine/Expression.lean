import Holant.OneHot.StackProgram.Serialization
import Holant.OneHot.ArithmeticSizeEncoding


namespace Holant.LocalDrafts.Tractability.ProductMachine

inductive Expr (A : Type) where
  | zero
  | one
  | literal (a : A)
  | add (a b : Expr A)
  | mul (a b : Expr A)
  deriving DecidableEq

namespace Expr

open Holant.OneHot Holant.OneHot.StackProgram
variable {A K B : Type} [CommSemiring K]

def eval (coeff : A → K) : Expr A → K
  | .zero => 0
  | .one => 1
  | .literal a => coeff a
  | .add a b => a.eval coeff + b.eval coeff
  | .mul a b => a.eval coeff * b.eval coeff

def size : Expr A → ℕ
  | .zero | .one | .literal _ => 1
  | .add a b | .mul a b => a.size + b.size + 1

theorem size_pos (e : Expr A) : 1 ≤ e.size := by cases e <;> simp [size]

/-- Evaluate the right child first so the top two stack cells have the exact
left/right order used in the source expression. Each child is compiled once. -/
def code : Expr A → Code A
  | .zero => [.zero]
  | .one => [.one]
  | .literal a => [.literal a]
  | .add a b => b.code ++ a.code ++ [.add]
  | .mul a b => b.code ++ a.code ++ [.mul]

def trace (coeff : A → K) : Expr A → List K
  | .zero | .one | .literal _ => []
  | .add a b => b.trace coeff ++ a.trace coeff ++ [a.eval coeff, b.eval coeff, a.eval coeff + b.eval coeff]
  | .mul a b => b.trace coeff ++ a.trace coeff ++ [a.eval coeff, b.eval coeff, a.eval coeff * b.eval coeff]

theorem code_length (e : Expr A) : e.code.length = e.size := by
  induction e <;> simp_all [code, size] <;> omega

/-- Actual underflow-checking interpreter semantics, for every stack suffix. -/
theorem run_code (coeff : A → K) (e : Expr A) (stack : List K) :
    run coeff e.code stack = some (e.eval coeff :: stack, e.trace coeff) := by
  induction e generalizing stack <;>
    simp_all [code, run_append, run, step, eval, trace, List.append_assoc]

def product : List (Expr A) → Expr A
  | [] => .one
  | e :: es => .mul e (product es)

theorem eval_product (coeff : A → K) (es : List (Expr A)) :
    (product es).eval coeff = (es.map (eval coeff)).prod := by
  induction es <;> simp_all [product, eval]

theorem size_product (es : List (Expr A)) :
    (product es).size = (es.map size).sum + es.length + 1 := by
  induction es <;> simp_all [product, size] <;> omega

theorem size_product_le (es : List (Expr A)) (h : ∀ e ∈ es, e.size ≤ 1) :
    (product es).size ≤ 2 * es.length + 1 := by
  induction es with
  | nil => simp [product, size]
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [product, size, List.length_cons]
    omega

variable (coeff : A → K) (family : B → K)

/-- Structural sum-product witnesses are constructed for the result and the
complete executed trace; they are not extra input certificates. -/
theorem arithmetic_bound (unit : B) (hunit : family unit = 1)
    (hc : ∀ a, ArithmeticSize.Bound family 1 (coeff a)) (e : Expr A) :
    ArithmeticSize.Bound family e.size (e.eval coeff) ∧
      ∀ x ∈ e.trace coeff, ArithmeticSize.Bound family e.size x := by
  induction e with
  | zero => exact ⟨ArithmeticSize.Bound.zero unit 1, by simp [trace]⟩
  | one => exact ⟨ArithmeticSize.Bound.one.mono unit hunit (Nat.zero_le _), by simp [trace]⟩
  | literal a => exact ⟨hc a, by simp [trace]⟩
  | add a b ha hb =>
    have haa := ha.1.mono unit hunit (show a.size ≤ a.size + b.size by omega)
    have hbb := hb.1.mono unit hunit (show b.size ≤ a.size + b.size by omega)
    have hz := haa.add unit hunit hbb
    refine ⟨hz, ?_⟩
    intro x hx
    simp only [trace, List.mem_append, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false, or_assoc] at hx
    rcases hx with hx | hx | rfl | rfl | rfl
    · exact (hb.2 x hx).mono unit hunit (by simp only [size]; omega)
    · exact (ha.2 x hx).mono unit hunit (by simp only [size]; omega)
    · exact ha.1.mono unit hunit (by simp only [size]; omega)
    · exact hb.1.mono unit hunit (by simp only [size]; omega)
    · exact hz
  | mul a b ha hb =>
    have hz := (ha.1.mul hb.1).mono unit hunit (show a.size + b.size ≤ a.size + b.size + 1 by omega)
    refine ⟨hz, ?_⟩
    intro x hx
    simp only [trace, List.mem_append, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false, or_assoc] at hx
    rcases hx with hx | hx | rfl | rfl | rfl
    · exact (hb.2 x hx).mono unit hunit (by simp only [size]; omega)
    · exact (ha.2 x hx).mono unit hunit (by simp only [size]; omega)
    · exact ha.1.mono unit hunit (by simp only [size]; omega)
    · exact hb.1.mono unit hunit (by simp only [size]; omega)
    · exact hz

end Expr
end Holant.LocalDrafts.Tractability.ProductMachine
