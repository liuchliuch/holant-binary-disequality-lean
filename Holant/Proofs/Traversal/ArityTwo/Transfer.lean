import Holant.Kernel
import Holant.Tractable.Criteria
import Mathlib.Tactic.Ring


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo
open Holant
open scoped BigOperators
variable {K : Type*} [CommSemiring K]

def product : List (Kernel K) → Kernel K
  | [] => Signature.equality
  | M::ms => Kernel.mul M (product ms)

/-- Literal successive summation over the shared internal Boolean indices. -/
def contraction : List (Kernel K) → Bool → Bool → K
  | [], a, b => Signature.equality a b
  | M::ms, a, b => ∑ x : Bool, M a x * contraction ms x b

theorem product_contraction (ms : List (Kernel K)) : product ms = contraction ms := by
  induction ms with
  | nil => rfl
  | cons M ms ih =>
    simp only [product, contraction, ih]
    rfl

theorem product_append (xs ys : List (Kernel K)) :
    product (xs++ys) = Kernel.mul (product xs) (product ys) := by
  induction xs with
  | nil => simp [product]
  | cons M xs ih => simp only [List.cons_append,product,ih,Kernel.mul_assoc]

/-- An open endpoint message; the empty list leaves an isolated unary intact. -/
def message (ms : List (Kernel K)) (right : Bool → K) : Bool → K :=
  Kernel.act (product ms) right

@[simp] theorem message_nil (right : Bool → K) : message [] right = right := by
  simp [message,product]

@[simp] theorem message_cons (M : Kernel K) (ms : List (Kernel K)) (right : Bool → K) :
    message (M::ms) right = Kernel.act M (message ms right) := by
  exact Kernel.act_mul M (product ms) right

def pathValue (left : Bool → K) (ms : List (Kernel K)) (right : Bool → K) : K :=
  ∑ a : Bool, left a * message ms right a

def cycleValue (ms : List (Kernel K)) : K := Kernel.trace (product ms)

theorem path_contraction (left right : Bool → K) (ms : List (Kernel K)) :
    pathValue left ms right = ∑ a : Bool, ∑ b : Bool, left a * contraction ms a b * right b := by
  rw [pathValue,message,product_contraction]
  simp [Kernel.act,Finset.mul_sum,mul_assoc,mul_add,Signature.equality]

theorem cycle_contraction (ms : List (Kernel K)) :
    cycleValue ms = ∑ a : Bool, contraction ms a a := by
  rw [cycleValue,Kernel.trace,product_contraction]

/-- Two unary occurrences and their real connecting edge. -/
theorem unary_edge (left right : Bool → K) (E : Kernel K) :
    pathValue left [E] right = ∑ a : Bool, ∑ b : Bool, left a * E a b * right b := by
  simp [pathValue,message,product,Kernel.act,Finset.mul_sum,mul_assoc,mul_add,Signature.equality]

/-- A self-loop consumes both distinct ports of one binary occurrence. -/
theorem self_loop (B E : Kernel K) :
    cycleValue [B,E] = ∑ a : Bool, ∑ b : Bool, B a b * E b a := by
  simp [cycleValue,product,Kernel.trace,Kernel.mul,Signature.equality,mul_add,mul_assoc]

/-- The length-two multigraph cycle retains both parallel edge occurrences. -/
theorem parallel_cycle (B E C F : Kernel K) :
    cycleValue [B,E,C,F] =
      ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
        B a b * E b c * C c d * F d a := by
  simp [cycleValue,product,Kernel.trace,Kernel.mul,Finset.mul_sum,mul_assoc,mul_add,Signature.equality]

theorem native_self_loop (B : Kernel K) :
    cycleValue [B,Signature.disequality] = B false true + B true false := by
  rw [self_loop]
  simp [Signature.disequality,add_comm]

theorem ordinary_self_loop (B : Kernel K) :
    cycleValue [B,Signature.equality] = B false false + B true true := by
  simp [cycleValue,product,Kernel.trace,add_comm]

def basis (b : Bool) : Bool → K := fun a => if a = b then 1 else 0

theorem message_basis (ms : List (Kernel K)) (a b : Bool) :
    message ms (basis b) a = product ms a b := by
  cases b <;> simp [message,Kernel.act,basis]

theorem cycle_two_columns (ms : List (Kernel K)) :
    cycleValue ms = message ms (basis false) false + message ms (basis true) true := by
  simp [message_basis,cycleValue,Kernel.trace,add_comm]

/-- Shape of a completed closed component. Cycles are nonempty by construction;
the algebraic empty trace (=2) is never used for an empty graph component. -/
inductive Component (A : Type*) where
  | scalar (a : A)
  | path (left : Bool → A) (matrices : List (Kernel A)) (right : Bool → A)
  | cycle (head : Kernel A) (tail : List (Kernel A))

def realizeMatrix {A : Type*} (coeff : A → K) (M : Kernel A) : Kernel K :=
  fun a b => coeff (M a b)

def Component.eval {A : Type*} (coeff : A → K) : Component A → K
  | .scalar a => coeff a
  | .path l ms r => pathValue (fun b => coeff (l b)) (ms.map (realizeMatrix coeff)) (fun b => coeff (r b))
  | .cycle M ms => cycleValue ((M::ms).map (realizeMatrix coeff))

def evaluateComponents {A : Type*} (coeff : A → K) (cs : List (Component A)) : K :=
  (cs.map (Component.eval coeff)).prod

@[simp] theorem empty_components {A : Type*} (coeff : A → K) : evaluateComponents coeff [] = 1 := rfl
@[simp] theorem nullary_component {A : Type*} (coeff : A → K) (a : A) :
    evaluateComponents coeff [.scalar a] = coeff a := by simp [evaluateComponents,Component.eval]

/-- Ordinary transpose records a traversal against the local ordered ports. -/
def orient {A : Type*} (reversed : Bool) (M : Kernel A) : Kernel A :=
  if reversed then Kernel.transpose M else M

@[simp] theorem realize_orient {A : Type*} (coeff : A → K) (r : Bool) (M : Kernel A) :
    realizeMatrix coeff (orient r M) = orient r (realizeMatrix coeff M) := by cases r <;> rfl

end Holant.LocalDrafts.TraversalCompletion.ArityTwo
