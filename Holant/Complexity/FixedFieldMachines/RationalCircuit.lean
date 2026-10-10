import Holant.Complexity.FixedFieldMachines.Concrete
import Holant.Complexity.RationalArithmetic.Inverse
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Fixed rational circuits compile to actual polynomial Boolean-stack programs.
Every dimension and finite sum here is fixed before the input arrives; this does
not assert a uniform variable-dimension determinant algorithm. -/
namespace Holant.Complexity.FixedFieldMachines.RationalCircuit
open Computability BinaryCompose Holant.Algebraic
open scoped BigOperators
noncomputable section
variable {α I : Type} {ea : Encoding α Bool}
set_option backward.isDefEq.respectTransparency false

def add {f g : α→ℚ} (a : Computes ea rationalEncoding f) (b : Computes ea rationalEncoding g) :
    Computes ea rationalEncoding (fun x => f x+g x) := Concrete.rationalProvider.addComputes a b

def mul {f g : α→ℚ} (a : Computes ea rationalEncoding f) (b : Computes ea rationalEncoding g) :
    Computes ea rationalEncoding (fun x => f x*g x) := Concrete.rationalProvider.mulComputes a b

def inv {f : α→ℚ} (a : Computes ea rationalEncoding f) :
    Computes ea rationalEncoding (fun x => (f x)⁻¹) :=
  congrComputes (a.andThen RationalArithmetic.inverseComputes) (fun _ => rfl)

def listSum (s : List I) (f : α→I→ℚ)
    (w : ∀i,Computes ea rationalEncoding (fun a => f a i)) :
    Computes ea rationalEncoding (fun a => (s.map (f a)).sum) :=
  match s with
  | [] => congrComputes (constantComputes ea rationalEncoding 0) (by simp)
  | i::s => congrComputes (add (w i) (listSum s f w)) (by simp)

def listProd (s : List I) (f : α→I→ℚ)
    (w : ∀i,Computes ea rationalEncoding (fun a => f a i)) :
    Computes ea rationalEncoding (fun a => (s.map (f a)).prod) :=
  match s with
  | [] => congrComputes (constantComputes ea rationalEncoding 1) (by simp)
  | i::s => congrComputes (mul (w i) (listProd s f w)) (by simp)

def sum [DecidableEq I] (s : Finset I) (f : α→I→ℚ)
    (w : ∀i,Computes ea rationalEncoding (fun a => f a i)) :
    Computes ea rationalEncoding (fun a => ∑i∈s,f a i) :=
  congrComputes (listSum s.toList f w) (fun a => Finset.sum_map_toList s (f a))

def prod [DecidableEq I] (s : Finset I) (f : α→I→ℚ)
    (w : ∀i,Computes ea rationalEncoding (fun a => f a i)) :
    Computes ea rationalEncoding (fun a => ∏i∈s,f a i) :=
  congrComputes (listProd s.toList f w) (fun a => Finset.prod_map_toList s (f a))

/-- Leibniz determinants have fixed program syntax and ordinary rational costs. -/
def determinant [Fintype I] [DecidableEq I] (M : α→Matrix I I ℚ)
    (w : ∀i j,Computes ea rationalEncoding (fun a => M a i j)) :
    Computes ea rationalEncoding (fun a => (M a).det) := by
  let term (σ : Equiv.Perm I) := mul
    (constantComputes ea rationalEncoding ((Equiv.Perm.sign σ : ℤ):ℚ))
    (prod Finset.univ (fun a i => M a (σ i) i) (fun i => w (σ i) i))
  exact congrComputes (sum Finset.univ
    (fun a σ => ((Equiv.Perm.sign σ : ℤ):ℚ)*∏i,M a (σ i) i) term)
    (fun a => (Matrix.det_apply' (M a)).symm)

end
end Holant.Complexity.FixedFieldMachines.RationalCircuit
