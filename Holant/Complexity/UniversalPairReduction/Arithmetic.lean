import Holant.Complexity.FixedFieldMachines.Concrete
import Holant.Complexity.UniversalPairReduction.BinaryTable

/-! Actual polynomial-time Boolean-stack arithmetic for the one-pair answer.
All subtraction and division are compiled as fixed-field addition and
multiplication by fixed constants; the original field encoding is unchanged. -/
namespace Holant.Complexity.UniversalPairReduction
open Computability BinaryCompose FixedFieldMachines Holant.Algebraic
noncomputable section
variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
variable (F : FixedField K n)

/-- Three answers, in the order S, T-plus, T-minus. -/
abbrev answerEncoding := pairEncoding F.encoding (pairEncoding F.encoding F.encoding)

def addComputes {α : Type} {e : Encoding α Bool} {f g : α → K}
    (a : Computes e F.encoding f) (b : Computes e F.encoding g) :
    Computes e F.encoding (fun x => f x + g x) :=
  congrComputes ((pairComputes a b).andThen (Concrete.fieldAddition F)) (fun _ => rfl)

def mulComputes {α : Type} {e : Encoding α Bool} {f g : α → K}
    (a : Computes e F.encoding f) (b : Computes e F.encoding g) :
    Computes e F.encoding (fun x => f x * g x) :=
  congrComputes ((pairComputes a b).andThen (Concrete.fieldMultiplication F)) (fun _ => rfl)

def scaleComputes {α : Type} {e : Encoding α Bool} {f : α → K}
    (a : Computes e F.encoding f) (c : K) :
    Computes e F.encoding (fun x => f x*c) :=
  mulComputes F a (constantComputes e F.encoding c)

/-- This is the concrete constant-multiply machine, not an arithmetic oracle. -/
def halfComputes : Computes F.encoding F.encoding (fun x => x/2) :=
  congrComputes (scaleComputes F (identityComputes F.encoding) (2:K)⁻¹)
    (fun _ => div_eq_mul_inv _ _ |>.symm)

def firstAnswer : Computes (answerEncoding F) F.encoding (fun p => p.1) :=
  Wiring.firstComputes F.encoding (pairEncoding F.encoding F.encoding)

def plusAnswer : Computes (answerEncoding F) F.encoding (fun p => p.2.1) :=
  congrComputes ((Wiring.secondComputes F.encoding (pairEncoding F.encoding F.encoding)).andThen
    (Wiring.firstComputes F.encoding F.encoding)) (fun _ => rfl)

def minusAnswer : Computes (answerEncoding F) F.encoding (fun p => p.2.2) :=
  congrComputes ((Wiring.secondComputes F.encoding (pairEncoding F.encoding F.encoding)).andThen
    (Wiring.secondComputes F.encoding F.encoding)) (fun _ => rfl)

/-- Fixed B is chosen once for the fixed family, so the inverse gap is a fixed
coefficient constant, rather than an input-dependent inversion operation. -/
def asymmetricComputes (b c : K) : Computes (answerEncoding F) F.encoding
    (fun p => (p.1 + (p.2.1-p.2.2)/(b-c))/2) := by
  let difference := addComputes F (plusAnswer F) (scaleComputes F (minusAnswer F) (-1))
  let scaled := scaleComputes F difference (b-c)⁻¹
  let added := addComputes F (firstAnswer F) scaled
  exact congrComputes (added.andThen (halfComputes F)) (fun p => by
    simp only [Function.comp_def,div_eq_mul_inv,mul_neg_one,sub_eq_add_neg])

theorem asymmetric_inFP (b c : K) : InFP (answerEncoding F) F.encoding
    (fun p => (p.1 + (p.2.1-p.2.2)/(b-c))/2) :=
  (asymmetricComputes F b c).inFP

end
end Holant.Complexity.UniversalPairReduction
