import Holant.Proofs.LinearProgramming.Interface
import Holant.Complexity.FixedFieldMachines.PairEncoding
import Holant.Algebraic.RationalHeight

set_option autoImplicit false

/-! Kernel-checked recovery component. Canonical, signed endpoint bytes and a binary denominator
bound. No recovered rational, LP solver, optimization witness or basis is an
input field. A pending response is deliberately distinct from certified none.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines

abbrev Query := (ℚ × ℚ) × ℕ
def queryEncoding := pairEncoding RationalArithmetic.inputEncoding encodingNatBool
def lo (q : Query) : ℚ := q.1.1
def hi (q : Query) : ℚ := q.1.2
def cap (q : Query) : ℕ := q.2
def Valid (q : Query) : Prop := lo q ≤ hi q ∧ 0 < cap q
def Isolating (q : Query) : Prop := Valid q ∧ hi q-lo q < 1/(cap q:ℚ)^2
def Candidate (q : Query) (r : ℚ) : Prop := lo q ≤ r ∧ r ≤ hi q ∧ r.den ≤ cap q
instance (q : Query) : Decidable (Valid q) := by unfold Valid; infer_instance
instance (q : Query) : Decidable (Isolating q) := by unfold Isolating; infer_instance

abbrev Fraction := ℤ × ℕ
def fractionEncoding := pairEncoding IntegerArithmetic.encoding encodingNatBool
abbrev Neighbors := Fraction × Fraction
def neighborsEncoding := pairEncoding fractionEncoding fractionEncoding
abbrev StepInput := Query × Neighbors
def stepEncoding := pairEncoding queryEncoding neighborsEncoding

/-- (done, found); an unfinished Euclidean state never denotes none. -/
abbrev Result := (Bool × Bool) × (ℚ × Neighbors)
def resultEncoding := pairEncoding (pairEncoding encodingBoolBool encodingBoolBool)
  (pairEncoding rationalEncoding neighborsEncoding)
def done (r : Result) : Bool := r.1.1
def found (r : Result) : Bool := r.1.2
def answer (r : Result) : ℚ := r.2.1
def neighbors (r : Result) : Neighbors := r.2.2
def pending (s : Neighbors) : Result := ((false,false),(0,s))
def miss (s : Neighbors) : Result := ((true,false),(0,s))
def hit (r : ℚ) (s : Neighbors) : Result := ((true,true),(r,s))

end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
