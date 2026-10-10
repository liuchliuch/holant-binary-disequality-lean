import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.CertificateMachine.Power


namespace Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.CertificateMachine.Evaluation
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open Scalars

abbrev State := RationalPolynomialCode × (Gaussian × (Gaussian × ℕ))
abbrev tailEncoding := pairEncoding gaussianEncoding (pairEncoding gaussianEncoding UnaryBinary.unaryEncoding)
abbrev stateEncoding := pairEncoding polynomialEncoding tailEncoding
abbrev inputEncoding := pairEncoding polynomialEncoding gaussianEncoding
def start (x : RationalPolynomialCode × Gaussian) : State := (x.1,x.2,(0,0),0)
def term (s : State) : ℕ × ℚ := s.1.getD s.2.2.2 (0,0)
def step (s : State) : State :=
  (s.1,s.2.1,gadd s.2.2.1 (gmul (scalar (term s).2) (Power.power (s.2.1,(term s).1))),s.2.2.2+1)
def evaluate (x : RationalPolynomialCode × Gaussian) : Gaussian :=
  (Iterate.value stateEncoding step (start x)).2.2.1

theorem eval_drop (z : GaussianRational) (p : RationalPolynomialCode) (i : ℕ) :
    evalGaussian z (p.drop i) =
      ((p.getD i (0,0)).2 : GaussianRational) * z ^ (p.getD i (0,0)).1 +
        evalGaussian z (p.drop (i+1)) := by
  induction p generalizing i with
  | nil => simp [evalGaussian]
  | cons t ps ih =>
    cases i with
    | zero => rfl
    | succ i => simpa using ih i

def invariant (s : State) : GaussianRational :=
  gaussian s.2.2.1 + evalGaussian (gaussian s.2.1) (s.1.drop s.2.2.2)

theorem invariant_step (s : State) : invariant (step s) = invariant s := by
  simp only [invariant, step, gaussian_gadd, gaussian_gmul, gaussian_scalar, Power.power_correct]
  rw [eval_drop (gaussian s.2.1) s.1 s.2.2.2]
  simp only [term]
  ring

theorem invariant_iterate (s : State) (n : ℕ) : invariant ((step^[n]) s) = invariant s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', invariant_step, ih]

theorem polynomial_iterate (s : State) (n : ℕ) : ((step^[n]) s).1 = s.1 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply', step] using ih
theorem index_iterate (s : State) (n : ℕ) : ((step^[n]) s).2.2.2 = s.2.2.2+n := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [Function.iterate_succ_apply', step, ih, Nat.add_assoc]

theorem evaluate_correct (x : RationalPolynomialCode × Gaussian) :
    gaussian (evaluate x) = evalGaussian (gaussian x.2) x.1 := by
  let n := (stateEncoding.encode (start x)).length
  have hlen : x.1.length ≤ n := by
    have h := framedListEncoding_length_lower termEncoding x.1
    change 2*x.1.length+1 ≤ (polynomialEncoding.encode x.1).length at h
    simp only [n, stateEncoding, start, pairEncoding_length]
    omega
  have hi := invariant_iterate (start x) n
  have hp := polynomial_iterate (start x) n
  have hn := index_iterate (start x) n
  have hd : (((step^[n]) (start x)).1).drop (((step^[n]) (start x)).2.2.2) = [] := by
    rw [hp, hn]
    simpa only [start, Nat.zero_add] using (List.drop_eq_nil_of_le hlen : x.1.drop n = [])
  change gaussian (evaluate x) = _
  have hz : gaussian (0,0) = (0 : GaussianRational) := rfl
  unfold invariant at hi
  rw [hd] at hi
  change gaussian ((step^[n]) (start x)).2.2.1 = _
  simpa only [evalGaussian, add_zero, start, List.drop_zero, hz, zero_add] using hi

noncomputable section
def polynomial : Computes stateEncoding polynomialEncoding (fun s => s.1) :=
  Wiring.firstComputes polynomialEncoding tailEncoding
def tail : Computes stateEncoding tailEncoding (fun s => s.2) := Wiring.secondComputes _ _
def base : Computes stateEncoding gaussianEncoding (fun s => s.2.1) :=
  tail.andThen (Wiring.firstComputes gaussianEncoding (pairEncoding gaussianEncoding UnaryBinary.unaryEncoding))
def accIndex : Computes stateEncoding (pairEncoding gaussianEncoding UnaryBinary.unaryEncoding)
    (fun s => s.2.2) := tail.andThen (Wiring.secondComputes _ _)
def acc : Computes stateEncoding gaussianEncoding (fun s => s.2.2.1) :=
  accIndex.andThen (Wiring.firstComputes _ _)
def index : Computes stateEncoding UnaryBinary.unaryEncoding (fun s => s.2.2.2) :=
  accIndex.andThen (Wiring.secondComputes _ _)
def termComputes : Computes stateEncoding termEncoding term :=
  (pairComputes polynomial index).andThen (WireLists.getD termEncoding (0,0))
def termExponent : Computes stateEncoding encodingNatBool (fun s => (term s).1) :=
  termComputes.andThen (Wiring.firstComputes _ _)
def termScalar : Computes stateEncoding gaussianEncoding (fun s => scalar (term s).2) :=
  pairComputes (termComputes.andThen (Wiring.secondComputes _ _))
    (constantComputes stateEncoding rationalEncoding 0)

def stepComputes : FiniteComputes stateEncoding stateEncoding step := by
  let power := (FiniteComputes.ofPoly (pairComputes base termExponent)).andThen Power.computes
  let product := ((FiniteComputes.ofPoly termScalar).pair power).andThen
    (FiniteComputes.ofPoly (gaussianMul (Wiring.firstComputes gaussianEncoding gaussianEncoding)
      (Wiring.secondComputes gaussianEncoding gaussianEncoding)))
  let sum := ((FiniteComputes.ofPoly acc).pair product).andThen
    (FiniteComputes.ofPoly (gaussianAdd (Wiring.firstComputes gaussianEncoding gaussianEncoding)
      (Wiring.secondComputes gaussianEncoding gaussianEncoding)))
  exact (FiniteComputes.ofPoly polynomial).pair ((FiniteComputes.ofPoly base).pair
    (sum.pair (FiniteComputes.ofPoly (index.andThen WireLists.succComputes))))

def startComputes : Computes inputEncoding stateEncoding start :=
  pairComputes (Wiring.firstComputes polynomialEncoding gaussianEncoding)
    (pairComputes (Wiring.secondComputes polynomialEncoding gaussianEncoding)
      (pairComputes (constantComputes inputEncoding gaussianEncoding (0,0))
        (constantComputes inputEncoding UnaryBinary.unaryEncoding 0)))

def computes : FiniteComputes inputEncoding gaussianEncoding evaluate :=
  ((FiniteComputes.ofPoly startComputes).andThen
    (Iterate.computes stateEncoding step stepComputes)).andThen (FiniteComputes.ofPoly acc)

end
end Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.CertificateMachine.Evaluation
