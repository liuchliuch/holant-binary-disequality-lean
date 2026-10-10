import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.CertificateMachine.Iterate
import Holant.Complexity.BinaryArithmetic.EncodedDivision
import Holant.Algebraic.EncodingSize


namespace Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.CertificateMachine.Power
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler
open Scalars

abbrev State := ℕ × (Gaussian × Gaussian)
abbrev stateEncoding := pairEncoding encodingNatBool (pairEncoding gaussianEncoding gaussianEncoding)
abbrev inputEncoding := pairEncoding gaussianEncoding encodingNatBool
def start (x : Gaussian × ℕ) : State := (x.2,x.1,(1,0))
def step (s : State) : State :=
  (s.1/2, gmul s.2.1 s.2.1, if s.1%2=0 then s.2.2 else gmul s.2.2 s.2.1)
def power (x : Gaussian × ℕ) : Gaussian := (Iterate.value stateEncoding step (start x)).2.2

theorem exponent_iterate (s : State) (n : ℕ) : ((step^[n]) s).1 = s.1 / 2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change ((step^[n]) s).1 / 2 = _
    rw [ih, Nat.div_div_eq_div_mul, pow_succ]

def invariant (s : State) : GaussianRational := gaussian s.2.2 * gaussian s.2.1 ^ s.1
theorem invariant_step (s : State) : invariant (step s) = invariant s := by
  rcases Nat.mod_two_eq_zero_or_one s.1 with h | h
  · have hk : s.1 = 2*(s.1/2) := by omega
    simp only [invariant, step, h, ite_true, gaussian_gmul]
    rw [← pow_two, ← pow_mul, ← hk]
  · have hk : s.1 = 2*(s.1/2)+1 := by omega
    simp only [invariant, step, h, Nat.one_ne_zero, if_false, gaussian_gmul]
    rw [← pow_two, ← pow_mul]
    calc
      _ = gaussian s.2.2 * gaussian s.2.1 ^ (2*(s.1/2)+1) := by rw [pow_succ]; ring
      _ = _ := by rw [← hk]

theorem invariant_iterate (s : State) (n : ℕ) : invariant ((step^[n]) s) = invariant s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', invariant_step, ih]

theorem power_correct (x : Gaussian × ℕ) : gaussian (power x) = gaussian x.1 ^ x.2 := by
  let n := (stateEncoding.encode (start x)).length
  have hs : Nat.size x.2 ≤ n := by
    simp only [n, stateEncoding, start, pairEncoding_length, encodingNatBool, encodeNat_length]
    omega
  have hk : x.2 < 2^n := (Nat.lt_size_self x.2).trans_le
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hs)
  have hz : ((step^[n]) (start x)).1 = 0 := by
    rw [exponent_iterate]
    exact Nat.div_eq_of_lt hk
  have hi := invariant_iterate (start x) n
  have hone : gaussian (1,0) = (1 : GaussianRational) := rfl
  unfold invariant at hi
  rw [hz,pow_zero,mul_one] at hi
  change gaussian ((step^[n]) (start x)).2.2 = _
  simpa only [start,hone,one_mul] using hi

noncomputable section
abbrev divisionMachine (remainder : Bool) : Machine where
  K := (BinaryArithmetic.EncodedDivision.computer remainder).K
  input := (BinaryArithmetic.EncodedDivision.computer remainder).k₀
  output := (BinaryArithmetic.EncodedDivision.computer remainder).k₁
  Label := (BinaryArithmetic.EncodedDivision.computer remainder).Λ
  main := (BinaryArithmetic.EncodedDivision.computer remainder).main
  State := (BinaryArithmetic.EncodedDivision.computer remainder).σ
  initial := (BinaryArithmetic.EncodedDivision.computer remainder).initialState
  program := (BinaryArithmetic.EncodedDivision.computer remainder).m

def quotientEncoded : Computes BinaryArithmetic.EncodedDivision.inputEncoding encodingNatBool
    (fun x => x.1/x.2) where
  machine := divisionMachine false
  time := BinaryArithmetic.EncodedDivision.divisionPolyTime.time
  outputs x := by
    have h := BinaryArithmetic.EncodedDivision.divisionPolyTime.outputsFun x
    change TM2OutputsInTime (divisionMachine false).computer
      (List.map id (BinaryArithmetic.EncodedDivision.inputEncoding.encode x))
      (some (List.map id (encodingNatBool.encode (x.1/x.2)))) _ at h
    simpa only [List.map_id] using h
def remainderEncoded : Computes BinaryArithmetic.EncodedDivision.inputEncoding encodingNatBool
    (fun x => x.1%x.2) where
  machine := divisionMachine true
  time := BinaryArithmetic.EncodedDivision.remainderPolyTime.time
  outputs x := by
    have h := BinaryArithmetic.EncodedDivision.remainderPolyTime.outputsFun x
    change TM2OutputsInTime (divisionMachine true).computer
      (List.map id (BinaryArithmetic.EncodedDivision.inputEncoding.encode x))
      (some (List.map id (encodingNatBool.encode (x.1%x.2)))) _ at h
    simpa only [List.map_id] using h

def half : Computes encodingNatBool encodingNatBool (fun n => n/2) :=
  ((pairComputes (identityComputes encodingNatBool) (constantComputes encodingNatBool encodingNatBool 2)).andThen
    Endpoints.prepareArithmeticComputes).andThen quotientEncoded
def remainderTwo : Computes encodingNatBool encodingNatBool (fun n => n%2) :=
  ((pairComputes (identityComputes encodingNatBool) (constantComputes encodingNatBool encodingNatBool 2)).andThen
    Endpoints.prepareArithmeticComputes).andThen remainderEncoded

def stepComputes : Computes stateEncoding stateEncoding step := by
  let exponent := Wiring.firstComputes encodingNatBool (pairEncoding gaussianEncoding gaussianEncoding)
  let tail := Wiring.secondComputes encodingNatBool (pairEncoding gaussianEncoding gaussianEncoding)
  let base := tail.andThen (Wiring.firstComputes gaussianEncoding gaussianEncoding)
  let acc := tail.andThen (Wiring.secondComputes gaussianEncoding gaussianEncoding)
  let even := (pairComputes (exponent.andThen remainderTwo)
    (constantComputes stateEncoding encodingNatBool 0)).andThen Endpoints.equalComputes
  exact congrComputes (pairComputes (exponent.andThen half)
    (pairComputes (gaussianMul base base) (ifComputes even acc (gaussianMul acc base))))
    (fun s => by
      dsimp only [Function.comp_apply]
      simp only [step, decide_eq_true_eq])

def startComputes : Computes inputEncoding stateEncoding start :=
  pairComputes (Wiring.secondComputes gaussianEncoding encodingNatBool)
    (pairComputes (Wiring.firstComputes gaussianEncoding encodingNatBool)
      (constantComputes inputEncoding gaussianEncoding (1,0)))

def computes : FiniteComputes inputEncoding gaussianEncoding power :=
  ((FiniteComputes.ofPoly startComputes).andThen
    (Iterate.computes stateEncoding step (FiniteComputes.ofPoly stepComputes))).andThen
      (FiniteComputes.ofPoly ((Wiring.secondComputes encodingNatBool
        (pairEncoding gaussianEncoding gaussianEncoding)).andThen
          (Wiring.secondComputes gaussianEncoding gaussianEncoding)))

end
end Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.CertificateMachine.Power
