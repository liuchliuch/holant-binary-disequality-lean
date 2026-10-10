import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.CertificateMachine.Output


namespace Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.RootSearchDriver.Height
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine CertificateMachine

abbrev State := ℕ × (ℕ × ℕ)
abbrev tailEncoding := pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding
abbrev stateEncoding := pairEncoding encodingNatBool tailEncoding
def start (h : ℕ) : State := (h,1,0)
def step (s : State) : State :=
  (s.1/2, s.2.1+s.2.1, if s.1%2=0 then s.2.2 else s.2.2+s.2.1)
def materialize (h : ℕ) : ℕ := (Iterate.value stateEncoding step (start h)).2.2

theorem quotient_iterate (s : State) (n : ℕ) : ((step^[n]) s).1 = s.1/2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change ((step^[n]) s).1/2 = _
    rw [ih, Nat.div_div_eq_div_mul, pow_succ]

def invariant (s : State) := s.2.2+s.2.1*s.1
theorem invariant_step (s : State) : invariant (step s) = invariant s := by
  rcases Nat.mod_two_eq_zero_or_one s.1 with he | ho
  · have h : s.1 = 2*(s.1/2) := by omega
    simp only [invariant, step, he, ite_true]
    calc
      _ = s.2.2+s.2.1*(2*(s.1/2)) := by ring
      _ = _ := by rw [← h]
  · have h : s.1 = 2*(s.1/2)+1 := by omega
    simp only [invariant, step, ho, Nat.one_ne_zero, ite_false]
    calc
      _ = s.2.2+s.2.1*(2*(s.1/2)+1) := by ring
      _ = _ := by rw [← h]

theorem invariant_iterate (s : State) (n : ℕ) : invariant ((step^[n]) s) = invariant s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', invariant_step, ih]

theorem materialize_eq (h : ℕ) : materialize h = h := by
  let n := (stateEncoding.encode (start h)).length
  have hs : Nat.size h ≤ n := by
    simp only [n, stateEncoding, start, pairEncoding_length, encodingNatBool, encodeNat_length]
    omega
  have hb : h < 2^n := (Nat.lt_size_self h).trans_le
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hs)
  have hz : ((step^[n]) (start h)).1 = 0 := by
    rw [quotient_iterate]
    exact Nat.div_eq_of_lt hb
  have hi := invariant_iterate (start h) n
  unfold invariant at hi
  rw [hz,Nat.mul_zero,Nat.add_zero] at hi
  change ((step^[n]) (start h)).2.2 = h
  simpa only [start,Nat.one_mul,Nat.zero_add] using hi

/-- Deliberately redundant finite cutoff. Every scalar of at most h bits fits
below it. Its tokens are actually constructed, not supplied as extra input. -/
def cutoff (h : ℕ) : ℕ := 2^(h+1)*(h+1)
def double (n : ℕ) : ℕ := n+n
theorem double_iterate (a n : ℕ) : (double^[n]) a = 2^n*a := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', double, ih, pow_succ]; ring
theorem expand_eq (h : ℕ) :
    Iterate.value UnaryBinary.unaryEncoding double (h+1) = cutoff h := by
  simp only [Iterate.value, UnaryBinary.unaryEncoding, List.length_replicate,
    double_iterate, cutoff]
theorem pow_le_cutoff (h : ℕ) : 2^h ≤ cutoff h := by
  have hp : 2^h ≤ 2^(h+1) := Nat.pow_le_pow_right (by decide) (by omega)
  exact hp.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos h))

noncomputable section
def stepComputes : Computes stateEncoding stateEncoding step := by
  let q := Wiring.firstComputes encodingNatBool tailEncoding
  let tail := Wiring.secondComputes encodingNatBool tailEncoding
  let base := tail.andThen (Wiring.firstComputes _ _)
  let acc := tail.andThen (Wiring.secondComputes _ _)
  let even := (pairComputes (q.andThen Power.remainderTwo)
    (constantComputes stateEncoding encodingNatBool 0)).andThen Endpoints.equalComputes
  let doubled := (pairComputes base base).andThen AccessPrograms.unaryAdd
  let added := (pairComputes acc base).andThen AccessPrograms.unaryAdd
  exact congrComputes (pairComputes (q.andThen Power.half)
    (pairComputes doubled (ifComputes even acc added)))
    (fun s => by simp only [Function.comp_apply, step, decide_eq_true_eq])

def startComputes : Computes encodingNatBool stateEncoding start :=
  pairComputes (identityComputes encodingNatBool)
    (pairComputes (constantComputes encodingNatBool UnaryBinary.unaryEncoding 1)
      (constantComputes encodingNatBool UnaryBinary.unaryEncoding 0))

def binaryToUnary : FiniteComputes encodingNatBool UnaryBinary.unaryEncoding id :=
  (((FiniteComputes.ofPoly startComputes).andThen
    (Iterate.computes stateEncoding step (FiniteComputes.ofPoly stepComputes))).andThen
      (FiniteComputes.ofPoly ((Wiring.secondComputes encodingNatBool tailEncoding).andThen
        (Wiring.secondComputes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)))).congr materialize_eq

def doubleComputes : Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding double :=
  (Wiring.diagonalComputes UnaryBinary.unaryEncoding).andThen AccessPrograms.unaryAdd

def expandComputes : FiniteComputes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding cutoff :=
  ((FiniteComputes.ofPoly WireLists.succComputes).andThen
    (Iterate.computes UnaryBinary.unaryEncoding double (FiniteComputes.ofPoly doubleComputes))).congr expand_eq

def computes : FiniteComputes encodingNatBool UnaryBinary.unaryEncoding cutoff :=
  (binaryToUnary.andThen expandComputes).congr (fun _ => rfl)
end
end Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.RootSearchDriver.Height
