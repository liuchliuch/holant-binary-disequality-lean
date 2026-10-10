import Holant.Proofs.LinearProgramming.Complexity.PrimitiveAccounting
import Holant.Proofs.LinearProgramming.Complexity.ListLemmas
import Holant.Proofs.LinearProgramming.Optimization.Search.RoundedTermination
import Holant.Proofs.LinearProgramming.Support.MachineCombinators

/-! Rational LP physical resource implementation, adapted from the supplied reference.
Physical center/factor storage on framed rational tables, driven by ORIGINAL
Codec.Input. This is exactly RoundedGeometry.value, including inflation.
Canonical bit bounds cover every actually stored rounded state and the
initial state. The separate StepProgram implements the matrix update and
executes this storage program; CounterLoop charges its real finite loops
and intermediate arithmetic on original-input-bounded query words.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.StorageProgram
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion
open Holant.LocalDrafts.RemoteWork.RationalLP.Optimization Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search
open Holant.LocalDrafts.RemoteWork.RationalLP.Complexity
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators

open FactorUpdate Codec
noncomputable section

abbrev Code := List ℚ × List (List ℚ)
def matrixEncoding := framedListEncoding pointEncoding
def encoding := pairEncoding pointEncoding matrixEncoding
def code {n : ℕ} (s : FactorUpdate.State n) : Code := (List.ofFn s.center,List.ofFn (fun i => List.ofFn (s.factor i)))
def decode (n : ℕ) (s : Code) : FactorUpdate.State n :=
  { center := fun i => s.1.getD i.val 0
    factor := fun i j => (s.2.getD i.val []).getD j.val 0 }

theorem decode_code {n : ℕ} (s : FactorUpdate.State n) : decode n (code s)=s := by
  cases s
  unfold decode code
  congr 1
  · funext i
    exact DensePrograms.getD_ofFn _ i _
  · funext i j
    rw [DensePrograms.getD_ofFn]
    exact DensePrograms.getD_ofFn _ j _

abbrev Query := Input × Code
def queryEncoding := pairEncoding inputEncoding encoding
def source : Computes queryEncoding inputEncoding Prod.fst := Wiring.firstComputes _ _
def stored : Computes queryEncoding encoding Prod.snd := Wiring.secondComputes _ _

def lambda (d : Raw) : ℚ := 1+RoundingDeterminant.eta d.dimension
def lambdaComputes : Computes inputEncoding rationalEncoding (fun d : Input => lambda d.val) :=
  (pairComputes (constantComputes inputEncoding rationalEncoding 1) GridPrecision.etaComputes).andThen
    RationalArithmetic.additionComputes

def scaleVector : Computes (pairEncoding rationalEncoding pointEncoding) pointEncoding
    (fun q : ℚ × List ℚ => q.2.map (fun x => q.1*x)) :=
  mapListComputes rationalEncoding rationalEncoding rationalEncoding (fun a x => a*x)
    RationalArithmetic.multiplicationComputes
def scaleMatrix : Computes (pairEncoding rationalEncoding matrixEncoding) matrixEncoding
    (fun q : ℚ × List (List ℚ) => q.2.map (fun row => row.map (fun x => q.1*x))) :=
  mapListComputes rationalEncoding pointEncoding pointEncoding (fun a row => row.map (fun x => a*x)) scaleVector

def value (q : Query) : Code :=
  (q.2.1.map (fun x => SignedRound.value (x,GridPrecision.grid q.1.val)),
    q.2.2.map (fun row => row.map (fun x => lambda q.1.val*SignedRound.value (x,GridPrecision.grid q.1.val))))

def computes : Computes queryEncoding encoding value := by
  let h := source.andThen GridPrecision.gridComputes
  let c := stored.andThen (Wiring.firstComputes pointEncoding matrixEncoding)
  let R := stored.andThen (Wiring.secondComputes pointEncoding matrixEncoding)
  let center := (pairComputes h c).andThen SignedRound.vectorComputes
  let matrix := (pairComputes h R).andThen SignedRound.matrixComputes
  let scaled := (pairComputes (source.andThen lambdaComputes) matrix).andThen scaleMatrix
  exact congrComputes (pairComputes center scaled) (fun q => by simp only [value,List.map_map,Function.comp_def])

private theorem rounded_center_entry {n : ℕ} (s : FactorUpdate.State n) (h : ℕ) (eta : ℚ) (i : Fin n) :
    (RoundedGeometry.value s h eta).center i=SignedRound.value (s.center i,h) := rfl
private theorem rounded_factor_entry {n : ℕ} (s : FactorUpdate.State n) (h : ℕ) (eta : ℚ)
    (i j : Fin n) :
    (RoundedGeometry.value s h eta).factor i j=(1+eta)*SignedRound.value (s.factor i j,h) := rfl

theorem correct (d : Input) (s : FactorUpdate.State d.val.dimension) :
    value (d,code s)=code (RoundedGeometry.value s (GridPrecision.grid d.val) (RoundingDeterminant.eta d.val.dimension)) := by
  apply Prod.ext
  · change (List.ofFn s.center).map (fun x => SignedRound.value (x,GridPrecision.grid d.val))=
      List.ofFn (RoundedGeometry.value s (GridPrecision.grid d.val) (RoundingDeterminant.eta d.val.dimension)).center
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact (rounded_center_entry s _ _ i).symm
  · change (List.ofFn (fun i => List.ofFn (s.factor i))).map (fun row =>
        row.map (fun x => lambda d.val*SignedRound.value (x,GridPrecision.grid d.val)))=
      List.ofFn (fun i => List.ofFn
        ((RoundedGeometry.value s (GridPrecision.grid d.val) (RoundingDeterminant.eta d.val.dimension)).factor i))
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    change (List.ofFn (fun j : Fin d.val.dimension => s.factor i j)).map
        (fun x => lambda d.val*SignedRound.value (x,GridPrecision.grid d.val))=
      List.ofFn (fun j : Fin d.val.dimension =>
        (RoundedGeometry.value s (GridPrecision.grid d.val)
          (RoundingDeterminant.eta d.val.dimension)).factor i j)
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    exact (rounded_factor_entry s _ _ i j).symm

def etaDenominator (n : ℕ) : ℕ := 64*n*(n^3+1)
def etaDenominatorComputes : Computes inputEncoding encodingNatBool
    (fun d : Input => etaDenominator d.val.dimension) := by
  let n := PrecisionProgram.dimensionComputes
  let nn := (pairComputes n n).andThen RationalArithmetic.naturalMultiplicationComputes
  let cube := (pairComputes nn n).andThen RationalArithmetic.naturalMultiplicationComputes
  let p := cube.andThen PrecisionProgram.successor
  let scale := (pairComputes (constantComputes inputEncoding encodingNatBool 64) n).andThen
    RationalArithmetic.naturalMultiplicationComputes
  exact congrComputes ((pairComputes scale p).andThen RationalArithmetic.naturalMultiplicationComputes)
    (fun d => by
      change (64*d.val.dimension)*(1+d.val.dimension*d.val.dimension*d.val.dimension)=
        etaDenominator d.val.dimension
      unfold etaDenominator
      ring)

theorem lambda_height (d : Raw) (hn : 1≤d.dimension) :
    rationalHeight (lambda d)≤2*etaDenominator d.dimension := by
  have hd : 0<etaDenominator d.dimension := by unfold etaDenominator; positivity
  have hz : (etaDenominator d.dimension:ℤ)≠0 := by exact_mod_cast Nat.ne_of_gt hd
  have he : RoundingDeterminant.eta d.dimension=Rat.divInt 1 (etaDenominator d.dimension) := by
    simp [RoundingDeterminant.eta,etaDenominator,Rat.divInt_eq_div]
  have hheight : rationalHeight (RoundingDeterminant.eta d.dimension)≤etaDenominator d.dimension := by
    rw [he]
    apply max_le
    · exact (divInt_num_le _ _ hz).trans (by simpa using (show 1≤etaDenominator d.dimension from by omega))
    · simpa using divInt_den_le 1 (etaDenominator d.dimension) hz
  have h := rationalHeight_add 1 (RoundingDeterminant.eta d.dimension)
  simp only [rationalHeight,Rat.num_one,Rat.den_one,Int.natAbs_one,max_self,mul_one] at h
  exact h.trans (Nat.mul_le_mul_left 2 hheight)

def cellBound (d : Raw) : ℕ :=
  2*((GridPrecision.inverseBudget d+1).size+(GridPrecision.grid d).size+(etaDenominator d.dimension).size+3)

theorem scalar_height (q : ℚ) (h U : ℕ) (hh : 0<h) (hq : |q|≤(U:ℚ)) :
    rationalBitHeight (SignedRound.value (q,h))≤(U+1).size+h.size := by
  obtain ⟨hn,hd⟩ := SignedRound.components q h U hh hq
  have hm : rationalHeight (SignedRound.value (q,h))≤(U+1)*h := by
    apply max_le
    · exact hn.trans (Nat.mul_le_mul_right h (Nat.le_succ U))
    · exact hd.trans (by nlinarith)
  exact (Nat.size_le_size hm).trans (natSize_mul_le _ _)

private theorem lambda_bits (d : Raw) (hn : 1≤d.dimension) :
    rationalBitHeight (lambda d)≤(etaDenominator d.dimension).size+2 := by
  have hs := Nat.size_le_size (lambda_height d hn)
  have hm := natSize_mul_le 2 (etaDenominator d.dimension)
  change rationalBitHeight (lambda d)≤_ at hs
  rw [show Nat.size 2=2 from rfl] at hm
  omega

/-- Abstract scalar bounds keep canonical encoding proofs separate from the
large programmes which physically produce U, h and E from the original input. -/
private theorem rounded_scalar_word (q : ℚ) (h U E : ℕ) (hh : 0<h) (hq : |q|≤(U:ℚ)) :
    (rationalEncoding.encode (SignedRound.value (q,h))).length≤
      2*((U+1).size+h.size+E.size+3) := by
  have hb := scalar_height q h U hh hq
  have he := rationalEncoding_length_le_height (SignedRound.value (q,h))
  omega

private theorem scaled_scalar_word (a q : ℚ) (h U E : ℕ) (hh : 0<h)
    (hq : |q|≤(U:ℚ)) (ha : rationalBitHeight a≤E.size+2) :
    (rationalEncoding.encode (a*SignedRound.value (q,h))).length≤
      2*((U+1).size+h.size+E.size+3) := by
  have hb := scalar_height q h U hh hq
  have hm := rationalBitHeight_mul a (SignedRound.value (q,h))
  have he := rationalEncoding_length_le_height (a*SignedRound.value (q,h))
  omega

theorem rounded_cell (d : Raw) (hn : 1≤d.dimension) (s : FactorUpdate.State d.dimension)
    (hs : RegisterGrowth.Bounded s (GridPrecision.inverseBudget d:ℕ)) :
    (∀ i, (rationalEncoding.encode ((RoundedGeometry.value s (GridPrecision.grid d)
      (RoundingDeterminant.eta d.dimension)).center i)).length≤cellBound d) ∧
    (∀ i j, (rationalEncoding.encode ((RoundedGeometry.value s (GridPrecision.grid d)
      (RoundingDeterminant.eta d.dimension)).factor i j)).length≤cellBound d) := by
  have hh := GridPrecision.grid_pos d
  have hlam := lambda_bits d hn
  refine ⟨?_,?_⟩
  · intro i
    rw [rounded_center_entry]
    exact rounded_scalar_word (s.center i) (GridPrecision.grid d) (GridPrecision.inverseBudget d)
      (etaDenominator d.dimension) hh (hs.1 i)
  · intro i j
    rw [rounded_factor_entry]
    exact scaled_scalar_word (lambda d) (s.factor i j) (GridPrecision.grid d) (GridPrecision.inverseBudget d)
      (etaDenominator d.dimension) hh (hs.2.1 i j) hlam

def cellPolynomial : Polynomial ℕ := 2*(GridPrecision.inverseBudgetComputes.outputBound.bound+
  GridPrecision.gridComputes.outputBound.bound+etaDenominatorComputes.outputBound.bound+4)
def rowPolynomial : Polynomial ℕ := (2*cellPolynomial+2)*Polynomial.X+1
def statePolynomial : Polynomial ℕ := 2*rowPolynomial+1+(2*rowPolynomial+2)*Polynomial.X+1

private theorem size_successor (U : ℕ) : (U+1).size≤U.size+1 := by
  apply Nat.size_le.mpr
  calc
    U+1 ≤ 2^U.size := Nat.succ_le_of_lt (Nat.lt_size_self U)
    _ < 2^(U.size+1) := by
      rw [pow_succ]
      have hp : 0<2^U.size := by positivity
      omega

private theorem natural_output_bits {A : Type} {ea : Encoding A Bool} {f : A → ℕ}
    (w : Computes ea encodingNatBool f) (a : A) :
    (f a).size≤w.outputBound.bound.eval (ea.encode a).length := by
  simpa only [encodingNatBool,encodeNat_length] using w.outputBound.length_le a

private theorem cellPolynomial_eval (L : ℕ) : cellPolynomial.eval L=
    2*(GridPrecision.inverseBudgetComputes.outputBound.bound.eval L+
      GridPrecision.gridComputes.outputBound.bound.eval L+etaDenominatorComputes.outputBound.bound.eval L+4) := by
  simp only [cellPolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_ofNat]

private theorem cell_arithmetic (U H E a b c : ℕ)
    (hU : U.size≤a) (hH : H.size≤b) (hE : E.size≤c) :
    2*((U+1).size+H.size+E.size+3)≤2*(a+b+c+4) := by
  have hs := size_successor U
  omega

theorem cell_bound (d : Input) : cellBound d.val≤cellPolynomial.eval (inputEncoding.encode d).length := by
  have hU := natural_output_bits GridPrecision.inverseBudgetComputes d
  have hH := natural_output_bits GridPrecision.gridComputes d
  have hD := natural_output_bits etaDenominatorComputes d
  rw [cellPolynomial_eval]
  exact cell_arithmetic (GridPrecision.inverseBudget d.val) (GridPrecision.grid d.val)
    (etaDenominator d.val.dimension) _ _ _ hU hH hD

private theorem encoded_code_bound {n : ℕ} (s : FactorUpdate.State n) (B L : ℕ)
    (hn : n≤L) (hc : ∀ i, (rationalEncoding.encode (s.center i)).length≤B)
    (hR : ∀ i j, (rationalEncoding.encode (s.factor i j)).length≤B) :
    (encoding.encode (code s)).length≤
      2*((2*B+2)*L+1)+1+(2*((2*B+2)*L+1)+2)*L+1 := by
  let R := (2*B+2)*L+1
  have hcenter : (pointEncoding.encode (List.ofFn s.center)).length≤R := by
    have h := ListBounds.framed_length rationalEncoding (List.ofFn s.center) B
      (fun x hx => by obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact hc i)
    simp only [List.length_ofFn] at h
    exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (2*B+2) hn) 1)
  have hrows : ∀ row∈List.ofFn (fun i => List.ofFn (s.factor i)),
      (pointEncoding.encode row).length≤R := by
    intro row hrow
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
    have h := ListBounds.framed_length rationalEncoding (List.ofFn (s.factor i)) B
      (fun x hx => by obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx; exact hR i j)
    simp only [List.length_ofFn] at h
    exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (2*B+2) hn) 1)
  have hmatrix : (matrixEncoding.encode (List.ofFn (fun i => List.ofFn (s.factor i)))).length≤
      (2*R+2)*L+1 := by
    have h := ListBounds.framed_length pointEncoding (List.ofFn (fun i => List.ofFn (s.factor i))) R hrows
    simp only [List.length_ofFn] at h
    exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (2*R+2) hn) 1)
  simp only [encoding,code,pairEncoding_length]
  change 2*(pointEncoding.encode (List.ofFn s.center)).length+1+
    (matrixEncoding.encode (List.ofFn (fun i => List.ofFn (s.factor i)))).length≤
      2*R+1+(2*R+2)*L+1
  omega

private theorem statePolynomial_eval (L : ℕ) : statePolynomial.eval L=
    2*((2*cellPolynomial.eval L+2)*L+1)+1+
      (2*((2*cellPolynomial.eval L+2)*L+1)+2)*L+1 := by
  simp only [statePolynomial,rowPolynomial,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]

theorem encoded_state (d : Input) (s : FactorUpdate.State d.val.dimension)
    (hc : ∀ i, (rationalEncoding.encode (s.center i)).length≤cellBound d.val)
    (hR : ∀ i j, (rationalEncoding.encode (s.factor i j)).length≤cellBound d.val) :
    (encoding.encode (code s)).length≤statePolynomial.eval (inputEncoding.encode d).length := by
  let L := (inputEncoding.encode d).length
  have hn : d.val.dimension≤L := InputBounds.dimension_le d.val
  have hB := cell_bound d
  rw [statePolynomial_eval]
  exact encoded_code_bound s (cellPolynomial.eval L) L hn
    (fun i => (hc i).trans hB) (fun i j => (hR i j).trans hB)

private theorem initial_scalar_word (q : ℚ) (U H E : ℕ) (hq : rationalHeight q≤U) :
    (rationalEncoding.encode q).length≤2*((U+1).size+H.size+E.size+3) := by
  have hs : rationalBitHeight q≤U.size := Nat.size_le_size hq
  have he := rationalEncoding_length_le_height q
  have hsucc : U.size≤(U+1).size := Nat.size_le_size (Nat.le_succ U)
  omega

theorem initial_cell (d : Raw) :
    (∀ i, (rationalEncoding.encode ((Containment.start d.dimension).center i)).length≤cellBound d) ∧
    (∀ i j, (rationalEncoding.encode ((Containment.start d.dimension).factor i j)).length≤cellBound d) := by
  let U := GridPrecision.inverseBudget d
  have hU : 1≤U := by have hp := GridPrecision.inverseBudget_pos d; change 0<U at hp; omega
  have hp : 1≤2^GridPrecision.exponent d := Nat.one_le_pow _ _ (by decide)
  have hinit : 2*(d.dimension+1)≤U := by
    dsimp [U,GridPrecision.inverseBudget]
    nlinarith [Nat.mul_le_mul_left (16*(d.dimension+1)) hp]
  have hzero : rationalHeight (0 : ℚ)≤U := by simpa [rationalHeight] using hU
  have hdiag : rationalHeight (2*((d.dimension:ℚ)+1))≤U := by
    have he : 2*((d.dimension:ℚ)+1)=((2*(d.dimension+1):ℕ):ℚ) := by push_cast; ring
    rw [he]
    simpa only [rationalHeight,Rat.num_natCast,Rat.den_natCast,Int.natAbs_natCast] using max_le hinit hU
  have hword (q : ℚ) (hq : rationalHeight q≤U) : (rationalEncoding.encode q).length≤cellBound d := by
    exact initial_scalar_word q U (GridPrecision.grid d) (etaDenominator d.dimension) hq
  refine ⟨?_,?_⟩
  · intro i
    change (rationalEncoding.encode (0 : ℚ)).length≤cellBound d
    exact hword 0 hzero
  intro i j
  change (rationalEncoding.encode ((2*((d.dimension:ℚ)+1))*((1 : Mat d.dimension) i j))).length≤cellBound d
  rw [Matrix.one_apply]
  split_ifs
  · simpa only [mul_one] using hword _ hdiag
  · simpa only [mul_zero] using hword 0 hzero

private theorem actual_update_budget (d : Raw) (hn : 2≤d.dimension) (k : ℕ)
    (hk : k≤GridPrecision.iterations d) (c : Separation.Constraint d)
    (hg : Separation.normal d c≠0) :
    RegisterGrowth.Bounded (FactorUpdate.update (RoundedTrajectory.run d k) (Separation.normal d c))
      (GridPrecision.inverseBudget d:ℚ) := by
  obtain ⟨hR,hs,_⟩ := RoundedTrajectory.invariant d hn k hk
  let M : ℚ := RoundedTrajectory.growth d.dimension k
  have hM : 0≤M := by dsimp [M]; positivity
  have hb := RegisterGrowth.update_bounded hn (RoundedTrajectory.run d k)
    (Separation.normal d c) hR hg M hM hs
  have hu : 16*((d.dimension:ℚ)+1)*M≤(GridPrecision.inverseBudget d:ℚ) := by
    dsimp only [M]
    exact_mod_cast RoundedTrajectory.intermediate_budget d k hk
  exact RegisterGrowth.bounded_mono _ hb hu

/-- Canonical storage bound for EVERY actual round, including inactive rounds
and infeasible inputs. Unlike a local magnitude premise, this is derived from
the original input and actual run; it can be used to retime the future loop.
-/
theorem actual_cell (d : Input) (hn : 2≤d.val.dimension) (k : ℕ)
    (hk : k≤GridPrecision.iterations d.val) :
    (∀ i, (rationalEncoding.encode ((RoundedTrajectory.run d.val k).center i)).length≤cellBound d.val) ∧
    (∀ i j, (rationalEncoding.encode ((RoundedTrajectory.run d.val k).factor i j)).length≤cellBound d.val) := by
  revert hk
  induction k with
  | zero => intro hk; simpa only [RoundedTrajectory.run_zero] using initial_cell d.val
  | succ k ih =>
    intro hk
    have prev := ih (by omega)
    rw [RoundedTrajectory.run_succ]
    cases hc : Separation.separate d.val (RoundedTrajectory.run d.val k).center with
    | none => simpa only [RoundedTrajectory.step,hc] using prev
    | some c =>
      by_cases hg : Separation.normal d.val c=0
      · simpa only [RoundedTrajectory.step,hc,if_pos hg] using prev
      · simp only [RoundedTrajectory.step,hc,if_neg hg]
        exact rounded_cell d.val (by omega) _ (actual_update_budget d.val hn k (by omega) c hg)

theorem actual_state_length (d : Input) (hn : 2≤d.val.dimension) (k : ℕ)
    (hk : k≤GridPrecision.iterations d.val) :
    (encoding.encode (code (RoundedTrajectory.run d.val k))).length≤statePolynomial.eval (inputEncoding.encode d).length := by
  obtain ⟨hc,hR⟩ := StorageProgram.actual_cell d hn k hk
  exact encoded_state d _ hc hR

def machine : Machine := computes.machine
def time : Polynomial ℕ := computes.time
def storagePolynomial : Polynomial ℕ := Polynomial.X+primitivePolynomial computes
@[simp] theorem same_machine : machine=computes.machine := rfl
@[simp] theorem same_clock : time=computes.time := rfl
theorem inFP : InFP queryEncoding encoding value := computes.inFP

theorem execution (q : Query) :
    StackProtocol.RunsExactly computes.machine.computer.step
      (Turing.initList computes.machine.computer (queryEncoding.encode q))
      (Turing.haltList computes.machine.computer (encoding.encode (value q)))
      (computes.outputs q).steps := (computes.outputs q).evals_in_steps

theorem steps_bound (q : Query) : (computes.outputs q).steps≤time.eval (queryEncoding.encode q).length :=
  (computes.outputs q).steps_le_m

private theorem computes_encoded_execution {A B : Type}
    {ea : Encoding A Bool} {eb : Encoding B Bool} {f : A → B}
    (M : Computes ea eb f) (a : A) (b : B) (he : f a=b) :
    (fun c : Option M.machine.Config => c.bind M.machine.computer.step)^[
      (M.outputs a).steps]
      (some (initList M.machine.computer (ea.encode a)))=
        some (haltList M.machine.computer (eb.encode b)) := by
  subst b
  exact (M.outputs a).evals_in_steps

theorem rounded_execution (d : Input) (s : FactorUpdate.State d.val.dimension) :
    StackProtocol.RunsExactly machine.computer.step
      (initList machine.computer (queryEncoding.encode (d,code s)))
      (haltList machine.computer (encoding.encode
        (code (RoundedGeometry.value s (GridPrecision.grid d.val) (RoundingDeterminant.eta d.val.dimension)))))
      (computes.outputs (d,code s)).steps := by
  dsimp only [machine]
  exact computes_encoded_execution computes (d,code s) _ (correct d s)

theorem physical_cost (q : Query) :
    primitiveCost computes.machine (computes.outputs q).steps
      (some (Turing.initList computes.machine.computer (queryEncoding.encode q)))≤
      (primitivePolynomial computes).eval (queryEncoding.encode q).length := computes_primitive_cost computes q

theorem prefix_storage (q : Query) (t : ℕ) (ht : t≤(computes.outputs q).steps)
    (c : machine.Config) (hc : (fun p => p.bind machine.computer.step)^[t]
      (some (initList machine.computer (queryEncoding.encode q)))=some c) :
    stackSize c.stk≤storagePolynomial.eval (queryEncoding.encode q).length := by
  have hs := machine.run_size_le _ c t hc
  rw [Machine.size_init] at hs
  have hcost := Nat.mul_le_mul_right machine.primitiveBudget (ht.trans (computes.outputs q).steps_le_m)
  apply hs.trans
  simpa only [storagePolynomial,FixedFieldMachines.primitivePolynomial,machine,time,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C] using
    Nat.add_le_add_left hcost (queryEncoding.encode q).length

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.StorageProgram
