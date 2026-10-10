import Holant.Proofs.LinearProgramming.Optimization.Search.InverseBounds
import Holant.Proofs.LinearProgramming.Optimization.Search.Decay

/-!
A genuine original-input-derived finite budget for the existing rational
trajectory in dimensions at least two. Inner-box containment bounds the
inverse determinant; each explicit block of active updates halves the upper
bound. Thus the concrete budgeted query decides original feasibility.
The exact trajectory can still have large rational denominators. This is a
correct finite algorithm, not a polynomial-time or physical-loop capstone.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.BudgetTermination
open FactorUpdate Containment
open scoped BigOperators Matrix
noncomputable section

def outerExponent (n : ℕ) : ℕ := (n+2)*n
def blocks (d : Codec.Raw) : ℕ := outerExponent d.dimension+InverseBounds.exponent d+1
def iterations (d : Codec.Raw) : ℕ := Decay.block d.dimension*blocks d
def value (d : Codec.Raw) : Bool :=
  decide (Separation.separate d (Trajectory.run d (iterations d)).center=none)

theorem start_det_bound (n : ℕ) : |(start n).factor.det|≤((2^outerExponent n:ℕ):ℚ) := by
  have hs : n+1≤2^(n+1) := (Nat.lt_two_pow_self (n := n+1)).le
  have hb : 2*(n+1)≤2^(n+2) := by
    have h := Nat.mul_le_mul_left 2 hs
    simpa only [show n+2=(n+1)+1 by omega,pow_succ,Nat.mul_comm] using h
  have hp := Nat.pow_le_pow_left hb n
  have he : (2*(n+1))^n≤2^outerExponent n := by simpa [outerExponent,← pow_mul] using hp
  simp only [start,Matrix.det_smul,Matrix.det_one,mul_one,Fintype.card_fin]
  rw [abs_of_nonneg (by positivity)]
  exact_mod_cast he

/-- A prefix hypothesis describes actual outcomes of the concrete separator.
It is discharged in budget_accepts below, never supplied as an LP premise. -/
theorem active_prefix_bound (d : Codec.Raw) (hn : 2≤d.dimension) (k : ℕ)
    (ha : ∀ i<k, ∃ c, Separation.separate d (Trajectory.run d i).center=some c ∧
      Separation.normal d c≠0) :
    |(Trajectory.run d k).factor.det|≤
      |(start d.dimension).factor.det| * Scales.contraction d.dimension^k := by
  revert ha
  induction k with
  | zero => intro ha; simp [Trajectory.run]
  | succ k ih =>
    intro ha
    obtain ⟨c,hc,hg⟩ := ha k (by omega)
    have hs := Trajectory.active_progress d hn k c hc hg
    have hp := ih (fun i hi => ha i (by omega))
    calc
      _ ≤ |(Trajectory.run d k).factor.det| * Scales.contraction d.dimension := hs
      _ ≤ (|(start d.dimension).factor.det| * Scales.contraction d.dimension^k)*
          Scales.contraction d.dimension :=
        mul_le_mul_of_nonneg_right hp (Scales.contraction_pos _).le
      _ = _ := by rw [pow_succ]; ring

theorem earlier_not_accepted (d : Codec.Raw) (N : ℕ)
    (hN : Separation.separate d (Trajectory.run d N).center≠none) (i : ℕ) (hi : i≤N) :
    Separation.separate d (Trajectory.run d i).center≠none := by
  intro h
  have hr := Trajectory.accepted_fixed d i (N-i) h
  rw [Nat.add_sub_of_le hi] at hr
  apply hN
  simpa only [hr] using h

theorem feasible_active (d : Codec.Raw) (N : ℕ) (hf : ∃ x, Codec.Feasible d x)
    (hN : Separation.separate d (Trajectory.run d N).center≠none) (i : ℕ) (hi : i<N) :
    ∃ c, Separation.separate d (Trajectory.run d i).center=some c ∧ Separation.normal d c≠0 := by
  cases hc : Separation.separate d (Trajectory.run d i).center with
  | none => exact (earlier_not_accepted d N hN i hi.le hc).elim
  | some c =>
    refine ⟨c,rfl,?_⟩
    intro hz
    exact Trajectory.rejected_zero d i c hc hz hf

/-- Original feasibility implies acceptance by the derived budget, including
lower-dimensional original feasible faces and redundant equalities. -/
theorem budget_accepts (d : Codec.Raw) (hn : 2≤d.dimension) (hf : ∃ x, Codec.Feasible d x) :
    Separation.separate d (Trajectory.run d (iterations d)).center=none := by
  by_contra hN
  have hl := InverseBounds.actual_det_lower d hn (iterations d) hf
  have hu := active_prefix_bound d hn (iterations d) (feasible_active d _ hf hN)
  have hinit := start_det_bound d.dimension
  have hdec : Scales.contraction d.dimension^iterations d≤
      1/((2^blocks d:ℕ):ℚ) := Decay.blocks_decay d.dimension (blocks d)
  have hupper : |(Trajectory.run d (iterations d)).factor.det|≤
      ((2^outerExponent d.dimension:ℕ):ℚ)/((2^blocks d:ℕ):ℚ) := by
    calc
      _ ≤ |(start d.dimension).factor.det| * Scales.contraction d.dimension^iterations d := hu
      _ ≤ ((2^outerExponent d.dimension:ℕ):ℚ)*(1/((2^blocks d:ℕ):ℚ)) :=
        mul_le_mul hinit hdec (pow_nonneg (Scales.contraction_pos _).le _)
          (by positivity)
      _ = _ := by ring
  have houterPos : (0:ℚ)<((2^outerExponent d.dimension:ℕ):ℚ) := by positivity
  have hinversePos : (0:ℚ)<((2^InverseBounds.exponent d:ℕ):ℚ) := by positivity
  have hden : (2^blocks d:ℕ)=
      2^outerExponent d.dimension*2^InverseBounds.exponent d*2 := by
    rw [blocks,pow_succ,pow_add]
  have hexact : ((2^outerExponent d.dimension:ℕ):ℚ)/((2^blocks d:ℕ):ℚ)=
      1/(2*((2^InverseBounds.exponent d:ℕ):ℚ)) := by
    rw [hden,Nat.cast_mul,Nat.cast_mul,Nat.cast_ofNat]
    field_simp [ne_of_gt houterPos,ne_of_gt hinversePos]
    <;> ring
  rw [hexact] at hupper
  have hdouble : ((2^InverseBounds.exponent d:ℕ):ℚ)<
      2*((2^InverseBounds.exponent d:ℕ):ℚ) := by linarith
  have hstrict : (1:ℚ)/(2*((2^InverseBounds.exponent d:ℕ):ℚ))<
      1/((2^InverseBounds.exponent d:ℕ):ℚ) :=
    one_div_lt_one_div_of_lt hinversePos hdouble
  exact (not_le_of_gt hstrict) (hl.trans hupper)

theorem correct (d : Codec.Raw) (hn : 2≤d.dimension) :
    value d=true ↔ ∃ x, Codec.Feasible d x := by
  simp only [value,decide_eq_true_eq]
  exact ⟨Trajectory.accepted d _,budget_accepts d hn⟩

def iterationPolynomial : Polynomial ℕ :=
  2*(Polynomial.X^3+1)*((Polynomial.X+2)*Polynomial.X+Polynomial.X^2+
    (RadiusBudget.computes.outputBound.bound+1)*Polynomial.X+1)

theorem iterations_bound (d : Codec.Input) :
    iterations d.val ≤ iterationPolynomial.eval (Codec.inputEncoding.encode d).length := by
  let L := (Codec.inputEncoding.encode d).length
  have hn : d.val.dimension≤L := InputBounds.dimension_le d.val
  have hB : RadiusBudget.exponent d.val≤RadiusBudget.computes.outputBound.bound.eval L :=
    RadiusBudget.original_length_bound d
  have h3 := Nat.pow_le_pow_left hn 3
  have h2 := Nat.pow_le_pow_left hn 2
  have hsquare : d.val.dimension*d.val.dimension≤L^2 := by
    simpa only [pow_two] using h2
  have houter := Nat.mul_le_mul (Nat.add_le_add_right hn 2) hn
  have hinner := Nat.mul_le_mul (Nat.add_le_add_right hB 1) hn
  have hblocks : blocks d.val≤(L+2)*L+L^2+(RadiusBudget.computes.outputBound.bound.eval L+1)*L+1 := by
    unfold blocks outerExponent InverseBounds.exponent
    simpa only [Nat.add_assoc] using
      Nat.add_le_add_right (Nat.add_le_add houter (Nat.add_le_add hsquare hinner)) 1
  have hblock : Decay.block d.val.dimension≤2*(L^3+1) := by
    simpa only [Decay.block] using Nat.mul_le_mul_left 2 (Nat.add_le_add_right h3 1)
  have h := Nat.mul_le_mul hblock hblocks
  simpa [iterations,iterationPolynomial,L] using h

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.BudgetTermination
