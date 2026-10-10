import Holant.Proofs.Closure.ClosureMarkedMatrixFacts
import Holant.Proofs.Closure.OccurrenceScalarScope
import Mathlib.Tactic.LinearCombination

/-! Literal native-X/Z entry equations for the noncyclic order-four branch.
No analytic conjugator, row classifier, SourceDeck or desired shape is assumed.
The source group adapter separately derives these local matrix hypotheses. -/
noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureKleinShape
open Holant
open Holant.Certificates.MatchingContractionClosure
variable {L : Type*} [Field L]

/-- a Z + b (Z X), in the source's ordered Boolean-port convention. -/
def axis (a b : L) : Binary (K:=L) := fun i j =>
  if i then (if j then -a else -b) else (if j then b else a)

theorem axis_decomposition (a b : L) : axis a b =
    a • ClosureMarkedReversal.nativeZ + b • (ClosureMarkedReversal.nativeZ * X) := by
  ext i j
  cases i <;> cases j <;>
    simp [axis,ClosureMarkedReversal.nativeZ,X,Signature.disequality,Matrix.mul_apply]

theorem axis_det (a b : L) : Matrix.det (axis a b) = b^2-a^2 := by
  rw [ClosureMarkedReversal.det_bool]
  simp [axis]
  ring

theorem commutation_scalar_pm (A : Binary (K:=L)) (nonzero : A ≠ 0)
    (c : L) (commutation : A * X = c • (X * A)) : c = 1 ∨ c = -1 := by
  have he : A = c^2 • A := by
    calc
      A = (A*X)*X := by rw [Matrix.mul_assoc,X_mul_X,Matrix.mul_one]
      _ = (c • (X*A))*X := congrArg (fun B : Binary (K:=L) => B*X) commutation
      _ = c • (X*(A*X)) := by rw [Matrix.smul_mul,Matrix.mul_assoc]
      _ = c • (X*(c • (X*A))) := by rw [commutation]
      _ = c^2 • A := by
        rw [Matrix.mul_smul,smul_smul,← Matrix.mul_assoc,X_mul_X,Matrix.one_mul,pow_two]
  have hc : c^2 = 1 := (smul_left_injective L nonzero (by simpa using he.symm))
  have hp : (c-1)*(c+1)=0 := by
    calc
      _ = c^2-1 := by ring
      _ = 0 := by rw [hc]; ring
  rcases mul_eq_zero.mp hp with h | h
  · exact .inl (sub_eq_zero.mp h)
  · exact .inr (eq_neg_of_add_eq_zero_left h)

theorem anticommutation_axis (A : Binary (K:=L)) (anti : A*X = -(X*A)) :
    A = axis (A false false) (A false true) := by
  have h00 := congrArg (fun B : Binary (K:=L) => B false false) anti
  have h01 := congrArg (fun B : Binary (K:=L) => B false true) anti
  simp [X,Signature.disequality,Matrix.mul_apply] at h00 h01
  have h10 : A true false = - A false true := by simpa using (congrArg Neg.neg h00).symm
  have h11 : A true true = - A false false := by simpa using (congrArg Neg.neg h01).symm
  ext i j
  cases i <;> cases j <;> simp [axis,h10,h11]

variable [CharZero L]

/-- A second projective involution commuting with native X cannot commute
literally: the literal-commuting involutions are only the I/X scalar lines. -/
theorem commuting_involution_scalar_line (A : Binary (K:=L)) (nonzero : A ≠ 0)
    (commutation : A*X = X*A)
    (square : ∃ d : L, d ≠ 0 ∧ A*A = d • (1 : Binary (K:=L))) :
    (∃ c : L, c ≠ 0 ∧ A=c • (1 : Binary (K:=L))) ∨
      (∃ c : L, c ≠ 0 ∧ A=c • X) := by
  have h00 := congrArg (fun B : Binary (K:=L) => B false false) commutation
  have h01 := congrArg (fun B : Binary (K:=L) => B false true) commutation
  simp [X,Signature.disequality,Matrix.mul_apply] at h00 h01
  have h10 : A true false = A false true := h00.symm
  have h11 : A true true = A false false := h01.symm
  obtain ⟨d,hd,hs⟩ := square
  have off := congrArg (fun B : Binary (K:=L) => B false true) hs
  simp [Matrix.mul_apply,Matrix.smul_apply,Matrix.one_apply,h10,h11] at off
  have hp : (2:L)*(A false false * A false true)=0 := by
    calc
      _ = A false false * A false true + A false true * A false false := by ring
      _ = 0 := by simpa [add_comm] using off
  have hz := (mul_eq_zero.mp hp).resolve_left (by norm_num : (2:L) ≠ 0)
  rcases mul_eq_zero.mp hz with hu | hv
  · right
    have hn : A false true ≠ 0 := by
      intro hv
      apply nonzero
      ext i j
      cases i <;> cases j <;> simp [hu,hv,h10,h11]
    refine ⟨A false true,hn,?_⟩
    ext i j
    cases i <;> cases j <;> simp [X,Signature.disequality,Matrix.smul_apply,hu,h10,h11]
  · left
    have hn : A false false ≠ 0 := by
      intro hu
      apply nonzero
      ext i j
      cases i <;> cases j <;> simp [hu,hv,h10,h11]
    refine ⟨A false false,hn,?_⟩
    ext i j
    cases i <;> cases j <;> simp [Matrix.one_apply,Matrix.smul_apply,hv,h10,h11]

/-- Exact second-involution native form, rather than a chosen basis. -/
theorem second_involution_axis (A : Binary (K:=L)) (nonzero : A ≠ 0)
    (commutation : ∃ c : L, c ≠ 0 ∧ A*X = c • (X*A))
    (square : ∃ d : L, d ≠ 0 ∧ A*A = d • (1 : Binary (K:=L)))
    (notI : ¬ ∃ c : L, c ≠ 0 ∧ A=c • (1 : Binary (K:=L)))
    (notX : ¬ ∃ c : L, c ≠ 0 ∧ A=c • X) :
    A = axis (A false false) (A false true) := by
  obtain ⟨c,hc,comm⟩ := commutation
  rcases commutation_scalar_pm A nonzero c comm with he | he
  · rw [he,one_smul] at comm
    rcases commuting_involution_scalar_line A nonzero comm square with hi | hx
    · exact False.elim (notI hi)
    · exact False.elim (notX hx)
  · rw [he,neg_one_smul] at comm
    exact anticommutation_axis A comm

/-- Z fixes or exchanges the two remaining involution classes. The entry
relations force exactly the standard or exotic source axis equations. -/
theorem axis_normalization_cases (a b : L)
    (normalization :
      (∃ c : L, c ≠ 0 ∧ ClosureMarkedReversal.nativeZ * axis a b * ClosureMarkedReversal.nativeZ = c • axis a b) ∨
      (∃ c : L, c ≠ 0 ∧ ClosureMarkedReversal.nativeZ * axis a b * ClosureMarkedReversal.nativeZ = c • (X * axis a b))) :
    a*b=0 ∨ a^2+b^2=0 := by
  rcases normalization with ⟨c,hc,he⟩ | ⟨c,hc,he⟩
  · left
    have h00 := congrArg (fun B : Binary (K:=L) => B false false) he
    have h01 := congrArg (fun B : Binary (K:=L) => B false true) he
    simp [ClosureMarkedReversal.nativeZ,axis,Matrix.mul_apply,Matrix.smul_apply] at h00 h01
    by_cases ha : a=0
    · simp [ha]
    · have hc1 : c=1 := by
        apply (mul_right_cancel₀ ha)
        simpa using h00.symm
      rw [hc1,one_mul] at h01
      have hb : b=0 := CharZero.neg_eq_self_iff.mp h01
      simp [hb]
  · right
    have h00 := congrArg (fun B : Binary (K:=L) => B false false) he
    have h01 := congrArg (fun B : Binary (K:=L) => B false true) he
    simp [ClosureMarkedReversal.nativeZ,axis,X,Signature.disequality,Matrix.mul_apply,Matrix.smul_apply] at h00 h01
    have ha : a+c*b=0 := by linear_combination h00
    have hb : b-c*a=0 := by linear_combination h01
    calc
      a^2+b^2 = a*(a+c*b)+b*(b-c*a) := by ring
      _ = 0 := by rw [ha,hb]; ring

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureKleinShape
end
