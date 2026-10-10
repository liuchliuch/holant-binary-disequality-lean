import Holant.Proofs.Reductions.EightVertexNonexception.Coefficients
import Holant.Marked.SupportAtlas.Boolean
import Mathlib.Tactic.LinearCombination

/-! Exact parity-sector algebra for the physical two-row construction. The
network identity is proved separately; this minimal-import module provides
its literal coefficient table, defect factorization and support tests. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeSectorAlgebra
open Holant Holant.LocalDrafts.Hardness.EightVertexNonexception
variable {K : Type} [Field K]

def evenFactor (u v : Fin 4 → K) : K := u 2*u 3 + v 2*v 3

def oddFactor (u v : Fin 4 → K) (cross : Bool) : K :=
  if cross then u 2*v 2 + u 3*v 3 else u 2*v 3 + u 3*v 2

def output (a b : K) (u v : Fin 4 → K) (cross : Bool) : Signature K 4 :=
  let E := evenFactor u v
  let O := oddFactor u v cross
  table ⟨a*b*E,a*b*v 0*v 1*E,a*b*u 1*v 1*O,a*b*u 1*v 0*O,
    a*b*u 0*v 1*O,a*b*u 0*v 0*O,a*b*u 0*u 1*E,a*b*u 0*u 1*v 0*v 1*E⟩

/-- The first complementary pair always agrees; the other pair records
exactly the two parity-sector factors. -/
theorem defect (a b : K) (u v : Fin 4 → K) (cross : Bool) :
    (entries (output a b u v cross)).a * (entries (output a b u v cross)).x -
      (entries (output a b u v cross)).c * (entries (output a b u v cross)).z =
    (a*b)^2*u 0*u 1*v 0*v 1 * (evenFactor u v ^ 2 - oddFactor u v cross ^ 2) := by
  change (a*b*evenFactor u v)*(a*b*u 0*u 1*v 0*v 1*evenFactor u v) -
    (a*b*u 1*v 1*oddFactor u v cross)*(a*b*u 0*v 0*oddFactor u v cross) = _
  ring

theorem straight_factor (u v : Fin 4 → K) :
    evenFactor u v ^ 2 - oddFactor u v false ^ 2 =
      (u 2 ^ 2-v 2 ^ 2)*(u 3 ^ 2-v 3 ^ 2) := by
  simp only [evenFactor,oddFactor,Bool.false_eq_true,ite_false]
  ring

theorem crossed_factor (u v : Fin 4 → K) :
    evenFactor u v ^ 2 - oddFactor u v true ^ 2 =
      (u 2 ^ 2-v 3 ^ 2)*(u 3 ^ 2-v 2 ^ 2) := by
  simp only [evenFactor,oddFactor,ite_true]
  ring

theorem self_crossed_factor (u : Fin 4 → K) :
    evenFactor u u ^ 2 - oddFactor u u true ^ 2 = -(u 2 ^ 2-u 3 ^ 2)^2 := by
  rw [crossed_factor]
  ring

theorem output_full (a b : K) (u v : Fin 4 → K) (cross : Bool)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0)
    (hE : evenFactor u v ≠ 0) (hO : oddFactor u v cross ≠ 0) :
    ∀ x, output a b u v cross x ≠ 0 ↔ Holant.Marked.SupportAtlas.parity x = false := by
  intro x
  rw [word_eta x]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;>
    simp [output,table,Holant.Marked.SupportAtlas.parity,ha,hb,hu,hv,hE,hO]

theorem self_crossed_live [CharZero K] (u : Fin 4 → K)
    (hu : ∀ i, u i ≠ 0) (different : u 2 ^ 4 ≠ u 3 ^ 4) :
    evenFactor u u ≠ 0 ∧ oddFactor u u true ≠ 0 := by
  constructor
  · have he : evenFactor u u = 2*u 2*u 3 := by unfold evenFactor; ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (hu 2)) (hu 3)
  · intro hz
    apply different
    have h : u 2 ^ 2 + u 3 ^ 2 = 0 := by
      simpa [oddFactor,pow_two] using hz
    linear_combination (u 2 ^ 2-u 3 ^ 2) * h

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeSectorAlgebra
end
