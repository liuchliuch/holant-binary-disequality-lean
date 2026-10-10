import Holant.Proofs.LinearProgramming.Recovery.DenominatorGap
import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.Completion.Minimum
import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.DenominatorProgram
import Holant.Algebraic.RationalHeight

set_option autoImplicit false

/-! Kernel-checked recovery component. Ported into the exclusive task namespace and validated with the pinned toolchain.
Canonical denominator bounds for the original LP's rational basic points,
and a strict separation bound for distinct bounded-denominator rationals.
The minimizing point occurs only in mathematical existence proofs; it is
never chosen as machine output. K=4L^2+2 is physically emitted in unary,
whereas D=2^(2L^2) remains binary and is never enumeration fuel.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators Codec Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.BasicPoint Matrix
namespace Denominator

theorem rigid_denominator (d : Raw) (x : Fin d.dimension → ℚ)
    (hx : Feasible d x) (hr : Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.FaceMove.Rigid d x) (j : Fin d.dimension) :
    (x j).den≤InputBounds.denominator d := by
  obtain ⟨select,ha,hd⟩ := exists_basis d x hr
  let A := InputBounds.matrix d select
  let b := fun i => rightSide d x (select i)
  have he := DeterminantGap.integral_numerator A b x (basis_system d x hx select ha) j
  have hdq : (A.det:ℚ)≠0 := by exact_mod_cast hd
  have hxq : x j=Rat.divInt ((A.adjugate *ᵥ b) j) A.det := by
    rw [Rat.divInt_eq_div]
    exact (eq_div_iff hdq).mpr (by simpa [mul_comm] using he)
  have hden := Holant.Algebraic.divInt_den_le ((A.adjugate *ᵥ b) j) A.det hd
  have hdet : A.det.natAbs≤InputBounds.denominator d := by
    have hi : (A.det.natAbs : ℤ) ≤ (InputBounds.denominator d : ℤ) := by
      rw [Int.natCast_natAbs]
      exact_mod_cast InputBounds.determinant_bound d select
    exact_mod_cast hi
  rw [hxq]
  exact hden.trans hdet

theorem rigid_word_length (d : Raw) (x : Fin d.dimension → ℚ)
    (hx : Feasible d x) (hr : Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.FaceMove.Rigid d x) (j : Fin d.dimension) :
    (Holant.Algebraic.rationalEncoding.encode (x j)).length≤4*InputBounds.size d^2+4 := by
  have hn := box_numerator (x j) (hx.2 j)
  have hd := rigid_denominator d x hx hr j
  have hh : Holant.Algebraic.rationalHeight (x j)≤InputBounds.denominator d :=
    max_le (hn.trans hd) hd
  have hs := Nat.size_le_size hh
  have hp : (InputBounds.denominator d).size=2*InputBounds.size d^2+1 := by
    simp [InputBounds.denominator,Nat.size_pow]
  rw [hp] at hs
  have hw := Holant.Algebraic.rationalEncoding_length_le_height (x j)
  unfold Holant.Algebraic.rationalBitHeight at hw
  omega

theorem minimum_bounded (d : Raw) (j : Fin d.dimension) (h : ∃ x, Feasible d x) :
    ∃ x, Feasible d x ∧ Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.FaceMove.Rigid d x ∧
      (∀ y, Feasible d y → x j≤y j) ∧ (x j).den≤InputBounds.denominator d := by
  obtain ⟨x,hx,hr,hm⟩ := Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion.Minimum.exists_minimum d j h
  exact ⟨x,hx,hr,hm,rigid_denominator d x hx hr j⟩

def rounds (d : Raw) : ℕ := 4*InputBounds.size d^2+2
theorem grid_exact (d : Raw) : 2^rounds d=4*(InputBounds.denominator d)^2 := by
  calc
    2^rounds d=2^(2*InputBounds.size d^2+2*InputBounds.size d^2+2) := by
      unfold rounds
      congr 1
      omega
    _=(2^(2*InputBounds.size d^2))*(2^(2*InputBounds.size d^2))*4 := by
      rw [pow_add,pow_add]
      norm_num
    _=4*(InputBounds.denominator d)^2 := by unfold InputBounds.denominator; ring
theorem grid_positive (d : Raw) : 0<2^rounds d := by positivity
theorem isolation_width (d : Raw) :
    (1:ℚ)/(2^rounds d:ℕ)<1/(InputBounds.denominator d:ℚ)^2 := by
  have hD : (0:ℚ)<InputBounds.denominator d := by exact_mod_cast InputBounds.denominator_pos d
  rw [grid_exact]
  push_cast
  apply (div_lt_div_iff₀ (by positivity : (0:ℚ)<4*(InputBounds.denominator d:ℚ)^2)
    (sq_pos_of_pos hD)).mpr
  nlinarith [sq_pos_of_pos hD]

noncomputable section
def countComputes : Computes coordinateEncoding UnaryBinary.unaryEncoding
    (fun c : CoordinateQuery => rounds c.1.val) := by
  let e := Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.DenominatorProgram.coordinateRaw.andThen Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.DenominatorProgram.exponent
  let twice := (pairComputes e e).andThen AccessPrograms.unaryAdd
  exact congrComputes ((twice.andThen WireLists.succComputes).andThen WireLists.succComputes)
    (fun c => by
      change (2*InputBounds.size c.1.val^2 + 2*InputBounds.size c.1.val^2 + 1) + 1 =
        4*InputBounds.size c.1.val^2 + 2
      ring)
theorem count_bound (c : CoordinateQuery) : rounds c.1.val≤
    countComputes.outputBound.bound.eval (coordinateEncoding.encode c).length := by
  have h := countComputes.outputBound.length_le c
  simpa [UnaryBinary.unaryEncoding] using h
theorem primitive_bound (c : CoordinateQuery) :
    primitiveCost countComputes.machine (countComputes.outputs c).steps
      (some (initList countComputes.machine.computer (coordinateEncoding.encode c)))≤
      (primitivePolynomial countComputes).eval (coordinateEncoding.encode c).length :=
  computes_primitive_cost countComputes c
end

end Denominator
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
