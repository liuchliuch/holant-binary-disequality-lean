import Holant.Tractable.TwoTranslate.Phase
import Holant.ReedMuller.CharacterFlat.Basic
import Holant.ReedMuller.LowArity.HalfDimension

/-! Exact quadratic-phase derivatives on an affine support. These statements use
actual source `QuadraticPhase` data and the original binary coordinates. -/
namespace Holant.ReedMuller.AffineRadon
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- The literal source normal form on binary-vector inputs. -/
def phaseValue (c : AlgebraicComplex) (a : BinaryVector n) (U : BinaryCode n)
    (Q : QuadraticPhase n) (x : BinaryVector n) : AlgebraicComplex :=
  if x-a ∈ U then c * fourthRootPhase (Q.eval (wordVector x)) else 0

/-- Binary signs in the exact algebraic-complex coefficient field. -/
def phaseSign (b : ZMod 2) : AlgebraicComplex := if b=0 then 1 else -1

@[simp] theorem phaseSign_zero : phaseSign 0 = 1 := by simp [phaseSign]
@[simp] theorem phaseSign_one : phaseSign 1 = -1 := by norm_num [phaseSign]

@[simp] theorem coe_phaseSign (b : ZMod 2) : (phaseSign b : ℂ) = CharacterFlat.sign b := by
  fin_cases b <;> simp

@[simp] theorem evenLift_phase (b : ZMod 2) :
    fourthRootPhase (TwoTranslate.evenLift b) = phaseSign b := by
  fin_cases b <;> simp

theorem phaseSign_add (b d : ZMod 2) : phaseSign (b+d)=phaseSign b*phaseSign d := by
  fin_cases b <;> fin_cases d <;> norm_num [phaseSign, show (1 : ZMod 2)+1=0 from rfl]

@[simp] theorem phaseSign_square (b : ZMod 2) : phaseSign b*phaseSign b=1 := by
  fin_cases b <;> norm_num [phaseSign]

theorem wordVector_add (x y : BinaryVector n) :
    wordVector (x+y)=xor (wordVector x) (wordVector y) := by
  funext i
  change boolEquiv.symm (x i+y i)=Bool.xor (boolEquiv.symm (x i)) (boolEquiv.symm (y i))
  generalize x i=b
  generalize y i=d
  fin_cases b <;> fin_cases d <;> decide

@[simp] theorem bitValue_wordVector (x : BinaryVector n) (i : Fin n) :
    bitValue (ZMod 2) (wordVector x i)=x i := by
  exact congrFun (vector_word x) i

/-- The additive derivative of an actual allowed quadratic, with no phase
witness assumed by the caller. The binary form is globally linear, so its
restriction to every translated support is affine linear. -/
theorem quadratic_derivative_vector (Q : QuadraticPhase n) (s : BinaryVector n) :
    ∃ α : ZMod 4, ∃ ell : BinaryVector n →ₗ[ZMod 2] ZMod 2, ∀ x,
      Q.eval (wordVector (x+s))-Q.eval (wordVector x)=
        α+TwoTranslate.evenLift (ell x) := by
  obtain ⟨α,b,h⟩ := TwoTranslate.quadratic_derivative Q (wordVector s)
  refine ⟨α,dotBilinear b,?_⟩
  intro x
  simpa only [wordVector_add,TwoTranslate.dot,bitValue_wordVector,dotBilinear_apply,dot]
    using h (wordVector x)

theorem phaseValue_ne_zero_iff (c : AlgebraicComplex) (hc : c≠0)
    (a : BinaryVector n) (U : BinaryCode n) (Q : QuadraticPhase n) (x : BinaryVector n) :
    phaseValue c a U Q x≠0 ↔ x-a∈U := by
  unfold phaseValue
  split_ifs with h
  · simp [h,mul_ne_zero hc (fourthRootPhase_ne_zero _)]
  · simp [h]

theorem translate_mem_iff (a : BinaryVector n) (U : BinaryCode n)
    (s : BinaryVector n) (hs : s∈U) (x : BinaryVector n) :
    x+s-a∈U ↔ x-a∈U := by
  have he : x+s-a=(x-a)+s := by abel
  rw [he,U.add_mem_iff_left hs]

/-- Actual translate ratios, retaining the exact scale, phase, and ambient
coordinates. This also provides the undivided formula at every input. -/
theorem phaseValue_translation (c : AlgebraicComplex) (hc : c≠0)
    (a : BinaryVector n) (U : BinaryCode n) (Q : QuadraticPhase n)
    (s : BinaryVector n) (hs : s∈U) :
    ∃ α : ZMod 4, ∃ ell : BinaryVector n →ₗ[ZMod 2] ZMod 2,
      (∀ x, phaseValue c a U Q (x+s)=
        phaseValue c a U Q x*(fourthRootPhase α*phaseSign (ell x))) ∧
      (∀ x, x-a∈U → phaseValue c a U Q (x+s)/phaseValue c a U Q x=
        fourthRootPhase α*phaseSign (ell x)) := by
  obtain ⟨α,ell,h⟩ := quadratic_derivative_vector Q s
  have hv (x : BinaryVector n) : phaseValue c a U Q (x+s)=
      phaseValue c a U Q x*(fourthRootPhase α*phaseSign (ell x)) := by
    have he : Q.eval (wordVector (x+s))=
        Q.eval (wordVector x)+(α+TwoTranslate.evenLift (ell x)) := by
      linear_combination h x
    simp only [phaseValue,translate_mem_iff a U s hs]
    split_ifs
    · rw [he,fourthRootPhase_add,fourthRootPhase_add,evenLift_phase]
      ring
    · ring
  refine ⟨α,ell,hv,?_⟩
  intro x hx
  rw [hv]
  exact mul_div_cancel_left₀ _ ((phaseValue_ne_zero_iff c hc a U Q x).mpr hx)

/-- The same derivative controls both signs of the orbit numerator. -/
theorem phaseValue_signed_factor (c : AlgebraicComplex) (hc : c≠0)
    (a : BinaryVector n) (U : BinaryCode n) (Q : QuadraticPhase n)
    (s : BinaryVector n) (hs : s∈U) :
    ∃ α : ZMod 4, ∃ ell : BinaryVector n →ₗ[ZMod 2] ZMod 2, ∀ b x,
      phaseValue c a U Q x+phaseSign b*phaseValue c a U Q (x+s)=
        phaseValue c a U Q x*(1+fourthRootPhase α*phaseSign (b+ell x)) := by
  obtain ⟨α,ell,h,_⟩ := phaseValue_translation c hc a U Q s hs
  refine ⟨α,ell,?_⟩
  intro b x
  rw [h,phaseSign_add]
  ring

end
end Holant.ReedMuller.AffineRadon
