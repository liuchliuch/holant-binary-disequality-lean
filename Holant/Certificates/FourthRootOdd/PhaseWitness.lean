import Holant.Certificates.FourthRootOdd.PhaseData
import Mathlib.Tactic.Abel

/-! Constructive soundness of the source's three-variable phase test. It
produces an actual four-port affine system and even-mixed quadratic phase. -/
noncomputable section
namespace Holant.Certificates.FourthRootOdd
open Holant Holant.Certificates.TwelveLoops Holant.Tractable

@[simp] theorem unit3_zero : unit3 0=![true,false,false] := by decide
@[simp] theorem unit3_one : unit3 1=![false,true,false] := by decide
@[simp] theorem unit3_two : unit3 2=![false,false,true] := by decide
@[simp] theorem pair3_zero_one : pair3 0 1=![true,true,false] := by decide
@[simp] theorem pair3_zero_two : pair3 0 2=![true,false,true] := by decide
@[simp] theorem pair3_one_two : pair3 1 2=![false,true,true] := by decide

def phasePoly3 (φ : (Fin 3 → Bool) → ZMod 4) (y : Fin 3 → Bool) : ZMod 4 :=
  φ origin3+phaseLinear φ 0*bitValue (ZMod 4) (y 0)+
    phaseLinear φ 1*bitValue (ZMod 4) (y 1)+phaseLinear φ 2*bitValue (ZMod 4) (y 2)+
    phaseMixed φ 0 1*bitValue (ZMod 4) (y 0)*bitValue (ZMod 4) (y 1)+
    phaseMixed φ 0 2*bitValue (ZMod 4) (y 0)*bitValue (ZMod 4) (y 2)+
    phaseMixed φ 1 2*bitValue (ZMod 4) (y 1)*bitValue (ZMod 4) (y 2)

theorem phasePoly3_eq (φ : (Fin 3 → Bool) → ZMod 4) (h : PhaseCriterion φ)
    (y : Fin 3 → Bool) : phasePoly3 φ y=φ y := by
  have hc : phasePoly3 φ ![true,true,true]=φ ![true,true,true] := by
    simpa [phasePoly3] using h.2.symm
  have hy : y=![y 0,y 1,y 2] := by funext i; fin_cases i <;> rfl
  rw [hy]
  cases h₀ : y 0 <;> cases h₁ : y 1 <;> cases h₂ : y 2
  all_goals simp only [phasePoly3,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,bitValue_false,bitValue_true,mul_zero,mul_one,add_zero,zero_add]
  all_goals first | (simpa only [phasePoly3,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,bitValue_true,mul_one] using hc) |
    (simp [phaseLinear,phaseMixed,origin3] <;> abel)

def oddSystem : AffineSystem 4 := ⟨1,fun _ _ => 1,fun _ => 1⟩

theorem oddSystem_holds_iff : ∀ x : Fin 4 → Bool,
    oddSystem.Holds x ↔ x 3=!(x 0 ^^ x 1 ^^ x 2) := by decide

theorem oddChart_original (x : Fin 4 → Bool) (h : oddSystem.Holds x) :
    oddChart ![x 0,x 1,x 2]=x := by
  have hx := (oddSystem_holds_iff x).mp h
  funext i
  fin_cases i <;> simp [oddChart,hx]

def phaseQuadratic (φ : (Fin 3 → Bool) → ZMod 4) (h : PhaseCriterion φ) : QuadraticPhase 4 where
  constant := φ origin3
  linear := ![phaseLinear φ 0,phaseLinear φ 1,phaseLinear φ 2,0]
  mixed := ![![0,phaseMixed φ 0 1,phaseMixed φ 0 2,0],
    ![0,0,phaseMixed φ 1 2,0],![0,0,0,0],![0,0,0,0]]
  even_mixed := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact h.1 0 1 (by decide)
    · exact h.1 0 2 (by decide)
    · exact h.1 1 2 (by decide)

theorem phaseQuadratic_eval (φ : (Fin 3 → Bool) → ZMod 4) (h : PhaseCriterion φ)
    (x : Fin 4 → Bool) : (phaseQuadratic φ h).eval x=phasePoly3 φ ![x 0,x 1,x 2] := by
  simp [QuadraticPhase.eval,phaseQuadratic,Fin.sum_univ_succ,phasePoly3]
  ring

def shiftedOdd (s : State) (δ : Fin 4) : Signature AlgebraicComplex 4 :=
  fun x => if oddSystem.Holds x then fourthRootPhase (phaseAt s δ x) else 0

theorem shiftedOdd_affine (s : State) (δ : Fin 4) (h : phaseTest s δ) :
    Affine (shiftedOdd s δ) := by
  change PhaseCriterion (chartPhase s δ) at h
  have ha := affine_formula 1 oddSystem (phaseQuadratic (chartPhase s δ) h)
  convert ha using 1
  funext x
  simp only [shiftedOdd,affineFormula]
  split_ifs with hx
  · rw [phaseQuadratic_eval _ h x,phasePoly3_eq _ h _,one_mul]
    simp [chartPhase,oddChart_original x hx]
  · rfl

theorem shiftedOdd_table (s : State) (δ : Fin 4) : shiftedOdd s δ=
    oddTable (fun j => fourthRootPhase ((alpha s j).val : ZMod 4))
      (fun j => fourthRootPhase ((beta s j).val+δ.val : ZMod 4)) := by
  funext x
  cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;> cases h₃ : x 3 <;>
    simp [shiftedOdd,oddSystem_holds_iff,phaseAt,oddTable,h₀,h₁,h₂,h₃]

end Holant.Certificates.FourthRootOdd
