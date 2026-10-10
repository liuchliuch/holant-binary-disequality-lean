import Holant.OneHot.StackProgram.Machine.Concrete
import Holant.OneHot.StackProgram.Machine.Cost

/-! Division-free formulas used to generate interpolation weights. Compilation
emits actual existing stack bytecode. A structural size budget bounds every
executed arithmetic value; a short program alone is not assumed to have small
coefficients. -/
namespace Holant.Complexity.BinaryInterpolation
open Holant.OneHot Holant.OneHot.StackProgram
open scoped BigOperators

inductive RingFormula (A : Type*) where
  | literal : A→RingFormula A
  | zero : RingFormula A
  | one : RingFormula A
  | add : RingFormula A→RingFormula A→RingFormula A
  | mul : RingFormula A→RingFormula A→RingFormula A
  deriving DecidableEq

namespace RingFormula
variable {A K : Type*}

def size : RingFormula A→ℕ
  | .literal _ | .zero | .one => 1
  | .add p q | .mul p q => p.size+q.size+1

def code : RingFormula A→Code A
  | .literal a => [.literal a]
  | .zero => [.zero]
  | .one => [.one]
  | .add p q => q.code++p.code++[.add]
  | .mul p q => q.code++p.code++[.mul]

@[simp] theorem code_length (p : RingFormula A) : p.code.length=p.size := by
  induction p with
  | literal a => rfl
  | zero => rfl
  | one => rfl
  | add p q hp hq | mul p q hp hq =>
    simp only [code,List.length_append,List.length_singleton,hp,hq,size]
    omega

variable [CommSemiring K]

def eval (coeff : A→K) : RingFormula A→K
  | .literal a => coeff a
  | .zero => 0
  | .one => 1
  | .add p q => p.eval coeff+q.eval coeff
  | .mul p q => p.eval coeff*q.eval coeff

def trace (coeff : A→K) : RingFormula A→List K
  | .literal _ | .zero | .one => []
  | .add p q => q.trace coeff++p.trace coeff++[p.eval coeff,q.eval coeff,p.eval coeff+q.eval coeff]
  | .mul p q => q.trace coeff++p.trace coeff++[p.eval coeff,q.eval coeff,p.eval coeff*q.eval coeff]

theorem run_code (p : RingFormula A) (coeff : A→K) (s : List K) :
    run coeff p.code s=some (p.eval coeff::s,p.trace coeff) := by
  induction p generalizing s with
  | literal a => rfl
  | zero => rfl
  | one => rfl
  | add p q hp hq => simp [code,run_append,hp,hq,run,step,eval,trace,List.append_assoc]
  | mul p q hp hq => simp [code,run_append,hp,hq,run,step,eval,trace,List.append_assoc]

/-- Every literal, operand and result is bounded by the explicit formula tree.
The designated unit is an existing coefficient, used only for proof padding. -/
theorem structural_bound (p : RingFormula A) (coeff : A→K) (aone : A)
    (hone : coeff aone=1) :
    ArithmeticSize.Bound coeff p.size (p.eval coeff) ∧
      ∀x∈p.trace coeff,ArithmeticSize.Bound coeff p.size x := by
  induction p with
  | literal a => exact ⟨ArithmeticSize.Bound.coefficient a,by simp [trace]⟩
  | zero => exact ⟨ArithmeticSize.Bound.zero aone 1,by simp [trace]⟩
  | one => exact ⟨ArithmeticSize.Bound.one.mono aone hone (by simp [size]),by simp [trace]⟩
  | add p q hp hq =>
    have hps := hp.1.mono aone hone (show p.size≤p.size+q.size by omega)
    have hqs := hq.1.mono aone hone (show q.size≤p.size+q.size by omega)
    have he := hps.add aone hone hqs
    refine ⟨he,?_⟩
    intro x hx
    simp only [trace,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with (hx|hx)|hx|hx|hx
    · exact (hq.2 x hx).mono aone hone (by simp [size];omega)
    · exact (hp.2 x hx).mono aone hone (by simp [size];omega)
    · subst x; exact hp.1.mono aone hone (by simp [size];omega)
    · subst x; exact hq.1.mono aone hone (by simp [size];omega)
    · subst x; exact he
  | mul p q hp hq =>
    have he := (hp.1.mul hq.1).mono aone hone (show p.size+q.size≤p.size+q.size+1 by omega)
    refine ⟨he,?_⟩
    intro x hx
    simp only [trace,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with (hx|hx)|hx|hx|hx
    · exact (hq.2 x hx).mono aone hone (by simp [size];omega)
    · exact (hp.2 x hx).mono aone hone (by simp [size];omega)
    · subst x; exact hp.1.mono aone hone (by simp [size];omega)
    · subst x; exact hq.1.mono aone hone (by simp [size];omega)
    · subst x; exact he

end RingFormula
end Holant.Complexity.BinaryInterpolation
