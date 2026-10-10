import Holant.Complexity.BinaryInterpolation.RingFormula

/-! The actual bounded-window stack code consumes each answer once while
accumulating its computed interpolation weight. No answer is duplicated into
finite control, discarded for being zero, or used as an inverse denominator. -/
namespace Holant.Complexity.BinaryInterpolation.WeightedStack
open Holant.OneHot.StackProgram
variable {A K : Type*}

def code : List (RingFormula A)→Code A
  | [] => []
  | p::ps => p.code++[.copy 2,.mul,.add,.erase 1]++code ps

variable [CommSemiring K]

def value (coeff : A→K) : List (RingFormula A×K)→K→K
  | [],a => a
  | (p,y)::ps,a => value coeff ps (y*p.eval coeff+a)

def trace (coeff : A→K) : List (RingFormula A×K)→K→List K
  | [],_ => []
  | (p,y)::ps,a => p.trace coeff++[y,p.eval coeff,y*p.eval coeff,
      y*p.eval coeff,a,y*p.eval coeff+a]++trace coeff ps (y*p.eval coeff+a)

theorem value_eq_sum (coeff : A→K) (ps : List (RingFormula A×K)) (a : K) :
    value coeff ps a=a+(ps.map (fun p => p.2*p.1.eval coeff)).sum := by
  induction ps generalizing a with
  | nil => simp [value]
  | cons p ps ih =>
    rcases p with ⟨p,y⟩
    simp [value,ih,add_assoc,add_comm,add_left_comm]

theorem run_code (coeff : A→K) (ps : List (RingFormula A×K)) (a : K) (tail : List K) :
    run coeff (code (ps.map Prod.fst)) (a::ps.map Prod.snd++tail)=
      some (value coeff ps a::tail,trace coeff ps a) := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨p,y⟩
    simp only [List.map_cons,code,List.cons_append]
    rw [run_append]
    simp only [RingFormula.run_code]
    rw [run_append]
    simp [RingFormula.run_code,run,step,eraseAt,ih,value,trace,List.append_assoc]
    have h := ih (y*p.eval coeff+a)
    simp only [List.cons_append] at h
    rw [h]
    rfl

theorem code_length (ps : List (RingFormula A)) :
    (code ps).length=(ps.map (fun p => p.size+4)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [code,ih,RingFormula.code_length];omega

end Holant.Complexity.BinaryInterpolation.WeightedStack
