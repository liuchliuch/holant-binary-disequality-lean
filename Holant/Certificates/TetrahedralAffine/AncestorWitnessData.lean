import Holant.Certificates.TetrahedralAffine.Data

/-! The source's actual affine systems and even-mixed quadratic phases for
f013, f130 and f301, checked against Frobenius reconstruction on every word. -/
namespace Holant.Certificates.TetrahedralAffine
open Holant Holant.Tractable
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false

def supportSystem (s : Orientation) : AffineSystem 6 where
  rows := 2
  matrix := fun row => if row = 0 then ![0,0,1,1,1,1]
    else if s = 2 then ![1,1,0,1,1,0] else fun _ => 0
  rhs := fun row => if s = 2 ∧ row = 1 then 1 else 0

def mixedPairs : Orientation → List (Fin 6 × Fin 6) :=
  ![[(0,1),(0,2),(0,4),(1,2),(1,3),(3,4)],
    [(0,1),(0,2),(0,3),(1,2),(1,4),(2,3),(2,4)],
    [(0,1),(0,2),(0,3),(2,3)]]

def phase (s : Orientation) : QuadraticPhase 6 where
  constant := if s = 2 then 2 else 0
  linear := ![![0,0,2,3,1,0],![3,1,0,3,1,0],![1,2,0,0,1,1]] s
  mixed := fun j k => if (j,k) ∈ mixedPairs s then 2 else 0
  even_mixed := by
    intro j k _
    by_cases h : (j,k) ∈ mixedPairs s
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)

def scale : Orientation → AlgebraicComplex :=
  ![-imaginaryUnit/4,-imaginaryUnit/4,(1-imaginaryUnit)/4]

theorem supportSystem_holds (s : Orientation) (x : Fin 6 → Bool) :
    (supportSystem s).Holds x ↔
      bitValue (ZMod 2) (x 2)+bitValue (ZMod 2) (x 3)+bitValue (ZMod 2) (x 4)+bitValue (ZMod 2) (x 5)=0 ∧
      (if s = 2 then bitValue (ZMod 2) (x 0)+bitValue (ZMod 2) (x 1)+
        bitValue (ZMod 2) (x 3)+bitValue (ZMod 2) (x 4)=1 else True) := by
  fin_cases s <;> dsimp [supportSystem,AffineSystem.Holds] <;>
    norm_num [Fin.forall_fin_succ,Fin.sum_univ_succ,add_assoc]

theorem parity4_zero (a b c d : Bool) :
    bitValue (ZMod 2) a+bitValue (ZMod 2) b+bitValue (ZMod 2) c+bitValue (ZMod 2) d=0 ↔
      (a ^^ b ^^ c ^^ d)=false := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem parity4_one (a b c d : Bool) :
    bitValue (ZMod 2) a+bitValue (ZMod 2) b+bitValue (ZMod 2) c+bitValue (ZMod 2) d=1 ↔
      (a ^^ b ^^ c ^^ d)=true := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem supportSystem_holds_bool (s : Orientation) (x : Fin 6 → Bool) :
    (supportSystem s).Holds x ↔ (x 2 ^^ x 3 ^^ x 4 ^^ x 5)=false ∧
      (if s = 2 then (x 0 ^^ x 1 ^^ x 3 ^^ x 4)=true else True) := by
  simp only [supportSystem_holds,parity4_zero,parity4_one]

def sourcePhase (s : Orientation) (x : Fin 6 → Bool) : ZMod 4 :=
  let b := fun j => bitValue (ZMod 4) (x j)
  ![2*b 2+3*b 3+b 4+2*(b 0*b 1+b 0*b 2+b 0*b 4+b 1*b 2+b 1*b 3+b 3*b 4),
    3*b 0+b 1+3*b 3+b 4+2*(b 0*b 1+b 0*b 2+b 0*b 3+b 1*b 2+b 1*b 4+b 2*b 3+b 2*b 4),
    2+b 0+2*b 1+b 4+b 5+2*(b 0*b 1+b 0*b 2+b 0*b 3+b 2*b 3)] s

theorem phase_eval (s : Orientation) (x : Fin 6 → Bool) : (phase s).eval x = sourcePhase s x := by
  fin_cases s <;> norm_num [phase,QuadraticPhase.eval,mixedPairs,sourcePhase,Fin.sum_univ_succ] <;> ring

end
end Holant.Certificates.TetrahedralAffine
