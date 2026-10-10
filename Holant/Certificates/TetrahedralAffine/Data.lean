import Holant.Certificates.TetrahedralOrientation.Data
import Holant.Tractable.AffinePhase.Roots

/-! Literal Frobenius reconstruction of the three orientation-preserving
ancestors over the existing exact algebraic-complex field. -/
namespace Holant.Certificates.TetrahedralAffine
open Holant Holant.Tractable Holant.Certificates.MatchingProductBridge
noncomputable section

abbrev Orientation := Fin 3
abbrev ABinary := Kernel AlgebraicComplex

def sigma : Orientation → Fin 3 → Fin 4 := ![![0,1,3],![1,3,0],![3,0,1]]

def Q : Fin 4 → ABinary :=
  ![Signature.equality,
    (fun a b => if a = b then 0 else imaginaryUnit),
    (fun a b => if a = b then 0 else if a then -1 else 1),
    (fun a b => if a = b then if a then -imaginaryUnit else imaginaryUnit else 0)]

def dual : Fin 4 → ABinary :=
  ![(1/2 : AlgebraicComplex) • Q 0,(-1/2 : AlgebraicComplex) • Q 1,
    (1/2 : AlgebraicComplex) • Q 2,(-1/2 : AlgebraicComplex) • Q 3]

def p2 (U V : ABinary) : Signature AlgebraicComplex 4 := fun x => U (x 0) (x 3)*V (x 1) (x 2)

def axisR : Fin 4 → Signature AlgebraicComplex 4 :=
  ![(1/2 : AlgebraicComplex) • p2 (Q 0) (Q 0),
    (-1/2 : AlgebraicComplex) • p2 (Q 1) (Q 1),0,
    (-1/2 : AlgebraicComplex) • p2 (Q 3) (Q 3)]

def cardImages (s : Orientation) : Fin 4 → Signature AlgebraicComplex 4 :=
  ![(1/2 : AlgebraicComplex) • p2 (Q 2) (Q 2),axisR (sigma s 0),axisR (sigma s 1),axisR (sigma s 2)]

def ancestor (s : Orientation) : Signature AlgebraicComplex 6 := fun x =>
  ∑ μ : Fin 4, dual μ (x 0) (x 1)*cardImages s μ (fun j => x j.succ.succ)

/-- The same source f_sigma formula as A.17, for the other three tuples. -/
def complexAncestor (s : Orientation) : Signature ℂ 6 := fun x =>
  ∑ μ : Fin 4, TetrahedralOrientation.dual μ (x 0) (x 1) *
    ![(1/2 : ℂ) • C,TetrahedralOrientation.axisR (sigma s 0),
      TetrahedralOrientation.axisR (sigma s 1),TetrahedralOrientation.axisR (sigma s 2)] μ
        (fun j => x j.succ.succ)

theorem coe_Q (k : Fin 4) (a b : Bool) : (Q k a b : ℂ) = quaternionBasis k a b := by
  fin_cases k <;> cases a <;> cases b <;> rfl

end
end Holant.Certificates.TetrahedralAffine
