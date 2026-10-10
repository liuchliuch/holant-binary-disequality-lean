import Holant.Certificates.MatchingProductBridge.Interface
import Holant.BoundaryAction

/-! Literal Frobenius reconstruction and the three rejected tetrahedral
orientations in Proposition A.17. Dual matrices reconstruct coefficients only. -/
namespace Holant.Certificates.TetrahedralOrientation
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section

abbrev Orientation := Fin 3

def sigma : Orientation → Fin 3 → Fin 4 := ![![0,3,1],![1,0,3],![3,1,0]]

def dual : Fin 4 → Binary := ![(1/2 : ℂ) • Q0,(-1/2 : ℂ) • Q1,(1/2 : ℂ) • Q2,(-1/2 : ℂ) • Q3]

def axisR : Fin 4 → FourTensor :=
  ![(1/2 : ℂ) • P2 Q0 Q0,(-1/2 : ℂ) • P2 Q1 Q1,0,(-1/2 : ℂ) • P2 Q3 Q3]

def cardImages (s : Orientation) : Fin 4 → FourTensor :=
  ![(1/2 : ℂ) • C,axisR (sigma s 0),axisR (sigma s 1),axisR (sigma s 2)]

/-- The actual six-port ancestor from the source's Frobenius-dual reconstruction. -/
def ancestor (s : Orientation) : Signature ℂ 6 := fun x =>
  ∑ μ : Fin 4, dual μ (x 0) (x 1) * cardImages s μ (fun j => x j.succ.succ)

/-- Ordered physical input positions: selected ports1,3, then surviving2,4,5,6. -/
def contractOrder : Equiv.Perm (Fin 6) where
  toFun := ![0,2,1,3,4,5]
  invFun := ![0,2,1,3,4,5]
  left_inv := by decide
  right_inv := by decide

/-- Existing bilinear Signature.contract with the literal I kernel. -/
def card (s : Orientation) : FourTensor :=
  Signature.contract Q0 (Tensor.reindex contractOrder (ancestor s))

theorem card_apply (s : Orientation) (x : Fin 4 → Bool) :
    card s x = ancestor s ![false,x 0,false,x 1,x 2,x 3] +
      ancestor s ![true,x 0,true,x 1,x 2,x 3] := by
  rw [card,Q0,Signature.contract_equality]
  apply congrArg₂ (· + ·)
  all_goals dsimp only [Tensor.reindex]
  all_goals apply congrArg (ancestor s)
  all_goals funext i; fin_cases i <;> rfl

def Gplus : Binary := Q0+Q1+Q2+Q3
def Gminus : Binary := Q0+Q1+Q2-Q3

def legs : Orientation → Fin 4 → Binary :=
  ![![Q0,Gminus,Gplus,Q1],![Q0,Q0,Gplus,Q0],![Q0,Gplus,Q0,Gminus]]

def dressed (s : Orientation) : FourTensor := Signature.coordinateAction (legs s) (card s)

/-- Exact raw multipliers preceding first-nonzero-entry normalization. -/
def rawScale : Orientation → ℂ := ![2+2*Complex.I,(1-Complex.I)/2,-1-Complex.I]

def evenTable : Orientation → Fin 8 → ℂ :=
  ![![1,0,0,0,0,0,0,-Complex.I],
    ![1,1,-Complex.I,Complex.I,1,-1,Complex.I,Complex.I],
    ![1,-1,1,1,-Complex.I,-Complex.I,Complex.I,-Complex.I]]

/-- Source even-word order0000,0011,0101,0110,1001,1010,1100,1111; odd entries zero. -/
def terminal (s : Orientation) : FourTensor := fun x =>
  match x 0,x 1,x 2,x 3 with
  | false,false,false,false => evenTable s 0
  | false,false,true,true => evenTable s 1
  | false,true,false,true => evenTable s 2
  | false,true,true,false => evenTable s 3
  | true,false,false,true => evenTable s 4
  | true,false,true,false => evenTable s 5
  | true,true,false,false => evenTable s 6
  | true,true,true,true => evenTable s 7
  | _,_,_,_ => 0

/-- An explicit enumeration of all four-port Boolean assignments. -/
def fourBits : (Fin 4 → Bool) ≃ (Bool × Bool × Bool × Bool) where
  toFun x := (x 0,x 1,x 2,x 3)
  invFun p := ![p.1,p.2.1,p.2.2.1,p.2.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

theorem sum_four {K : Type*} [AddCommMonoid K] (f : (Fin 4 → Bool) → K) :
    (∑ x : Fin 4 → Bool, f x) = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, f ![a,b,c,d] := by
  rw [← fourBits.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

end
end Holant.Certificates.TetrahedralOrientation
