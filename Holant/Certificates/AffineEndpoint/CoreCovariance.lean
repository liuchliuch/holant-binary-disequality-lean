import Holant.Certificates.AffineEndpoint.DiagonalForm
import Holant.Certificates.AffineEndpoint.BaseTensorData
import Holant.ReedMuller.AffinePatching.Walsh

/-! Exact input-phase and output-complement covariance for the eighteen
literal source cores. All identities retain the original ordered tensor action. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.EightVertex.ProductAnchor
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 def coreAction (k : CoreIndex) (f : Signature AlgebraicComplex n) :
    Signature AlgebraicComplex n := Signature.coordinateAction (fun _ => coreMatrix k) f

 def phaseTwist (j : Fin 4) (f : Signature AlgebraicComplex n) :
    Signature AlgebraicComplex n := fun x => (imaginaryUnit^j.val)^(Holant.weight x)*f x

 def uniformPhase (n : ℕ) (j : Fin 4) : QuadraticPhase n where
  constant := 0
  linear := fun _ => (j.val : ZMod 4)
  mixed := fun _ _ => 0
  even_mixed := by intros; exact Or.inl rfl

 theorem uniformPhase_value (j : Fin 4) (x : Word n) :
    fourthRootPhase ((uniformPhase n j).eval x)=(imaginaryUnit^j.val)^(Holant.weight x) := by
  simp only [QuadraticPhase.eval,uniformPhase,zero_mul,ite_self,Finset.sum_const_zero,
    zero_add,add_zero]
  rw [fourthRootPhase_sum]
  unfold Holant.weight
  rw [←Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro k _
  cases x k <;> simp [bitValue,fourthRootPhase,ZMod.val_natCast,Nat.mod_eq_of_lt j.isLt]

 theorem phaseTwist_affine (j : Fin 4) {f : Signature AlgebraicComplex n} (hf : Affine f) :
    Affine (phaseTwist j f) := by
  have hp := affine_formula 1 (AffineSystem.unconstrained n) (uniformPhase n j)
  have he : affineFormula 1 (AffineSystem.unconstrained n) (uniformPhase n j)=
      fun x => (imaginaryUnit^j.val)^(Holant.weight x) := by
    funext x
    simp only [affineFormula,AffineSystem.unconstrained_holds,ite_true,one_mul,
      uniformPhase_value]
  rw [he] at hp
  exact hp.mul hf

 theorem phaseTwist_eq_zero_iff (j : Fin 4) (f : Signature AlgebraicComplex n) :
    phaseTwist j f=0 ↔ f=0 := by
  constructor
  · intro h
    funext x
    have hx := congrFun h x
    have hi : (imaginaryUnit^j.val)^(Holant.weight x)≠0 :=
      pow_ne_zero _ (by
        intro hz
        have hp := fourth_power_one j
        rw [hz] at hp
        norm_num at hp)
    exact (mul_eq_zero.mp hx).resolve_left hi
  · intro h
    subst f
    funext x
    simp [phaseTwist]

 theorem phaseTwist_ne_zero (j : Fin 4) {f : Signature AlgebraicComplex n} (hf : f≠0) :
    phaseTwist j f≠0 := fun h => hf ((phaseTwist_eq_zero_iff j f).mp h)

 theorem phaseTwist_eq_action (j : Fin 4) (f : Signature AlgebraicComplex n) :
    phaseTwist j f=Signature.coordinateAction (fun _ => diagonalKernel 1 (imaginaryUnit^j.val)) f := by
  rw [coordinateAction_diagonal]
  funext x
  simp [phaseTwist,diagonalCoefficient_eq_weight]

 theorem algMat_mul_diagonal (a b c d t : AlgebraicComplex) :
    Kernel.mul (algMat a b c d) (diagonalKernel 1 t)=algMat a (b*t) c (d*t) := by
  funext x y
  cases x <;> cases y <;> simp [Kernel.mul_apply,algMat,diagonalKernel]

 theorem algMat_flip (a b c d : AlgebraicComplex) :
    Kernel.mul Signature.disequality (algMat a b c d)=algMat c d a b := by
  funext x y
  cases x <;> cases y <;> simp [Kernel.mul_apply,algMat,Signature.disequality]

 theorem coreAction_hadamard_even (j : Fin 4) (f : Signature AlgebraicComplex n) :
    coreAction (.inr (.inl ⟨2*j.val,by omega⟩)) f=
      coreAction (numberedCore 2) (phaseTwist j f) := by
  rw [phaseTwist_eq_action]
  unfold coreAction
  rw [Signature.coordinateAction_comp]
  congr 1
  funext i
  rw [core_hadamard]
  change algMat 1 (zetaEight^(2*j.val)) 1 (-(zetaEight^(2*j.val)))=
    Kernel.mul (coreMatrix (.inr (.inl 0))) (diagonalKernel 1 (imaginaryUnit^j.val))
  rw [core_hadamard,algMat_mul_diagonal,pow_mul,zetaEight_sq]
  simp

 theorem coreAction_hadamard_odd (j : Fin 4) (f : Signature AlgebraicComplex n) :
    coreAction (.inr (.inl ⟨2*j.val+1,by omega⟩)) f=
      coreAction (numberedCore 3) (phaseTwist j f) := by
  rw [phaseTwist_eq_action]
  unfold coreAction
  rw [Signature.coordinateAction_comp]
  congr 1
  funext i
  rw [core_hadamard]
  change algMat 1 (zetaEight^(2*j.val+1)) 1 (-(zetaEight^(2*j.val+1)))=
    Kernel.mul (coreMatrix (.inr (.inl 1))) (diagonalKernel 1 (imaginaryUnit^j.val))
  rw [core_hadamard,algMat_mul_diagonal,pow_add,pow_mul,zetaEight_sq]
  simp [mul_comm]

 theorem coreAction_mixed_positive (j : Fin 4) (f : Signature AlgebraicComplex n) :
    coreAction (.inr (.inr (j,false))) f=
      coreAction (numberedCore 10) (phaseTwist j f) := by
  rw [phaseTwist_eq_action]
  unfold coreAction
  rw [Signature.coordinateAction_comp]
  congr 1
  funext i
  rw [core_mixed]
  change algMat 1 (imaginaryUnit^j.val*(1+sqrtTwo)) 1 (imaginaryUnit^j.val*(1-sqrtTwo))=
    Kernel.mul (coreMatrix (.inr (.inr (0,false)))) (diagonalKernel 1 (imaginaryUnit^j.val))
  rw [core_mixed,algMat_mul_diagonal]
  simp [mul_comm]

 theorem coreAction_mixed_negative (j : Fin 4) (f : Signature AlgebraicComplex n) :
    coreAction (.inr (.inr (j,true))) f=
      fun x => coreAction (numberedCore 10) (phaseTwist j f) (complementWord x) := by
  rw [←coreAction_mixed_positive]
  rw [←coordinateAction_disequality]
  unfold coreAction
  rw [Signature.coordinateAction_comp]
  congr 1
  funext i
  rw [core_mixed,core_mixed,algMat_flip]
  simp [sub_eq_add_neg]

end
end Holant.Certificates.AffineEndpoint
