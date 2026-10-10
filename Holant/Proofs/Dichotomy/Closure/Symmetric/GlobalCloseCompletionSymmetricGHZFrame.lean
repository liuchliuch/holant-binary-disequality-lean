import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZCapGraph
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZCommonBasis

/-! A genuine scalar inverse of a nonsingular GHZ unary cap gives an
ordinary weighted-equality frame. The two square roots are algebraic fixed
coefficients; they are never installed as physical matrix vertices. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZFrame
open Holant Holant.Tractable
namespace C
export GlobalCloseCompletionSymmetricGHZCoordinates (ghz ghz_value)
export GlobalCloseCompletionSymmetricGHZCapGraph (symmetric)
end C
namespace T
export GlobalCloseCompletionEq4CommonBasis (transpose)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false

def diagonal (a b : AlgebraicComplex) : Kernel AlgebraicComplex := fun p q=>
  if p=q then (if p then b else a) else 0

def diagonalBasis (a b : AlgebraicComplex) (ha : a≠0) (hb : b≠0) : InvertibleKernel where
  matrix:=diagonal a b
  inverse:=diagonal a⁻¹ b⁻¹
  matrix_inverse:=by
    funext p q
    cases p <;> cases q <;> simp [diagonal,Kernel.mul_apply,Signature.equality,ha,hb]
  inverse_matrix:=by
    funext p q
    cases p <;> cases q <;> simp [diagonal,Kernel.mul_apply,Signature.equality,ha,hb]

def capKernel (M : InvertibleKernel) (a b : AlgebraicComplex) : Kernel AlgebraicComplex :=
  Kernel.mul (Kernel.mul M.matrix (diagonal a b)) (Kernel.transpose M.matrix)

def weight (M : InvertibleKernel) (u : Bool→AlgebraicComplex) (t : Bool) : AlgebraicComplex :=
  u false*M.matrix false t+u true*M.matrix true t

theorem cap_ghz (M : InvertibleKernel) (u : Bool→AlgebraicComplex) (x : Fin 2→Bool) :
    u false*C.ghz M.matrix ![false,x 0,x 1]+u true*C.ghz M.matrix ![true,x 0,x 1]=
      capKernel M (weight M u false) (weight M u true) (x 0) (x 1) := by
  simp [C.ghz_value,capKernel,weight,diagonal,Kernel.mul_apply,Kernel.transpose]
  ring

def capBasis (M : InvertibleKernel) (a b : AlgebraicComplex) (ha : a≠0) (hb : b≠0) : InvertibleKernel :=
  (M.comp (diagonalBasis a b ha hb)).comp (T.transpose M)

theorem cap_det (M : InvertibleKernel) (a b : AlgebraicComplex) :
    SymmetricBinaryPullback.determinant (capKernel M a b)=
      SymmetricBinaryPullback.determinant M.matrix^2*a*b := by
  simp [capKernel,diagonal,SymmetricBinaryPullback.determinant,Kernel.mul_apply,Kernel.transpose]
  ring

theorem cap_weights_nonzero (M : InvertibleKernel) (a b : AlgebraicComplex)
    (det : SymmetricBinaryPullback.determinant (capKernel M a b)≠0) : a≠0 ∧ b≠0 := by
  rw [cap_det] at det
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp det).1).2,(mul_ne_zero_iff.mp det).2⟩

theorem scalar_inverse (B : InvertibleKernel) (J : Kernel AlgebraicComplex) (c : AlgebraicComplex)
    (inverse : Kernel.mul J B.matrix=fun p q=>c*Signature.equality p q) :
    J=fun p q=>c*B.inverse p q := by
  have h:=congrArg (fun E=>Kernel.mul E B.inverse) inverse
  rw [Kernel.mul_assoc,B.matrix_inverse,Kernel.mul_equality] at h
  refine h.trans ?_
  funext p q
  cases p <;> simp [Kernel.mul_apply,Signature.equality]

theorem inverse_pullback (M : InvertibleKernel) (a b : AlgebraicComplex) (ha : a≠0) (hb : b≠0)
    (J : Kernel AlgebraicComplex) (c : AlgebraicComplex)
    (inverse : Kernel.mul J (capKernel M a b)=fun p q=>c*Signature.equality p q) :
    Kernel.pullback J M.matrix=fun p q=>c*diagonal a⁻¹ b⁻¹ p q := by
  have h:=scalar_inverse (capBasis M a b ha hb) J c inverse
  rw [h,Conformal.pullback_scale]
  have transpose_cancel : Kernel.mul (Kernel.transpose M.matrix) (Kernel.transpose M.inverse)=Signature.equality := by
    rw [←Kernel.transpose_mul,M.inverse_matrix,Kernel.transpose_equality]
  have cancel : Kernel.pullback (capBasis M a b ha hb).inverse M.matrix=diagonal a⁻¹ b⁻¹ := by
    simp only [capBasis,InvertibleKernel.comp,T.transpose,diagonalBasis,Kernel.pullback,Kernel.mul_assoc]
    rw [←Kernel.mul_assoc (Kernel.transpose M.matrix) (Kernel.transpose M.inverse),transpose_cancel,Kernel.equality_mul,
      M.inverse_matrix,Kernel.mul_equality]
  rw [cancel]

theorem weighted_eq3 (a b : AlgebraicComplex) (ha : a≠0) (hb : b≠0) :
    (diagonalBasis a b ha hb).symm.action GlobalCloseCompletionSymmetricGHZCoordinates.eq3=
      C.symmetric (a⁻¹^3) 0 0 (b⁻¹^3) := by
  change C.ghz (diagonal a⁻¹ b⁻¹)=_
  funext x
  rw [C.ghz_value]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [diagonal,C.symmetric,h0,h1,h2,pow_succ]

theorem frame (M : InvertibleKernel) (a b : AlgebraicComplex) (ha : a≠0) (hb : b≠0)
    (J : Kernel AlgebraicComplex) (c : AlgebraicComplex) (hc : c≠0)
    (inverse : Kernel.mul J (capKernel M a b)=fun p q=>c*Signature.equality p q) :
    ∃R : InvertibleKernel,Kernel.pullback J R.matrix=Signature.equality ∧
      ∃p q : AlgebraicComplex,p≠0 ∧ q≠0 ∧ R.symm.action (C.ghz M.matrix)=C.symmetric p 0 0 q := by
  letI : IsAlgClosed AlgebraicComplex:=IsAlgClosure.isAlgClosed ℚ
  obtain ⟨u,hu⟩:=IsAlgClosed.exists_pow_nat_eq (a/c) (by decide : 0<2)
  obtain ⟨v,hv⟩:=IsAlgClosed.exists_pow_nat_eq (b/c) (by decide : 0<2)
  have un : u≠0:=by intro zero;rw [zero,zero_pow (by decide : 2≠0)] at hu;exact div_ne_zero ha hc hu.symm
  have vn : v≠0:=by intro zero;rw [zero,zero_pow (by decide : 2≠0)] at hv;exact div_ne_zero hb hc hv.symm
  let D:=diagonalBasis u v un vn
  refine ⟨M.comp D,?_,u⁻¹^3,v⁻¹^3,pow_ne_zero _ (inv_ne_zero un),pow_ne_zero _ (inv_ne_zero vn),?_⟩
  · change Kernel.pullback J (Kernel.mul M.matrix D.matrix)=_
    rw [pullback_mul,inverse_pullback M a b ha hb J c inverse,Conformal.pullback_scale]
    funext p q
    cases p <;> cases q <;> simp [D,diagonalBasis,diagonal,Kernel.pullback,Kernel.mul_apply,Kernel.transpose,Signature.equality]
    · rw [show u*a⁻¹*u=u^2/a by ring,hu]
      field_simp
    · rw [show v*b⁻¹*v=v^2/b by ring,hv]
      field_simp
  · change (M.comp D).symm.action (M.action GlobalCloseCompletionSymmetricGHZCoordinates.eq3)=_
    rw [InvertibleKernel.comp_symm,InvertibleKernel.comp_action,InvertibleKernel.symm_action_action]
    exact weighted_eq3 u v un vn

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZFrame
end
