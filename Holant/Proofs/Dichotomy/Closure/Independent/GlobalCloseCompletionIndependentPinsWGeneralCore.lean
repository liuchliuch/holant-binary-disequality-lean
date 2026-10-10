import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsWX

/-! The cyclic W symmetrizer with three independently transformed ports.
An equality or Z edge is selected for one cyclic orientation. Three nonzero
repeated columns cannot have disjoint coordinate supports pairwise, so one
of these six genuine triangles has nonzero repeated-column contraction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsWGeneralCore
open Holant Holant.Tractable
open scoped BigOperators
namespace W
export GlobalCloseCompletionIndependentPinsWCore (twist image columns columns_determinant)
end W
namespace T
export GlobalCloseCompletionTernaryGHZCore (triangle action cyclic)
end T
namespace C
export GlobalCloseCompletionSymmetricGHZCoordinates (ghz ghz_value)
end C
namespace B
export Holant.Tractable.SymmetricBinaryPullback (determinant determinant_ne_zero invertibleOfDeterminant)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

def image (A B C : Kernel K) : Signature K 3 := fun x=>
  A (x 0) true*B (x 1) false*C (x 2) false+
  A (x 0) false*B (x 1) true*C (x 2) false+
  A (x 0) false*B (x 1) false*C (x 2) true

def gram (t : K) (B C : Kernel K) (i j : Bool) : K := B false i*C false j+t*B true i*C true j

def core (p q r s : K) : Signature K 3 := fun x=>
  if x 0 then
    if x 1 then (if x 2 then p^3 else p^2*(q+r)) else
      (if x 2 then p^2*(q+r) else p*(p*s+q^2+q*r+r^2))
  else if x 1 then (if x 2 then p^2*(q+r) else p*(p*s+q^2+q*r+r^2))
    else (if x 2 then p*(p*s+q^2+q*r+r^2) else (q+r)*(3*p*s+q^2-q*r+r^2))

theorem triangle_image (t : K) (A B C : Kernel K) :
    T.triangle (W.twist t (image A B C))=T.action (Matrix.of A)
      (core (gram t B C false false) (gram t B C false true)
        (gram t B C true false) (gram t B C true true)) := by
  funext x
  simp [T.triangle,W.twist,GlobalCloseCompletionIndependentPinsWCore.sign,image,T.action,core,gram,Fintype.sum_bool]
  ring

theorem gram_determinant (t : K) (B C : Kernel K) :
    gram t B C false false*gram t B C true true-gram t B C false true*gram t B C true false=
      t*(B false false*B true true-B false true*B true false)*(C false false*C true true-C false true*C true false) := by
  simp only [gram]
  ring

theorem core_ghz [CharZero K] (p q r s d c : K)
    (square : d^2=p*s-q*r) (cube : c^3=(2:K)⁻¹) :
    core p q r s=C.ghz (W.columns p ((q+r)/2) d c) := by
  funext x
  rw [C.ghz_value]
  cases e0 : x 0 <;> cases e1 : x 1 <;> cases e2 : x 2 <;>
    simp only [core,W.columns,e0,e1,e2,Bool.false_eq_true,ite_false,ite_true]
  all_goals ring_nf
  all_goals rw [cube]
  all_goals try rw [square]
  all_goals ring

theorem zero_products [CharZero K] (A B : Kernel K)
    (same : gram (1:K) A B false false=0) (opposite : gram (-1:K) A B false false=0) :
    ∀v : Bool,A v false*B v false=0 := by
  simp only [gram,one_mul,neg_one_mul] at same opposite
  intro v
  cases v
  · linear_combination (same+opposite)/2
  · linear_combination (same-opposite)/2

theorem choose_pair [CharZero K] (A B C : Kernel K)
    (ha : A false false*A true true-A false true*A true false≠0)
    (hb : B false false*B true true-B false true*B true false≠0)
    (hc : C false false*C true true-C false true*C true false≠0) :
    (∃v : Bool,gram (if v then -1 else 1) B C false false≠0) ∨
    (∃v : Bool,gram (if v then -1 else 1) A B false false≠0) ∨
    (∃v : Bool,gram (if v then -1 else 1) C A false false≠0) := by
  classical
  by_contra bad
  push_neg at bad
  obtain ⟨bc,ab,ca⟩:=bad
  have hbc:=zero_products B C (bc false) (bc true)
  have hab:=zero_products A B (ab false) (ab true)
  have hca:=zero_products C A (ca false) (ca true)
  by_cases a0 : A false false=0
  · have a1 : A true false≠0 := by intro h;exact ha (by rw [a0,h];ring)
    have b1 : B true false=0 := (mul_eq_zero.mp (hab true)).resolve_left a1
    have c1 : C true false=0 := (mul_eq_zero.mp (hca true)).resolve_right a1
    have b0 : B false false≠0 := by intro h;exact hb (by rw [h,b1];ring)
    have c0 : C false false≠0 := by intro h;exact hc (by rw [h,c1];ring)
    exact (mul_ne_zero b0 c0) (hbc false)
  · have b0 : B false false=0 := (mul_eq_zero.mp (hab false)).resolve_left a0
    have c0 : C false false=0 := (mul_eq_zero.mp (hca false)).resolve_right a0
    have b1 : B true false≠0 := by intro h;exact hb (by rw [b0,h];ring)
    have c1 : C true false≠0 := by intro h;exact hc (by rw [c0,h];ring)
    exact (mul_ne_zero b1 c1) (hbc true)

theorem core_basis (p q r s : AlgebraicComplex) (hp : p≠0) (hd : p*s-q*r≠0) :
    ∃R : InvertibleKernel,core p q r s=C.ghz R.matrix := by
  letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨d,square⟩:=IsAlgClosed.exists_pow_nat_eq (p*s-q*r) (by decide : 0<2)
  obtain ⟨c,cube⟩:=IsAlgClosed.exists_pow_nat_eq ((2:AlgebraicComplex)⁻¹) (by decide : 0<3)
  have dn : d≠0 := by intro zero;rw [zero,zero_pow (by decide : 2≠0)] at square;exact hd square.symm
  have cn : c≠0 := by
    intro zero
    rw [zero,zero_pow (by decide : 3≠0)] at cube
    exact (inv_ne_zero (by norm_num : (2:AlgebraicComplex)≠0)) cube.symm
  have det : B.determinant (W.columns p ((q+r)/2) d c)≠0 := by
    rw [B.determinant,W.columns_determinant]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ cn)) hp) dn
  exact ⟨B.invertibleOfDeterminant (W.columns p ((q+r)/2) d c) det,core_ghz p q r s d c square cube⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsWGeneralCore
end
