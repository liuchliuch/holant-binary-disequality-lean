import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoRegularize

/-! Rank-two parity repair retains non-Affineness with all original scales.
Every correction is an affine full-support unary obtained by pinning an
actual information port; cancellation is proved algebraically, not assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoRegularizeValue
open Holant Holant.Tractable
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSignedPortsCore
open OrdinaryNegativeRankTwoPorts OrdinaryNegativeRankTwoRegularize
open scoped BigOperators
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end I
namespace R
export OrdinaryNegativeSignedRowsCore (trace trace_value)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f 2)

def factor (axis : Fin 2) (j : Fin 3) (z : Fin 3→Bool) : AlgebraicComplex :=
  if Odd (I.bundleSize (port D) j) then f (D.encode (line axis (z j)))
    else f (D.encode ![false,false])

def multiplier (axis : Fin 2) : Signature AlgebraicComplex 3 :=
  fun z=>∏j,factor D axis j z

theorem correction_value (axis : Fin 2) (j : Fin 3) (z : Fin 3→Bool) :
    f (word (correction (port D) axis j) z)=factor D axis j z := by
  unfold correction factor
  split_ifs
  · rw [original_line_word]
  · rw [base_word]
    have h : (fun _ : Fin 3=>false)=A.codeThree ![false,false] := by decide
    rw [h,word_code]

theorem trace_value (axis : Fin 2) (z : Fin 3→Bool) :
    R.trace f (rows (port D) axis) z=f (word (port D) z)*multiplier D axis z := by
  rw [R.trace_value,Fin.prod_univ_succ]
  simp only [rows,Fin.cases_zero,Fin.cases_succ,correction_value]
  rfl

theorem factor_full (axis : Fin 2) (j : Fin 3) (z : Fin 3→Bool) : factor D axis j z≠0 := by
  unfold factor
  split_ifs <;> exact D.supported _

theorem multiplier_full (axis : Fin 2) (z : Fin 3→Bool) : multiplier D axis z≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact factor_full D axis j z

theorem factor_affine (axis : Fin 2)
    (ha : Affine (fun z : Fin 1→Bool=>f (D.encode (line axis (z 0))))) (j : Fin 3) :
    Affine (factor D axis j) := by
  unfold factor
  by_cases h : Odd (I.bundleSize (port D) j)
  · simp only [h,ite_true]
    exact ha.precompose (fun z _=>z j) (by intro x y;funext k;simp [AffinePhase.xor,AffinePhase.origin])
  · simp only [h,ite_false]
    exact affine_constant 3 _

theorem multiplier_affine (axis : Fin 2)
    (ha : Affine (fun z : Fin 1→Bool=>f (D.encode (line axis (z 0))))) :
    Affine (multiplier D axis) := by
  have h := (factor_affine D axis ha 0).mul
    ((factor_affine D axis ha 1).mul (factor_affine D axis ha 2))
  convert h using 1
  funext z
  simp [multiplier,Fin.prod_univ_three,mul_assoc]

theorem trace_nonaffine (axis : Fin 2)
    (square : Affine (fun x=>f x^2)) (nonzero : f≠0) (bad : ¬Affine f)
    (ha : Affine (fun z : Fin 1→Bool=>f (D.encode (line axis (z 0))))) :
    ¬Affine (R.trace f (rows (port D) axis)) := by
  have h := OrdinaryNegativeSparseMixingAlpha.multiply_affine_core
    (fun z=>f (word (port D) z)) (multiplier D axis)
    (essential_nonaffine D square nonzero bad) (multiplier_affine D axis ha)
    (multiplier_full D axis)
  rw [show R.trace f (rows (port D) axis)=(fun x=>f (word (port D) x)*multiplier D axis x) from
    funext (trace_value D axis)]
  exact h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoRegularizeValue
end
