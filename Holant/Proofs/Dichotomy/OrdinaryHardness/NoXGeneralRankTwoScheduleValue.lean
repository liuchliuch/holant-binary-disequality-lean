import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankTwoSchedule
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoRegularizeValue
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsUniform

/-! Every correction in the seven-copy separate-sign schedule is an actual
proper pin face or a supported constant pinning. Their full affine product
preserves the original non-Affine core and every original scalar. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoScheduleValue
open Holant Holant.Tractable
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace S
export NoXGeneralRankTwoSchedule (flag correction rows)
end S
namespace F
export NoXGeneralRankTwoFaces (correction_affine correction_full)
end F
namespace Q
export OrdinaryNegativeRankTwoPorts (port word_code essential_nonaffine)
export OrdinaryNegativeSparseMixingAlpha (codeThree)
end Q
namespace R
export OrdinaryNegativeRankTwoRegularize (basePort base_word)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f 2)
variable (i : Fin 4) (flags : Fin 3→Bool×Bool)

def factor (reverse : Bool) (j : Fin 3) : Signature AlgebraicComplex 3 :=
  fun z=>f (word (S.correction (Q.port D) i flags reverse j) z)

def multiplier : Signature AlgebraicComplex 3 :=
  fun z=>(∏j,factor D i flags false j z)*(∏j,factor D i flags true j z)

theorem base_value (z : Fin 3→Bool) :
    f (word (R.basePort (Q.port D)) z)=f (D.encode ![false,false]) := by
  rw [R.base_word]
  have h : (fun _ : Fin 3=>false)=Q.codeThree ![false,false] := by decide
  rw [h,Q.word_code]

theorem factor_full (reverse : Bool) (j : Fin 3) (z : Fin 3→Bool) :
    factor D i flags reverse j z≠0 := by
  unfold factor S.correction
  split_ifs
  · exact F.correction_full D i j reverse z
  · rw [base_value D z]
    exact D.supported _

theorem multiplier_full (z : Fin 3→Bool) : multiplier D i flags z≠0 := by
  apply mul_ne_zero
  all_goals apply Finset.prod_ne_zero_iff.mpr
  all_goals intro j _
  all_goals exact factor_full D i flags _ j z

variable (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (minor D S z))
include minimal in
theorem factor_affine (reverse : Bool) (j : Fin 3) : Affine (factor D i flags reverse j) := by
  unfold factor S.correction
  by_cases h : S.flag flags reverse j
  · simp only [h,ite_true]
    exact F.correction_affine D minimal i j reverse
  · simp only [h]
    convert affine_constant 3 (f (D.encode ![false,false])) using 1
    funext z
    exact base_value D z

include minimal in
theorem multiplier_affine : Affine (multiplier D i flags) := by
  exact (OrdinaryNegativeSignedRowsUniform.affine_prod Finset.univ
    (factor D i flags false) (fun j _=>factor_affine D i flags minimal false j)).mul
      (OrdinaryNegativeSignedRowsUniform.affine_prod Finset.univ
        (factor D i flags true) (fun j _=>factor_affine D i flags minimal true j))

theorem value (z : Fin 3→Bool) :
    (∏v : Fin 7,f (word (S.rows (Q.port D) i flags v) z))=
      f (word (Q.port D) z)*multiplier D i flags z := by
  rw [Fin.prod_univ_succ]
  simp only [S.rows,Fin.cases_zero,Fin.cases_succ]
  rw [Fin.prod_univ_add (a:=3) (b:=3)]
  simp only [Fin.addCases_left,Fin.addCases_right,multiplier,factor]

include minimal in
theorem nonaffine (square : Affine (fun x=>f x^2)) (nonzero : f≠0) (bad : ¬Affine f) :
    ¬Affine (fun z=>∏v : Fin 7,f (word (S.rows (Q.port D) i flags v) z)) := by
  have h:=OrdinaryNegativeSparseMixingAlpha.multiply_affine_core
    (fun z=>f (word (Q.port D) z)) (multiplier D i flags)
    (Q.essential_nonaffine D square nonzero bad) (multiplier_affine D i flags minimal)
    (multiplier_full D i flags)
  rw [show (fun z=>∏v : Fin 7,f (word (S.rows (Q.port D) i flags v) z))=
    (fun z=>f (word (Q.port D) z)*multiplier D i flags z) from funext (value D i flags)]
  exact h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoScheduleValue
end
