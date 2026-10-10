import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesInverse
import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesRelabel

/-! Equalize the two nonzero diagonal coefficients through an actual inverse
of the binary loop. The entire source extension and all old labels survive. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesNormalize
open Holant Holant.Complexity Holant.Algebraic
open Holant.Certificates.MatchingContractionClosure
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
export OrdinaryNegativeCubicGadgets.Macro (row row_denote)
end M
namespace P
export GlobalCloseCompletionPairedSeriesCore (row)
export GlobalCloseCompletionPairedSeriesCaps (loop_value output)
end P
namespace R
export GlobalCloseCompletionPairedSeriesRelabel (relabel correct correct_value)
end R
namespace D
export OrdinaryTargetInterpolationDiagonal (diagonal)
end D
namespace I
export GlobalCloseCompletionPairedSeriesInverse (produce matrix)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K]

theorem diagonal_inverse (B : Matrix Bool Bool K) (a d c : K) (ha : a≠0) (hd : d≠0)
    (inverse : D.diagonal a d*B=c • (1 : Matrix Bool Bool K)) :
    B=D.diagonal (c/a) (c/d) := by
  ext i j
  have h:=congrFun₂ inverse i j
  cases i <;> cases j <;>
    simp [D.diagonal,Matrix.mul_apply,Matrix.one_apply] at h ⊢
  · apply (eq_div_iff ha).mpr
    linear_combination h
  · exact h.resolve_left ha
  · exact h.resolve_left hd
  · apply (eq_div_iff hd).mpr
    linear_combination h

variable [Algebra ℚ K] {s degree : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (F : FixedField K degree)
variable (N : M.Macro H 4) (B : Matrix Bool Bool K)
variable (hN : N.network.denote=P.row B) (ha : B false false≠0) (hd : B true true≠0)

def extension := I.produce H F N.contract (B false false) (B true true) ha hd (P.loop_value N B hN)
abbrev E := extension H F N B hN ha hd

include hN in
theorem loop_matrix : GlobalCloseCompletionSymmetricGHZInverse.matrix H (P.output N.contract)=
    D.diagonal (B false false) (B true true) :=
  I.matrix H N.contract _ _ (P.loop_value N B hN)

theorem inverse_value : (E H F N B hN ha hd).inverse=
    D.diagonal ((E H F N B hN ha hd).scalar/B false false)
      ((E H F N B hN ha hd).scalar/B true true) := by
  apply diagonal_inverse _ _ _ _ ha hd
  rw [←loop_matrix H N B hN]
  exact (E H F N B hN ha hd).right_inverse

def oldRow : M.Macro (E H F N B hN ha hd).table 4 :=
  R.relabel H (E H F N B hN ha hd).table (E H F N B hN ha hd).old
    (E H F N B hN ha hd).old_literal N

def inverseRow : M.Macro (E H F N B hN ha hd).table 2 :=
  M.row (E H F N B hN ha hd).label (binarySignature (E H F N B hN ha hd).inverse)
    (E H F N B hN ha hd).literal

def normalized : M.Macro (E H F N B hN ha hd).table 4 :=
  R.correct (E H F N B hN ha hd).table (oldRow H F N B hN ha hd) (inverseRow H F N B hN ha hd)

theorem value : (normalized H F N B hN ha hd).network.denote=
    P.row (B*(E H F N B hN ha hd).inverse) := by
  rw [normalized,inverse_value H F N B hN ha hd]
  apply R.correct_value
  · exact hN
  · rw [inverseRow,M.row_denote,inverse_value H F N B hN ha hd]

theorem diagonal (bit : Bool) : (B*(E H F N B hN ha hd).inverse) bit bit=(E H F N B hN ha hd).scalar := by
  rw [inverse_value H F N B hN ha hd]
  cases bit <;> simp [Matrix.mul_apply,D.diagonal] <;> field_simp

include ha hd in
theorem nonsingular (det : B.det≠0) : (B*(E H F N B hN ha hd).inverse).det≠0 := by
  rw [Matrix.det_mul]
  apply mul_ne_zero det
  intro zero
  have h:=congrArg Matrix.det (E H F N B hN ha hd).left_inverse
  rw [Matrix.det_mul,zero,zero_mul] at h
  simp only [Matrix.det_smul,Matrix.det_one,Fintype.card_bool,mul_one] at h
  exact pow_ne_zero _ (E H F N B hN ha hd).nonzero h.symm


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesNormalize
end
