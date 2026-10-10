import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixBellCoordinates

/-! The normalized I tensor I first card pins the dictionary's first label
and its real coefficient exactly; no projective first-card choice remains. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixAnchorUnique
open Holant
namespace D
export GlobalCloseCompletionKleinSixFiniteData (line)
end D
namespace B
export GlobalCloseCompletionKleinSixBellNorm (card)
end B
namespace C
export GlobalCloseCompletionKleinSixBellCoordinates (Normal)
end C
namespace W
export GlobalCloseCompletionKleinRMPhaseSupport (word4 index_word)
end W
namespace S
export GlobalCloseCompletionKleinRMPhaseSource (index4)
end S
namespace M
export GlobalCloseCompletionKleinSixMatchingCoordinates (sign)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

theorem line_origin : ∀a : Fin 48,D.line a 0=0 ∨ D.line a 0=1 := by decide +kernel
theorem line_zero_unique : ∀a : Fin 48,(∀i : Fin 16,D.line a i=D.line 0 i)→a=0 := by decide +kernel
theorem zero_value : D.line 0 0=1 := by decide +kernel

theorem label_zero (f : Signature ℝ 6) (R : C.Normal f) (d : ℝ) (hd : d≠0)
    (first : ∀z : Fin 4→Bool,B.card f 0 z=d*(D.line 0 (S.index4 z):ℝ)) :
    R.label 0=0 ∧ R.scale=d := by
  have pivot := (R.value 0 0).symm.trans (first (W.word4 0))
  simp only [R.phase_zero,M.sign,Bool.false_eq_true,ite_false,Int.cast_one,mul_one,
    W.index_word,zero_value] at pivot
  have scale : R.scale=d := by
    rcases line_origin (R.label 0) with zero|one
    · rw [zero,Int.cast_zero,mul_zero] at pivot
      exact (hd pivot.symm).elim
    · simpa only [one,Int.cast_one,mul_one] using pivot
  refine ⟨?_,scale⟩
  apply line_zero_unique
  intro i
  have h := (R.value 0 i).symm.trans (first (W.word4 i))
  simp only [R.phase_zero,M.sign,Bool.false_eq_true,ite_false,Int.cast_one,mul_one,
    W.index_word,scale] at h
  exact_mod_cast mul_left_cancel₀ hd h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixAnchorUnique
