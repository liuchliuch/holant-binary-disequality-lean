import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixBellNorm
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixMatchingCoordinates

/-! Actual real Bell-card coordinates share one nonzero scalar and Boolean
signs. Equal norms and orthogonality are derived from the original Gram data,
not supplied as a finite coefficient classification assumption. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixBellCoordinates
open Holant
namespace B
export GlobalCloseCompletionKleinSixBellNorm (card orthogonal_cards)
end B
namespace D
export GlobalCloseCompletionKleinSixFiniteData (line orthogonal)
end D
namespace M
export GlobalCloseCompletionKleinSixMatchingCoordinates (sign square_sum orthogonal_correct)
end M
namespace W
export GlobalCloseCompletionKleinRMPhaseSupport (word4 index_word word_index)
end W
namespace S
export GlobalCloseCompletionKleinRMPhaseSource (index4)
end S
namespace N
export GlobalCloseCompletionKleinGramNorm (OrthogonalPair)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false

def wordEquiv : Fin 16≃(Fin 4→Bool) where
  toFun := W.word4
  invFun := S.index4
  left_inv := W.index_word
  right_inv := W.word_index

theorem sum_words (f : (Fin 4→Bool)→ℝ) : (∑x,f x)=∑i : Fin 16,f (W.word4 i) :=
  (Equiv.sum_comp wordEquiv f).symm

theorem square_sum (a : Fin 48) : (∑i : Fin 16,(D.line a i:ℝ)^2)=4 := by
  exact_mod_cast M.square_sum a

structure Normal (f : Signature ℝ 6) where
  label : Fin 4→Fin 48
  scale : ℝ
  scale_nonzero : scale≠0
  phase : Fin 4→Bool
  phase_zero : phase 0=false
  value : ∀k : Fin 4,∀x : Fin 16,
    B.card f k (W.word4 x)=scale*(M.sign (phase k):ℝ)*(D.line (label k) x:ℝ)
  orthogonal : ∀k l : Fin 4,k≠l→D.orthogonal (label k) (label l)=true

theorem normal (f : Signature ℝ 6) (orthogonal : N.OrthogonalPair (n:=4) f)
    (forms : ∀k : Fin 4,∃a : Fin 48,∃c : ℝ,c≠0 ∧
      ∀x : Fin 16,B.card f k (W.word4 x)=c*(D.line a x:ℝ)) : Nonempty (Normal f) := by
  classical
  choose label coeff nonzero value using forms
  obtain ⟨d,positive,grams,_⟩ := B.orthogonal_cards f orthogonal
  have norm (k : Fin 4) : (∑z : Fin 4→Bool,B.card f k z^2)=4*coeff k^2 := by
    rw [sum_words]
    simp_rw [value,mul_pow]
    rw [←Finset.mul_sum,square_sum]
    ring
  have squares (k : Fin 4) : coeff k^2=coeff 0^2 := by
    have h := grams k k
    have h0 := grams 0 0
    simp only [←pow_two,ite_true] at h h0
    rw [norm] at h h0
    linarith
  let phase : Fin 4→Bool := fun k=>decide (coeff k≠coeff 0)
  have signs (k : Fin 4) : coeff k=coeff 0*(M.sign (phase k):ℝ) := by
    by_cases equal : coeff k=coeff 0
    · simp [phase,equal,M.sign]
    · have opposite := (sq_eq_sq_iff_eq_or_eq_neg.mp (squares k)).resolve_left equal
      simp [phase,M.sign,opposite]
  refine ⟨⟨label,coeff 0,nonzero 0,phase,by simp [phase],?_,?_⟩⟩
  · intro k x
    rw [value,signs]
  · intro k l different
    have h := grams k l
    rw [if_neg different,sum_words] at h
    simp_rw [value] at h
    have term (x : Fin 16) : coeff k*(D.line (label k) x:ℝ)*(coeff l*(D.line (label l) x:ℝ))=
        (coeff k*coeff l)*((D.line (label k) x:ℝ)*(D.line (label l) x:ℝ)) := by ring
    simp_rw [term] at h
    rw [←Finset.mul_sum] at h
    have zero := (mul_eq_zero.mp h).resolve_left (mul_ne_zero (nonzero k) (nonzero l))
    apply (M.orthogonal_correct (label k) (label l)).mpr
    exact_mod_cast zero

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixBellCoordinates
end
