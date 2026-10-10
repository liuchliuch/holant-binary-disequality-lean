import Holant.Projective.CyclicPhasePencil.Rigidity
import Holant.Tractable.Scalars

/-! Exact source-field version of Lemma 7.1. Every complex root of positive
finite order is algebraic, so both sample quantification and existential phases
are transported to the manuscript's actual algebraic-complex field. -/
noncomputable section
namespace Holant.Projective.CyclicPhasePencil
open Holant.Tractable

/-- The finite-order certificate itself supplies algebraicity. -/
def algebraicRoot {m : ℕ} (hm : 0<m) (z : ℂ) (hz : z^m=1) : AlgebraicComplex :=
  ⟨z,IsIntegral.of_pow hm (by rw [hz]; exact isIntegral_one)⟩

@[simp] theorem coe_algebraicRoot {m : ℕ} (hm : 0<m) (z : ℂ) (hz : z^m=1) :
    (algebraicRoot hm z hz : ℂ)=z := rfl

theorem algebraicRoot_pow {m : ℕ} (hm : 0<m) (z : ℂ) (hz : z^m=1) :
    (algebraicRoot hm z hz)^m=1 := by
  apply Subtype.ext
  exact hz

theorem scalarSample_coe_iff (m : ℕ) (u v : AlgebraicComplex) :
    ScalarSample m (u : ℂ) (v : ℂ) ↔ ScalarSample m u v := by
  unfold ScalarSample
  norm_cast

theorem scalarSamples_coe_iff {m : ℕ} (hm : 0<m) (a b c d : AlgebraicComplex) :
    ScalarSamples m (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) ↔ ScalarSamples m a b c d := by
  constructor
  · intro h s hs
    have hr : (s : ℂ)^m=1 := by exact_mod_cast hs
    have hh := h (s : ℂ) hr
    exact (scalarSample_coe_iff m (a-s*b) (-c+s*d)).mp hh
  · intro h s hs
    have hh := h (algebraicRoot hm s hs) (algebraicRoot_pow hm s hs)
    exact (scalarSample_coe_iff m (a-algebraicRoot hm s hs*b) (-c+algebraicRoot hm s hs*d)).mpr hh

theorem relation_coe_iff {m : ℕ} (hm : 0<m) (a b c d : AlgebraicComplex) :
    Relation m (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) ↔ Relation m a b c d := by
  constructor
  · rintro ⟨α,hα,h | h | h⟩
    all_goals refine ⟨algebraicRoot hm α hα,algebraicRoot_pow hm α hα,?_⟩
    · left
      constructor <;> apply Subtype.ext
      · exact h.1
      · exact h.2
    · right; left
      exact ⟨by exact_mod_cast h.1,by exact_mod_cast h.2.1,Subtype.ext h.2.2⟩
    · right; right
      exact ⟨by exact_mod_cast h.1,by exact_mod_cast h.2.1,Subtype.ext h.2.2⟩
  · rintro ⟨α,hα,h | h | h⟩
    all_goals refine ⟨(α : ℂ),by exact_mod_cast hα,?_⟩
    · left
      constructor
      · exact_mod_cast h.1
      · exact_mod_cast h.2
    · right; left
      exact ⟨by exact_mod_cast h.1,by exact_mod_cast h.2.1,by exact_mod_cast h.2.2⟩
    · right; right
      exact ⟨by exact_mod_cast h.1,by exact_mod_cast h.2.1,by exact_mod_cast h.2.2⟩

/-- Manuscript Lemma 7.1 in the exact algebraic coefficient domain. The root
phase and every projective multiplier are also algebraic complex numbers. -/
theorem cyclic_phase_pencil_algebraic {m : ℕ} (hm : 3≤m) (a b c d : AlgebraicComplex) :
    Relation m a b c d ↔ MatrixSamples m a b c d := by
  rw [← relation_coe_iff (by omega),matrixSamples_iff (by omega),
    ← scalarSamples_coe_iff (by omega),relation_iff_scalarSamples hm]

end Holant.Projective.CyclicPhasePencil
