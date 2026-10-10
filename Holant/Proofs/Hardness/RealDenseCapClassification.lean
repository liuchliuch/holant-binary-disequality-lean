import Holant.Proofs.Hardness.GeneralGeometricCapLocal

/-! Finite real coefficient classification when neither accepted direct nor
geometric binary pin access applies. This is structural progress only: the
exceptional and signed regions still require their actual source consumers. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.RealDenseCapClassification
open Holant
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace Cap
export GeneralCancellationCapPin (coefficients oriented Applicable)
end Cap

def sums (M : Signature ℝ 4) : Fin 3→ℝ :=
  ![(entries M).b+(entries M).y,(entries M).c+(entries M).z,(entries M).d+(entries M).w]
def differences (M : Signature ℝ 4) : Fin 3→ℝ :=
  ![(entries M).b-(entries M).y,(entries M).c-(entries M).z,(entries M).d-(entries M).w]
def BalancedCaps (M : Signature ℝ 4) : Prop :=
  ∀c : Fin 6,(Cap.coefficients M c).1^2=(Cap.coefficients M c).2^2

theorem no_access_balanced (M : Signature ℝ 4) (hd : ¬Cap.Applicable M)
    (hg : ¬GeneralGeometricCapLocal.Applicable M) : BalancedCaps M := by
  intro c
  let p := (Cap.coefficients M c).1
  let q := (Cap.coefficients M c).2
  have hn : ‖p‖=‖q‖ := by
    by_contra hn
    by_cases hp : p=0
    · have hq : q≠0 := by intro hq; apply hn; simp [hp,hq]
      exact hd ⟨(c,true),by simpa [Cap.oriented,p,q] using hq,by simpa [Cap.oriented,p,q] using hp⟩
    by_cases hq : q=0
    · exact hd ⟨(c,false),by simpa [Cap.oriented,p,q] using hp,by simpa [Cap.oriented,p,q] using hq⟩
    exact hg ⟨(c,false),hp,hq,hn⟩
  have hs := congrArg (fun x : ℝ=>x^2) hn
  simpa only [Real.norm_eq_abs,sq_abs,p,q] using hs

theorem balance_relations (M : Signature ℝ 4) (h : BalancedCaps M)
    (i j : Fin 3) (hij : i≠j) :
    differences M i*(sums M i+sums M j)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  norm_num [Cap.coefficients] at h0 h1 h2 h3 h4 h5
  fin_cases i <;> fin_cases j
  all_goals try exact False.elim (hij rfl)
  all_goals dsimp [differences, sums]
  · linear_combination (1 / 2 : ℝ) * h2 + (1 / 2 : ℝ) * h3
  · linear_combination (1 / 2 : ℝ) * h1 + (1 / 2 : ℝ) * h4
  · linear_combination (1 / 2 : ℝ) * h3 - (1 / 2 : ℝ) * h2
  · linear_combination (1 / 2 : ℝ) * h0 + (1 / 2 : ℝ) * h5
  · linear_combination (1 / 2 : ℝ) * h4 - (1 / 2 : ℝ) * h1
  · linear_combination (1 / 2 : ℝ) * h5 - (1 / 2 : ℝ) * h0

theorem balanced_of_relations (M : Signature ℝ 4)
    (h : ∀i j : Fin 3,i≠j → differences M i*(sums M i+sums M j)=0) :
    BalancedCaps M := by
  have h01 := h 0 1 (by decide)
  have h02 := h 0 2 (by decide)
  have h10 := h 1 0 (by decide)
  have h12 := h 1 2 (by decide)
  have h20 := h 2 0 (by decide)
  have h21 := h 2 1 (by decide)
  dsimp [differences,sums] at h01 h02 h10 h12 h20 h21
  intro c
  fin_cases c <;> dsimp [Cap.coefficients]
  · linear_combination h12-h21
  · linear_combination h02-h20
  · linear_combination h01-h10
  · linear_combination h01+h10
  · linear_combination h02+h20
  · linear_combination h12+h21

theorem balanced_iff_relations (M : Signature ℝ 4) :
    BalancedCaps M ↔ ∀i j : Fin 3,i≠j → differences M i*(sums M i+sums M j)=0 :=
  ⟨balance_relations M,balanced_of_relations M⟩

/-- Exact finite algebra, not a Helly assertion on arbitrary profiles. -/
theorem three_pair_classification (s t : Fin 3→ℝ)
    (h : ∀i j,i≠j → t i*(s i+s j)=0) :
    (∀i,t i=0) ∨ (∀i,s i=0) ∨
      ∃i,t i≠0 ∧ ∀j,j≠i → t j=0 ∧ s j= -s i := by
  by_cases ht : ∀i,t i=0
  · exact Or.inl ht
  push Not at ht
  obtain ⟨i,hi⟩ := ht
  have hs : ∀j,j≠i → s j= -s i := by
    intro j hji
    have he := (mul_eq_zero.mp (h i j (Ne.symm hji))).resolve_left hi
    linarith
  by_cases hj : ∀j,j≠i → t j=0
  · exact Or.inr (Or.inr ⟨i,hi,fun j hji=>⟨hj j hji,hs j hji⟩⟩)
  push Not at hj
  obtain ⟨j,hji,hj⟩ := hj
  have hk : ∃k : Fin 3,k≠i ∧ k≠j := by
    fin_cases i <;> fin_cases j <;> simp_all
    all_goals first | exact ⟨0,by decide,by decide⟩ | exact ⟨1,by decide,by decide⟩ | exact ⟨2,by decide,by decide⟩
  obtain ⟨k,hki,hkj⟩ := hk
  have he := (mul_eq_zero.mp (h j k (Ne.symm hkj))).resolve_left hj
  have hsj := hs j hji
  have hsk := hs k hki
  have hsi : s i=0 := by linarith
  exact Or.inr (Or.inl (fun l=>by
    by_cases hl : l=i
    · simpa only [hl] using hsi
    · rw [hs l hl,hsi,neg_zero]))

theorem original_classification (M : Signature ℝ 4) (h : BalancedCaps M) :
    (∀i,differences M i=0) ∨ (∀i,sums M i=0) ∨
      ∃i,differences M i≠0 ∧ ∀j,j≠i → differences M j=0 ∧ sums M j= -sums M i :=
  three_pair_classification (sums M) (differences M) (balance_relations M h)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.RealDenseCapClassification
