import Holant.Certificates.MatchingProductBridge.Flattenings

namespace Holant.Certificates.MatchingProductBridge
open Matrix
noncomputable section

/-- A nonzero product on one ordered matching, with both factors invertible. -/
def InvertibleMatching (r : Fin 3) (W : FourTensor) : Prop :=
  ∃ U V : Matrix Bool Bool ℂ, U.det ≠ 0 ∧ V.det ≠ 0 ∧ W = matchingTensor r U V

/-- The full invertible matching cone, including the origin. Nonzero scales are
absorbed in the first factor; `invertibleMatchingCone_iff_scaled` makes this exact. -/
def InvertibleMatchingCone (W : FourTensor) : Prop :=
  W = 0 ∨ ∃ r, InvertibleMatching r W

theorem matchingTensor_smul_left (r : Fin 3) (c : ℂ) (U V : Matrix Bool Bool ℂ) :
    matchingTensor r (c • U) V = c • matchingTensor r U V := by
  fin_cases r <;> funext x <;> simp [matchingTensor,P0,P1,P2,smul_eq_mul,mul_assoc]

theorem InvertibleMatching.smul {r : Fin 3} {W : FourTensor}
    (h : InvertibleMatching r W) (c : ℂ) (hc : c ≠ 0) :
    InvertibleMatching r (c • W) := by
  obtain ⟨U,V,hU,hV,rfl⟩ := h
  refine ⟨c • U,V,?_,hV,(matchingTensor_smul_left r c U V).symm⟩
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ hc) hU

theorem InvertibleMatching.rank {r : Fin 3} {W : FourTensor}
    (h : InvertibleMatching r W) (s : Fin 3) :
    (flatten s W).rank = if s = r then 1 else 4 := by
  obtain ⟨U,V,hU,hV,rfl⟩ := h
  exact matching_flattening_rank s r U V hU hV

theorem InvertibleMatching.ne_zero {r : Fin 3} {W : FourTensor}
    (h : InvertibleMatching r W) : W ≠ 0 := by
  intro he
  have hr := h.rank r
  simp [he] at hr

theorem invertibleMatchingCone_iff_scaled (W : FourTensor) :
    InvertibleMatchingCone W ↔ W = 0 ∨
      ∃ (r : Fin 3) (c : ℂ) (U V : Matrix Bool Bool ℂ),
        U.det ≠ 0 ∧ V.det ≠ 0 ∧ W = c • matchingTensor r U V := by
  constructor
  · rintro (h | ⟨r,U,V,hU,hV,h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r,1,U,V,hU,hV,by simpa using h⟩
  · rintro (h | ⟨r,c,U,V,hU,hV,h⟩)
    · exact Or.inl h
    · by_cases hc : c = 0
      · exact Or.inl (by simp [hc] at h; exact h)
      · exact Or.inr ⟨r,h ▸ (InvertibleMatching.smul ⟨U,V,hU,hV,rfl⟩ c hc)⟩

theorem InvertibleMatching.unique {r s : Fin 3} {W : FourTensor}
    (hr : InvertibleMatching r W) (hs : InvertibleMatching s W) : r = s := by
  by_contra h
  have h₁ := hr.rank r
  have h₂ := hs.rank r
  simp [h] at h₁ h₂
  omega

/-- The source's line exclusion, phrased independently of a chosen factorization. -/
theorem invertible_matching_line_exclusion {r s : Fin 3} {X Y Z : FourTensor}
    (hX : InvertibleMatching r X) (hY : InvertibleMatching r Y)
    (hZ : InvertibleMatching s Z) (hrs : r ≠ s) (a b : ℂ) : a • X + b • Y ≠ Z := by
  obtain ⟨U,V,hU,hV,rfl⟩ := hX
  obtain ⟨U',V',hU',hV',rfl⟩ := hY
  obtain ⟨L,N,hL,hN,rfl⟩ := hZ
  exact no_mixed_matching_line r s hrs U V U' V' L N hU hV hU' hV' hL hN a b

/-- Three nonzero matching products on a line either have one common matching
or have three different matchings. -/
theorem invertible_matching_sum_indices {r s t : Fin 3} {X Y Z : FourTensor}
    (hX : InvertibleMatching r X) (hY : InvertibleMatching s Y)
    (hZ : InvertibleMatching t Z) (he : X + Y = Z) :
    (r = s ∧ s = t) ∨ (r ≠ s ∧ r ≠ t ∧ s ≠ t) := by
  by_cases hrs : r = s
  · left
    refine ⟨hrs,?_⟩
    subst s
    by_contra hrt
    exact invertible_matching_line_exclusion hX hY hZ hrt 1 1 (by simpa using he)
  · right
    refine ⟨hrs,?_,?_⟩
    · intro hrt
      subst t
      apply invertible_matching_line_exclusion hZ hX hY hrs 1 (-1)
      rw [← he]
      module
    · intro hst
      subst t
      apply invertible_matching_line_exclusion hZ hY hX (Ne.symm hrs) 1 (-1)
      rw [← he]
      module

@[simp] theorem Q0_matrix : Q0 = (1 : Matrix Bool Bool ℂ) := by
  ext a b; cases a <;> cases b <;> simp [Q0,Holant.Signature.equality]

theorem A_invertibleMatching : InvertibleMatching 0 A := by
  refine ⟨1,1,by simp,by simp,?_⟩
  simp [A,matchingTensor,Q0_matrix]

theorem B_invertibleMatching : InvertibleMatching 1 B := by
  refine ⟨1,1,by simp,by simp,?_⟩
  simp [B,matchingTensor,Q0_matrix]

/-- This determines all three matchings in a nonexceptional bridge before any
matrix-factor calculation is used. -/
theorem invertible_bridge_matching_indices (W : FourTensor) (r s t : Fin 3)
    (hW : InvertibleMatching r W) (hA : InvertibleMatching s (A-(2:ℂ)•W))
    (hB : InvertibleMatching t ((2:ℂ)•W-B)) :
    (r=0 ∧ s=0 ∧ t=2) ∨ (r=1 ∧ s=2 ∧ t=1) ∨ (r=2 ∧ s=1 ∧ t=0) := by
  have hw := hW.smul 2 (by norm_num)
  have ha := invertible_matching_sum_indices hw hA A_invertibleMatching
    (show (2:ℂ)•W+(A-(2:ℂ)•W)=A by module)
  have hb := invertible_matching_sum_indices (hB.smul (-1) (by norm_num)) hw B_invertibleMatching
    (show (-1:ℂ)•((2:ℂ)•W-B)+(2:ℂ)•W=B by module)
  fin_cases r <;> fin_cases s <;> fin_cases t <;> simp_all

end
end Holant.Certificates.MatchingProductBridge
