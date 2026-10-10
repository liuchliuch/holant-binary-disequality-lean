import Holant.Projective.CyclicPhasePencil.Algebraic

/-! Exact two-complement block algebra for manuscript Lemma 7.2. The input is
the pair of source relations obtained from both normalized phase deletions.
No central coordinate, endpoint, or sampled card is assumed nonzero. -/
noncomputable section
namespace Holant.Projective.CyclicQuaternary
open CyclicPhasePencil
variable {K : Type*} [Field K]

def BlockCondition (m : ℕ) (p t x y : K) : Prop :=
  CyclicPhasePencil.Relation m p x y t ∧ CyclicPhasePencil.Relation m p y x t

def NonzeroBlock (m : ℕ) (p t x y : K) : Prop :=
  (x=0 ∧ y=0) ∨ ∃ α : K, α^m=1 ∧ x= -p*(t/p)*α⁻¹ ∧ y= -p*α

def ZeroBlock (m : ℕ) (x y : K) : Prop :=
  (x=0 ∧ y=0) ∨ ∃ ρ α : K, ρ≠0 ∧ α^m=1 ∧ x=ρ ∧ y=ρ*α

/-- The two complementary deletions exclude either mixed endpoint-zero pattern. -/
theorem endpoint_zero_iff {m : ℕ} (hm : 0<m) (p t x y : K)
    (h : BlockCondition m p t x y) : p=0 ↔ t=0 := by
  obtain ⟨⟨α,hα,ha | ha | ha⟩,hsecond⟩ := h
  all_goals have hα0 := root_ne_zero hm hα
  · obtain ⟨β,hβ,hb | hb | hb⟩ := hsecond
    all_goals have hβ0 := root_ne_zero hm hβ
    · rw [ha.2,hb.1]
      simp [hα0,hβ0]
    · rw [hb.2.2]
      simp [hβ0]
    · simp [hb.1,hb.2.1]
  · rw [ha.2.2]
    simp [hα0]
  · simp [ha.1,ha.2.1]

/-- Nonzero endpoints force the exact root ratio and parametrized central block. -/
theorem nonzero_block {m : ℕ} (hm : 0<m) (p t x y : K)
    (hp : p≠0) (ht : t≠0) (h : BlockCondition m p t x y) :
    (t/p)^m=1 ∧ NonzeroBlock m p t x y := by
  obtain ⟨⟨α,hα,ha | ha | ha⟩,hsecond⟩ := h
  · obtain ⟨hy,htx⟩ := ha
    have hα0 := root_ne_zero hm hα
    have hy0 : y≠0 := by rw [hy]; exact mul_ne_zero (neg_ne_zero.mpr hα0) hp
    obtain ⟨β,hβ,hb | hb | hb⟩ := hsecond
    · obtain ⟨hx,hty⟩ := hb
      have hratio : t/p=α*β := by rw [htx,hx]; field_simp <;> ring
      refine ⟨?_,Or.inr ⟨α,hα,?_,?_⟩⟩
      · rw [hratio,mul_pow,hα,hβ,mul_one]
      · rw [hratio,hx]; field_simp <;> ring
      · rw [hy]; ring
    · exact (hy0 hb.1).elim
    · exact (hp hb.1).elim
  · obtain ⟨hx,hy,htp⟩ := ha
    refine ⟨?_,Or.inl ⟨hx,hy⟩⟩
    rw [htp,mul_div_cancel_right₀ _ hp]
    exact hα
  · exact (hp ha.1).elim

/-- With both endpoints zero, a nonzero block is a root-ratio vector with its
actual nonzero first coordinate retained as the scalar. -/
theorem zero_block {m : ℕ} (hm : 0<m) (x y : K)
    (h : BlockCondition m (0 : K) 0 x y) : ZeroBlock m x y := by
  obtain ⟨⟨α,hα,ha | ha | ha⟩,_⟩ := h
  · left
    have hα0 := root_ne_zero hm hα
    obtain ⟨hy,hx⟩ := ha
    simp only [mul_zero,neg_zero] at hy
    refine ⟨?_,hy⟩
    exact (mul_eq_zero.mp hx.symm).resolve_left (neg_ne_zero.mpr hα0)
  · exact Or.inl ⟨ha.1,ha.2.1⟩
  · by_cases hx : x=0
    · exact Or.inl ⟨hx,by rw [ha.2.2,hx,mul_zero]⟩
    · exact Or.inr ⟨x,α,hx,hα,rfl,by rw [ha.2.2]; ring⟩

/-- Converse for the nonzero endpoint parametrization, including zero blocks. -/
theorem block_of_nonzero {m : ℕ} (hm : 0<m) (p t x y : K)
    (hp : p≠0) (hphase : (t/p)^m=1) (h : NonzeroBlock m p t x y) :
    BlockCondition m p t x y := by
  rcases h with ⟨rfl,rfl⟩ | ⟨α,hα,hx,hy⟩
  · have ht : t=(t/p)*p := (div_mul_cancel₀ _ hp).symm
    exact ⟨⟨t/p,hphase,Or.inr (Or.inl ⟨rfl,rfl,ht⟩)⟩,
      ⟨t/p,hphase,Or.inr (Or.inl ⟨rfl,rfl,ht⟩)⟩⟩
  · have hα0 := root_ne_zero hm hα
    refine ⟨⟨α,hα,Or.inl ⟨?_,?_⟩⟩,⟨(t/p)/α,?_,Or.inl ⟨?_,?_⟩⟩⟩
    · rw [hy]; ring
    · rw [hx]; field_simp <;> ring
    · rw [div_pow,hphase,hα,div_one]
    · rw [hx]; ring
    · rw [hy]; field_simp <;> ring

/-- Converse for a zero endpoint block uses the inverse phase in the reversed
complementary deletion. The actual scalar is retained in both relations. -/
theorem block_of_zero {m : ℕ} (hm : 0<m) (x y : K) (h : ZeroBlock m x y) :
    BlockCondition m (0 : K) 0 x y := by
  rcases h with ⟨rfl,rfl⟩ | ⟨ρ,α,hρ,hα,rfl,rfl⟩
  · exact ⟨relation_zero m,relation_zero m⟩
  · have hα0 := root_ne_zero hm hα
    refine ⟨⟨α,hα,Or.inr (Or.inr ⟨rfl,rfl,by ring⟩)⟩,
      ⟨α⁻¹,?_,Or.inr (Or.inr ⟨rfl,rfl,?_⟩)⟩⟩
    · rw [inv_pow,hα,inv_one]
    · field_simp <;> ring

end Holant.Projective.CyclicQuaternary
