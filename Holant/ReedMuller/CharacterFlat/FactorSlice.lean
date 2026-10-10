import Holant.ReedMuller.CharacterFlat.FactorCode

/-! Fixing a supported word of one tensor factor restricts both the affine
support and the true linear character; no factor-flatness premise is used. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

theorem character_join (ell : Character (m+n)) (x : BinaryVector m) (y : BinaryVector n) :
    ell (joinVector x y)=ell (leftEmbedding x)+ell (rightEmbedding y) := by
  have h : joinVector x y=leftEmbedding x+rightEmbedding y := by
    change joinVector x y=joinVector x 0+joinVector 0 y
    rw [←join_add];simp
  rw [h,map_add]

theorem value_left_slice (c : ℂ) (a : BinaryVector (m+n)) (D : BinaryCode (m+n))
    (ell : Character (m+n)) (x : BinaryVector m) :
    value c a D ell (joinVector x (rightVector a))=
      value (c*sign (ell (rightEmbedding (rightVector a)))) (leftVector a)
        (leftCode D) (ell.comp leftEmbedding) x := by
  have he : joinVector x (rightVector a)-a=joinVector (x-leftVector a) (0:BinaryVector n) := by
    conv_lhs => rw [←join_parts a]
    rw [←join_sub];simp
  simp only [value,he,mem_leftCode,LinearMap.comp_apply,character_join,sign_add]
  split_ifs <;> ring

theorem value_right_slice (c : ℂ) (a : BinaryVector (m+n)) (D : BinaryCode (m+n))
    (ell : Character (m+n)) (y : BinaryVector n) :
    value c a D ell (joinVector (leftVector a) y)=
      value (c*sign (ell (leftEmbedding (leftVector a)))) (rightVector a)
        (rightCode D) (ell.comp rightEmbedding) y := by
  have he : joinVector (leftVector a) y-a=joinVector (0:BinaryVector m) (y-rightVector a) := by
    conv_lhs => rw [←join_parts a]
    rw [←join_sub];simp
  simp only [value,he,mem_rightCode,LinearMap.comp_apply,character_join,sign_add]
  split_ifs <;> ring

theorem value_div (c d : ℂ) (a : BinaryVector m) (D : BinaryCode m)
    (ell : Character m) (x : BinaryVector m) :
    value (c/d) a D ell x=value c a D ell x/d := by
  simp only [value]
  split_ifs <;> ring

theorem factor_code_splits (F : BinaryVector m → ℂ) (G : BinaryVector n → ℂ)
    (c : ℂ) (hc : c≠0) (a : BinaryVector (m+n)) (D : BinaryCode (m+n))
    (ell : Character (m+n))
    (he : ∀ x y,F x*G y=value c a D ell (joinVector x y)) : Splits D := by
  apply splits_of_cartesian D (fun x => F (leftVector a+x)≠0)
    (fun y => G (rightVector a+y)≠0)
  intro x y
  have H := value_nonzero_iff c hc a D ell (joinVector (leftVector a+x) (rightVector a+y))
  have hm : joinVector (leftVector a+x) (rightVector a+y)-a=joinVector x y := by
    rw [join_add,join_parts]
    abel
  rw [hm,←he] at H
  exact H.symm.trans mul_ne_zero_iff

theorem factor_values (F : BinaryVector m → ℂ) (G : BinaryVector n → ℂ)
    (c : ℂ) (hc : c≠0) (a : BinaryVector (m+n)) (D : BinaryCode (m+n))
    (ell : Character (m+n))
    (he : ∀ x y,F x*G y=value c a D ell (joinVector x y)) :
    ∃ c₁ c₂ : ℂ,c₁≠0 ∧ c₂≠0 ∧
      F=value c₁ (leftVector a) (leftCode D) (ell.comp leftEmbedding) ∧
      G=value c₂ (rightVector a) (rightCode D) (ell.comp rightEmbedding) := by
  have hb : F (leftVector a)*G (rightVector a)≠0 := by
    rw [he,join_parts]
    exact (value_nonzero_iff c hc a D ell a).mpr (by simp)
  have hf := (mul_ne_zero_iff.mp hb).1
  have hg := (mul_ne_zero_iff.mp hb).2
  refine ⟨c*sign (ell (rightEmbedding (rightVector a)))/G (rightVector a),
    c*sign (ell (leftEmbedding (leftVector a)))/F (leftVector a),
    div_ne_zero (mul_ne_zero hc (sign_nonzero _)) hg,
    div_ne_zero (mul_ne_zero hc (sign_nonzero _)) hf,?_,?_⟩
  · funext x
    rw [value_div,←value_left_slice,←he,mul_div_cancel_right₀ _ hg]
  · funext y
    rw [value_div,←value_right_slice,←he,mul_comm, mul_div_cancel_right₀ _ hf]

end
end Holant.ReedMuller.CharacterFlat
