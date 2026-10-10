import Holant.Certificates.RainbowOrbit.Geometry

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Algebraic closure conditions, instantiated below by the literal external
matrix dictionary. These do not postulate any line classification. -/
structure MatrixFamily (G : BinaryMatrix→Prop) : Prop where
  one : G 1
  mul : ∀{U V : BinaryMatrix},G U→G V→G (U*V)
  inverse : ∀{U : BinaryMatrix},G U→G U⁻¹
  transpose : ∀{U : BinaryMatrix},G U→G U.transpose
  smul : ∀{U : BinaryMatrix},G U→∀{c : ℂ},c≠0→G (c • U)
  nonsingular : ∀{U : BinaryMatrix},G U→U.det≠0

theorem MatrixFamily.normalization {G : BinaryMatrix→Prop} (hG : MatrixFamily G)
    (U V S : BinaryMatrix) (hU : G U) (hV : G V) (hS : G S) :
    ∀j,G (normalization U V S j) := by
  have hs := hG.mul (hG.mul (hG.inverse hU) hS) (hG.transpose (hG.inverse hV))
  have hfirst : ∀j,G (firstNormalization U V j) := by
    intro j
    fin_cases j
    · exact hG.inverse hU
    · exact hG.one
    · exact hG.inverse hV
    · exact hG.one
  have hsecond : ∀j,G (secondNormalization (U⁻¹*S*V⁻¹.transpose) j) := by
    intro j
    fin_cases j
    · exact hG.inverse hs
    · exact hG.transpose hs
    · exact hG.one
    · exact hG.one
  exact fun j => hG.mul (hsecond j) (hfirst j)

/-- Every rainbow over a saturated transpose-stable actual matrix family forces
membership of the literal alternating matrix Y. This includes vanishing-free
coefficients and arbitrary original representatives. -/
theorem rainbow_forces_Q2 {G : BinaryMatrix→Prop} (hG : MatrixFamily G)
    (U V S T M N : BinaryMatrix) (hU : G U) (hV : G V) (hS : G S) (hT : G T) (hM : G M) (hN : G N)
    (hcol : Projectivization.IsCollinear
      {Projectivization.mk ℂ (P0 U V) (matching_nonzero 0 U V (hG.nonsingular hU) (hG.nonsingular hV)),
       Projectivization.mk ℂ (P1 S T) (matching_nonzero 1 S T (hG.nonsingular hS) (hG.nonsingular hT)),
       Projectivization.mk ℂ (P2 M N) (matching_nonzero 2 M N (hG.nonsingular hM) (hG.nonsingular hN))}) :
    G (Matrix.of Q2) := by
  have hn (r s : Fin 3) (hrs : r≠s) (A B C D : BinaryMatrix)
      (ha : G A) (hb : G B) (hc : G C) (hd : G D) :
      ¬Proportional (matchingTensor r A B) (matchingTensor s C D) := by
    intro h
    exact hrs (proportional_matching_labels r s A B C D (hG.nonsingular ha)
      (hG.nonsingular hb) (hG.nonsingular hc) (hG.nonsingular hd) h)
  obtain ⟨α,β,hα,hβ,hline⟩ := (collinear_triple_iff _ _ _ _ _ _
    (hn 0 1 (by decide) U V S T hU hV hS hT)
    (hn 2 0 (by decide) M N U V hM hN hU hV)
    (hn 2 1 (by decide) M N S T hM hN hS hT)).mp hcol
  have hnormal := normalize_rainbow U V S T M N (hG.nonsingular hU) (hG.nonsingular hV)
    (hG.nonsingular hS) (hG.nonsingular hM) (hG.nonsingular hN) α β hα hβ hline
  let L := normalization U V S
  have hL := hG.normalization U V S hU hV hS
  have hM' : G (L 0*M*(L 3).transpose) := hG.mul (hG.mul (hL 0) hM) (hG.transpose (hL 3))
  have hN' : G (L 1*N*(L 2).transpose) := hG.mul (hG.mul (hL 1) hN) (hG.transpose (hL 2))
  have he : Proportional (matchingTensor 2 (L 0*M*(L 3).transpose) (L 1*N*(L 2).transpose))
      (matchingTensor 2 (Matrix.of Q2) (Matrix.of Q2)) := by
    refine ⟨α,hα,?_⟩
    funext x
    have hx := congrFun hnormal.2.2 x
    simpa [act_P2,L,matchingTensor,C,P2,Matrix.of_apply] using hx
  obtain ⟨⟨c,hc,hcM⟩,_⟩ := proportional_matching_factors 2 _ _ _ _
    (hG.nonsingular hM') (hG.nonsingular hN') he
  have hg := hG.smul hM' (inv_ne_zero hc)
  rw [hcM,smul_smul,inv_mul_cancel₀ hc,one_smul] at hg
  exact hg

end
end Holant.Certificates.RainbowOrbit
