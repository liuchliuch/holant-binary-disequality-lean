import Holant.Certificates.RainbowOrbit.FamilyGeometry

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

def FamilyDeckPoint (G : BinaryMatrix→Prop) (p : Point) : Prop :=
  ∃r F,∃hF : F≠0,FamilyInMatching G r F ∧ p=Projectivization.mk ℂ F hF

/-- Three invertible matching points with two distinct points of the same label
and one different label cannot lie on a projective line. -/
theorem no_same_label_rich_triple (r s : Fin 3) (hrs : r≠s)
    (U V U' V' S T : BinaryMatrix)
    (hU : U.det≠0) (hV : V.det≠0) (hU' : U'.det≠0) (hV' : V'.det≠0)
    (hS : S.det≠0) (hT : T.det≠0)
    (hne : ¬Proportional (matchingTensor r U V) (matchingTensor r U' V')) :
    ¬Projectivization.IsCollinear
      {Projectivization.mk ℂ (matchingTensor r U V) (matching_nonzero r U V hU hV),
       Projectivization.mk ℂ (matchingTensor r U' V') (matching_nonzero r U' V' hU' hV'),
       Projectivization.mk ℂ (matchingTensor s S T) (matching_nonzero s S T hS hT)} := by
  intro hc
  have hn0 : ¬Proportional (matchingTensor s S T) (matchingTensor r U V) :=
    fun h => hrs (proportional_matching_labels s r S T U V hS hT hU hV h).symm
  have hn1 : ¬Proportional (matchingTensor s S T) (matchingTensor r U' V') :=
    fun h => hrs (proportional_matching_labels s r S T U' V' hS hT hU' hV' h).symm
  obtain ⟨a,b,_,_,he⟩ := (collinear_triple_iff _ _ _ _ _ _ hne hn0 hn1).mp hc
  exact no_mixed_matching_line r s hrs U V U' V' S T hU hV hU' hV' hS hT a b he.symm

/-- Each semantic rainbow is the complete intersection of its projective line
with the actual matching deck. In particular, the counted triples are maximal. -/
theorem FamilyRainbowLine.maximal {G : BinaryMatrix→Prop}
    (hdet : ∀{U : BinaryMatrix},G U→U.det≠0)
    {S : Finset Point} (hS : FamilyRainbowLine G S) (q : Point) (hq : FamilyDeckPoint G q)
    (hcol : Projectivization.IsCollinear (insert q (S : Set Point))) : q∈S := by
  classical
  obtain ⟨p,hp,rfl⟩ := hS
  by_contra hnot
  obtain ⟨r,F,hF,⟨U',V',hU',hV',rfl⟩,heq⟩ := hq
  let s : Fin 3 := if r=0 then 1 else 0
  have hrs : r≠s := by fin_cases r <;> simp [s]
  obtain ⟨F0,hF0,⟨U,V,hU,hV,rfl⟩,he0⟩ := hp.1 r
  obtain ⟨F1,hF1,⟨M,N,hM,hN,rfl⟩,he1⟩ := hp.1 s
  have hp_mem (i : Fin 3) : p i∈points p := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hne : ¬Proportional (matchingTensor r U V) (matchingTensor r U' V') := by
    intro h
    have he := (proportional_point_iff _ _ hF0 hF).mp h
    have hqp : q=p r := by rw [heq,he0,he]
    exact hnot (hqp ▸ hp_mem r)
  have hc : Projectivization.IsCollinear {p r,q,p s} := by
    apply Projectivization.isCollinear_subset _ _ ?_ hcol
    intro x hx
    rcases hx with rfl|rfl|hx
    · exact Or.inr (hp_mem r)
    · exact Or.inl rfl
    · rcases hx with rfl
      exact Or.inr (hp_mem s)
  rw [he0,heq,he1] at hc
  exact no_same_label_rich_triple r s hrs U V U' V' M N
    (hdet hU) (hdet hV) (hdet hU') (hdet hV') (hdet hM) (hdet hN) hne hc

end
end Holant.Certificates.RainbowOrbit
