import Holant.Certificates.AffineEndpoint.WitnessSoundness

/-! The source's 21-entry diagonal invariant is complete for arbitrary actual
endpoint-nondegenerate even signatures, without any affine or finite-list
hypothesis. Original central-word order is retained. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.EightVertex.ProductAnchor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev InvariantIndex := {p : Fin 6 × Fin 6 // p.1≤p.2}
 theorem invariant_index_card : Fintype.card InvariantIndex=21 := by decide +kernel

 def diagonalInvariant (g : Signature AlgebraicComplex 4) (p : InvariantIndex) : AlgebraicComplex :=
  g (centralWord p.val.1)*g (centralWord p.val.2)/(g zeroWord*g oneWord)

 def DiagonalOrbit (g h : Signature AlgebraicComplex 4) : Prop :=
  ∃gamma t : AlgebraicComplex,gamma≠0 ∧ t≠0 ∧ h=gamma • diagonalAction t g

 theorem invariant_cross_products (g h : Signature AlgebraicComplex 4)
    (hg : EndpointEven g) (hh : EndpointEven h) (he : diagonalInvariant g=diagonalInvariant h)
    (i j : Fin 6) :
    g (centralWord i)*g (centralWord j)*(h zeroWord*h oneWord)=
      h (centralWord i)*h (centralWord j)*(g zeroWord*g oneWord) := by
  have H (i j : Fin 6) (hij : i≤j) := congrFun he ⟨(i,j),hij⟩
  have hg01 : g zeroWord*g oneWord≠0 := mul_ne_zero hg.1 hg.2.1
  have hh01 : h zeroWord*h oneWord≠0 := mul_ne_zero hh.1 hh.2.1
  by_cases hij : i≤j
  · exact (div_eq_div_iff hg01 hh01).mp (H i j hij)
  · have hji : j ≤ i := le_of_not_ge hij
    simpa only [mul_comm (g (centralWord j)) (g (centralWord i)),
      mul_comm (h (centralWord j)) (h (centralWord i))] using
      (div_eq_div_iff hg01 hh01).mp (H j i hji)

 theorem diagonal_form_of_general_cross_products (g h : Signature AlgebraicComplex 4)
    (hg : EndpointEven g) (hh : EndpointEven h)
    (p : Fin 6) (hgp : g (centralWord p)≠0) (hhp : h (centralWord p)≠0)
    (hcross : ∀i,g (centralWord i)*h (centralWord p)=g (centralWord p)*h (centralWord i))
    (hend : g oneWord*g zeroWord*h (centralWord p)^2=g (centralWord p)^2*h zeroWord*h oneWord) :
    ∃gamma t : AlgebraicComplex,gamma≠0 ∧ t≠0 ∧ g=gamma • diagonalAction t h := by
  let gamma := g zeroWord/h zeroWord
  let lam := g (centralWord p)/(gamma*h (centralWord p))
  have hg0 : g zeroWord≠0 := hg.1
  have hh0 : h zeroWord≠0 := hh.1
  have hc : gamma≠0 := div_ne_zero hg0 hh0
  have hl : lam≠0 := div_ne_zero hgp (mul_ne_zero hc hhp)
  obtain ⟨t,ht,he⟩ := diagonal_form_of_layers g h hg.2.2 hh.2.2 gamma lam hc hl
    (by exact (div_mul_cancel₀ _ hh0).symm)
    (by dsimp [lam,gamma]; field_simp [hg0,hh0,hhp]; linear_combination hend)
    (by intro i; dsimp [lam,gamma]; field_simp [hg0,hh0,hhp]; linear_combination hcross i)
  exact ⟨gamma,t,hc,ht,he⟩

 theorem equalInvariant_diagonal_form (g h : Signature AlgebraicComplex 4)
    (hg : EndpointEven g) (hh : EndpointEven h) (he : diagonalInvariant g=diagonalInvariant h) :
    ∃gamma t : AlgebraicComplex,gamma≠0 ∧ t≠0 ∧ g=gamma • diagonalAction t h := by
  have H := invariant_cross_products g h hg hh he
  by_cases hzero : ∀i,g (centralWord i)=0
  · have hhz : ∀i,h (centralWord i)=0 := by
      intro i
      have hz := H i i
      rw [hzero i,zero_mul,zero_mul] at hz
      have heq : h (centralWord i)*h (centralWord i)=0 :=
        (mul_eq_zero.mp hz.symm).resolve_right (mul_ne_zero hg.1 hg.2.1)
      exact (mul_self_eq_zero.mp heq)
    exact diagonal_form_of_endpoints g h hg hh hzero hhz
  · obtain ⟨p,hgp⟩ := not_forall.mp hzero
    have hdiag := H p p
    have hhp : h (centralWord p)≠0 := by
      intro hz
      rw [hz,zero_mul,zero_mul] at hdiag
      exact mul_ne_zero (mul_ne_zero hgp hgp) (mul_ne_zero hh.1 hh.2.1) hdiag
    have hcross (i : Fin 6) :
        g (centralWord i)*h (centralWord p)=g (centralWord p)*h (centralWord i) := by
      have hh0 : h zeroWord≠0 := hh.1
      have hh1 : h oneWord≠0 := hh.2.1
      apply mul_left_cancel₀ (mul_ne_zero hgp (mul_ne_zero hh0 hh1))
      linear_combination h (centralWord p)*(H i p) - h (centralWord i)*hdiag
    apply diagonal_form_of_general_cross_products g h hg hh p hgp hhp hcross
    linear_combination -hdiag

 theorem diagonalInvariant_action (g : Signature AlgebraicComplex 4) (gamma t : AlgebraicComplex)
    (hgamma : gamma≠0) (ht : t≠0) :
    diagonalInvariant (gamma • diagonalAction t g)=diagonalInvariant g := by
  funext p
  simp only [diagonalInvariant,Pi.smul_apply,smul_eq_mul,diagonalAction_apply,
    centralWord_weight,zeroWord_weight,oneWord_weight,pow_zero,one_mul]
  field_simp [hgamma,ht]

 theorem diagonalInvariant_complete (g h : Signature AlgebraicComplex 4)
    (hg : EndpointEven g) (hh : EndpointEven h) :
    diagonalInvariant g=diagonalInvariant h ↔ DiagonalOrbit g h := by
  constructor
  · intro he
    exact equalInvariant_diagonal_form h g hh hg he.symm
  · rintro ⟨gamma,t,hgamma,ht,rfl⟩
    exact (diagonalInvariant_action g gamma t hgamma ht).symm

end
end Holant.Certificates.AffineEndpoint
