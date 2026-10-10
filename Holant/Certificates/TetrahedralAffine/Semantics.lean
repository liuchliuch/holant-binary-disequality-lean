import Holant.Certificates.TetrahedralAffine.Data

/-! Exact coefficient embedding into the existing complex Frobenius formula.
All coercions are structural field-homomorphism identities. -/
namespace Holant.Certificates.TetrahedralAffine
open Holant Holant.Tractable Holant.Certificates.MatchingProductBridge
noncomputable section

theorem coe_dual (k : Fin 4) (a b : Bool) :
    (dual k a b : ℂ) = TetrahedralOrientation.dual k a b := by
  fin_cases k <;> cases a <;> cases b <;> rfl

theorem coe_axisR (k : Fin 4) (x : Fin 4 → Bool) :
    (axisR k x : ℂ) = TetrahedralOrientation.axisR k x := by
  rcases TetrahedralOrientation.fourBits.symm.surjective x with ⟨⟨a,b,c,d⟩,rfl⟩
  fin_cases k <;> cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem coe_cardImages (s : Orientation) (k : Fin 4) (x : Fin 4 → Bool) :
    (cardImages s k x : ℂ) =
      ![(1/2 : ℂ) • C,TetrahedralOrientation.axisR (sigma s 0),
        TetrahedralOrientation.axisR (sigma s 1),TetrahedralOrientation.axisR (sigma s 2)] k x := by
  fin_cases k
  · change ((1/2 : AlgebraicComplex) * (Q 2 (x 0) (x 3)*Q 2 (x 1) (x 2)) : ℂ) =
      (1/2 : ℂ)*(Q2 (x 0) (x 3)*Q2 (x 1) (x 2))
    rw [coe_Q,coe_Q]
    rfl
  · exact coe_axisR _ _
  · exact coe_axisR _ _
  · exact coe_axisR _ _

theorem coe_ancestor (s : Orientation) (x : Fin 6 → Bool) :
    (ancestor s x : ℂ) = complexAncestor s x := by
  change (algebraicClosure ℚ ℂ).val (∑ k : Fin 4, dual k (x 0) (x 1)*
    cardImages s k (fun j => x j.succ.succ)) = _
  rw [map_sum]
  unfold complexAncestor
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_mul]
  exact congrArg₂ (· * ·) (coe_dual k (x 0) (x 1)) (coe_cardImages s k _)

end
end Holant.Certificates.TetrahedralAffine
