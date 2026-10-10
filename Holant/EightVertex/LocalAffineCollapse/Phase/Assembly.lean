import Holant.EightVertex.LocalAffineCollapse.Phase.Geometry

/-! The genuine affine output is constructed from the supported local twist.
The hypotheses contain no support description or finite classification premise. -/
namespace Holant.EightVertex.LocalAffineCollapse.Phase
open Holant.Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

def addCoordinate {n : ℕ} (Q : QuadraticPhase n) (j : Fin n) (q : ZMod 4) :
    QuadraticPhase n :=
  ⟨Q.constant, fun i => Q.linear i + if i = j then q else 0, Q.mixed, Q.even_mixed⟩

theorem addCoordinate_eval {n : ℕ} (Q : QuadraticPhase n) (j : Fin n) (q : ZMod 4)
    (x : Fin n → Bool) :
    (addCoordinate Q j q).eval x = Q.eval x + q * bitValue (ZMod 4) (x j) := by
  simp only [QuadraticPhase.eval, addCoordinate, add_mul, Finset.sum_add_distrib,
    ite_mul, zero_mul]
  simp
  ring

theorem affine_coordinate_phase {n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : Affine f) (j : Fin n) (q : ZMod 4) :
    Affine (fun x => fourthRootPhase (q * bitValue (ZMod 4) (x j)) * f x) := by
  rcases hf with rfl | ⟨a, ha, S, Q, rfl⟩
  · left
    funext x
    simp
  · convert affine_formula a S (addCoordinate Q j q) using 1
    funext x
    by_cases hx : S.Holds x
    · simp [affineFormula, hx, addCoordinate_eval, fourthRootPhase_add]
      ring
    · simp [affineFormula, hx]

theorem plane_weight_phase (rho : AlgebraicComplex) (q : ZMod 4)
    (hq : fourthRootPhase q = rho ^ 2) (b : Fin 3) (x : W) (hx : OnPlane b x) :
    rho ^ Holant.weight x = fourthRootPhase (q * bitValue (ZMod 4) (x 0)) *
      fourthRootPhase (q * bitValue (ZMod 4) (x (otherPort b))) := by
  rw [plane_weight b x hx, pow_mul, pow_add, ← hq]
  cases h0 : x 0 <;> cases h1 : x (otherPort b) <;> simp [bitValue]

theorem affine_weight_phase_on_plane (N : Signature AlgebraicComplex 4)
    (rho : AlgebraicComplex) (hr : rho ^ 8 = 1) (hN : Affine N) (b : Fin 3)
    (hb : ∀ x, N x ≠ 0 → OnPlane b x) :
    Affine (fun x => rho ^ Holant.weight x * N x) := by
  have hr2 : (rho ^ 2) ^ 4 = 1 := by simpa only [← pow_mul] using hr
  obtain ⟨q, hq⟩ := fourthRootPhase_surjective_of_pow_four hr2
  convert affine_coordinate_phase (affine_coordinate_phase hN 0 q) (otherPort b) q using 1
  funext x
  by_cases hx : N x = 0
  · simp [hx]
  · rw [plane_weight_phase rho q hq b x (hb x hx)]
    ring

/-- Core coefficient form of the source local-affine collapse. Complement
symmetry and the actual selected twists suffice, including the zero signature. -/
theorem affine_of_localAffine_complement (N : Signature AlgebraicComplex 4)
    (rho : AlgebraicComplex) (hN : LocalAffine N) (hr0 : rho ≠ 0) (hr : rho ^ 8 = 1)
    (hc : ∀ x, rho ^ Holant.weight (complementWord x) * N (complementWord x) =
      rho ^ Holant.weight x * N x) :
    Affine (fun x => rho ^ Holant.weight x * N x) := by
  classical
  obtain ⟨b, hb⟩ := support_contained_plane N
    (support_even N rho hr0 hr hc hN) (support_orthogonal N rho hr0 hr hc hN)
  by_cases h0 : N zeroWord ≠ 0
  · have hNa : Affine N := by
      have hh := hN zeroWord h0
      change Affine (localTwist (fun _ => false) N) at hh
      rw [localTwist_false] at hh
      exact hh
    exact affine_weight_phase_on_plane N rho hr hNa b hb
  · have h0 : N zeroWord = 0 := not_ne_iff.mp h0
    by_cases hNz : N = 0
    · left
      funext x
      simp [hNz]
    · have hex : ∃ s, N s ≠ 0 := by
        by_contra hn
        push Not at hn
        exact hNz (funext hn)
      obtain ⟨s, hs⟩ := hex
      have h1 : N oneWord = 0 := by
        by_contra hn
        have hh := support_complement N rho hr0 hc oneWord hn
        rw [complement_one, h0] at hh
        exact hh rfl
      have hs0 : s ≠ zeroWord := by intro he; exact hs (he ▸ h0)
      have hs1 : s ≠ oneWord := by intro he; exact hs (he ▸ h1)
      have htw := hN s hs
      rcases htw with hz | ⟨a, ha, S, Q, he⟩
      · exact False.elim (((twist_nonzero_iff s N s).mpr hs) (congrFun hz s))
      · have hS (x : W) : S.Holds x ↔ N x ≠ 0 := by
          rw [← twist_nonzero_iff s N x, he]
          by_cases hx : S.Holds x <;>
            simp [affineFormula, hx, ha, fourthRootPhase_ne_zero]
        convert (affine_indicator S).scale (rho ^ Holant.weight s * N s) using 1
        funext x
        by_cases hx : N x = 0
        · have hxS : ¬S.Holds x := by rw [hS]; simp [hx]
          simp [hx, hxS]
        · have hxS := (hS x).mpr hx
          have hx0 : x ≠ zeroWord := by intro he; exact hx (he ▸ h0)
          have hx1 : x ≠ oneWord := by intro he; exact hx (he ▸ h1)
          rcases plane_central_pair b s x (hb s hs) (hb x hx) hs0 hs1 hx0 hx1 with hxs | hxs
          · subst x
            simp [hxS]
          · subst x
            simp only [ite_eq_left hxS, mul_one]
            exact hc s

end
end Holant.EightVertex.LocalAffineCollapse.Phase
