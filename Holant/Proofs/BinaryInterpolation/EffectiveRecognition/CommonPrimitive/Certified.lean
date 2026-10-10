import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonPrimitive.CertificateBox
import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.Completeness


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonPrimitive
open Holant.Tractable
open Holant.LocalDrafts.EffectiveAlgebraic
open ComplexIsolation PowerArithmetic

/-- The isolation owner's neighborhood conclusion controls the actual rational
radius. Two interior points half a radius either side have separation r. -/
theorem radius_lt_of_rectangle_small (t : Certificate) {θ : ℂ} {δ : ℝ}
    (hr : (0 : ℝ) < t.radius)
    (hs : ∀ z : ℂ, t.rectangle.Contains z → ‖z - θ‖ < δ) :
    (t.radius : ℝ) < 2 * δ := by
  let u : ℂ := value t.center + (((t.radius : ℝ) / 2 : ℝ) : ℂ)
  let v : ℂ := value t.center - (((t.radius : ℝ) / 2 : ℝ) : ℂ)
  have hu : ‖u - value t.center‖ = (t.radius : ℝ) / 2 := by
    rw [show u - value t.center = (((t.radius : ℝ) / 2 : ℝ) : ℂ) by dsimp [u]; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  have hv : ‖v - value t.center‖ = (t.radius : ℝ) / 2 := by
    rw [show v - value t.center = -(((t.radius : ℝ) / 2 : ℝ) : ℂ) by dsimp [v]; ring]
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  have huc : t.rectangle.Contains u := t.contains_of_norm_lt (by rw [hu]; linarith)
  have hvc : t.rectangle.Contains v := t.contains_of_norm_lt (by rw [hv]; linarith)
  have hd : ‖u - v‖ = (t.radius : ℝ) := by
    rw [show u - v = ((t.radius : ℝ) : ℂ) by dsimp [u, v]; push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have ht : ‖u - v‖ ≤ ‖u - θ‖ + ‖v - θ‖ := by
    have h := norm_add_le (u - θ) (θ - v)
    simpa only [sub_add_sub_cancel, norm_sub_rev θ v] using h
  have h₁ := hs u huc
  have h₂ := hs v hvc
  rw [hd] at ht
  linarith

/-- Source completeness for the literal coefficient descriptors and an actual
algebraic solution. The returned primitive polynomial is the exact rational
code computed from the returned relation coefficients. Both existing checks
really return true, and both pieces of finite data have concrete enumeration
indices. This does not define or claim termination of a new search algorithm. -/
theorem exists_certified_raw {m k : ℕ} (w : Fin m → AlgebraicComplex)
    (target : Fin m → RootCode) (ht : ∀ i, (target i).Represents (w i : ℂ))
    (S : EncodedSystem.System m (5 + k)) (y : Fin (5 + k) → AlgebraicComplex)
    (hy : ∀ f ∈ S, MvPolynomial.aeval (fun j => (y j : ℂ))
      (EncodedSystem.polynomial (fun i => (w i : ℂ)) f) = 0)
    (hg : y (Fin.castAdd k 4) *
      (y (Fin.castAdd k 0) * y (Fin.castAdd k 3) -
        y (Fin.castAdd k 1) * y (Fin.castAdd k 2)) = 1) :
    ∃ (θ : ℂ) (r : MatrixWitness.RawCandidate m k) (t : Certificate)
      (rawIndex certificateIndex : ℕ),
      MatrixWitness.rawAt m k rawIndex = some r ∧
      tupleAt 1 certificateIndex = some (fun _ : Fin 1 => t) ∧
      r ∈ MatrixWitness.rawThrough m k rawIndex ∧
      (fun _ : Fin 1 => t) ∈ tuplesThrough 1 certificateIndex ∧
      r.2.2.1 = RationalBox.ofRectangle t.rectangle ∧
      PowerArithmetic.polynomial r.2.1 = minpoly ℚ θ ∧
      t.check (relationCode r.2.1) = true ∧
      (t.rootCode (relationCode r.2.1)).Represents θ ∧
      MatrixWitness.precheckRaw target S r = true ∧
      (∀ i, decode θ (CommonFieldCheck.familyCoordinates r.2.1 r.2.2.2.1 i) = (w i : ℂ)) ∧
      (∀ j, decode θ (r.2.2.2.2 j) = (y j : ℂ)) := by
  obtain ⟨θ, d, c, e, x, p, ε, hpcode, hp, hmin, hroot, hsimple, hε, he, hx, hb⟩ :=
    candidate_certificate_radius w target ht S y hy hg
  subst p
  obtain ⟨t, hcheck, hrep, hsmall⟩ := exists_certificate (relationCode c) θ hroot hsimple
    (show 0 < ε / 2 by linarith)
  have hrad : (t.radius : ℝ) < ε := by
    have hpos := ((Certificate.check_iff (relationCode c) t).mp hcheck).1
    have h := radius_lt_of_rectangle_small t hpos hsmall
    linarith
  let r : MatrixWitness.RawCandidate m k := ⟨d, c, RationalBox.ofRectangle t.rectangle, e, x⟩
  have hpre := hb t hrep.2.1 hrad
  have hr := relation_of_root θ c (by rw [hmin]; exact minpoly.aeval ℚ θ)
  refine ⟨θ, r, t, Encodable.encode (fun _ : Fin 1 => r), Encodable.encode (fun _ : Fin 1 => t),
    MatrixWitness.rawAt_complete r, tupleAt_encode _, MatrixWitness.rawThrough_complete r,
    tuplesThrough_complete _, rfl, hmin, hcheck, hrep, hpre, ?_, hx⟩
  intro i
  change decode θ (CommonFieldCheck.reduce c (e i)) = (w i : ℂ)
  rw [CommonFieldCheck.decode_reduce θ c hr, he]

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonPrimitive
