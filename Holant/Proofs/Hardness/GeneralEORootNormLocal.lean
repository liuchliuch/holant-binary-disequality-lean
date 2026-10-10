import Holant.Projective.BinaryPencil
import Holant.Proofs.Hardness.GeneralEOBinaryARS
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionLoopTomography

/-! Unit-root contraction rigidity. A degree-two Hermitian polynomial
recovers the two norm sums and their cross term from at least three phases.
This gives a direct ARS route without expanding an arbitrary kth power. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEORootNormLocal
open Holant Polynomial
namespace F
export SelfDualPinObstruction (flip)
end F
namespace O
export GeneralEOPinnedDescentOperations (word)
end O
namespace T
export GeneralEOPhaseExtractionLoopTomography (merge selfDual_of_merges)
end T
namespace S
export GeneralEOPhaseExtractionSigns (flip_word)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def mass (z : ℂ) : ℂ := z * star z

theorem mass_eq_of_norm_eq {a b : ℂ} (h : ‖a‖ = ‖b‖) : mass a = mass b := by
  simp only [mass,Complex.star_def,Complex.mul_conj',h]

theorem norm_eq_of_mass_eq {a b : ℂ} (h : mass a = mass b) : ‖a‖ = ‖b‖ := by
  have hn := congrArg norm h
  simp only [mass,norm_mul,norm_star] at hn
  nlinarith [norm_nonneg a,norm_nonneg b]

theorem finite_unit_norm_coefficients (phases : Finset ℂ) (many : 3 ≤ phases.card)
    (unit : ∀ t ∈ phases, ‖t‖ = 1) (a b c d : ℂ)
    (samples : ∀ t ∈ phases, ‖a + t*b‖ = ‖t*c + d‖) :
    mass a + mass b = mass c + mass d ∧ b * star a = c * star d := by
  let q : ℂ[X] := C (a*star b-d*star c) +
    C (mass a+mass b-mass c-mass d)*X + C (b*star a-c*star d)*X^2
  have hdeg : q.natDegree ≤ 2 := by
    apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · simp only [natDegree_C]
        omega
      · simpa using (natDegree_C_mul_X_pow_le (mass a+mass b-mass c-mass d) 1).trans
          (by decide : 1 ≤ 2)
    · exact natDegree_C_mul_X_pow_le _ 2
  have hq : q = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' q phases
    · intro t ht
      have hn := unit t ht
      have hu : t * star t = 1 := by
        simp only [Complex.star_def,Complex.mul_conj',hn,Complex.ofReal_one,one_pow]
      have he := mass_eq_of_norm_eq (samples t ht)
      simp only [mass,star_add,star_mul] at he
      simp only [q,eval_add,eval_mul,eval_C,eval_X,eval_pow,mass]
      linear_combination t*he - (a*star b+t*b*star b-t*c*star c-d*star c)*hu
    · omega
  have h1 := congrArg (fun p : ℂ[X] => p.coeff 1) hq
  have h2 := congrArg (fun p : ℂ[X] => p.coeff 2) hq
  norm_num only [q,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C,coeff_zero,
    ite_false,ite_true,zero_add,add_zero] at h1 h2
  exact ⟨by linear_combination h1,sub_eq_zero.mp h2⟩

theorem three_unit_norm_coefficients (t : Fin 3 → ℂ) (distinct : Function.Injective t)
    (unit : ∀ i, ‖t i‖ = 1) (a b c d : ℂ)
    (samples : ∀ i, ‖a+t i*b‖ = ‖t i*c+d‖) :
    mass a + mass b = mass c + mass d ∧ b*star a = c*star d := by
  classical
  apply finite_unit_norm_coefficients (Finset.univ.image t)
    (by simp [Finset.card_image_of_injective _ distinct])
    (fun z hz => by obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz; exact unit i) a b c d
  intro z hz
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
  exact samples i

variable {n : ℕ}

def NormSymmetry (f : Signature ℂ n) : Prop := ∀ x, mass (f (F.flip x)) = mass (f x)

def Related (f : Signature ℂ n) (x y : Fin n → Bool) : Prop :=
  f (F.flip x) * star (f (F.flip y)) = star (f x) * f y

def rootMerge (f : Signature ℂ (n+2)) (e : Equiv.Perm (Fin (n+2))) (t : ℂ) :
    Signature ℂ n := fun x => f (O.word false true x ∘ e) + t*f (O.word true false x ∘ e)

theorem ars_norm (f : Signature ℂ n) (h : GeneralEOARSBoundary.ARSUpToScale f) :
    NormSymmetry f := fun x => mass_eq_of_norm_eq (GeneralEOARSBoundary.opposite_norm f h x)

theorem ars_related (f : Signature ℂ n) (h : GeneralEOARSBoundary.ARSUpToScale f)
    (x y : Fin n → Bool) : Related f x y := by
  obtain ⟨c,_,g,hg,rfl⟩ := h
  change (c*g (F.flip x))*star (c*g (F.flip y))=star (c*g x)*(c*g y)
  have hx : g (F.flip x) = star (g x) := hg x
  have hy : g (F.flip y) = star (g y) := hg y
  rw [hx,hy]
  simp only [star_mul,star_star]
  ring

theorem flip_zero (f : Signature ℂ n) (h : NormSymmetry f) (x : Fin n → Bool)
    (hx : f x = 0) : f (F.flip x) = 0 := by
  have hn := norm_eq_of_mass_eq (h x)
  apply norm_eq_zero.mp
  simpa only [hx,norm_zero] using hn

theorem related_through (f : Signature ℂ n) (hf : NormSymmetry f)
    (x y z : Fin n → Bool) (hz : f z ≠ 0)
    (hxz : Related f x z) (hzy : Related f z y) : Related f x y := by
  apply mul_right_cancel₀ (mul_ne_zero hz (star_ne_zero.mpr hz))
  calc
    _ = (f (F.flip x)*star (f (F.flip z)))*(f (F.flip z)*star (f (F.flip y))) := by
      change _ * mass (f z) = _
      rw [← hf z]
      unfold mass
      ring
    _ = (star (f x)*f z)*(star (f z)*f y) := by rw [hxz,hzy]
    _ = _ := by ring

/-- One normalized conjugate-reversal scalar works on the complete tensor. -/
theorem ars_of_related (f : Signature ℂ n) (hf : NormSymmetry f)
    (related : ∀ x y, Related f x y) : GeneralEOARSBoundary.ARSUpToScale f := by
  classical
  by_cases hz : ∀ x, f x = 0
  · refine ⟨1,one_ne_zero,fun _ => 0,?_,?_⟩
    · intro x
      simp
    · funext x
      simp [hz]
  push Not at hz
  obtain ⟨w,hw⟩ := hz
  have hflip : f (F.flip w) ≠ 0 := by
    intro h
    have hh := norm_eq_of_mass_eq (hf w)
    rw [h,norm_zero] at hh
    exact hw (norm_eq_zero.mp hh.symm)
  obtain ⟨c,hc,hs⟩ := GeneralEOBinaryARS.exists_scale (f w) (f (F.flip w))
    (norm_eq_of_mass_eq (hf w)).symm
  have hsc := congrArg star hs
  rw [star_div₀,star_star] at hsc
  have hscale := (div_eq_div_iff (star_ne_zero.mpr hc) hc).mp hsc
  refine ⟨c,hc,fun x => f x/c,?_,?_⟩
  · intro x
    change f (F.flip x)/c = star (f x/c)
    rw [star_div₀]
    apply (div_eq_div_iff hc (star_ne_zero.mpr hc)).mpr
    apply mul_right_cancel₀ (star_ne_zero.mpr hflip)
    calc
      _ = star c * (f (F.flip x)*star (f (F.flip w))) := by ring
      _ = star c * (star (f x)*f w) := by rw [related x w]
      _ = star (f x) * (f w*star c) := by ring
      _ = star (f x) * (star (f (F.flip w))*c) := by rw [← hscale]
      _ = _ := by ring
  · funext x
    change f x = c*(f x/c)
    field_simp

theorem norm_of_root_children (t : Fin 3 → ℂ) (distinct : Function.Injective t)
    (unit : ∀ i, ‖t i‖ = 1) (f : Signature ℂ (n+3))
    (hE : Signature.CentralSupport f)
    (children : ∀ e i, NormSymmetry (rootMerge f e (t i))) : NormSymmetry f := by
  let g : Signature ℂ (n+3) := fun x => mass (f x)
  have hg : Signature.CentralSupport g := by
    intro x hx
    simp only [g,hE x hx,mass,zero_mul]
  apply T.selfDual_of_merges g hg
  intro e x
  have hp := (three_unit_norm_coefficients t distinct unit
    (f (O.word false true x ∘ e)) (f (O.word true false x ∘ e))
    (f (O.word true false (F.flip x) ∘ e)) (f (O.word false true (F.flip x) ∘ e))
    (fun i => by
      have h := (norm_eq_of_mass_eq (children e i x)).symm
      simpa only [rootMerge,add_comm] using h)).1
  change mass (f (O.word false true (F.flip x) ∘ e)) +
    mass (f (O.word true false (F.flip x) ∘ e)) =
      mass (f (O.word false true x ∘ e)) + mass (f (O.word true false x ∘ e))
  linear_combination -hp

theorem related_adjacent (t : Fin 3 → ℂ) (distinct : Function.Injective t)
    (unit : ∀ i, ‖t i‖ = 1) (f : Signature ℂ (n+2))
    (children : ∀ i, NormSymmetry (rootMerge f (Equiv.refl _) (t i)))
    (x : Fin n → Bool) : Related f (O.word false true x) (O.word true false x) := by
  have hp := (three_unit_norm_coefficients t distinct unit
    (f (O.word false true x)) (f (O.word true false x))
    (f (O.word true false (F.flip x))) (f (O.word false true (F.flip x)))
    (fun i => by
      have h := (norm_eq_of_mass_eq (children i x)).symm
      simpa only [rootMerge,Equiv.coe_refl,Function.comp_id,add_comm] using h)).2
  simp only [Related,S.flip_word,Bool.not_false,Bool.not_true]
  linear_combination -hp

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEORootNormLocal
