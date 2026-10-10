import Holant.Marked.SupportAtlas.Source

/-!
The monomial row of A.7/A.8 in the original physical coordinates.  The
fixed actual binary representatives, their nonzero scalars, native X edges,
all ordered port permutations, and zero cards remain explicit.  The root
pencil and support atlas are proved dependencies, not hypotheses.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary
open Holant Holant.Marked Holant.Tractable
open Holant.Marked.SupportAtlas
set_option backward.isDefEq.respectTransparency false

def standard (p : Bool) (t : Scalar) : Mat := if p then S t else R t

/-- One fixed actual representative of each projective group element. -/
structure MonomialRepresentatives (F : SignatureFamily Scalar) (m : ℕ) where
  matrix : Bool → Phase m → Mat
  multiplier : Bool → Phase m → Scalar
  multiplier_ne_zero : ∀ p t, multiplier p t ≠ 0
  actual : ∀ p t, Gadget.Realizes F .disequality (kernelSignature (matrix p t))
  normal_form : ∀ p t, matrix p t = scale (multiplier p t) (standard p t.val)

/-- Card membership uses the original representatives, not normalized lines. -/
def ActualMonomialLine {F : SignatureFamily Scalar} {m : ℕ}
    (reps : MonomialRepresentatives F m) (B : Mat) : Prop :=
  ∃ p t c, c ≠ 0 ∧ B = scale c (reps.matrix p t)

/-- The 24 port orders include all six pairs and both orders on both boundaries. -/
def MonomialPhysicalDeck {F : SignatureFamily Scalar} {m : ℕ}
    (reps : MonomialRepresentatives F m) (q : Signature Scalar 4) : Prop :=
  ∀ (e : Equiv.Perm (Fin 4)) (p : Bool) (t : Phase m),
    physicalCard q e (reps.matrix p t) = 0 ∨
      ActualMonomialLine reps (physicalCard q e (reps.matrix p t))

theorem standard_mem {m : ℕ} (p : Bool) (t : Phase m) : standard p t.val ∈ groupM m := by
  refine ⟨t.val,t.property,?_⟩
  cases p
  · exact Or.inl ⟨1,one_ne_zero,by funext a b; simp [standard,scale]⟩
  · exact Or.inr ⟨1,one_ne_zero,by funext a b; simp [standard,scale]⟩

theorem actualMonomialLine_mem {F : SignatureFamily Scalar} {m : ℕ} (hm : 0 < m)
    (reps : MonomialRepresentatives F m) {B : Mat} (h : ActualMonomialLine reps B) :
    B ∈ groupM m := by
  obtain ⟨p,t,c,hc,rfl⟩ := h
  rw [reps.normal_form]
  exact (groupM_is_group hm).scale_mem _
    ((groupM_is_group hm).scale_mem _ (standard_mem p t) _ (reps.multiplier_ne_zero p t)) _ hc

/-- The two native edges invert the phase and contribute its actual factor t. -/
theorem standard_native_sandwich (p : Bool) (t : Scalar) (ht : t ≠ 0) :
    Kernel.mul (Kernel.mul Signature.disequality (standard p t)) Signature.disequality =
      scale t (standard p t⁻¹) := by
  funext a b
  cases p <;> cases a <;> cases b <;>
    simp [standard,S,R,diagonalKernel,Kernel.mul_apply,Signature.disequality,scale,ht]

/-- Exact equality before any cancellation of the recorded scalar. -/
theorem physical_card_normalization {F : SignatureFamily Scalar} {m : ℕ} (hm : 0 < m)
    (reps : MonomialRepresentatives F m) (q : Signature Scalar 4)
    (e : Equiv.Perm (Fin 4)) (p : Bool) (t : Phase m) :
    complexMatrix (physicalCard q e (reps.matrix p t)) =
      ((reps.multiplier p t * t.val : Scalar) : ℂ) •
        weightedCard 1 (complexTensor q) e p ((t.val : ℂ)⁻¹) := by
  rw [physicalCard,reps.normal_form,scale_mul_right,scale_mul_left,
    standard_native_sandwich p t.val (t.property.ne_zero hm),contract0_scale,
    contract0_scale,complexMatrix_scale,complexMatrix_scale,smul_smul]
  have h := complex_weighted_card q e (1 : Scalar) t.val⁻¹ p
  have he : Kernel.mul (diagonalKernel 1 (1 : Scalar)) (standard p t.val⁻¹) =
      standard p t.val⁻¹ := by
    have hI : diagonalKernel 1 (1 : Scalar) = Signature.equality := by
      funext a b; cases a <;> cases b <;> rfl
    rw [hI,Kernel.equality_mul]
  change complexMatrix (contract0 (reorder q e)
    (Kernel.mul (diagonalKernel 1 1) (standard p t.val⁻¹))) = _ at h
  rw [he] at h
  rw [h]
  rfl

theorem monomial_safeDeck {F : SignatureFamily Scalar} {m : ℕ} (hm : 3 ≤ m)
    (reps : MonomialRepresentatives F m) (q : Signature Scalar 4)
    (hdeck : MonomialPhysicalDeck reps q) : SafeDeck m 1 (complexTensor q) := by
  intro e p t ht
  let z : Phase m := ⟨Projective.CyclicPhasePencil.algebraicRoot (by omega) t⁻¹
      (by rw [inv_pow,ht,inv_one]),
    Projective.CyclicPhasePencil.algebraicRoot_pow (by omega) t⁻¹
      (by rw [inv_pow,ht,inv_one])⟩
  let c : ℂ := (reps.multiplier p z * z.val : Scalar)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast mul_ne_zero (reps.multiplier_ne_zero p z) (z.property.ne_zero (by omega))
  have hnormal : complexMatrix (physicalCard q e (reps.matrix p z)) =
      c • weightedCard 1 (complexTensor q) e p t := by
    simpa only [c,z,Projective.CyclicPhasePencil.algebraicRoot,inv_inv] using
      physical_card_normalization (by omega) reps q e p z
  have hs : complexMatrix (physicalCard q e (reps.matrix p z)) = 0 ∨
      Projective.IsRootMonomial m (complexMatrix (physicalCard q e (reps.matrix p z))) := by
    rcases hdeck e p z with hz | hs
    · left; rw [hz]; rfl
    · exact Or.inr (groupM_complex_root (by omega) _ (actualMonomialLine_mem (by omega) reps hs))
  rw [hnormal] at hs
  have hI : diagonalC (1 : ℂ) = Signature.equality := by
    funext a b; cases a <;> cases b <;> rfl
  unfold SafeWeighted
  rw [hI,Kernel.mul_equality]
  rcases hs with hz | hs
  · exact Or.inl ((smul_eq_zero.mp hz).resolve_left hc)
  · exact Or.inr ((rootMonomial_smul_iff m c hc _).mp hs)

/-- Source A.8(ii), the full support assertion in original coordinates. -/
theorem source_monomial_support {F : SignatureFamily Scalar} {m : ℕ} (hm : 3 ≤ m)
    (reps : MonomialRepresentatives F m) (q : Signature Scalar 4) (hq : q ≠ 0)
    (hdeck : MonomialPhysicalDeck reps q) :
    ∃ (p : Bool) (selected : PairIndex → Bool), (∃ i, selected i = true) ∧
      ∀ w, q w ≠ 0 ↔ ∃ i, selected i = true ∧
        (w = representative p i ∨ w = complement (representative p i)) := by
  have hn : complexTensor q ≠ 0 := by
    intro hz; apply hq; funext w
    have h := congrFun hz w
    simpa [complexTensor] using h
  simpa only [complexTensor,ne_eq,AlgebraicComplex.coe_eq_zero] using
    support_atlas_of_samples hm 1 one_ne_zero (by simp) (complexTensor q) hn
      (monomial_safeDeck hm reps q hdeck)

end Holant.Certificates.EqualityQuaternary
