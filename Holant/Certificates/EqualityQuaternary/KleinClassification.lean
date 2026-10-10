import Holant.Certificates.EqualityQuaternary.KleinFiniteCoverage
import Holant.Certificates.EqualityQuaternary.KleinPlaneTensor

/-! Complete original-coefficient safe-locus coverage for both Klein rows.
The finite certificates are connected to the literal physical card sums;
the zero coefficients of every partial injection are retained.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
open Holant Holant.Marked Holant.Tractable
open Holant.Marked.SupportAtlas
open Linear
set_option backward.isDefEq.respectTransparency false

theorem safe_semantics (kind : Kind) (p : Fin 24) (c : Fin 4 → Scalar)
    (h : AllStandardCards kind (normalized kind (permutation p) c)) : (problem kind p).Safe c := by
  intro ctx
  obtain ⟨axis,ha⟩ := onLine_coefficients (h (crossPermutation (firstLabel ctx)) (secondLabel ctx))
  refine ⟨axis,?_⟩
  intro out hout
  change evaluate (cards kind p ctx out) c=0
  have he : cards kind p ctx out=cardFormula kind p ctx out := funext (cards_correct kind p ctx out)
  rw [he,cardFormula_semantics]
  exact ha out hout

def InCoefficientPlane (kind : Kind) (p : Fin 24) (c : Fin 4 → Scalar)
    (j : Fin (planeCount kind)) : Prop :=
  ∀ col,coefficientVector p c col=
    ∑ r : Fin 4,embed (planes kind j r col)*coefficientVector p c (pivots kind j r)

theorem accepted_plane (kind : Kind) (p : Fin 24) (c : Fin 4 → Scalar)
    (h : (problem kind p).Accepted c) : ∃ j,InCoefficientPlane kind p c j := by
  obtain ⟨j,hj⟩ := h
  refine ⟨j,?_⟩
  intro col
  change Satisfies (targets kind p j) c at hj
  rw [targets_correct] at hj
  have hh := hj _ (List.mem_ofFn.mpr ⟨col,rfl⟩)
  rw [evaluate_target] at hh
  exact sub_eq_zero.mp hh

/-- The safe physical source supplies all hypotheses of the exact finite
cover. No partial-injection support or surviving plane is assumed. -/
theorem source_klein_plane {F : SignatureFamily Scalar} {kind : Kind}
    (reps : Representatives F kind) (q : Signature Scalar 4) (h : PhysicalDeck reps q) :
    ∃ (p : Fin 24) (c : Fin 4 → Scalar) (j : Fin (planeCount kind)),
      q=normalized kind (permutation p) c ∧ InCoefficientPlane kind p c j := by
  have hs := standardCards_of_physical reps q h
  obtain ⟨e,c,hq⟩ := source_permutation_form (dualCards_of_standard hs)
  obtain ⟨p,hp⟩ := permutations_complete e
  rw [←hp] at hq
  have hsafe := safe_semantics kind p c (hq ▸ hs)
  have haccepted := all_covers kind p c (by intro r hr; cases hr) hsafe
  obtain ⟨j,hj⟩ := accepted_plane kind p c haccepted
  exact ⟨p,c,j,hq,hj⟩

@[simp] theorem firstLabel_cell (a b : Fin 4) : firstLabel (cell a b)=a := by
  fin_cases a <;> fin_cases b <;> rfl
@[simp] theorem secondLabel_cell (a b : Fin 4) : secondLabel (cell a b)=b := by
  fin_cases a <;> fin_cases b <;> rfl

theorem normalized_vector (kind : Kind) (p : Fin 24) (c : Fin 4 → Scalar) (w : Fin 4 → Bool) :
    normalized kind (permutation p) c w=
      ∑ col : Fin 16,coefficientVector p c col*basisTensor kind (firstLabel col) (secondLabel col) w := by
  rw [sum_cells]
  simp [normalized,coefficientVector,permutation_apply]

theorem plane_expansion (kind : Kind) (p : Fin 24) (c : Fin 4 → Scalar)
    (j : Fin (planeCount kind)) (h : InCoefficientPlane kind p c j) (w : Fin 4 → Bool) :
    normalized kind (permutation p) c w=
      ∑ r : Fin 4,coefficientVector p c (pivots kind j r)*planeTensor kind j r w := by
  rw [normalized_vector]
  conv_lhs =>
    arg 2
    intro col
    rw [h col,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [planeTensor,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro col _
  ring

end Holant.Certificates.EqualityQuaternary.Klein.Finite
