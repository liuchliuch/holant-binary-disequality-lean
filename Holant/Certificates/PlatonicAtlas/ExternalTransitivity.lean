import Holant.Certificates.RainbowOrbit.GammaOrbit
import Holant.Certificates.RainbowOrbit.ExternalDeckIntegration

/-! Actual external-group deck transitivity. This uses only literal current
external representatives, their inverses, and original port permutations. -/
namespace Holant.Certificates.PlatonicAtlas
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def matchingNormalizer (r : Fin 3) (U V : BinaryMatrix) : Legs :=
  if r=0 then ![U⁻¹,1,V⁻¹,1] else ![U⁻¹,V⁻¹,1,1]

theorem matchingNormalizer_exact (r : Fin 3) (U V : BinaryMatrix)
    (hU : U.det≠0) (hV : V.det≠0) :
    act (matchingNormalizer r U V) (matchingTensor r U V)=
      matchingTensor r (1 : BinaryMatrix) (1 : BinaryMatrix) := by
  fin_cases r
  · change act (matchingNormalizer 0 U V) (P0 U V)=P0 (1 : BinaryMatrix) (1 : BinaryMatrix)
    rw [act_P0]
    simp [matchingNormalizer,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hU),
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hV),matchingTensor]
  · change act (matchingNormalizer 1 U V) (P1 U V)=P1 (1 : BinaryMatrix) (1 : BinaryMatrix)
    rw [act_P1]
    simp [matchingNormalizer,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hU),
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hV),matchingTensor]
  · change act (matchingNormalizer 2 U V) (P2 U V)=P2 (1 : BinaryMatrix) (1 : BinaryMatrix)
    rw [act_P2]
    simp [matchingNormalizer,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hU),
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hV),matchingTensor]

def normalMatchingPoint (r : Fin 3) : Point :=
  Projectivization.mk ℂ (matchingTensor r (1 : BinaryMatrix) (1 : BinaryMatrix))
    (matching_nonzero r _ _ (by simp) (by simp))

theorem external_normalization_word (r : Fin 3) (i j : Fin 12) :
    ∃k : Fin 4→Fin 12,runPointWord External.representative External.representative_det_ne_zero
      (fourWord k) (External.deckPoint (r,i,j))=normalMatchingPoint r := by
  let L := matchingNormalizer r (External.representative i) (External.representative j)
  have hL (a : Fin 4) : External.Direction (L a) := by
    fin_cases r <;> fin_cases a <;> simp only [L,matchingNormalizer,↓reduceIte,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Matrix.cons_val_fin_one]
    all_goals first
      | exact (External.Direction.representative _).inverse
      | exact External.direction_one
  choose k c hc he using hL
  have hn : (∏a,c a)≠0 := Finset.prod_ne_zero_iff.mpr (fun a _ => hc a)
  have hlegs : L=(fun a => c a • External.representative (k a)) := funext he
  have hh := matchingNormalizer_exact r (External.representative i) (External.representative j)
    (External.representative_det_ne_zero i) (External.representative_det_ne_zero j)
  change act L _=_ at hh
  rw [hlegs,act_rescale_legs] at hh
  refine ⟨k,?_⟩
  rw [fourWord_action]
  apply (proportional_point_iff _ _ _ _).mp
  refine ⟨(∏a,c a)⁻¹,inv_ne_zero hn,?_⟩
  change act (fun a => External.representative (k a)) _=_
  rw [←hh,smul_smul,inv_mul_cancel₀ hn,one_smul]

def matchingLabelWord (r : Fin 3) : List (Operation 12) :=
  if r=0 then [] else if r=1 then [.swap 1] else [.swap 0,.swap 1]

theorem adjacent_normal_point (j r : Fin 3) :
    portPoint (adjacent j) (normalMatchingPoint r)=normalMatchingPoint (adjacentLabels j r) := by
  apply (proportional_point_iff _ _ _ _).mp
  refine ⟨1,one_ne_zero,?_⟩
  rw [one_smul]
  change Tensor.reindex (adjacent j) (matchingTensor r (1 : BinaryMatrix) (1 : BinaryMatrix))=_
  fin_cases j <;> fin_cases r <;> funext x <;>
    simp [adjacent,adjacentLabels,Tensor.reindex,matchingTensor,P0,P1,P2,
      Equiv.swap_apply_def,Matrix.one_apply,mul_comm,eq_comm]
  all_goals split_ifs <;> simp_all

theorem matchingLabelWord_exact (r : Fin 3) :
    runPointWord External.representative External.representative_det_ne_zero
      (matchingLabelWord r) (normalMatchingPoint r)=normalMatchingPoint 0 := by
  fin_cases r <;> simp [matchingLabelWord,runPointWord,operationPoint,adjacent_normal_point,
    adjacentLabels,Equiv.swap_apply_def]

theorem runPointWord_append {n : ℕ} (R : Fin n→BinaryMatrix) (hR : ∀i,(R i).det≠0)
    (v w : List (Operation n)) (p : Point) :
    runPointWord R hR (v++w) p=runPointWord R hR w (runPointWord R hR v p) := by
  induction v generalizing p with
  | nil => rfl
  | cons a v ih => exact ih _

theorem external_deck_word_to_base (p : Point) (hp : p∈External.deck) :
    ∃w : List (Operation 12),runPointWord External.representative
      External.representative_det_ne_zero w p=normalMatchingPoint 0 := by
  obtain ⟨⟨r,i,j⟩,_,rfl⟩ := Finset.mem_map.mp hp
  obtain ⟨k,hk⟩ := external_normalization_word r i j
  refine ⟨fourWord k++matchingLabelWord r,?_⟩
  change runPointWord External.representative External.representative_det_ne_zero
    (fourWord k++matchingLabelWord r) (External.deckPoint (r,i,j))=_
  rw [runPointWord_append,hk,matchingLabelWord_exact]

/-- The generated group of actual external binary attachments and adjacent
port swaps is transitive on all 432 literal deck points. -/
theorem externalGamma_transitive (p q : {p : Point // p∈External.deck}) :
    ∃γ : Equiv.Perm {p : Point // p∈External.deck},γ∈externalGamma ∧ γ p=q := by
  obtain ⟨v,hv⟩ := external_deck_word_to_base p p.property
  obtain ⟨w,hw⟩ := external_deck_word_to_base q q.property
  let a := wordPermutation externalOperationPermutation v
  let b := wordPermutation externalOperationPermutation w
  have ha : a∈externalGamma := (gamma_mem_iff_word _ _).mpr ⟨v,rfl⟩
  have hb : b∈externalGamma := (gamma_mem_iff_word _ _).mpr ⟨w,rfl⟩
  have he : a p=b q := by
    apply Subtype.ext
    change (wordPermutation externalOperationPermutation v p).val=
      (wordPermutation externalOperationPermutation w q).val
    rw [restricted_word_apply External.deck External.representative External.representative_det_ne_zero
      externalOperationPermutation (fun _ _ => rfl),
      restricted_word_apply External.deck External.representative External.representative_det_ne_zero
      externalOperationPermutation (fun _ _ => rfl),hv,hw]
  refine ⟨b⁻¹*a,externalGamma.mul_mem (externalGamma.inv_mem hb) ha,?_⟩
  change b.symm (a p)=q
  rw [he,b.symm_apply_apply]

end
end Holant.Certificates.PlatonicAtlas
