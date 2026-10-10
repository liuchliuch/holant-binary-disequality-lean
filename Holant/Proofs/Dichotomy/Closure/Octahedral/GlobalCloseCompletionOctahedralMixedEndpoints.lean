import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralMixedCheck0
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralMixedCheck1
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralMixedCheck2
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralMixedCheck3

set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.MixedEndpointBridge
open Holant Holant.Algebraic Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.LocalDrafts.MainChain
open Holant.Certificates.TetrahedralPreservers
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry
open Preserver RankTwo.QuotientEnumeration RankTwo.HarmonicProjectivities
open RankTwo.PhysicalOrbit RankTwo.CanonicalEndpointBridge
open scoped Matrix BigOperators

theorem reconstruction_table : ∀ b : Bool,∀ k : Fin 16,
    rawReconstructed b (TetrahedralDeck.words k) = prototype b (TetrahedralDeck.words k) := by
  intro b k
  cases b with
  | false =>
      fin_cases k
      · exact reconstruction_0_0
      · exact reconstruction_0_1
      · exact reconstruction_0_2
      · exact reconstruction_0_3
      · exact reconstruction_0_4
      · exact reconstruction_0_5
      · exact reconstruction_0_6
      · exact reconstruction_0_7
      · exact reconstruction_0_8
      · exact reconstruction_0_9
      · exact reconstruction_0_10
      · exact reconstruction_0_11
      · exact reconstruction_0_12
      · exact reconstruction_0_13
      · exact reconstruction_0_14
      · exact reconstruction_0_15
  | true =>
      fin_cases k
      · exact reconstruction_1_0
      · exact reconstruction_1_1
      · exact reconstruction_1_2
      · exact reconstruction_1_3
      · exact reconstruction_1_4
      · exact reconstruction_1_5
      · exact reconstruction_1_6
      · exact reconstruction_1_7
      · exact reconstruction_1_8
      · exact reconstruction_1_9
      · exact reconstruction_1_10
      · exact reconstruction_1_11
      · exact reconstruction_1_12
      · exact reconstruction_1_13
      · exact reconstruction_1_14
      · exact reconstruction_1_15

theorem mixed_table : ∀ b : Bool,∀ k : Fin 16,
    Signature.coordinateAction (mixedPorts b) (prototype b) (TetrahedralDeck.words k) =
      exteriorScale b * mixedShape b imag (TetrahedralDeck.words k) := by
  intro b k
  cases b with
  | false =>
      fin_cases k
      · exact mixed_0_0
      · exact mixed_0_1
      · exact mixed_0_2
      · exact mixed_0_3
      · exact mixed_0_4
      · exact mixed_0_5
      · exact mixed_0_6
      · exact mixed_0_7
      · exact mixed_0_8
      · exact mixed_0_9
      · exact mixed_0_10
      · exact mixed_0_11
      · exact mixed_0_12
      · exact mixed_0_13
      · exact mixed_0_14
      · exact mixed_0_15
  | true =>
      fin_cases k
      · exact mixed_1_0
      · exact mixed_1_1
      · exact mixed_1_2
      · exact mixed_1_3
      · exact mixed_1_4
      · exact mixed_1_5
      · exact mixed_1_6
      · exact mixed_1_7
      · exact mixed_1_8
      · exact mixed_1_9
      · exact mixed_1_10
      · exact mixed_1_11
      · exact mixed_1_12
      · exact mixed_1_13
      · exact mixed_1_14
      · exact mixed_1_15

noncomputable section

theorem rawModel_complex (b : Bool) : lift4 (rawModel b) =
    lineMatrix (mixedRow b) baseLine * liftSmall (smallInverse b) *
      dualMatrix (mixedRow b) baseLine := by
  ext i j
  have hp (a : Fin 2) (i : Fin 4) :
      embed (rawPoint (mixedRow b) (canonicalPair baseLine a) i) =
        point (mixedRow b) (canonicalPair baseLine a) i :=
    congrFun (RankThree.lift_point _ _) i
  have hs (j : Fin 4) : embed (rawSign j) = frobeniusSigns j := by
    fin_cases j <;> simp [rawSign,frobeniusSigns,embed_one,embed_neg]
  change embedding (∑ a : Fin 2,∑ c : Fin 2,
    rawPoint (mixedRow b) (canonicalPair baseLine a) i * smallInverse b a c *
      rawSign j * rawPoint (mixedRow b) (canonicalPair baseLine c) j) = _
  simp only [map_sum,map_mul,embedding_apply,hp,hs,Matrix.mul_apply,lineMatrix,liftSmall,dualMatrix]
  simp only [Fin.sum_univ_two]
  ring

theorem model_mixed_raw (b : Bool) :
    model (mixedRow b) baseCode baseCode 0 = lift4 (rawModel b) := by
  have hinv : (liftSmall (smallInverse b))⁻¹ = liftSmall (smallInverse b) := by
    apply Matrix.inv_eq_right_inv
    cases b with
    | false => exact base_flip_square
    | true =>
        have hid : liftSmall (smallInverse true) = (1 : SmallMatrix) := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [smallInverse,liftSmall,embed_one,embed_zero]
        rw [hid,Matrix.one_mul]
  rw [model,baseCode,parameter_zero,Matrix.mul_one,mixed_quotient,hinv]
  exact (rawModel_complex b).symm

theorem reconstructed_complex (b : Bool) : complexTensor (rawReconstructed b) =
    Holant.Certificates.TetrahedralPreservers.reconstruct (rightX*lift4 (rawModel b)) := by
  have h := rawReconstruct_complex (rawRightX*rawModel b)
  rw [lift4_mul,rawRightX_complex] at h
  exact h

theorem prototype_complex (b : Bool) :
    complexTensor (prototype b) = Holant.Certificates.TetrahedralPreservers.reconstruct (rightX*model (mixedRow b) baseCode baseCode 0) := by
  have hraw : rawReconstructed b = prototype b := by
    funext x
    obtain ⟨k,rfl⟩ := TetrahedralDeck.words_surjective x
    exact reconstruction_table b k
  rw [model_mixed_raw,←reconstructed_complex,hraw]

theorem physical_slots (b : Bool) :
    (fun i => complexMatrix (mixedPorts b i)) = fun i =>
      correctionSlotScale (mixedRow b) i •
        (if correctionReverse i then (kernel (mixedRow b) (mixedCodes b i)).transpose
          else kernel (mixedRow b) (mixedCodes b i)) := by
  cases b with
  | false => exact correction_slots 2
  | true =>
      funext i
      fin_cases i
      · change kernel 3 17 = 1 • kernel 3 17
        rw [one_smul]
      · change kernel 3 16 = 1 • kernel 3 16
        rw [one_smul]
      · exact congrFun (correction_slots 3) 2
      · have h := congrFun (correction_slots 3) (3 : Fin 4)
        have hc : correctionCodes 3 3 = xConjugateIndex 3 1 := rfl
        rw [hc] at h
        simpa only [mixedPorts,mixedRow,mixedCodes,correctionSlotScale,correctionReverse,ite_true,
          Matrix.cons_val_succ',Matrix.cons_val_zero',Matrix.cons_val_three,
          Matrix.head_cons,Matrix.tail_cons] using h


theorem mixed_complex_exact (b : Bool) :
    Signature.coordinateAction (fun i => complexMatrix (mixedPorts b i))
      (Holant.Certificates.TetrahedralPreservers.reconstruct (rightX*model (mixedRow b) baseCode baseCode 0)) =
        embed (exteriorScale b) • mixedShape b Complex.I := by
  rw [←prototype_complex,←complexTensor_action]
  have ht : Signature.coordinateAction (mixedPorts b) (prototype b) =
      exteriorScale b • mixedShape b imag := by
    funext x
    obtain ⟨k,rfl⟩ := TetrahedralDeck.words_surjective x
    exact mixed_table b k
  rw [ht]
  change complexTensor (fun x => exteriorScale b * mixedShape b imag x) = _
  rw [complexTensor_scale]
  have hm : complexTensor (mixedShape b imag) = mixedShape b Complex.I := by
    change RingHomRealization.mapSignature fieldEmbedding (mixedShape b imag) = _
    rw [map_shape]
    change mixedShape b (embed imag) = mixedShape b Complex.I
    rw [embed_imag]
  rw [hm]

/-- Two actual row channels give the upper rank bound for every matching.
This is a coefficient factorization, not a binary-pair gadget assertion. -/
def factorLeft (b : Bool) : Matrix (Bool × Bool) (Fin 2) ℂ := fun i k =>
  if k = 0 then if i.1 = i.2 then 1 else 0
  else if i.1 = i.2 then 0 else if i.1 then 1 else phaseValue b Complex.I

def factorRight (b : Bool) : Matrix (Fin 2) (Bool × Bool) ℂ := fun k j =>
  if k = 0 then if j.1 = j.2 then if j.1 then phaseValue b Complex.I else 1 else 0
  else if j.1 = j.2 then 0 else 1

theorem flatten_factor (b : Bool) (r : Fin 3) :
    Holant.Certificates.MatchingProductBridge.flatten r (mixedShape b Complex.I) =
      factorLeft b * factorRight b := by
  ext i j
  rcases i with ⟨i₁,i₂⟩
  rcases j with ⟨j₁,j₂⟩
  cases b <;> fin_cases r <;> cases i₁ <;> cases i₂ <;> cases j₁ <;> cases j₂ <;>
    simp [Holant.Certificates.MatchingProductBridge.flatten,
      Holant.Certificates.MatchingProductBridge.flatten0,
      Holant.Certificates.MatchingProductBridge.flatten1,
      Holant.Certificates.MatchingProductBridge.flatten2,
      mixedShape,phaseWord,Holant.Marked.SupportAtlas.parity,
      Matrix.mul_apply,Fin.sum_univ_two,factorLeft,factorRight,phaseValue]

def rankKeys : Fin 2 → Bool × Bool := ![(false,false),(true,false)]

theorem flatten_minor (b : Bool) (r : Fin 3) :
    (Holant.Certificates.MatchingProductBridge.flatten r (mixedShape b Complex.I)).submatrix
      rankKeys rankKeys = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  cases b <;> fin_cases r <;> fin_cases i <;> fin_cases j <;>
    simp [Holant.Certificates.MatchingProductBridge.flatten,
      Holant.Certificates.MatchingProductBridge.flatten0,
      Holant.Certificates.MatchingProductBridge.flatten1,
      Holant.Certificates.MatchingProductBridge.flatten2,
      Matrix.submatrix,rankKeys,mixedShape,phaseWord,
      Holant.Marked.SupportAtlas.parity,Matrix.one_apply]

/-- The literal original ordered mixed tables have ranks (2,2,2),
proved by the produced factorization and actual nonsingular minor. -/
theorem mixed_shape_rank (b : Bool) (r : Fin 3) :
    (Holant.Certificates.MatchingProductBridge.flatten r (mixedShape b Complex.I)).rank = 2 := by
  apply le_antisymm
  · rw [flatten_factor]
    exact (Matrix.rank_mul_le_left _ _).trans (by
      simpa only [Fintype.card_fin] using Matrix.rank_le_card_width (factorLeft b))
  · have h := Matrix.rank_submatrix_le
      (Holant.Certificates.MatchingProductBridge.flatten r (mixedShape b Complex.I)) rankKeys rankKeys
    rw [flatten_minor,Matrix.rank_one] at h
    simpa only [Fintype.card_fin] using h

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.MixedEndpointBridge
