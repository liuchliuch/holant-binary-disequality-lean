import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPrototypeCheck0
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPrototypeCheck1
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPrototypeCheck2
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPrototypeCheck3

set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.CanonicalEndpointBridge
open Holant Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.Certificates.MatchingProductBridge Holant.Certificates.PlatonicIncidence
open Holant.Certificates.TetrahedralPreservers
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry
open Preserver RankTwo.QuotientEnumeration RankTwo.HarmonicProjectivities
open RankTwo.PhysicalOrbit RankTwo.BaseTerminals
open scoped Matrix BigOperators

theorem corrected_raw_table : ∀ b : Bool,∀ k : Fin 16,
    Signature.coordinateAction (correctionPorts (baseForm b)) (rawPrototype (baseForm b))
      (TetrahedralDeck.words k) = baseTensor b (TetrahedralDeck.words k) := by
  intro b k
  cases b with
  | false =>
      fin_cases k
      · exact corrected_raw_0_0
      · exact corrected_raw_0_1
      · exact corrected_raw_0_2
      · exact corrected_raw_0_3
      · exact corrected_raw_0_4
      · exact corrected_raw_0_5
      · exact corrected_raw_0_6
      · exact corrected_raw_0_7
      · exact corrected_raw_0_8
      · exact corrected_raw_0_9
      · exact corrected_raw_0_10
      · exact corrected_raw_0_11
      · exact corrected_raw_0_12
      · exact corrected_raw_0_13
      · exact corrected_raw_0_14
      · exact corrected_raw_0_15
  | true =>
      fin_cases k
      · exact corrected_raw_1_0
      · exact corrected_raw_1_1
      · exact corrected_raw_1_2
      · exact corrected_raw_1_3
      · exact corrected_raw_1_4
      · exact corrected_raw_1_5
      · exact corrected_raw_1_6
      · exact corrected_raw_1_7
      · exact corrected_raw_1_8
      · exact corrected_raw_1_9
      · exact corrected_raw_1_10
      · exact corrected_raw_1_11
      · exact corrected_raw_1_12
      · exact corrected_raw_1_13
      · exact corrected_raw_1_14
      · exact corrected_raw_1_15

noncomputable section

theorem embedding_apply (z : Scalar) : embedding z = embed z := rfl

def lift4 (A : Matrix (Fin 4) (Fin 4) Scalar) : End := fun i j => embed (A i j)

theorem q_complex (j : Fin 4) : complexMatrix (q j) = Matrix.of (quaternionBasis j) := by
  ext u v
  fin_cases j <;> cases u <;> cases v <;>
    simp [complexMatrix,q,mat,quaternionBasis,Q0,Q1,Q2,Q3,Signature.equality,embed_imag,embed_one,embed_zero,embed_neg]

theorem rawDual_complex (i : Fin 4) : complexMatrix (rawDual i) =
    Matrix.of (Holant.Platonic.FixedMatchingRuling.Physical.quaternionDual i) := by
  have htwo : embed (2 : Scalar) = (2 : ℂ) := map_natCast embedding 2
  ext u v
  fin_cases i <;> cases u <;> cases v <;>
    norm_num [complexMatrix,rawDual,ms,q,mat,
      Holant.Platonic.FixedMatchingRuling.Physical.quaternionDual,
      Q0,Q1,Q2,Q3,Signature.equality,embed_mul,embed_div,embed_neg,
      embed_imag,embed_one,embed_zero,embed_inv,htwo]

theorem rawAssemble_complex (v : Fin 4 → Scalar) :
    complexMatrix (rawAssemble v) = assemble (fun i => embed (v i)) := by
  ext u w
  change embedding (∑ i : Fin 4,v i*q i u w) = _
  simp only [map_sum,map_mul,embedding_apply]
  have hq (i : Fin 4) : embed (q i u w) = quaternionBasis i u w :=
    congrFun (congrFun (q_complex i) u) w
  simp [hq,Fin.sum_univ_succ,assemble,quaternionBasis] <;> ring

theorem lift4_mul (A B : Matrix (Fin 4) (Fin 4) Scalar) :
    lift4 (A*B) = lift4 A*lift4 B := by
  ext i j
  change embedding (∑ k : Fin 4,A i k*B k j) = _
  simp only [map_sum,map_mul,embedding_apply,Matrix.mul_apply,lift4]

theorem rawRightX_complex : lift4 rawRightX = rightX := by
  ext i j
  have h := congrFun (RankThree.lift_rawCoordinates (mm (q j) flip)) i
  rw [complexMatrix_mm,q_complex,complexMatrix_flip] at h
  simpa only [lift4,rawRightX,RankThree.lift,rightX,sandwich,Matrix.one_mul,
    show Holant.Certificates.MatchingContractionClosure.X =
      Matrix.of Holant.Certificates.MatchingProductBridge.X from rfl] using h

theorem rawProjection_complex (f : Form) :
    lift4 (rawProjection f) = lineMatrix f baseLine*(lineMatrix f baseLine).transpose := by
  ext i j
  have hp (a : Fin 2) (i : Fin 4) : embed (rawPoint f (canonicalPair baseLine a) i) =
      point f (canonicalPair baseLine a) i := congrFun (RankThree.lift_point _ _) i
  change embedding (∑ a : Fin 2,rawPoint f (canonicalPair baseLine a) i*
    rawPoint f (canonicalPair baseLine a) j) = _
  simp only [map_sum,map_mul,embedding_apply,hp,Matrix.mul_apply,Matrix.transpose_apply,lineMatrix]

theorem base_flip_square : liftSmall baseFlip*liftSmall baseFlip = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [liftSmall,baseFlip,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply,embed_neg,embed_one,embed_zero]

theorem base_dual (b : Bool) : dualMatrix (baseForm b) baseLine =
    liftSmall baseFlip*(lineMatrix (baseForm b) baseLine).transpose := by
  ext a i
  have h := congrArg embed (base_dual_raw b a i)
  have hp (f : Form) (k : Fin 24) (j : Fin 4) : embed (rawPoint f k j)=point f k j :=
    congrFun (RankThree.lift_point f k) j
  fin_cases a <;> fin_cases i <;>
    simpa [dualMatrix,lineMatrix,Matrix.mul_apply,Matrix.transpose_apply,
      baseFlip,liftSmall,Fin.sum_univ_two,frobeniusSigns,rawSign,
      embed_mul,embed_neg,embed_one,embed_zero,hp] using h

theorem model_base_projection (b : Bool) :
    model (baseForm b) baseCode baseCode 0 = lift4 (rawProjection (baseForm b)) := by
  have hi : (liftSmall baseFlip)⁻¹ = liftSmall baseFlip := Matrix.inv_eq_right_inv base_flip_square
  rw [model,baseCode,parameter_zero,Matrix.mul_one,base_quotient,hi,base_dual,
    Matrix.mul_assoc,←Matrix.mul_assoc (liftSmall baseFlip),base_flip_square,Matrix.one_mul,
    rawProjection_complex]

theorem embed_sum {ι : Type*} [Fintype ι] (v : ι → Scalar) :
    embed (∑ i,v i) = ∑ i,embed (v i) := by
  exact map_sum embedding v Finset.univ

theorem rawReconstruct_complex (A : Matrix (Fin 4) (Fin 4) Scalar) :
    complexTensor (fun x => ∑ i : Fin 4,rawDual i (x 0) (x 1)*
      rawAssemble (fun j => A j i) (x 2) (x 3)) = Holant.Certificates.TetrahedralPreservers.reconstruct (lift4 A) := by
  funext x
  simp only [complexTensor,embed_sum,embed_mul,Holant.Certificates.TetrahedralPreservers.reconstruct]
  apply Finset.sum_congr rfl
  intro i hi
  have hd : embed (rawDual i (x 0) (x 1)) =
      Holant.Platonic.FixedMatchingRuling.Physical.quaternionDual i (x 0) (x 1) :=
    congrFun (congrFun (rawDual_complex i) (x 0)) (x 1)
  have ha : embed (rawAssemble (fun j => A j i) (x 2) (x 3)) =
      assemble (fun j => embed (A j i)) (x 2) (x 3) :=
    congrFun (congrFun (rawAssemble_complex (fun j => A j i)) (x 2)) (x 3)
  rw [hd,ha]
  rfl

theorem rawPrototype_complex (f : Form) :
    complexTensor (rawPrototype f) = Holant.Certificates.TetrahedralPreservers.reconstruct (rightX*lift4 (rawProjection f)) := by
  have h := rawReconstruct_complex (rawRightX*rawProjection f)
  rw [lift4_mul,rawRightX_complex] at h
  exact h

/-- Exact canonical-to-base bridge. It consumes the SAME right-X
prototype produced by canonical_cell, with no BaseNormalization input. -/
theorem prototype_correction (b : Bool) :
    Signature.coordinateAction (fun i => complexMatrix (correctionPorts (baseForm b) i))
      (Holant.Certificates.TetrahedralPreservers.reconstruct (rightX*model (baseForm b) baseCode baseCode 0)) = complexBase b := by
  rw [model_base_projection,←rawPrototype_complex,←complexTensor_action]
  change complexTensor
    (Signature.coordinateAction (correctionPorts (baseForm b)) (rawPrototype (baseForm b))) =
      complexTensor (baseTensor b)
  congr 1
  funext x
  obtain ⟨k,rfl⟩ := TetrahedralDeck.words_surjective x
  exact corrected_raw_table b k

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.CanonicalEndpointBridge
