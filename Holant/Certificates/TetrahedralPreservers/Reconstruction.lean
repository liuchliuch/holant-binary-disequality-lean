import Holant.Certificates.TetrahedralPreservers.RankOne
import Holant.Platonic.FixedMatchingRuling.Reconstruction

/-! Original ordered four-port tensors and the literal Frobenius dual basis.
These are analytic equalities of tensors, with no gadget realization claim. -/
noncomputable section
namespace Holant.Certificates.TetrahedralPreservers
open Holant Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence
open Holant.Platonic.FixedMatchingRuling.Physical
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- The source's reconstruction sum, on the original four ordered ports. -/
def reconstruct (A : End) : FourTensor := fun x =>
  ∑ i : Fin 4, quaternionDual i (x 0) (x 1) *
    assemble (fun j => A j i) (x 2) (x 3)

/-- The actual card map of a four-port tensor, in quaternion coordinates. -/
def cardMatrix (f : FourTensor) : End := fun i j =>
  coordinates (fun c d => ∑ a : Bool, ∑ b : Bool,
    quaternionBasis j a b * f ![a,b,c,d]) i

theorem reconstruct_cardMatrix (f : FourTensor) : reconstruct (cardMatrix f) = f := by
  funext x
  unfold reconstruct cardMatrix
  change (∑ i : Fin 4, quaternionDual i (x 0) (x 1) *
    assemble (quaternionCoefficient (fun c d => ∑ a : Bool, ∑ b : Bool,
      quaternionBasis i a b * f ![a,b,c,d])) (x 2) (x 3)) = f x
  simp only [assemble_coefficient]
  have h := quaternion_reconstruction (fun a b => f ![a,b,x 2,x 3]) (x 0) (x 1)
  have hx : ![x 0,x 1,x 2,x 3] = x := by ext i; fin_cases i <;> rfl
  simpa only [hx] using h

theorem reconstruct_outer (u v : V) :
    reconstruct (outer u v) = (2 : ℂ)⁻¹ • P0 (assemble v) (assemble u) := by
  funext x
  rcases h0 : x 0 with _ | _ <;> rcases h1 : x 1 with _ | _ <;>
    rcases h2 : x 2 with _ | _ <;> rcases h3 : x 3 with _ | _ <;>
    simp [reconstruct,outer,quaternionDual,assemble,frobeniusSigns,P0,
      Q0,Q1,Q2,Q3,Signature.equality,Fin.sum_univ_succ,h0,h1,h2,h3] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

def sandwich (U W : BinaryMatrix) : End := fun i j =>
  coordinates (U * Matrix.of (quaternionBasis j) * W) i

def transposeSandwich (U W : BinaryMatrix) : End := fun i j =>
  coordinates (U * (Matrix.of (quaternionBasis j)).transpose * W) i

theorem reconstruct_sandwich (U W : BinaryMatrix) :
    reconstruct (sandwich U W) = P1 U.transpose W := by
  funext x
  unfold reconstruct sandwich
  change (∑ i : Fin 4, quaternionDual i (x 0) (x 1) *
    assemble (quaternionCoefficient (U * Matrix.of (quaternionBasis i) * W))
      (x 2) (x 3)) = _
  simp only [assemble_coefficient]
  rcases h0 : x 0 with _ | _ <;> rcases h1 : x 1 with _ | _ <;>
    rcases h2 : x 2 with _ | _ <;> rcases h3 : x 3 with _ | _ <;>
    simp [quaternionDual,quaternionBasis,P1,Q0,Q1,Q2,Q3,Signature.equality,
      Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,h0,h1,h2,h3] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem reconstruct_transposeSandwich (U W : BinaryMatrix) :
    reconstruct (transposeSandwich U W) = P2 W U.transpose := by
  funext x
  unfold reconstruct transposeSandwich
  change (∑ i : Fin 4, quaternionDual i (x 0) (x 1) *
    assemble (quaternionCoefficient (U * (Matrix.of (quaternionBasis i)).transpose * W))
      (x 2) (x 3)) = _
  simp only [assemble_coefficient]
  rcases h0 : x 0 with _ | _ <;> rcases h1 : x 1 with _ | _ <;>
    rcases h2 : x 2 with _ | _ <;> rcases h3 : x 3 with _ | _ <;>
    simp [quaternionDual,quaternionBasis,P2,Q0,Q1,Q2,Q3,Signature.equality,
      Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,h0,h1,h2,h3] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

/-- Every actual rank-one linear map reconstructs a nontrivial binary-pair
factorization. The factors come from its outer form, not from a finite atlas. -/
theorem rank_one_reconstruction (A : End) (hA : A.rank = 1) :
    ∃ U W : BinaryMatrix, U ≠ 0 ∧ W ≠ 0 ∧
      reconstruct A = (2 : ℂ)⁻¹ • P0 U W := by
  obtain ⟨u,v,hu,hv,rfl⟩ := (rank_one_iff A).mp hA
  refine ⟨assemble v,assemble u,?_,?_,reconstruct_outer u v⟩
  · intro h
    apply hv
    exact coordinates.symm.injective (h.trans (map_zero coordinates.symm).symm)
  · intro h
    apply hu
    exact coordinates.symm.injective (h.trans (map_zero coordinates.symm).symm)

end Holant.Certificates.TetrahedralPreservers
