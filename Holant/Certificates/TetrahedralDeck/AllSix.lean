import Holant.Certificates.TetrahedralDeck.Matching
import Holant.Certificates.TetrahedralOrientation.Interface

/-! Literal completeness of the six permutations and actual Frobenius card-map
rank. This does not assume the rank assertion from the preceding bridge lemma. -/
namespace Holant.Certificates.TetrahedralDeck
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def permutations : Fin 6 → Fin 3 → Fin 4 :=
  ![![0,1,3],![1,3,0],![3,0,1],![0,3,1],![1,0,3],![3,1,0]]

theorem permutations_complete : ∀ τ : Fin 3 → Fin 4,
    List.Perm [τ 0,τ 1,τ 2] [0,1,3] ↔ ∃ s : Fin 6, τ = permutations s := by decide

theorem permutations_injective : Function.Injective permutations := by decide

theorem classes_disjoint : ∀ s t : Fin 3, permutations (s.castAdd 3) ≠ permutations (t.natAdd 3) := by decide

def allImages (s : Fin 6) : Fin 4 → FourTensor :=
  ![(1/2 : ℂ) • C,TetrahedralOrientation.axisR (permutations s 0),
    TetrahedralOrientation.axisR (permutations s 1),TetrahedralOrientation.axisR (permutations s 2)]

def allAncestor (s : Fin 6) : Signature ℂ 6 := fun x =>
  ∑ k : Fin 4, TetrahedralOrientation.dual k (x 0) (x 1)*allImages s k (fun j => x j.succ.succ)

theorem survivor_ancestor (s : Fin 3) : allAncestor (s.castAdd 3) = TetrahedralAffine.complexAncestor s := by
  fin_cases s <;> rfl

theorem rejected_ancestor (s : Fin 3) : allAncestor (s.natAdd 3) = TetrahedralOrientation.ancestor s := by
  fin_cases s <;> rfl

/-- Actual contraction on original ports1/2 recovers every prescribed basis image. -/
theorem basis_recovered (s : Fin 6) (k : Fin 4) :
    Signature.contract (quaternionBasis k) (allAncestor s) = allImages s k := by
  fin_cases k <;> funext x <;>
    simp [Signature.contract,allAncestor,TetrahedralOrientation.dual,
      Fin.sum_univ_succ,quaternionBasis,Q0,Q1,Q2,Q3,Signature.equality,smul_eq_mul] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring

def basisCardMatrix (s : Fin 6) : Matrix (Fin 16) (Fin 4) ℂ := fun i k =>
  Signature.contract (quaternionBasis k) (allAncestor s) (words i)

def rankRows : Fin 4 → Fin 16 := ![0,3,5,6]

theorem basis_minor_nonzero (s : Fin 6) :
    Matrix.det ((basisCardMatrix s).submatrix rankRows id) ≠ 0 := by
  fin_cases s <;>
    norm_num [basisCardMatrix,basis_recovered,rankRows,Matrix.det_succ_row_zero,
      Matrix.det_fin_zero,Matrix.submatrix_apply,Fin.sum_univ_succ,Fin.succAbove,
      allImages,permutations,words,TetrahedralOrientation.axisR,C,P2,Q0,Q1,Q2,Q3,
      Signature.equality,smul_eq_mul] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.ext_iff]

/-- Matrix rank of the genuine card map in the quaternion basis is four. -/
theorem basis_card_rank_four (s : Fin 6) : (basisCardMatrix s).rank = 4 := by
  have hl := Matrix.rank_submatrix_le (basisCardMatrix s) rankRows id
  have hr := Matrix.rank_of_det_ne_zero (basis_minor_nonzero s)
  have hu := Matrix.rank_le_card_width (basisCardMatrix s)
  norm_num at hr hu
  rw [hr] at hl
  omega

end
end Holant.Certificates.TetrahedralDeck
