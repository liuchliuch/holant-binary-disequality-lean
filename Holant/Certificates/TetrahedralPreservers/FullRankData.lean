import Holant.Certificates.TetrahedralPreservers.FullRankRaw

namespace Holant.Certificates.TetrahedralPreservers
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Holant.Certificates.MatchingProductBridge

def liftVector (r : ZV) : V := fun i => (r i : ℂ)
def liftMatrix (A : ZEnd) : End := fun i j => (A i j : ℂ)

theorem lift_zstandard (k : Fin 12) : liftVector (zstandard k) = standardPoint k := by
  rw [standardPoint_table]
  ext i
  fin_cases k <;> fin_cases i <;> norm_num [liftVector,zstandard,standardTable]

theorem lift_mulVec (A : ZEnd) (r : ZV) : liftMatrix A *ᵥ liftVector r = liftVector (A *ᵥ r) := by
  ext i
  simp [liftMatrix,liftVector,Matrix.mulVec,dotProduct]

theorem lift_zsharp (A : ZEnd) : liftMatrix (zsharp A)=sharp (liftMatrix A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [liftMatrix,zsharp,zJ,sharp_apply,frobeniusSigns,Matrix.diagonal_mul,Matrix.mul_diagonal]

theorem lift_preserves {A : ZEnd} (h : PreservesRaw A) : OneSided Standard (liftMatrix A) := by
  intro r hr
  obtain ⟨k,c,hc,rfl⟩ := (standard_iff r).mp hr
  obtain ⟨j,d,hd,he⟩ := h k
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [Matrix.mulVec_smul,← lift_zstandard,lift_mulVec,he]
  have hl : liftVector (d • zstandard j) =
      (d : ℂ) • standardPoint j := by
    rw [← lift_zstandard]
    ext i
    simp [liftVector]
  rw [hl]
  exact Or.inr (standard_saturated (standard_saturated (standardPoint_mem j) hd') hc)

theorem lift_rank_four {A : ZEnd} (h : A.det ≠ 0) : (liftMatrix A).rank = 4 := by
  apply (rank_four_iff_det_ne_zero _).mpr
  have he : (liftMatrix A).det=(A.det : ℂ) := by
    exact (Int.cast_det A).symm
  rw [he]
  exact_mod_cast h

def signedMap (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) : End := liftMatrix (signedRaw σ ε)
def leftMap (k : Fin 12) : End := liftMatrix (leftRaw k)

theorem signedMap_twoSided (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) :
    TwoSided Standard (signedMap σ ε) := by
  exact ⟨lift_preserves (checked_preserves (signedRaw_certificate σ ε).1),
    by rw [signedMap,← lift_zsharp]; exact lift_preserves (checked_preserves (signedRaw_certificate σ ε).2.1)⟩

theorem signedMap_rank (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) :
    (signedMap σ ε).rank=4 := lift_rank_four (signedRaw_certificate σ ε).2.2

theorem leftMap_twoSided (k : Fin 12) : TwoSided Standard (leftMap k) := by
  exact ⟨lift_preserves (checked_preserves (leftRaw_certificate k).1),
    by rw [leftMap,← lift_zsharp]; exact lift_preserves (checked_preserves (leftRaw_certificate k).2.1)⟩

theorem leftMap_rank (k : Fin 12) : (leftMap k).rank=4 :=
  lift_rank_four (leftRaw_certificate k).2.2

end
end Holant.Certificates.TetrahedralPreservers
