import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseRankThreePorts

/-! The finite certificate applied to actual natural-number port counts.
There are exactly seven original-row substitutions, with no signed port or
private occurrence suppressed. All formal character coordinates are exposed;
none is asserted to satisfy a virtual XOR constraint. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseRankThreeRegularization
open Holant Holant.Tractable OrdinaryNegativeSignedPortsCore
open scoped BigOperators
namespace P
export OrdinaryNegativeSparseRankThreeParity (Transform schedule contribution certificate)
end P
namespace R
export OrdinaryNegativeSparseRankThreePorts (transformed transformed_count)
end R
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false
attribute [local irreducible] OrdinaryNegativeSparseRankThreeParity.image
  OrdinaryNegativeSparseRankThreeParity.schedule
variable {n : ℕ} (p : Fin n→Port 7)

def pattern (j : Fin 7) : Bool := decide (I.bundleSize p j%2=1)
def rows : Fin 7→Fin n→Port 7 := Fin.cases p (fun i=>R.transformed p (P.schedule (pattern p) i))

theorem rows_count (j : Fin 7) :
    (∑i : Fin 7,I.bundleSize (rows p i) j)=I.bundleSize p j+
      ∑i : Fin 6,∑k : Fin 7,if OrdinaryNegativeSparseRankThreeParity.image (P.schedule (pattern p) i) k=j.succ
        then I.bundleSize p k else 0 := by
  rw [Fin.sum_univ_succ]
  simp only [rows,Fin.cases_zero,Fin.cases_succ,R.transformed_count]

theorem pattern_mod (j : Fin 7) : I.bundleSize p j%2=if pattern p j then 1 else 0 := by
  unfold pattern
  have hlt := Nat.mod_lt (I.bundleSize p j) (by decide : 0<2)
  split_ifs with h <;> simp_all <;> omega

theorem contribution_mod (t : P.Transform) (j : Fin 7) :
    (∑k : Fin 7,if OrdinaryNegativeSparseRankThreeParity.image t k=j.succ
      then I.bundleSize p k else 0)%2=P.contribution (pattern p) t j%2 := by
  rw [Finset.sum_nat_mod]
  unfold P.contribution
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases he : OrdinaryNegativeSparseRankThreeParity.image t k=j.succ
  · simp only [he,ite_true,pattern_mod]
    cases pattern p k <;> simp
  · simp [he]

theorem even_rows (h : ¬∀j,Odd (I.bundleSize p j)) :
    ∀j,Even (∑i : Fin 7,I.bundleSize (rows p i) j) := by
  intro j
  have hq : ¬∀j,pattern p j=true := by
    intro hh
    apply h
    intro k
    exact Nat.odd_iff.mpr (of_decide_eq_true (hh k))
  have cert := P.certificate (pattern p) hq j
  rw [Nat.even_iff,rows_count,Nat.add_mod,Finset.sum_nat_mod]
  simp_rw [contribution_mod]
  rw [←Finset.sum_nat_mod,pattern_mod]
  cases hh : pattern p j <;> simpa [hh,Nat.add_mod] using cert

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseRankThreeRegularization
end
