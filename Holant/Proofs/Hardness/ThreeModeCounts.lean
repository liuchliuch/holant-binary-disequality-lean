import Holant.Proofs.BinaryInterpolation.RawPolynomial

/-! Exact finite mode multiplicities. These are semantic proof indices only;
the real annihilator generator scans the original vertex-label count. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeCounts
open scoped BigOperators
variable {V : Type*} [Fintype V]

def count (σ : V → Fin 3) (i : Fin 3) : ℕ := by
  classical
  exact (Finset.univ.filter (fun v=>σ v=i)).card

theorem count_total (σ : V → Fin 3) :
    count σ 0+count σ 1+count σ 2=Fintype.card V := by
  classical
  have h : Fintype.card V=∑i : Fin 3,count σ i := by
    exact Finset.card_eq_sum_card_fiberwise (fun _ _=>Finset.mem_univ _)
  simpa [Fin.sum_univ_succ,add_assoc] using h.symm

theorem count_zero_iff (σ : V → Fin 3) (i : Fin 3) :
    count σ i=0 ↔ ∀v,σ v≠i := by
  classical
  simp [count,Finset.card_eq_zero,Finset.filter_eq_empty_iff]

theorem nonzero_counts (σ : V → Fin 3) (hσ : σ≠fun _=>0) :
    0<count σ 1+count σ 2 := by
  by_contra hn
  have h1 : count σ 1=0 := by omega
  have h2 : count σ 2=0 := by omega
  apply hσ
  funext v
  have hv1 := (count_zero_iff σ 1).mp h1 v
  have hv2 := (count_zero_iff σ 2).mp h2 v
  generalize hs : σ v=t at *
  fin_cases t <;> simp_all

theorem prod_eq_counts {K : Type*} [CommMonoid K] (σ : V → Fin 3) (eig : Fin 3 → K) :
    (∏v,eig (σ v))=eig 0^count σ 0*eig 1^count σ 1*eig 2^count σ 2 := by
  classical
  rw [←Finset.prod_fiberwise' Finset.univ σ eig]
  simp [count,Fin.prod_univ_succ,mul_assoc]

theorem prod_eq_grid {K : Type*} [CommMonoid K] (σ : V → Fin 3) (eig : Fin 3 → K) :
    (∏v,eig (σ v))=
      eig 0^(Fintype.card V-count σ 1-count σ 2)*eig 1^count σ 1*eig 2^count σ 2 := by
  rw [prod_eq_counts]
  have h := count_total σ
  have h0 : count σ 0=Fintype.card V-count σ 1-count σ 2 := by omega
  rw [h0]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeCounts
