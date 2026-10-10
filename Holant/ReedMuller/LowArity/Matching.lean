import Holant.ReedMuller.LowArity.Dimension0
import Holant.ReedMuller.LowArity.Dimension2
import Holant.ReedMuller.LowArity.Dimension4
import Holant.ReedMuller.LowArity.Dimension6

namespace Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section

/-- All self-dual binary codes in lengths at most six have literal matching
coordinates. The finite checker ranges over arbitrary code membership. -/
theorem low_arity_matching (r : ℕ) (hr : r ≤ 3) (D : BinaryCode (2*r)) (hD : SelfDual D) :
    ∃ M : Matching r (2*r), ∀ x, x ∈ D ↔ M.Holds x := by
  have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  · obtain ⟨a,ha⟩ := Dimension0.selfDual_matching D hD
    exact ⟨Dimension0.model a,ha⟩
  · obtain ⟨a,ha⟩ := Dimension2.selfDual_matching D hD
    exact ⟨Dimension2.model a,ha⟩
  · obtain ⟨a,ha⟩ := Dimension4.selfDual_matching D hD
    exact ⟨Dimension4.model a,ha⟩
  · obtain ⟨a,ha⟩ := Dimension6.selfDual_matching D hD
    exact ⟨Dimension6.model a,ha⟩

def pairVector {r n : ℕ} (M : Matching r n) (e : Fin r) : BinaryVector n :=
  fun k => if (M.symm k).1 = e then 1 else 0

theorem matching_expansion {r n : ℕ} (M : Matching r n) (x : BinaryVector n) (hx : M.Holds x) :
    x = ∑ e, x (M (e,0)) • pairVector M e := by
  funext k
  obtain ⟨⟨e,b⟩,rfl⟩ := M.surjective k
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,pairVector,Equiv.symm_apply_apply]
  simp only [mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  fin_cases b
  · rfl
  · exact (hx e).symm

theorem matching_expansion_unique {r n : ℕ} (M : Matching r n) (c d : Fin r → ZMod 2)
    (h : (∑ e, c e • pairVector M e) = ∑ e, d e • pairVector M e) : c = d := by
  funext e
  have he := congrArg (fun x : BinaryVector n => x (M (e,0))) h
  simpa [Finset.sum_apply,pairVector,smul_eq_mul] using he

end
end Holant.ReedMuller.LowArity
