import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching.Local


noncomputable section
namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching
open Holant
open scoped BigOperators
namespace Extensions

def paddedPartition (side : Bool) (m p : ℕ) (w : List Bool) : ℚ :=
  ∑ a : Fin p → Bool,
    OldTree.localPartition m
      (normalizedWord side w++List.ofFn (fun i => if side then !a i else a i)) *
        ∏ i : Fin p,paddingWeight side (a i)

/-- Summing real pad networks forces their main-vertex bits to side and
leaves two extensions per loop. No success/normalization/value-law input. -/
theorem padded_exact (side : Bool) (m p : ℕ) (w : List Bool)
    (hw : w.length+p=m+3) :
    paddedPartition side m p w=(2 : ℚ)^p*indicator side w := by
  classical
  let chosen : Fin p → Bool := fun _ => side
  have hpad : List.ofFn (fun i : Fin p => if side then !(chosen i) else chosen i)=
      List.replicate p false := by
    cases side <;> simp [chosen]
  have hlen : (normalizedWord side w++List.replicate p false).length=m+3 := by
    simpa [normalizedWord] using hw
  have hbase : OldTree.localPartition m
      (normalizedWord side w++List.replicate p false)=indicator side w := by
    rw [OldTree.local_partition_exact m _ hlen]
    simp [indicator,List.count_append,List.count_replicate]
  have hchosen : (∏ i : Fin p,paddingWeight side (chosen i))=(2 : ℚ)^p := by
    simp [chosen,padding_exact]
  unfold paddedPartition
  rw [Finset.sum_eq_single chosen]
  · rw [hpad,hbase,hchosen,mul_comm]
  · intro a _ha hne
    have hm : ∃ i : Fin p,a i≠side := by
      by_contra h
      push_neg at h
      apply hne
      funext i
      exact h i
    obtain ⟨i,hi⟩ := hm
    have hz : (∏ j : Fin p,paddingWeight side (a j))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [padding_exact,if_neg hi,mul_zero]
    rw [hz,mul_zero]
  · intro h
    exact (h (Finset.mem_univ chosen)).elim

def padding (d : ℕ) : ℕ := 3-d
def depth (d : ℕ) : ℕ := d-3
theorem degree_balance (d : ℕ) : d+padding d=depth d+3 := by
  unfold padding depth
  omega

/-- Degree zero is INCLUDED and yields a genuine zero tensor; a missing
row cannot be confused with the empty graph's multiplicative identity. -/
def degreePartition (side : Bool) (w : List Bool) : ℚ :=
  paddedPartition side (depth w.length) (padding w.length) w
theorem degree_exact (side : Bool) (w : List Bool) :
    degreePartition side w=(2 : ℚ)^(padding w.length)*indicator side w :=
  padded_exact side _ _ w (degree_balance w.length)
theorem isolated_exact (side : Bool) : degreePartition side []=0 := by
  rw [degree_exact]
  simp [indicator,normalizedWord]
theorem padding_le (d : ℕ) : padding d≤3 := Nat.sub_le _ _

end Extensions
end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching
