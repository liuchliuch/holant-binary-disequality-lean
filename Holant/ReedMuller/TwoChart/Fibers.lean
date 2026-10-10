import Holant.ReedMuller.TwoChart.RadonCharts

/-! Literal signed localizer sums over an actual subspace. Matching the chart
character on that subspace prevents cancellation; the surviving factor is the
exact finite fiber cardinality. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

 def chartFiber (C : Chart n) (J : BinaryCode n) (x : BinaryVector n) : Finset J := by
  letI : Fintype J := Fintype.ofFinite J
  exact Finset.univ.filter (fun j => x+j.val-C.shift∈C.direction)

 def signedChartSum (C : Chart n) (J : BinaryCode n) (chi : Character n)
    (x : BinaryVector n) : AlgebraicComplex := by
  letI : Fintype J := Fintype.ofFinite J
  exact ∑ j : J,fourthRootPhase (evenLift (chi j.val))*C.eval (wordVector (x+j.val))

 theorem signedChartSum_eq_card (C : Chart n) (J : BinaryCode n) (chi : Character n)
    (hchi : ∀ j : J,chi j.val=C.character j.val) (x : BinaryVector n) :
    signedChartSum C J chi x=
      (chartFiber C J x).card*(C.scalar*fourthRootPhase (evenLift (C.character x))) := by
  letI : Fintype J := Fintype.ofFinite J
  have hterm (j : J) : fourthRootPhase (evenLift (chi j.val))*C.eval (wordVector (x+j.val))=
      if x+j.val-C.shift∈C.direction then
        C.scalar*fourthRootPhase (evenLift (C.character x)) else 0 := by
    simp only [Chart.eval,vector_word]
    split_ifs with h
    · have he : evenLift (chi j.val)+evenLift (C.character (x+j.val))=
          evenLift (C.character x) := by
        rw [←evenLift_add,hchi,map_add]
        congr 1
        have hh : C.character j.val+C.character j.val=0 := CharTwo.add_self_eq_zero _
        linear_combination hh
      calc
        fourthRootPhase (evenLift (chi j.val))*(C.scalar*fourthRootPhase (evenLift (C.character (x+j.val))))=
          C.scalar*fourthRootPhase (evenLift (chi j.val)+evenLift (C.character (x+j.val))) := by
            rw [fourthRootPhase_add];ring
        _=C.scalar*fourthRootPhase (evenLift (C.character x)) := by rw [he]
    · exact mul_zero _
  unfold signedChartSum
  simp_rw [hterm]
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  rfl

 theorem chartFiber_nonempty_iff (C : Chart n) (J : BinaryCode n) (x : BinaryVector n) :
    (chartFiber C J x).Nonempty ↔ ∃ j : J,x+j.val-C.shift∈C.direction := by
  simp only [chartFiber,Finset.filter_nonempty_iff,Finset.mem_univ,true_and]

 theorem signedChartSum_nonzero_iff (C : Chart n) (J : BinaryCode n) (chi : Character n)
    (hchi : ∀ j : J,chi j.val=C.character j.val) (x : BinaryVector n) :
    signedChartSum C J chi x≠0 ↔ ∃ j : J,x+j.val-C.shift∈C.direction := by
  rw [signedChartSum_eq_card C J chi hchi,mul_ne_zero_iff]
  have hc : C.scalar*fourthRootPhase (evenLift (C.character x))≠0 :=
    mul_ne_zero C.nonzero (fourthRootPhase_ne_zero _)
  simp only [hc,Nat.cast_ne_zero,ne_eq,Finset.card_eq_zero,not_false_eq_true,and_true]
  exact Finset.nonempty_iff_ne_empty.symm.trans (chartFiber_nonempty_iff C J x)

end
end Holant.ReedMuller.TwoChart
