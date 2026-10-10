import Holant.Certificates.TwelveLoops.Blocks0
import Holant.Certificates.TwelveLoops.Blocks1
import Holant.Certificates.TwelveLoops.Blocks2
import Holant.Certificates.TwelveLoops.Blocks3
import Holant.Certificates.TwelveLoops.Blocks4
import Holant.Certificates.TwelveLoops.Blocks5
import Holant.Certificates.TwelveLoops.Blocks6
import Holant.Certificates.TwelveLoops.Blocks7

namespace Holant.Certificates.TwelveLoops
open scoped BigOperators
theorem all_blocks_checked (x : AState) : blockHistogram x = printedBlocks x := by
  rcases x with ⟨i,j,k⟩
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact block000
  · exact block001
  · exact block002
  · exact block003
  · exact block010
  · exact block011
  · exact block012
  · exact block013
  · exact block020
  · exact block021
  · exact block022
  · exact block023
  · exact block030
  · exact block031
  · exact block032
  · exact block033
  · exact block100
  · exact block101
  · exact block102
  · exact block103
  · exact block110
  · exact block111
  · exact block112
  · exact block113
  · exact block120
  · exact block121
  · exact block122
  · exact block123
  · exact block130
  · exact block131
  · exact block132
  · exact block133
  · exact block200
  · exact block201
  · exact block202
  · exact block203
  · exact block210
  · exact block211
  · exact block212
  · exact block213
  · exact block220
  · exact block221
  · exact block222
  · exact block223
  · exact block230
  · exact block231
  · exact block232
  · exact block233
  · exact block300
  · exact block301
  · exact block302
  · exact block303
  · exact block310
  · exact block311
  · exact block312
  · exact block313
  · exact block320
  · exact block321
  · exact block322
  · exact block323
  · exact block330
  · exact block331
  · exact block332
  · exact block333

def routeCoordinate (r : Route) (v : ℕ × ℕ × ℕ) : ℕ :=
  match r with
  | .rankOne => v.1
  | .infiniteOrder => v.2.1
  | .remaining => v.2.2

theorem blockCount_eq (x : AState) (r : Route) :
    blockCount x r = routeCoordinate r (printedBlocks x) := by
  have h := congrArg (routeCoordinate r) (all_blocks_checked x)
  cases r <;> exact h

def routeCount (r : Route) : ℕ :=
  ((Finset.univ : Finset State).filter (fun s => classify s=r)).card

theorem routeCount_eq_sum (r : Route) : routeCount r = ∑ x : AState, blockCount x r := by
  simp only [routeCount,blockCount,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Fintype.sum_prod_type]

theorem deterministic_partition :
    Fintype.card State=16384 ∧ routeCount .rankOne=15792 ∧
    routeCount .infiniteOrder=224 ∧ routeCount .remaining=368 := by
  refine ⟨state_count,?_,?_,?_⟩
  all_goals rw [routeCount_eq_sum]
  all_goals simp_rw [blockCount_eq]
  all_goals decide

end Holant.Certificates.TwelveLoops
