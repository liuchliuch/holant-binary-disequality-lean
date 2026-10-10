import Holant.Certificates.TetrahedralOrientation.Coefficients
import Holant.Certificates.TetrahedralOrientation.RankCertificate
import Holant.Certificates.TetrahedralOrientation.CardValues

/-! Exact rank(2,2,2) proofs for both the actual raw cards and the normalized
printed terminals. Every factorization is checked against the reconstructed tensor. -/
namespace Holant.Certificates.TetrahedralOrientation
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

def rowNumbers (stage : Bool) : Orientation → Fin 3 → Fin 4 × Fin 4 :=
  if stage then ![![(0,3),(0,3),(0,3)],![(0,1),(0,1),(0,1)],![(0,1),(0,1),(0,1)]]
  else ![![(0,2),(0,2),(1,2)],![(0,1),(0,1),(0,1)],![(0,1),(0,1),(0,1)]]

def colNumbers (stage : Bool) : Orientation → Fin 3 → Fin 4 × Fin 4 :=
  if stage then ![![(0,3),(0,3),(0,3)],![(0,1),(0,1),(0,1)],![(0,1),(0,1),(0,1)]]
  else ![![(0,1),(0,1),(0,1)],![(0,2),(0,1),(0,1)],![(0,1),(0,2),(0,2)]]

def rowPivot (stage : Bool) (s : Orientation) (r : Fin 3) (b : Bool) : PairIndex :=
  swapPairOrder (if b then (rowNumbers stage s r).2 else (rowNumbers stage s r).1)
def colPivot (stage : Bool) (s : Orientation) (r : Fin 3) (b : Bool) : PairIndex :=
  swapPairOrder (if b then (colNumbers stage s r).2 else (colNumbers stage s r).1)

def stageMatrix (stage : Bool) (s : Orientation) (r : Fin 3) : PairMatrix :=
  flatten r (if stage then terminal s else card s)

theorem stage_minor_nonzero (stage : Bool) (s : Orientation) (r : Fin 3) :
    pivotMinor (stageMatrix stage s r) (rowPivot stage s r) (colPivot stage s r) ≠ 0 := by
  cases stage <;> fin_cases s <;> fin_cases r <;>
    norm_num [pivotMinor,stageMatrix,rowPivot,colPivot,rowNumbers,colNumbers,swapPairOrder,
      flatten,flatten0,flatten1,flatten2,terminal,evenTable,card_value,rawCardNumerator,smul_eq_mul] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.ext_iff]

theorem stage_factorization (stage : Bool) (s : Orientation) (r : Fin 3) :
    stageMatrix stage s r = rankLeft (stageMatrix stage s r) (rowPivot stage s r) (colPivot stage s r) *
      rankRight (stageMatrix stage s r) (rowPivot stage s r) := by
  cases stage <;> fin_cases s <;> fin_cases r <;> ext ⟨a,b⟩ ⟨c,d⟩ <;>
    cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [rankLeft,rankRight,pivotMinor,Matrix.mul_apply,stageMatrix,rowPivot,colPivot,
      rowNumbers,colNumbers,swapPairOrder,flatten,flatten0,flatten1,flatten2,terminal,evenTable,
      card_value,rawCardNumerator,smul_eq_mul] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.ext_iff] <;> ring

theorem stage_rank_two (stage : Bool) (s : Orientation) (r : Fin 3) : (stageMatrix stage s r).rank = 2 :=
  rank_two_of_certificate _ _ _ (stage_minor_nonzero stage s r) (stage_factorization stage s r)

theorem card_rank_two (s : Orientation) (r : Fin 3) : (flatten r (card s)).rank = 2 := stage_rank_two false s r

theorem terminal_rank_two (s : Orientation) (r : Fin 3) : (flatten r (terminal s)).rank = 2 := stage_rank_two true s r

theorem dressed_rank_two (s : Orientation) (r : Fin 3) : (flatten r (dressed s)).rank = 2 := by
  rw [dressed_exact,flatten_smul,Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero (rawScale_ne_zero s))]
  exact terminal_rank_two s r

end
end Holant.Certificates.TetrahedralOrientation
