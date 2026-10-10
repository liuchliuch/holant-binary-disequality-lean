import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoRegularizeValue
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoMinimalLines
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsPins

/-! Genuine rank-two regularization in the original coefficient field. The
minimal pinning and every parity correction are flattened into unchanged
original f labels. The only residual branch is the three-odd-bundle supply;
otherwise one or four original rows form an actual non-Affine even block. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoActualSource
open Holant Holant.Tractable Holant.Algebraic
open OrdinaryNegativeSignedPortsCore OrdinaryNegativeRankTwoPorts
open OrdinaryNegativeRankTwoRegularize OrdinaryNegativeSparseRankDescent
open scoped BigOperators
namespace P
export OrdinaryNegativeSparseMinimalRank (PinWitness row)
end P
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end I
namespace S
export OrdinaryNegativeSignedRowsPins (block block_value)
end S
namespace R
export OrdinaryNegativeSignedRowsCore (trace_value)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {N : ℕ} {f : Signature K N}
variable (W : P.PinWitness f 2)

structure Data where
  count : ℕ
  rows : Fin count→Fin W.arity→Port 3
  bound : count≤4
  even : ∀j,Even (∑i,I.bundleSize (rows i) j)
  bad : ¬Affine (fun z=>∏i,P.row f W.pins (word (rows i) z))

variable (square : Affine (fun x=>(f x : AlgebraicComplex)^2))
variable (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (minor W.chart S z))

include square minimal in
/-- The recipe and branch selection are supplied internally from the actual
signed bundle sizes; caller-provided even gadgets or class conclusions are
not used. -/
theorem choose : (∀j,Odd (I.bundleSize (port W.chart) j)) ∨ Nonempty (Data W) := by
  rcases even_or_all_odd_or_line (port W.chart) with even|odd|⟨axis,lineOdd⟩
  · right
    refine ⟨⟨1,(fun _=>port W.chart),by decide,?_,?_⟩⟩
    · intro j
      simpa only [Fin.sum_univ_one] using even j
    · simpa only [Fin.prod_univ_one] using
        essential_nonaffine W.chart (W.square square) W.nonzero W.bad
  · exact Or.inl odd
  · right
    refine ⟨⟨4,rows (port W.chart) axis,by decide,even_rows _ axis lineOdd,?_⟩⟩
    have h := OrdinaryNegativeRankTwoRegularizeValue.trace_nonaffine W.chart axis
      (W.square square) W.nonzero W.bad
      (OrdinaryNegativeRankTwoMinimalLines.line_affine W.chart minimal axis)
    have he := funext (R.trace_value (P.row f W.pins) (rows (port W.chart) axis))
    rwa [he] at h

section Source
local instance : Algebra ℚ K := K.algebra'
variable {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (labels : Fin 4→Fin s)
variable (literal : ∀i,(⟨b (labels i).val,H (labels i)⟩ : AnySignature K)=⟨arity N i.val,table f i⟩)
variable (D : Data W)

def block := S.block W.pins W.pure H labels f literal D.rows D.even

theorem block_value (z : Fin 3→Bool) :
    (block W H labels literal D).signature H z=
      ∏i,f (Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor.substitute
        W.pins (word (D.rows i) z)) := S.block_value W.pins W.pure H labels f literal D.rows D.even z

/-- Non-Affineness belongs to the actual unchanged-field block that is sent
to the compiler, rather than to a merely semantic compressed signature. -/
theorem block_nonaffine :
    ¬Affine (fun z=>((block W H labels literal D).signature H z : AlgebraicComplex)) := by
  have he : (fun z=>((block W H labels literal D).signature H z : AlgebraicComplex))=
      (fun z=>∏i,P.row f W.pins (word (D.rows i) z)) := by
    funext z
    rw [block_value]
    change K.subtype (∏i,f (_))=∏i,K.subtype (f (_))
    exact map_prod K.subtype _ _
  rw [he]
  exact D.bad

end Source
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoActualSource
end
