import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoOddSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseUniformMinimal
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsUniform

/-! Uniform-bad rank-two parity regularization. Twisting is only a semantic
class test: every physical row is still the unchanged original-field pinning.
Even total signed incidence removes the octic gauge by a proved Affine
multiplier, producing an actual non-Affine original-label source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoUniformSource
open Holant Holant.Tractable Holant.Algebraic
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSignedPortsCore
open OrdinaryNegativeRankTwoPorts OrdinaryNegativeRankTwoRegularize
open OrdinaryNegativeSparseRankDescent
open scoped BigOperators
namespace W
export OrdinaryNegativeSparseUniformMinimal (UniformPinWitness supportChart)
export OrdinaryNegativeSparseMinimalRank (row)
end W
namespace U
export OrdinaryNegativeAffineRankOne (uniform uniform_square uniform_support)
end U
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end I
namespace G
export OrdinaryNegativeSignedRowsUniform (product actual_nonaffine)
end G
namespace P
export OrdinaryNegativeSparsePinTwist (uniform_pin_affine_iff)
end P
namespace S
export OrdinaryNegativeSignedRowsPins (block block_value)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {N : ℕ} {f : Signature K N}
variable (W : W.UniformPinWitness f 2)

def chart : SystematicSupport (U.uniform (OrdinaryNegativeSparseMinimalRank.row f W.pins)) 2 :=
  OrdinaryNegativeSparseUniformMinimal.supportChart W.chart
    (fun z=>(U.uniform_support (OrdinaryNegativeSparseMinimalRank.row f W.pins) z).symm)

theorem port_chart : port (chart W)=port W.chart := rfl

theorem nonzero : U.uniform (OrdinaryNegativeSparseMinimalRank.row f W.pins)≠0 := by
  intro hz
  exact (chart W).supported (fun _=>false) (congrFun hz _)

variable (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,
  Affine (U.uniform (minor W.chart S z)))

include minimal in
theorem chart_minimal (T : Finset (Fin 2)) (ht : T.card<2) (z : Fin 2→Bool) :
    Affine (minor (chart W) T z) := by
  change Affine (literal (U.uniform (OrdinaryNegativeSparseMinimalRank.row f W.pins))
    (remaining W.chart T) (W.chart.encode z))
  rw [literal_substitution]
  apply (P.uniform_pin_affine_iff (OrdinaryNegativeSparseMinimalRank.row f W.pins)
    (substitution (remaining W.chart T) (W.chart.encode z)) (substitution_unique _ _)).mpr
  have h := minimal T ht z
  unfold minor at h
  rwa [literal_substitution] at h

structure Data where
  count : ℕ
  rows : Fin count→Fin W.arity→Port 3
  bound : count≤4
  even : ∀j,Even (∑i,I.bundleSize (rows i) j)
  bad : ¬Affine (fun z=>∏i,OrdinaryNegativeSparseMinimalRank.row f W.pins (word (rows i) z))

variable (square : Affine (fun x=>(f x : AlgebraicComplex)^2))
include square minimal in
theorem choose : (∀j,Odd (I.bundleSize (port W.chart) j)) ∨ Nonempty (Data W) := by
  let hsq := U.uniform_square _ (W.square square)
  rcases even_or_all_odd_or_line (port W.chart) with even|odd|⟨axis,lineOdd⟩
  · right
    have counts : ∀j,Even (∑i : Fin 1,I.bundleSize ((fun _ : Fin 1=>port W.chart) i) j) := by
      intro j;simpa only [Fin.sum_univ_one] using even j
    refine ⟨⟨1,(fun _=>port W.chart),by decide,counts,?_⟩⟩
    have ht := essential_nonaffine (chart W) hsq (nonzero W) W.bad
    have ht' : ¬Affine (G.product (fun _ : Fin 1=>U.uniform (OrdinaryNegativeSparseMinimalRank.row f W.pins))
        (fun _=>port W.chart)) := by
      change ¬Affine (fun z=>∏_i : Fin 1,U.uniform (OrdinaryNegativeSparseMinimalRank.row f W.pins) (word (port W.chart) z))
      simpa only [Fin.prod_univ_one,port_chart] using ht
    exact G.actual_nonaffine (fun _ : Fin 1=>OrdinaryNegativeSparseMinimalRank.row f W.pins)
      (fun _=>port W.chart) counts ht'
  · exact Or.inl odd
  · right
    have counts := even_rows (port W.chart) axis lineOdd
    refine ⟨⟨4,rows (port W.chart) axis,by decide,counts,?_⟩⟩
    have ht := OrdinaryNegativeRankTwoRegularizeValue.trace_nonaffine (chart W) axis hsq (nonzero W) W.bad
      (OrdinaryNegativeRankTwoMinimalLines.line_affine (chart W) (chart_minimal W minimal) axis)
    have ht' : ¬Affine (G.product (fun _ : Fin 4=>U.uniform (OrdinaryNegativeSparseMinimalRank.row f W.pins))
        (rows (port W.chart) axis)) := by
      have he := funext (OrdinaryNegativeSignedRowsCore.trace_value
        (U.uniform (OrdinaryNegativeSparseMinimalRank.row f W.pins)) (rows (port W.chart) axis))
      rw [port_chart,he] at ht
      exact ht
    exact G.actual_nonaffine (fun _ : Fin 4=>OrdinaryNegativeSparseMinimalRank.row f W.pins)
      (rows (port W.chart) axis) counts ht'

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

theorem block_nonaffine :
    ¬Affine (fun z=>((block W H labels literal D).signature H z : AlgebraicComplex)) := by
  have he : (fun z=>((block W H labels literal D).signature H z : AlgebraicComplex))=
      (fun z=>∏i,OrdinaryNegativeSparseMinimalRank.row f W.pins (word (D.rows i) z)) := by
    funext z
    rw [block_value]
    change K.subtype (∏i,f (_))=∏i,K.subtype (f (_))
    exact map_prod K.subtype _ _
  rw [he]
  exact D.bad
end Source
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoUniformSource
end
