import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseRankThreeAlphaLift
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseRankThreeUniformSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsUniformDouble

/-! The uniform-bad residual rank-three seven-odd-bundle resource is an actual original
label recipe. It has odd boundary incidence, even private and constant
incidence, exact coefficients, and internally proved canonical support and
Affine class. Later even outer gadgets may flatten this literal recipe. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseRankThreeUniformOddSource
open Holant Holant.Tractable Holant.Algebraic
open OrdinaryNegativeMixedBlockData OrdinaryNegativeSignedPortsCore
namespace P
export OrdinaryNegativeSparseUniformMinimal (UniformPinWitness)
export OrdinaryNegativeSparseMinimalRank (row)
end P
namespace Q
export OrdinaryNegativeSparseRankThreePorts (port)
export OrdinaryNegativeSparseRankThreeSupport (essential support_iff)
end Q
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize external_count private_count constant_count)
end I
namespace S
export OrdinaryNegativeSignedRowsPins (signedCompose word_compose bundleSize_compose)
end S
namespace R
export OrdinaryNegativeMixedBlockRelabel (exactRecipe ports_eq coefficient_eq)
end R
namespace M
export OrdinaryNegativeMixedBlockSource (trace)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {N : ℕ} {f : Signature K N}
local instance : Algebra ℚ K := K.algebra'
variable (W : P.UniformPinWitness f 3)
variable {s : ℕ} {b : ℕ→ℕ} (H : (j : Fin s)→Signature K (b j.val)) (labels : Fin 4→Fin s)
variable (literal : ∀i,(⟨b (labels i).val,H (labels i)⟩ : AnySignature K)=⟨arity N i.val,table f i⟩)

def p : Fin N→Port 7 := S.signedCompose W.pins (Q.port W.chart)

def recipe : Recipe (u:=1) (s:=s) (a:=fun _=>7+N) (b:=b) :=
  R.exactRecipe labels (table f) H literal (OrdinaryNegativeSignedPortsCore.recipe (p W))

def signature : Signature K 7 := M.trace H N (recipe W H labels literal) 0

theorem value (z : Fin 7→Bool) :
    (signature W H labels literal z : AlgebraicComplex)=Q.essential W.chart z := by
  unfold signature M.trace recipe
  simp_rw [R.coefficient_eq]
  change (OrdinaryNegativeSignedPortsCore.trace (K:=K) f (p W) z : AlgebraicComplex)=_
  rw [OrdinaryNegativeSignedPortsCore.trace_value,p,S.word_compose]
  rfl

theorem port_counts (q : Bool ⊕ Fin (7+N)) :
    (ports (recipe W H labels literal) 0).count q=
      (ports (OrdinaryNegativeSignedPortsCore.recipe (p W)) 0).count q := by
  unfold recipe OrdinaryNegativeMixedBlockRelabel.exactRecipe
  rw [R.ports_eq]

theorem private_even (i : Fin N) :
    Even ((ports (recipe W H labels literal) 0).count (Sum.inr (privatePort (m:=7) i))) := by
  rw [port_counts,I.private_count]
  decide

theorem constant_even (c : Bool) :
    Even ((ports (recipe W H labels literal) 0).count (Sum.inl c)) := by
  rw [port_counts,I.constant_count]
  exact Even.mul_right (by decide : Even 2) _

variable (odd : ∀j,Odd (I.bundleSize (Q.port W.chart) j))
include odd in
theorem boundary_odd (j : Fin 7) :
    Odd ((ports (recipe W H labels literal) 0).count (Sum.inr (external (n:=N) j))) := by
  rw [port_counts,I.external_count,p,S.bundleSize_compose W.pins W.pure]
  exact odd j

include odd in
theorem all_present : ∀j,0<I.bundleSize (Q.port W.chart) j := by
  intro j
  rcases odd j with ⟨k,hk⟩
  omega

include odd in
theorem support_exact (z : Fin 7→Bool) :
    (signature W H labels literal z : AlgebraicComplex)≠0 ↔ z=OrdinaryNegativeSparseMixingAlpha.codeSeven ![z 0,z 1,z 2] := by
  rw [value]
  exact Q.support_iff W.chart (all_present W odd) z

namespace U
export OrdinaryNegativeAffineRankOne (uniform uniform_square)
end U
namespace G
export OrdinaryNegativeSignedRowsUniform (product)
end G
namespace T
export OrdinaryNegativeSparseRankThreeUniformSource (chart port_chart nonzero)
end T

variable (square : Affine (fun x=>(f x : AlgebraicComplex)^2))
variable (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Fin 3→Bool,
  Affine (U.uniform (OrdinaryNegativeSparseRankDescent.minor W.chart S z)))

include square minimal odd in
/-- The actual unchanged-field odd resource lies in A. The semantic input
uniform twist and its output uniform twist cancel by the proved odd gauge. -/
theorem affine : Affine (fun z=>(signature W H labels literal z : AlgebraicComplex)) := by
  have hsq := U.uniform_square _ (W.square square)
  have present : ∀j,0<I.bundleSize (Q.port (T.chart W)) j := by
    rw [T.port_chart]
    exact all_present W odd
  have ha := OrdinaryNegativeSparseRankThreeAlphaLift.alpha (T.chart W) present hsq
    (OrdinaryNegativeRankThreeAlphaCore.uniform_minimal_phaseSeven_affine W.chart
      (W.square square) W.bad minimal)
  have ho : ∀j,Odd (∑i : Fin 1,I.bundleSize ((fun _ : Fin 1=>Q.port W.chart) i) j) := by
    intro j
    simpa only [Fin.sum_univ_one] using odd j
  have hu : Affine (U.uniform (G.product
      (fun _ : Fin 1=>U.uniform (P.row f W.pins)) (fun _=>Q.port W.chart))) := by
    rw [OrdinaryNegativeSparseMixingAlpha.twist_action] at ha
    convert ha using 1
    funext z
    simp only [U.uniform,SymmetricBinaryPullback.localTwist_apply,Bool.true_and,
      OrdinaryNegativeSparseMixingAlpha.twist,G.product,Fin.prod_univ_one,
      OrdinaryNegativeSparseRankThreeSupport.essential,T.port_chart]
  have actual := (OrdinaryNegativeSignedRowsUniformDouble.odd_double_affine_iff
    (fun _ : Fin 1=>P.row f W.pins) (fun _=>Q.port W.chart) ho).mp hu
  have he : (fun z=>(signature W H labels literal z : AlgebraicComplex))=Q.essential W.chart :=
    funext (value W H labels literal)
  rw [he]
  change Affine (fun z=>∏_i : Fin 1,P.row f W.pins (word (Q.port W.chart) z)) at actual
  unfold OrdinaryNegativeSparseRankThreeSupport.essential
  simpa only [Fin.prod_univ_one] using actual

include square odd in
/-- The A-type resource still rejects the uniform/alpha class, retaining
the precise obstruction selected by the actual original pinning. -/
theorem not_alpha : ¬Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action
    (fun z=>(signature W H labels literal z : AlgebraicComplex))) := by
  have bad := OrdinaryNegativeSparseRankThreeSupport.essential_nonaffine (T.chart W)
    (U.uniform_square _ (W.square square)) (T.nonzero W) W.bad
  have ho : ∀j,Odd (∑i : Fin 1,I.bundleSize ((fun _ : Fin 1=>Q.port W.chart) i) j) := by
    intro j
    simpa only [Fin.sum_univ_one] using odd j
  intro ha
  rw [OrdinaryNegativeSparseMixingAlpha.twist_action] at ha
  have he : (fun z=>(signature W H labels literal z : AlgebraicComplex))=Q.essential W.chart :=
    funext (value W H labels literal)
  simp_rw [value] at ha
  have hu : Affine (U.uniform (G.product (fun _ : Fin 1=>P.row f W.pins) (fun _=>Q.port W.chart))) := by
    convert ha using 1
    funext z
    simp only [U.uniform,SymmetricBinaryPullback.localTwist_apply,Bool.true_and,
      OrdinaryNegativeSparseMixingAlpha.twist,G.product,Fin.prod_univ_one,
      OrdinaryNegativeSparseRankThreeSupport.essential]
  have ht := (OrdinaryNegativeSignedRowsUniformOdd.affine_iff
    (fun _ : Fin 1=>P.row f W.pins) (fun _=>Q.port W.chart) ho).mpr hu
  apply bad
  change Affine (fun z=>∏_i : Fin 1,U.uniform (P.row f W.pins) (word (Q.port W.chart) z)) at ht
  unfold OrdinaryNegativeSparseRankThreeSupport.essential
  rw [T.port_chart]
  simpa only [Fin.prod_univ_one] using ht

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseRankThreeUniformOddSource
end
