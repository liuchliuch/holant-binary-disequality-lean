import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedSignedRows
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXRankThreeSupplier

/-! Both genuine rank-three suppliers with equal-fourth weighted anti gates.
The old semantic parity choice is retained, while every emitted signed edge
uses the actual anti label and its checked invertible Affine multiplier. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedRankThreeSupply
open Holant Holant.Tractable
open OrdinaryNegativeSignedPortsCore (Port word arity)
open OrdinaryNegativeSparseRankDescent
open scoped BigOperators
namespace P
export OrdinaryNegativeSparseMinimalRank (PinWitness row)
export OrdinaryNegativeSparseUniformMinimal (UniformPinWitness)
end P
namespace Q
export OrdinaryNegativeSparseRankThreePorts (port word_code)
export OrdinaryNegativeSparseRankThreeSupport (essential)
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end Q
namespace S
export OrdinaryNegativeSignedRowsPins (signedCompose word_compose bundleSize_compose)
end S
namespace Wt
export NoXWeightedSignedPorts (table weight_ne_zero)
end Wt
namespace R
export NoXWeightedSignedSource (signature oddResource ambient_value affine_iff alpha_iff)
end R
namespace U
export OrdinaryNegativeXUniversalResource (AlphaResource AffineResource EvenBad)
export OrdinaryNegativeAffineRankOne (uniform uniform_square)
end U
namespace A
export OrdinaryNegativeSparseRankThreeActualSource (choose)
end A
namespace V
export OrdinaryNegativeSparseRankThreeUniformSource (choose chart port_chart nonzero)
end V
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {N : ℕ} {f : Signature K N}
local instance : Algebra ℚ K := K.algebra'
variable {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (labels : Fin 4→Fin s)
variable (v w : K)
variable (literal : ∀i,(⟨b (labels i).val,H (labels i)⟩ : AnySignature K)=⟨arity N i.val,Wt.table f v w i⟩)
variable (hv : v≠0) (hw : w≠0) (fourth : (v : AlgebraicComplex)^4=(w : AlgebraicComplex)^4)
variable (square : Affine (fun x=>(f x : AlgebraicComplex)^2))

section Ordinary
variable (W : P.PinWitness f 3)
variable (odd : ∀j,Odd (Q.bundleSize (Q.port W.chart) j))
variable (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Fin 3→Bool,Affine (minor W.chart S z))

def p : Fin N→Port 7 := S.signedCompose W.pins (Q.port W.chart)

include odd in
theorem p_odd (j : Fin 7) : Odd (Q.bundleSize (p W) j) := by
  rw [p,S.bundleSize_compose W.pins W.pure]
  exact odd j

theorem original_value (z : Fin 7→Bool) : (f (word (p W) z) : AlgebraicComplex)=Q.essential W.chart z := by
  rw [p,S.word_compose]
  rfl

def alphaResource : U.AlphaResource H .seven where
  toOddResource := R.oddResource H labels f v w literal (p W) (p_odd W odd)
  alpha := by
    change Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action
      (fun z=>(R.signature H labels f v w literal (p W) z : AlgebraicComplex)))
    apply (R.alpha_iff H labels f v w literal (p W) hv hw fourth).mpr
    simp only [original_value]
    have present : ∀j,0<Q.bundleSize (Q.port W.chart) j := by
      intro j
      obtain ⟨k,hk⟩ := odd j
      omega
    exact OrdinaryNegativeSparseRankThreeAlphaLift.alpha_of_minimal W.chart present (W.square square)
      W.nonzero W.bad minimal
  full := by
    intro x
    change (R.signature H labels f v w literal (p W) (OrdinaryNegativeSparseMixingAlpha.codeSeven x) : AlgebraicComplex)≠0
    rw [R.ambient_value,original_value]
    apply mul_ne_zero (Wt.weight_ne_zero (v : AlgebraicComplex) (w : AlgebraicComplex)
      (fun h=>hv (Subtype.ext h)) (fun h=>hw (Subtype.ext h)) _ _)
    change P.row f W.pins (word (Q.port W.chart) (OrdinaryNegativeSparseMixingAlpha.codeSeven x))≠0
    rw [Q.word_code]
    exact W.chart.supported x

include literal hv hw fourth square minimal in
theorem ordinary : U.EvenBad H ∨ Nonempty (U.AlphaResource H .seven) := by
  rcases A.choose W minimal square with odd|data
  · exact Or.inr ⟨alphaResource H labels v w literal hv hw fourth square W odd minimal⟩
  · obtain ⟨data⟩ := data
    exact Or.inl (NoXWeightedSignedRows.evenBad H labels f v w literal W.pins W.pure
      data.rows data.even hv hw fourth data.bad)
end Ordinary

section Uniform
variable (W : P.UniformPinWitness f 3)
variable (odd : ∀j,Odd (Q.bundleSize (Q.port W.chart) j))
variable (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Fin 3→Bool,Affine (U.uniform (minor W.chart S z)))

def uniformP : Fin N→Port 7 := S.signedCompose W.pins (Q.port W.chart)

include odd in
theorem uniform_p_odd (j : Fin 7) : Odd (Q.bundleSize (uniformP W) j) := by
  rw [uniformP,S.bundleSize_compose W.pins W.pure]
  exact odd j

theorem uniform_original_value (z : Fin 7→Bool) :
    (f (word (uniformP W) z) : AlgebraicComplex)=Q.essential W.chart z := by
  rw [uniformP,S.word_compose]
  rfl

include square minimal odd in
theorem original_affine : Affine (Q.essential W.chart) := by
  have hsq := U.uniform_square _ (W.square square)
  have present : ∀j,0<Q.bundleSize (Q.port (V.chart W)) j := by
    rw [V.port_chart]
    intro j
    obtain ⟨k,hk⟩ := odd j
    omega
  have ha := OrdinaryNegativeSparseRankThreeAlphaLift.alpha (V.chart W) present hsq
    (OrdinaryNegativeRankThreeAlphaCore.uniform_minimal_phaseSeven_affine W.chart
      (W.square square) W.bad minimal)
  have ho : ∀j,Odd (∑i : Fin 1,Q.bundleSize ((fun _ : Fin 1=>Q.port W.chart) i) j) := by
    intro j
    simpa only [Fin.sum_univ_one] using odd j
  have hu : Affine (U.uniform (OrdinaryNegativeSignedRowsUniform.product
      (fun _ : Fin 1=>U.uniform (P.row f W.pins)) (fun _=>Q.port W.chart))) := by
    rw [OrdinaryNegativeSparseMixingAlpha.twist_action] at ha
    convert ha using 1
    funext z
    simp only [U.uniform,SymmetricBinaryPullback.localTwist_apply,Bool.true_and,
      OrdinaryNegativeSparseMixingAlpha.twist,OrdinaryNegativeSignedRowsUniform.product,Fin.prod_univ_one,
      Q.essential,V.port_chart]
  have actual := (OrdinaryNegativeSignedRowsUniformDouble.odd_double_affine_iff
    (fun _ : Fin 1=>P.row f W.pins) (fun _=>Q.port W.chart) ho).mp hu
  change Affine (fun z=>∏_i : Fin 1,P.row f W.pins (word (Q.port W.chart) z)) at actual
  change Affine (fun z=>P.row f W.pins (word (Q.port W.chart) z))
  simpa only [Fin.prod_univ_one] using actual

def affineResource : U.AffineResource H .seven where
  toOddResource := R.oddResource H labels f v w literal (uniformP W) (uniform_p_odd W odd)
  affine := by
    change Affine (fun z=>(R.signature H labels f v w literal (uniformP W) z : AlgebraicComplex))
    apply (R.affine_iff H labels f v w literal (uniformP W) hv hw fourth).mpr
    simp only [uniform_original_value]
    exact original_affine square W odd minimal
  full := by
    intro x
    change (R.signature H labels f v w literal (uniformP W) (OrdinaryNegativeSparseMixingAlpha.codeSeven x) : AlgebraicComplex)≠0
    rw [R.ambient_value,uniform_original_value]
    apply mul_ne_zero (Wt.weight_ne_zero (v : AlgebraicComplex) (w : AlgebraicComplex)
      (fun h=>hv (Subtype.ext h)) (fun h=>hw (Subtype.ext h)) _ _)
    change P.row f W.pins (word (Q.port W.chart) (OrdinaryNegativeSparseMixingAlpha.codeSeven x))≠0
    rw [Q.word_code]
    exact W.chart.supported x

include literal hv hw fourth square minimal in
theorem uniform : U.EvenBad H ∨ Nonempty (U.AffineResource H .seven) := by
  rcases V.choose W minimal square with odd|data
  · exact Or.inr ⟨affineResource H labels v w literal hv hw fourth square W odd minimal⟩
  · obtain ⟨data⟩ := data
    exact Or.inl (NoXWeightedSignedRows.evenBad H labels f v w literal W.pins W.pure
      data.rows data.even hv hw fourth data.bad)
end Uniform


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedRankThreeSupply
end
