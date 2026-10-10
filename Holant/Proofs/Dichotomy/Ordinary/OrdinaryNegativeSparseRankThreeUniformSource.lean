import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseRankThreeRegularization
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseUniformMinimal
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsUniform
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsPins

/-! Uniform-class seven-row rank-three regularization in the unchanged coefficient
field. A codeSeven pullback is only a semantic class test, never an available
XOR resource. Off-code support is unrestricted. Each of the six correction
factors is full on that pullback and Affine by a proper original pinning. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseRankThreeUniformSource
open Holant Holant.Tractable Holant.Algebraic
open OrdinaryNegativeSignedPortsCore OrdinaryNegativeSparseRankDescent
open scoped BigOperators
namespace U
export OrdinaryNegativeSparseUniformMinimal (UniformPinWitness supportChart)
export OrdinaryNegativeAffineRankOne (uniform uniform_support uniform_square)
end U
namespace P
export OrdinaryNegativeSparseRankThreeParity (schedule linearWord linearWord_pin linearWord_affine)
end P
namespace R
export OrdinaryNegativeSparseRankThreePorts (port word_code transformed_code)
export OrdinaryNegativeSparseRankThreeRegularization (pattern rows even_rows)
end R
namespace A
export OrdinaryNegativeSparseMixingAlpha (codeSeven codeSeven_affine multiply_affine_core)
end A
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end I
namespace S
export OrdinaryNegativeSignedRowsPins (block block_value)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false

variable {K : IntermediateField ℚ AlgebraicComplex} {N : ℕ} {f : Signature K N}
variable (W : U.UniformPinWitness f 3)

/-- The same literal support chart, with only its semantic row twisted. -/
def chart := U.supportChart W.chart
  (fun x=>(U.uniform_support (OrdinaryNegativeSparseMinimalRank.row f W.pins) x).symm)

theorem port_chart : R.port (chart W)=R.port W.chart := rfl

theorem nonzero : U.uniform (OrdinaryNegativeSparseMinimalRank.row f W.pins)≠0 := by
  intro hz
  exact (chart W).supported (AffinePhase.origin 3) (congrFun hz _)

def factor (i : Fin 6) (x : Fin 3→Bool) : AlgebraicComplex :=
  U.uniform (OrdinaryNegativeSparseMinimalRank.row f W.pins) (W.chart.encode (P.linearWord (P.schedule (R.pattern (R.port W.chart)) i) x))

def multiplier : Signature AlgebraicComplex 3 := fun x=>∏i : Fin 6,factor W i x

theorem factor_full (i : Fin 6) (x : Fin 3→Bool) : factor W i x≠0 :=
  (U.uniform_support _ _).mpr (W.chart.supported _)

theorem multiplier_full (x : Fin 3→Bool) : multiplier W x≠0 := by
  exact Finset.prod_ne_zero_iff.mpr (by intro i _;exact factor_full W i x)

variable (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Fin 3→Bool,Affine (U.uniform (minor W.chart S z)))

include minimal in
theorem factor_affine (i : Fin 6) : Affine (factor W i) := by
  let t := P.schedule (R.pattern (R.port W.chart)) i
  exact W.affine_of_fixed_coordinate minimal (P.linearWord t) (P.linearWord_affine t)
    t.axis false (P.linearWord_pin t)

include minimal in
theorem multiplier_affine : Affine (multiplier W) := by
  have h (s : Finset (Fin 6)) : Affine (fun x=>∏i∈s,factor W i x) := by
    induction s using Finset.induction_on with
    | empty=>simpa using affine_constant 3 1
    | @insert i s hi ih=>
      simpa only [Finset.prod_insert hi] using (factor_affine W minimal i).mul ih
  exact h Finset.univ

theorem pullback_value (x : Fin 3→Bool) :
    (∏i : Fin 7,U.uniform (OrdinaryNegativeSparseMinimalRank.row f W.pins) (word (R.rows (R.port W.chart) i) (A.codeSeven x)))=
      U.uniform (OrdinaryNegativeSparseMinimalRank.row f W.pins) (W.chart.encode x)*multiplier W x := by
  rw [Fin.prod_univ_succ]
  simp only [R.rows,Fin.cases_zero,Fin.cases_succ,R.word_code,R.transformed_code]
  rfl

variable (square : Affine (fun x=>(f x : AlgebraicComplex)^2))

include square minimal in
theorem uniform_rows_nonaffine :
    ¬Affine (fun z=>∏i : Fin 7,U.uniform (OrdinaryNegativeSparseMinimalRank.row f W.pins)
      (word (R.rows (R.port W.chart) i) z)) := by
  let chart := U.supportChart W.chart
    (fun x=>(U.uniform_support (OrdinaryNegativeSparseMinimalRank.row f W.pins) x).symm)
  have nz : U.uniform (OrdinaryNegativeSparseMinimalRank.row f W.pins)≠0 := by
    intro hz
    exact chart.supported (AffinePhase.origin 3) (congrFun hz _)
  have bad := A.multiply_affine_core chart.reduced (multiplier W)
    (chart.nonAffine_reduced (U.uniform_square _ (W.square square)) nz W.bad)
    (multiplier_affine W minimal) (multiplier_full W)
  dsimp [chart,OrdinaryNegativeAffineSystematicSupport.SystematicSupport.reduced,
    OrdinaryNegativeSparseUniformMinimal.supportChart] at bad
  intro h
  apply bad
  have pull := h.precompose A.codeSeven A.codeSeven_affine
  simpa only [pullback_value W] using pull

include square minimal in
theorem rows_nonaffine (h : ¬∀j,Odd (I.bundleSize (R.port W.chart) j)) :
    ¬Affine (fun z=>∏i : Fin 7,OrdinaryNegativeSparseMinimalRank.row f W.pins
      (word (R.rows (R.port W.chart) i) z)) := by
  exact OrdinaryNegativeSignedRowsUniform.actual_nonaffine
    (fun _ : Fin 7=>OrdinaryNegativeSparseMinimalRank.row f W.pins)
    (R.rows (R.port W.chart)) (R.even_rows _ h) (uniform_rows_nonaffine W minimal square)

structure Data where
  rows : Fin 7→Fin W.arity→Port 7
  even : ∀j,Even (∑i,I.bundleSize (rows i) j)
  bad : ¬Affine (fun z=>∏i,OrdinaryNegativeSparseMinimalRank.row f W.pins (word (rows i) z))

include square minimal in
/-- Except for the already-seven-odd branch, seven actual original-row
substitutions form an even resource outside Affine. -/
theorem choose : (∀j,Odd (I.bundleSize (R.port W.chart) j)) ∨ Nonempty (Data W) := by
  classical
  by_cases odd : ∀j,Odd (I.bundleSize (R.port W.chart) j)
  · exact Or.inl odd
  · exact Or.inr ⟨⟨R.rows (R.port W.chart),R.even_rows _ odd,rows_nonaffine W minimal square odd⟩⟩

section Source
local instance : Algebra ℚ K := K.algebra'
variable {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (labels : Fin 4→Fin s)
variable (literal : ∀i,(⟨b (labels i).val,H (labels i)⟩ : AnySignature K)=⟨arity N i.val,table f i⟩)
variable (D : Data W)

def block := S.block W.pins W.pure H labels f literal D.rows D.even

theorem block_value (z : Fin 7→Bool) :
    (block W H labels literal D).signature H z=
      ∏i,f (Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor.substitute
        W.pins (word (D.rows i) z)) := S.block_value W.pins W.pure H labels f literal D.rows D.even z

theorem block_nonaffine :
    ¬Affine (fun z=>((block W H labels literal D).signature H z : AlgebraicComplex)) := by
  have he : (fun z=>((block W H labels literal D).signature H z : AlgebraicComplex))=
      (fun z=>∏i,OrdinaryNegativeSparseMinimalRank.row f W.pins (word (D.rows i) z)) := by
    funext z
    rw [block_value]
    simp only [IntermediateField.coe_prod,OrdinaryNegativeSparseMinimalRank.row]
  rw [he]
  exact D.bad

end Source
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseRankThreeUniformSource
end
