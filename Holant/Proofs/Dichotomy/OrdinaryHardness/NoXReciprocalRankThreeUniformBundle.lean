import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeAffinePorts
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseRankThreeActualSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralSeparateParity
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseRankThreeUniformSource

/-! Every explicitly supplied finite proper-face schedule preserves the
nonaffine rank-three core. Separate even counts then compile it physically. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeUniformBundle
open Holant Holant.Tractable
open OrdinaryNegativeSparseRankDescent
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace A
export NoXReciprocalRankThreeAffinePorts (Transform input input_pin input_affine transformed transformed_code)
end A
namespace P
export OrdinaryNegativeSparseRankThreePorts (port word_code)
export NoXSeparateSignedProjection (signedCount)
end P
namespace U
export OrdinaryNegativeSparseUniformMinimal (UniformPinWitness)
export OrdinaryNegativeAffineRankOne (uniform uniform_support uniform_square)
end U
namespace C
export OrdinaryNegativeSparseMixingAlpha (codeSeven codeSeven_affine multiply_affine_core)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {N l : ℕ} {f : Signature K N}
variable (W : U.UniformPinWitness f 3) (schedule : Fin l→A.Transform)
def rows : Fin (l+1)→Fin W.arity→Port 7 :=
  Fin.cases (P.port W.chart) (fun i=>A.transformed (P.port W.chart) (schedule i))
def factor (i : Fin l) (x : Fin 3→Bool) : AlgebraicComplex :=
  U.uniform (OrdinaryNegativeSparseMinimalRank.row f W.pins) (W.chart.encode (A.input (schedule i) x))
def multiplier : Signature AlgebraicComplex 3 := fun x=>∏i,factor W schedule i x

theorem multiplier_full (x : Fin 3→Bool) : multiplier W schedule x≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact (U.uniform_support _ _).mpr (W.chart.supported _)

variable (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Fin 3→Bool,Affine (U.uniform (minor W.chart S z)))
include minimal in
theorem factor_affine (i : Fin l) : Affine (factor W schedule i) :=
  W.affine_of_fixed_coordinate minimal (A.input (schedule i)) (A.input_affine (schedule i))
    (schedule i).base.axis (OrdinaryNegativeSparseRankThreeParity.bits (schedule i).shift (schedule i).base.axis)
    (A.input_pin (schedule i))

include minimal in
theorem multiplier_affine : Affine (multiplier W schedule) := by
  have h (s : Finset (Fin l)) : Affine (fun x=>∏i∈s,factor W schedule i x) := by
    induction s using Finset.induction_on with
    | empty=>simpa using affine_constant 3 1
    | @insert i s hi ih=>simpa only [Finset.prod_insert hi] using (factor_affine W schedule minimal i).mul ih
  exact h Finset.univ

theorem pullback (x : Fin 3→Bool) :
    (∏i : Fin (l+1),U.uniform (OrdinaryNegativeSparseMinimalRank.row f W.pins) (word (rows W schedule i) (C.codeSeven x)))=
      U.uniform (OrdinaryNegativeSparseMinimalRank.row f W.pins) (W.chart.encode x)*multiplier W schedule x := by
  rw [Fin.prod_univ_succ]
  simp only [rows,Fin.cases_zero,Fin.cases_succ,P.word_code,A.transformed_code]
  rfl

variable (square : Affine (fun x=>(f x : AlgebraicComplex)^2))
include minimal square in
theorem uniform_nonaffine : ¬Affine (fun z=>∏i : Fin (l+1),U.uniform (OrdinaryNegativeSparseMinimalRank.row f W.pins) (word (rows W schedule i) z)) := by
  let chart := OrdinaryNegativeSparseUniformMinimal.supportChart W.chart
    (fun x=>(U.uniform_support (OrdinaryNegativeSparseMinimalRank.row f W.pins) x).symm)
  have nz : U.uniform (OrdinaryNegativeSparseMinimalRank.row f W.pins)≠0 := by
    intro hz
    exact chart.supported (AffinePhase.origin 3) (congrFun hz _)
  have bad:=C.multiply_affine_core chart.reduced (multiplier W schedule)
    (chart.nonAffine_reduced (U.uniform_square _ (W.square square)) nz W.bad)
    (multiplier_affine W schedule minimal) (multiplier_full W schedule)
  dsimp [chart,OrdinaryNegativeAffineSystematicSupport.SystematicSupport.reduced,
    OrdinaryNegativeSparseUniformMinimal.supportChart] at bad
  intro aff
  apply bad
  have h:=aff.precompose C.codeSeven C.codeSeven_affine
  simpa only [pullback] using h

include minimal square in
theorem nonaffine
    (even : ∀q bit,Even (∑i,P.signedCount (rows W schedule i) q bit)) :
    ¬Affine (fun z=>∏i : Fin (l+1),OrdinaryNegativeSparseMinimalRank.row f W.pins
      (word (rows W schedule i) z)) := by
  exact OrdinaryNegativeSignedRowsUniform.actual_nonaffine
    (fun _ : Fin (l+1)=>OrdinaryNegativeSparseMinimalRank.row f W.pins)
    (rows W schedule) (NoXGeneralSeparateParity.total_even (rows W schedule) even)
    (uniform_nonaffine W schedule minimal square)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeUniformBundle
end
