import Holant.Proofs.Closure.ClosureCyclicCurrentScalar
import Holant.Proofs.Closure.ClosureSixPortDescent

/-! The actual doubled branch has an exact original-field 2+2 factor split.
A factor is accessed through the genuine support-derived power macro and the
existing original-G machine; it is not assumed directly realized over P. The
actual square separately has its full old-tree-preserving saturated palette. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.Hardness.GeneralExtraction

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) {m : ℕ}
variable (d : CyclicBoundary.NonsquareExit.DoubledOutside
  (RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) P.family) m)

def doubledBinary : Signature ℂ 2 :=
  CyclicBoundary.ActualCards.physical₂ (CyclicBoundary.DihedralFactor.anti d.ratio)
def doubledTensor : Signature ℂ 4 := CyclicBoundary.NonsquareExit.doubled (doubledBinary G P d)

theorem doubledTensor_nonzero : doubledTensor G P d ≠ 0 := by
  have hn : doubledBinary G P d ≠ 0 := d.binary_nonzero
  obtain ⟨x,hx⟩ : ∃ x, doubledBinary G P d x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hn (funext h)
  intro zero
  have he := congrFun zero (fun i => Sum.elim x x
    ((CyclicBoundary.ZeroEndpointFactor.ports 0).symm i))
  have hval : doubledTensor G P d
      (fun i => Sum.elim x x ((CyclicBoundary.ZeroEndpointFactor.ports 0).symm i)) =
      doubledBinary G P d x * doubledBinary G P d x := by
    simp [doubledTensor,CyclicBoundary.NonsquareExit.doubled,Tensor.reindex,Tensor.tensor]
  exact (mul_ne_zero hx hx) (hval.symm.trans he)

def doubledOutput : ProjectiveOutput G P (doubledTensor G P d) :=
  projectiveOutput G P _ d.doubled_actual

def ambientDoubleSplit : ProperSplit
    (Holant.LocalDrafts.FinitePGL2.Stabilization.mapSignature
      (ClosurePhysicalBridge.complexEmbedding G) (⟨4,(doubledOutput G P d).output⟩ : AnySignature (OI.K G)))
    (⟨2,doubledBinary G P d⟩ : AnySignature ℂ) ⟨2,doubledBinary G P d⟩ where
  left_pos := by norm_num
  right_pos := by norm_num
  ports := CyclicBoundary.ZeroEndpointFactor.ports 0
  scale := Units.mk0 (doubledOutput G P d).multiplier (doubledOutput G P d).multiplierNonzero
  equation := by
    change RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G)
      (doubledOutput G P d).output = _
    rw [(doubledOutput G P d).mapped]
    rfl

/-- Exact same original partition, with ambient scale absorbed into a source
factor and the descended split normalized to scale one. -/
theorem originalDoubleSplit : ∃ u v : Signature (OI.K G) 2,
    ∃ split : ProperSplit (⟨4,(doubledOutput G P d).output⟩ : AnySignature (OI.K G)) ⟨2,u⟩ ⟨2,v⟩,
      split.ports = CyclicBoundary.ZeroEndpointFactor.ports 0 ∧ split.scale = 1 :=
  ClosureSixPort.exact_split_descent (ClosurePhysicalBridge.complexEmbedding G)
    ⟨4,(doubledOutput G P d).output⟩
    (ProjectiveOutput.source_nonzero G P (doubledTensor G P d) (doubledOutput G P d) (doubledTensor_nonzero G P d))
    (ambientDoubleSplit G P d)

structure OriginalDoubleFactors where
  left : Signature (OI.K G) 2
  right : Signature (OI.K G) 2
  split : ProperSplit (⟨4,(doubledOutput G P d).output⟩ : AnySignature (OI.K G)) ⟨2,left⟩ ⟨2,right⟩
  samePorts : split.ports = CyclicBoundary.ZeroEndpointFactor.ports 0
  unit : split.scale = 1

def doubleFactors : OriginalDoubleFactors G P d := by
  let hs := originalDoubleSplit G P d
  let left := Classical.choose hs
  let hs' := Classical.choose_spec hs
  let right := Classical.choose hs'
  let hs'' := Classical.choose_spec hs'
  let split := Classical.choose hs''
  have hp := Classical.choose_spec hs''
  exact ⟨left,right,split,hp.1,hp.2⟩

/-- The precise descended factor, not an independent analytic choice, supplies
its actual source-labelled power network and fully charged original-G machine. -/
def doubleFactorPower : GeneralPowerExposure.PowerMacro P.table (doubleFactors G P d).left :=
  Classical.choice ((doubleFactors G P d).split.left_power_labelled P.table
    (P.retainsIdentity G) (by norm_num) (mixedSupport_of_identity P.family (P.retainsIdentity G))
    (ProjectiveOutput.source_nonzero G P (doubledTensor G P d) (doubledOutput G P d) (doubledTensor_nonzero G P d))
    (doubledOutput G P d).source_actual)

def doubleFactorToOriginal : RetainedBranch.ToOriginalProgramme G P ⟨2,(doubleFactors G P d).left⟩ :=
  RetainedBranch.toOriginal G P _ (doubleFactorPower G P d)
def doubleFactorFromOriginal : RetainedBranch.FromOriginalProgramme G P ⟨2,(doubleFactors G P d).left⟩ :=
  RetainedBranch.fromOriginal G P _

@[simp] theorem doubleFactor_same_controlled :
    (doubleFactorToOriginal G P d).controlled = RetainedBranch.controlledToOriginal G P
      ⟨2,(doubleFactors G P d).left⟩ (doubleFactorPower G P d) := rfl
@[simp] theorem doubleFactor_reverse_controlled :
    (doubleFactorFromOriginal G P d).controlled = RetainedBranch.controlledFromOriginal G P
      ⟨2,(doubleFactors G P d).left⟩ := rfl

def doubleFactor_prefix_costs := (doubleFactorToOriginal G P d).primitives
def doubleFactor_transcript_bits := (doubleFactorToOriginal G P d).transcriptBits
def doubleFactor_prefix_storage := (doubleFactorToOriginal G P d).storage
def doubleFactor_reverse_prefix_costs := (doubleFactorFromOriginal G P d).primitives
def doubleFactor_reverse_transcript_bits := (doubleFactorFromOriginal G P d).transcriptBits
def doubleFactor_reverse_prefix_storage := (doubleFactorFromOriginal G P d).storage

def doubledPalette : Palette G :=
  ProjectiveOutput.palette G P (doubledTensor G P d) (doubledOutput G P d) (by norm_num) (doubledTensor_nonzero G P d)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
