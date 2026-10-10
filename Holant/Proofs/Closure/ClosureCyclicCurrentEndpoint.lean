import Holant.Proofs.Closure.ClosureCyclicCurrentScalar

/-! Real cyclic endpoint and outside-card alternatives carry exact descended
original-field tables, original-G physical programmes and saturated palettes.
The source endpoint's support, both endpoints and primality are preserved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Projective.CyclicQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.Pauli.ExoticKlein.Fiber
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

structure EndpointReceipt where
  target : Signature ℂ 4
  actual : Gadget.RealizesUpTo
    (RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) P.family) .disequality target
  even : EvenSupported target
  endpoint0 : target (fun _ => false) ≠ 0
  endpoint1 : target (fun _ => true) ≠ 0
  prime : ¬HasProperTensorFactor target
  access : ProjectiveOutput G P target
  factory : access = projectiveOutput G P target actual

namespace EndpointReceipt
variable (e : EndpointReceipt G P)
abbrev output := e.access.output

theorem target_nonzero : e.target ≠ 0 := fun zero => e.endpoint0 (congrFun zero (fun _ => false))

theorem source_prime : Prime (⟨4,output G P e⟩ : AnySignature (OI.K G)) :=
  ProjectiveOutput.source_prime G P e.target e.access ((PrimalityInterfaces.retained_complex_prime e.target).mpr
    ⟨target_nonzero G P e,e.prime⟩)

theorem source_even : EvenSupported (output G P e) := by
  intro w odd
  apply (ClosurePhysicalBridge.complexEmbedding G).injective
  have h := congrFun e.access.mapped w
  rw [map_zero]
  simpa only [RingHomRealization.mapSignature,Pi.smul_apply,smul_eq_mul,e.even w odd,mul_zero] using h

theorem source_endpoint0 : output G P e (fun _ => false) ≠ 0 := by
  intro zero
  have h := congrFun e.access.mapped (fun _ => false)
  change ClosurePhysicalBridge.complexEmbedding G (output G P e (fun _ => false)) =
    e.access.multiplier * e.target (fun _ => false) at h
  rw [zero,map_zero] at h
  exact (mul_ne_zero e.access.multiplierNonzero e.endpoint0) h.symm

theorem source_endpoint1 : output G P e (fun _ => true) ≠ 0 := by
  intro zero
  have h := congrFun e.access.mapped (fun _ => true)
  change ClosurePhysicalBridge.complexEmbedding G (output G P e (fun _ => true)) =
    e.access.multiplier * e.target (fun _ => true) at h
  rw [zero,map_zero] at h
  exact (mul_ne_zero e.access.multiplierNonzero e.endpoint1) h.symm

abbrev toOriginal := e.access.toOriginal
abbrev fromOriginal := e.access.fromOriginal
def palette : Palette G := ProjectiveOutput.palette G P e.target e.access (by norm_num) (target_nonzero G P e)
end EndpointReceipt

/-- Concrete resource factory for the actual chosen source theorem endpoint. -/
def endpointReceipt (h : CyclicBoundary.SourceDispatch.EndpointOutput
    (RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) P.family)) :
    EndpointReceipt G P := by
  let target := Classical.choose h
  have properties := Classical.choose_spec h
  let d := projectiveOutput G P target properties.1
  exact ⟨target,properties.1,properties.2.1,properties.2.2.1,properties.2.2.2.1,
    properties.2.2.2.2,d,rfl⟩

structure OutsideReceipt (m : ℕ) where
  card : CyclicBoundary.ActualCards.OutsideCard
    (RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) P.family) m
  access : ProjectiveOutput G P card.signature
  factory : access = projectiveOutput G P card.signature card.actual

def outsideReceipt {m : ℕ} (card : CyclicBoundary.ActualCards.OutsideCard
    (RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) P.family) m) :
    OutsideReceipt G P m := ⟨card,projectiveOutput G P _ card.actual,rfl⟩

namespace OutsideReceipt
variable {m : ℕ} (o : OutsideReceipt G P m)
abbrev output := o.access.output
abbrev toOriginal := o.access.toOriginal
abbrev fromOriginal := o.access.fromOriginal
def palette : Palette G := ProjectiveOutput.palette G P o.card.signature o.access (by norm_num) o.card.nonzero

theorem source_outside : ¬CP.IsPhase m (CyclicBoundary.ActualCards.walshTransfer
    (RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) (output G P o))) :=
  ProjectiveOutput.source_outside G P o.card.signature o.access o.card.outside
end OutsideReceipt

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
