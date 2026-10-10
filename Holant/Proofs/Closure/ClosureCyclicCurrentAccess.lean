import Holant.Proofs.Closure.ClosureCyclicCurrentCards
import Holant.Proofs.Closure.ProgrammeSaturation

/-! Exact graph descent and original-G charged access/saturation for the real
cyclic dispatch outputs. A projectively realized analytic output is stored as
its exact original-field graph tensor; its ambient scalar is retained explicitly.
No preimage of an arbitrary analytic coefficient is postulated. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable {n : ℕ} (target : Signature ℂ n)

structure ProjectiveOutput where
  multiplier : ℂ
  multiplierNonzero : multiplier ≠ 0
  actual : Gadget.Realizes
    (RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) P.family)
    .disequality (multiplier • target)
  graph : ClosurePhysicalBridge.ActualAccess G P (ClosurePhysicalBridge.complexEmbedding G)
    (multiplier • target) actual
  sameGraphFactory : graph = ClosurePhysicalBridge.fromActual G P
    (ClosurePhysicalBridge.complexEmbedding G) (multiplier • target) actual

def projectiveOutput (actual : Gadget.RealizesUpTo
    (RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) P.family)
    .disequality target) : ProjectiveOutput G P target := by
  let c := Classical.choose actual
  have h := Classical.choose_spec actual
  let d := ClosurePhysicalBridge.fromActual G P (ClosurePhysicalBridge.complexEmbedding G)
    (c • target) h.2
  exact ⟨c,h.1,h.2,d,rfl⟩

namespace ProjectiveOutput
variable (d : ProjectiveOutput G P target)
abbrev output : Signature (OI.K G) n := d.graph.access.output
abbrev toOriginal := d.graph.access.toOriginal
abbrev fromOriginal := d.graph.access.fromOriginal

theorem mapped : RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G)
    (output G P target d) = d.multiplier • target := d.graph.mappedOutput

theorem source_actual : Gadget.Realizes P.family .disequality (output G P target d) :=
  d.graph.access.actual

include d in
theorem source_nonzero (nonzero : target ≠ 0) : output G P target d ≠ 0 := by
  intro zero
  have h := mapped G P target d
  rw [zero] at h
  have h0 : d.multiplier • target = 0 := by
    rw [← h]
    funext x
    exact map_zero (ClosurePhysicalBridge.complexEmbedding G)
  exact (smul_ne_zero d.multiplierNonzero nonzero) h0

/-- Saturation chooses only this actual descended output's new factor tree;
every old whole tree remains unchanged, with both charged original-G directions. -/
def palette (positive : 0 < n) (nonzero : target ≠ 0) : Palette G :=
  ProgrammeSaturation.palette G P ⟨n,output G P target d⟩
    (source_nonzero G P target d nonzero) positive (source_actual G P target d)

@[simp] theorem palette_factory (positive : 0 < n) (nonzero : target ≠ 0) :
    palette G P target d positive nonzero = ProgrammeSaturation.palette G P ⟨n,output G P target d⟩
      (source_nonzero G P target d nonzero) positive (source_actual G P target d) := rfl

theorem old_saved (positive : 0 < n) (nonzero : target ≠ 0) (i : Fin P.count) :
    let Q := palette G P target d positive nonzero
    let j := RetainedFactorCatalogue.oldLabel G P ⟨n,output G P target d⟩
      (source_nonzero G P target d nonzero) i
    (⟨⟨Q.arity j.val,Q.table j⟩,Q.trees j⟩ : TreeOccurrence (OI.K G)) =
      ⟨⟨P.arity i.val,P.table i⟩,P.trees i⟩ :=
  ProgrammeSaturation.old_saved G P ⟨n,output G P target d⟩
    (source_nonzero G P target d nonzero) positive (source_actual G P target d) i

theorem root_saved (positive : 0 < n) (nonzero : target ≠ 0) :
    let Q := palette G P target d positive nonzero
    let j := RetainedFactorCatalogue.rootLabel G P ⟨n,output G P target d⟩
      (source_nonzero G P target d nonzero)
    (⟨⟨Q.arity j.val,Q.table j⟩,Q.trees j⟩ : TreeOccurrence (OI.K G)) =
      ⟨⟨n,output G P target d⟩,RetainedFactorCatalogue.tree G ⟨n,output G P target d⟩
        (source_nonzero G P target d nonzero)⟩ :=
  ProgrammeSaturation.root_saved G P ⟨n,output G P target d⟩
    (source_nonzero G P target d nonzero) positive (source_actual G P target d)

@[simp] theorem toOriginal_controlled : (toOriginal G P target d).controlled =
    RetainedBranch.controlledToOriginal G P ⟨n,output G P target d⟩ d.graph.access.power :=
  d.graph.access.toOriginal_controlled
@[simp] theorem fromOriginal_controlled : (fromOriginal G P target d).controlled =
    RetainedBranch.controlledFromOriginal G P ⟨n,output G P target d⟩ :=
  d.graph.access.fromOriginal_controlled

def toOriginal_prefix_costs := (toOriginal G P target d).primitives
def toOriginal_transcript_bits := (toOriginal G P target d).transcriptBits
def toOriginal_prefix_storage := (toOriginal G P target d).storage
def fromOriginal_prefix_costs := (fromOriginal G P target d).primitives
def fromOriginal_transcript_bits := (fromOriginal G P target d).transcriptBits
def fromOriginal_prefix_storage := (fromOriginal G P target d).storage

def palette_toOriginal_prefix_costs (positive : 0 < n) (nonzero : target ≠ 0) :=
  Palette.toOriginal_prefix_costs G (palette G P target d positive nonzero)
def palette_fromOriginal_prefix_costs (positive : 0 < n) (nonzero : target ≠ 0) :=
  Palette.fromOriginal_prefix_costs G (palette G P target d positive nonzero)
def palette_toOriginal_prefix_storage (positive : 0 < n) (nonzero : target ≠ 0) :=
  Palette.toOriginal_prefix_storage G (palette G P target d positive nonzero)
def palette_fromOriginal_prefix_storage (positive : 0 < n) (nonzero : target ≠ 0) :=
  Palette.fromOriginal_prefix_storage G (palette G P target d positive nonzero)
end ProjectiveOutput
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
