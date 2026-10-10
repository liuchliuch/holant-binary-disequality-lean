import Holant.Proofs.Closure.RetainedSingle
import Holant.Proofs.Algorithms.RingHomDescent
import Holant.Proofs.Tetrahedral.CyclicResource.PhaseProvenance.FrozenSources

/-! Genuine mapped-current-family graph outputs are recovered in the ORIGINAL
field from their actual vertices and native edges. The same descended open graph
is saved, while an actual ordinary direct macro is compiled at the explicitly
charged P+output boundary, with the frozen original-G codecs in both directions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosurePhysicalBridge
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.GeneralExtraction
namespace RH
export Holant.LocalDrafts.MainChain.RingHomRealization (mapFamily mapSignature mapNetwork)
end RH

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

abbrev algebraicEmbedding : OI.K G →+* AlgebraicComplex :=
  (OriginalFrozenForest.OriginalInput.embedding G).toRingHom

abbrev complexEmbedding : OI.K G →+* ℂ :=
  CyclicBoundary.AlgebraicRepresentatives.inclusion.comp (algebraicEmbedding G)

variable {A : Type} [Field A] (φ : OI.K G →+* A) {n : ℕ}
variable (N : OpenNetwork A n)
variable (labels : ∀ v, (⟨N.shape.arity v,N.vertex v⟩ : AnySignature A) ∈ RH.mapFamily φ P.family)
variable (native : N.HasDefaultEdges .disequality)

structure OpenGraphAccess where
  sourceGraph : OpenNetwork (OI.K G) n
  sourceGraphIdentity : sourceGraph = RingHomDescent.descendNetwork φ N labels
  sameShape : sourceGraph.shape = N.shape
  sameEdges : HEq sourceGraph.edge N.edge
  mappedGraph : RH.mapNetwork φ sourceGraph = N
  output : Signature (OI.K G) n
  outputIdentity : output = sourceGraph.tensor
  mappedOutput : RH.mapSignature φ output = N.tensor
  actual : Gadget.Realizes P.family .disequality output
  power : GeneralPowerExposure.PowerMacro P.table output
  powerIdentity : power = DeckDirect.directPower P.table (P.retainsIdentity G) actual
  toOriginal : RetainedBranch.ToOriginalProgramme G P ⟨n,output⟩
  toOriginalIdentity : toOriginal = RetainedBranch.toOriginal G P ⟨n,output⟩ power
  fromOriginal : RetainedBranch.FromOriginalProgramme G P ⟨n,output⟩
  fromOriginalIdentity : fromOriginal = RetainedBranch.fromOriginal G P ⟨n,output⟩

/-- No output preimage, field extension, terminal compiler or local exit is
an input. Descent reads the literal mapped source labels of this exact graph. -/
def fromOpenGraph : OpenGraphAccess G P φ N labels := by
  let D := RingHomDescent.descendNetwork φ N labels
  have hactual : Gadget.Realizes P.family .disequality D.tensor :=
    ⟨D,RingHomDescent.descend_labels φ N labels,native,rfl⟩
  let M := DeckDirect.directPower P.table (P.retainsIdentity G) hactual
  exact ⟨D,rfl,rfl,HEq.rfl,RingHomDescent.map_descendNetwork φ N labels,
    D.tensor,rfl,RingHomDescent.descend_tensor φ N labels,hactual,M,rfl,
    RetainedBranch.toOriginal G P ⟨n,D.tensor⟩ M,rfl,
    RetainedBranch.fromOriginal G P ⟨n,D.tensor⟩,rfl⟩

/-- Full controlled equality, retaining machine, clock and source bytes. -/
theorem OpenGraphAccess.toOriginal_controlled
    (d : OpenGraphAccess G P φ N labels) : d.toOriginal.controlled =
    RetainedBranch.controlledToOriginal G P ⟨n,d.output⟩ d.power := by
  rw [d.toOriginalIdentity]
  rfl

theorem OpenGraphAccess.fromOriginal_controlled
    (d : OpenGraphAccess G P φ N labels) : d.fromOriginal.controlled =
    RetainedBranch.controlledFromOriginal G P ⟨n,d.output⟩ := by
  rw [d.fromOriginalIdentity]
  rfl

/-- An existential actual realization is converted into saved graph DATA and
both actual charged programmes. Its chosen witness is retained exactly. -/
structure ActualAccess (q : Signature A n) (actual : Gadget.Realizes (RH.mapFamily φ P.family) .disequality q) where
  graph : OpenNetwork A n
  graphIdentity : graph = Classical.choose actual
  labels : ∀ v, (⟨graph.shape.arity v,graph.vertex v⟩ : AnySignature A) ∈ RH.mapFamily φ P.family
  native : graph.HasDefaultEdges .disequality
  value : graph.tensor = q
  access : OpenGraphAccess G P φ graph labels
  mappedOutput : RH.mapSignature φ access.output = q

/-- The field-valued output is derived from the actual native source graph,
never assumed to be an arbitrary analytic value in the original field. -/
def fromActual (q : Signature A n) (actual : Gadget.Realizes (RH.mapFamily φ P.family) .disequality q) :
    ActualAccess G P φ q actual := by
  let N := Classical.choose actual
  have hN := Classical.choose_spec actual
  let d := fromOpenGraph G P φ N hN.1 hN.2.1
  exact ⟨N,rfl,hN.1,hN.2.1,hN.2.2,d,d.mappedOutput.trans hN.2.2⟩

/-- Agreement with the frozen actual-preimage theorem: injectivity makes its
source table identical to the graph-derived output, regardless of graph choice. -/
theorem agrees_with_actual_preimage {q : Signature ℂ n}
    (actual : Gadget.Realizes (RH.mapFamily (complexEmbedding G) P.family) .disequality q)
    (g : Signature (OI.K G) n)
    (mapped : RH.mapSignature (complexEmbedding G) g = q) :
    g = (fromActual G P (complexEmbedding G) q actual).access.output :=
  RingHomDescent.signature_injective (complexEmbedding G)
    (mapped.trans (fromActual G P (complexEmbedding G) q actual).mappedOutput.symm)

/-- The concrete frozen provenance theorem supplies its preimage internally. -/
def actualComplexPreimage {q : Signature ℂ n}
    (actual : Gadget.Realizes (RH.mapFamily (complexEmbedding G) P.family) .disequality q) :
    ∃ g : Signature (OI.K G) n, Gadget.Realizes P.family .disequality g ∧
      RH.mapSignature (complexEmbedding G) g = q :=
  Holant.LocalDrafts.TetrahedralCompletion.CyclicResource.PhaseProvenance.actual_preimage
    (complexEmbedding G) actual

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosurePhysicalBridge
