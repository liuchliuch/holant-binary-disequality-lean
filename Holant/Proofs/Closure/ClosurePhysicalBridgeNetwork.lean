import Holant.Proofs.Closure.ClosurePhysicalBridge
import Holant.Certificates.EqualityQuaternary.Source

/-! Exact ordinary-network descent, preserving every vertex, edge, port and
scalar component of the actual mapped-current-family source witness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosurePhysicalBridge
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.FinitePGL2.Stabilization

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) {A : Type} [Field A] (φ : OI.K G →+* A) {n : ℕ}
variable (N : Network A n)
variable (labels : ∀ v, (⟨N.shape.arity v,N.vertex v⟩ : AnySignature A) ∈ RH.mapFamily φ P.family)

abbrev nativeOpen := N.asOpen (fun _ => EdgeKind.disequality)

/-- The ordinary source vertex is exactly the vertex of the frozen descended
open graph. Incidence is the original N.shape; native edges keep their tags. -/
def sourceNetwork : Network (OI.K G) n where
  shape := N.shape
  vertex := (RingHomDescent.descendNetwork φ (nativeOpen N) labels).vertex
  edge := fun _ => Signature.disequality

@[simp] theorem sourceNetwork_asOpen :
    (sourceNetwork G P φ N labels).asOpen (fun _ => EdgeKind.disequality) =
      RingHomDescent.descendNetwork φ (nativeOpen N) labels := rfl

theorem sourceNetwork_uses (v : Fin N.shape.vertices) :
    (⟨(sourceNetwork G P φ N labels).shape.arity v,
      (sourceNetwork G P φ N labels).vertex v⟩ : AnySignature (OI.K G)) ∈ P.family :=
  RingHomDescent.descend_labels φ (nativeOpen N) labels v

theorem sourceNetwork_maps (native : ∀ e, N.edge e = Signature.disequality) :
    (sourceNetwork G P φ N labels).map φ = N := by
  cases N with
  | mk shape vertex edge =>
    unfold sourceNetwork Network.map
    dsimp only [nativeOpen,Network.asOpen,RingHomDescent.descendNetwork]
    congr 1
    · funext v x
      exact congrFun ((RingHomDescent.vertex_preimage φ (vertex v) (labels v)).choose_spec.2) x
    · funext e b c
      have he := native e
      change edge e = Signature.disequality at he
      rw [he]
      exact RingHomRealization.map_edge φ .disequality b c

structure NetworkGraphAccess where
  source : Network (OI.K G) n
  sourceIdentity : source = sourceNetwork G P φ N labels
  sameShape : source.shape = N.shape
  uses : ∀ v, (⟨source.shape.arity v,source.vertex v⟩ : AnySignature (OI.K G)) ∈ P.family
  native : ∀ e, source.edge e = Signature.disequality
  mappedNetwork : source.map φ = N
  access : OpenGraphAccess G P φ (nativeOpen N) labels
  sameOpenWitness : access.sourceGraph = source.asOpen (fun _ => EdgeKind.disequality)
  outputIdentity : access.output = source.denote
  mappedOutput : RH.mapSignature φ access.output = N.denote

/-- Concrete input is an actual native graph and its real mapped source labels.
Both charged original-G programmes are constructed inside `access`. -/
def fromNetwork (native : ∀ e, N.edge e = Signature.disequality) :
    NetworkGraphAccess G P φ N labels := by
  let D := sourceNetwork G P φ N labels
  let d := fromOpenGraph G P φ (nativeOpen N) labels (fun _ => rfl)
  have hd : d.output = D.denote := by
    rw [d.outputIdentity]
    change (RingHomDescent.descendNetwork φ (nativeOpen N) labels).tensor = D.denote
    rw [←sourceNetwork_asOpen G P φ N labels]
    exact D.tensor_asOpen (fun _ => EdgeKind.disequality) (fun _ => rfl)
  have hn : (nativeOpen N).tensor = N.denote :=
    N.tensor_asOpen (fun _ => EdgeKind.disequality) (fun e => (native e).symm)
  exact ⟨D,rfl,rfl,sourceNetwork_uses G P φ N labels,fun _ => rfl,
    sourceNetwork_maps G P φ N labels native,d,rfl,hd,d.mappedOutput.trans hn⟩

abbrev NetworkGraphAccess.output (d : NetworkGraphAccess G P φ N labels) := d.access.output
abbrev NetworkGraphAccess.toOriginal (d : NetworkGraphAccess G P φ N labels) := d.access.toOriginal
abbrev NetworkGraphAccess.fromOriginal (d : NetworkGraphAccess G P φ N labels) := d.access.fromOriginal

/-- The frozen coefficient-descent identity retains the entire original
ordinary graph, including loops, parallel edges and scalar-only components. -/
@[simp] theorem sourceNetwork_shape : (sourceNetwork G P φ N labels).shape = N.shape := rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosurePhysicalBridge
