import Holant.OneHot.Computable.Evaluation.OriginalNetwork
import Holant.OneHot.Computable.Tables

/-!
# Actual encoded connected trees to executable arithmetic programs

This completes the data-algorithm path from the framed Boolean encoding through
validation, original incidence lookup, computed parents, finite child lists and
literal semiring instructions. It is not a TM2 implementation or bit-time bound.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot.Computable.Graph

open Holant.OneHot.Decomposition

variable (g : Graph) (root : g.Vertex)

/-- The existing executed component search checks this finite predicate. -/
abbrev Connected := ∀ v, v ∈ g.reach root g.vertices

/-- The connected component is the full original vertex type, with unchanged IDs. -/
def fullVertexEquiv (hc : g.Connected root) : g.Fiber root ≃ g.Vertex where
  toFun := Subtype.val
  invFun v := ⟨v, hc v⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The connected component contains every original edge, retaining parallel IDs. -/
def fullEdgeEquiv (hc : g.Connected root) : g.FiberEdge root ≃ g.Edge where
  toFun := Subtype.val
  invFun e := ⟨e, hc (g.endpoint e false)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Computed parent data, on the full original finite index types. -/
def connectedSpanning (hc : g.Connected root) : RootedSpanning g.endpoint root :=
  Holant.OneHot.Computable.transportSpanning (g.fullVertexEquiv root hc)
    (g.fullEdgeEquiv root hc) (fun _ _ => rfl) (g.rootedSpanning root)

theorem connectedSpanning_depth_le (hc : g.Connected root) (v : g.Vertex) :
    (g.connectedSpanning root hc).depth v ≤ g.vertices := g.depth_le root _

end Holant.OneHot.Computable.Graph

namespace Holant.Complexity.RawClosedNetwork

open Holant.OneHot Holant.OneHot.Computable Holant.OneHot.Decomposition

variable {s b : ℕ} {arity : ℕ → ℕ} (r : RawClosedNetwork)

/-- Replace the old inverse-permutation choice with its verified finite lookup. -/
def executableShape (h : r.WellFormed s b arity) : Holant.NetworkShape 0 where
  vertices := r.vertices.length
  arity v := arity (r.vertices.get v).1
  edges := r.edges.length
  ports := (r.incidenceEquiv h).trans (closedEndsEquiv r.edges.length)

@[simp] theorem executableShape_eq (h : r.WellFormed s b arity) :
    r.executableShape h = r.shape h := by
  unfold executableShape shape
  rw [r.incidenceEquiv_eq h]

/-- The actual fixed-family input interpretation is now executable as well. -/
def executableRealize {K : Type*} (h : r.WellFormed s b arity)
    (signatures : (i : Fin s) → Holant.Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) : Holant.Network K 0 where
  shape := r.executableShape h
  vertex v x := signatures (r.signatureLabel h v) x
  edge e x y := kernels (r.edgeLabel h e) x y

@[simp] theorem executableRealize_eq {K : Type*} (h : r.WellFormed s b arity)
    (signatures : (i : Fin s) → Holant.Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) :
    r.executableRealize h signatures kernels = r.realize h signatures kernels := by
  unfold executableRealize realize
  congr 1
  exact r.executableShape_eq h

/-- Parent selection still uses the executed original edge-table scan. -/
def executableSpanning (h : r.WellFormed s b arity) (root : Fin r.vertices.length)
    (hc : (r.graph h).Connected root) : RootedSpanning (r.executableShape h).endpoint root :=
  transportSpanning (Equiv.refl _) (r.graphEdgeEquiv h)
    (fun e z => (r.graph_endpoint h e z).trans (r.lookup_vertex h _ z).symm)
    ((r.graph h).connectedSpanning root hc)

theorem executableSpanning_depth_le (h : r.WellFormed s b arity)
    (root : Fin r.vertices.length) (hc : (r.graph h).Connected root) (v : Fin r.vertices.length) :
    (r.executableSpanning h root hc).depth v ≤ r.vertices.length :=
  (r.graph h).connectedSpanning_depth_le root hc v

variable {K : Type*} [CommSemiring K]
variable (h : r.WellFormed s b arity)
variable (signatures : (i : Fin s) → Holant.Signature K (arity i.val))
variable (kernels : Fin b → Bool → Bool → K)

/-- Original labels and original incidence feed the actual recursive tree builder. -/
def executableTree (root : Fin r.vertices.length) (hc : (r.graph h).Connected root) : Tree K :=
  (r.executableRealize h signatures kernels).executableTree
    (r.executableSpanning h root hc) r.vertices.length

/-- Exact original input-network value and arithmetic count, using computed
parents and executable construction, without an assumed recursive decomposition. -/
theorem executableTree_program_spec (root : Fin r.vertices.length)
    (hc : (r.graph h).Connected root)
    (ht : r.edges.length + 1 = r.vertices.length)
    (hf : ∀ i, Holant.Signature.OneHot (signatures i))
    (hX : ∀ i, kernels i = Holant.Signature.disequality) :
    (r.executableTree h signatures kernels root hc).closedProgram.run =
      ((r.realize h signatures kernels).denote Fin.elim0,
        3 * r.vertices.length + 5 * r.edges.length - 1) := by
  have hn := (r.executableRealize h signatures kernels).executableTree_program_spec
    (r.executableSpanning h root hc) r.vertices.length
    (r.executableSpanning_depth_le h root hc) ht
    (fun v => hf (r.signatureLabel h v)) (fun e => hX (r.edgeLabel h e))
  have he := congrArg (fun N : Holant.Network K 0 => N.denote Fin.elim0)
    (r.executableRealize_eq h signatures kernels)
  rw [he] at hn
  exact hn

/-- Reject non-trees and disconnected records by executed finite tests. -/
def compileTree : Option (Arithmetic K K) :=
  if hn : 0 < r.vertices.length then
    let root : Fin r.vertices.length := ⟨0, hn⟩
    if hc : (r.graph h).Connected root then
      if r.edges.length + 1 = r.vertices.length then
        some (r.executableTree h signatures kernels root hc).closedProgram
      else none
    else none
  else none

/-- Every successful compiled program evaluates precisely the original record.
Malformed inputs are rejected by the decoder used in `compileTreeBits`. -/
theorem compileTree_spec
    (hf : ∀ i, Holant.Signature.OneHot (signatures i))
    (hX : ∀ i, kernels i = Holant.Signature.disequality)
    (p : Arithmetic K K) (hp : r.compileTree h signatures kernels = some p) :
    p.run = ((r.realize h signatures kernels).denote Fin.elim0,
      3 * r.vertices.length + 5 * r.edges.length - 1) := by
  unfold compileTree at hp
  split at hp
  · dsimp only at hp
    split at hp
    · split at hp
      · cases Option.some.inj hp
        exact r.executableTree_program_spec h signatures kernels _ _ (by assumption) hf hX
      · contradiction
    · contradiction
  · contradiction

end Holant.Complexity.RawClosedNetwork

namespace Holant.OneHot.Computable.Evaluation

open Holant.Complexity

/-- An actual Boolean input string is parsed, validated, tested and compiled. -/
def compileTreeBits {K : Type*} [CommSemiring K] (s b : ℕ) (arity : ℕ → ℕ)
    (signatures : (i : Fin s) → Holant.Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) (bits : List Bool) : Option (Arithmetic K K) :=
  ((RawClosedNetwork.validatedEncoding s b arity).decode bits).bind fun r =>
    r.1.compileTree r.2 signatures kernels

/-- The compiled program is produced from the real round-trip codec. -/
theorem compileTreeBits_encode {K : Type*} [CommSemiring K] {s b : ℕ} {arity : ℕ → ℕ}
    (signatures : (i : Fin s) → Holant.Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) (r : RawClosedNetwork)
    (h : r.WellFormed s b arity) :
    compileTreeBits s b arity signatures kernels (RawClosedNetwork.encoding.encode r) =
      r.compileTree h signatures kernels := by
  unfold compileTreeBits
  have hd := (RawClosedNetwork.validatedEncoding s b arity).decode_encode ⟨r, h⟩
  change (RawClosedNetwork.validatedEncoding s b arity).decode
    (RawClosedNetwork.encoding.encode r) = some ⟨r, h⟩ at hd
  rw [hd]
  rfl

end Holant.OneHot.Computable.Evaluation
