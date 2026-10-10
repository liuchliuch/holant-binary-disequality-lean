import Holant.Complexity.FramedEncoding
import Holant.Network
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Fintype.Card

/-!
# Framed closed-network input records

A vertex record explicitly stores its signature label and ordered endpoint list;
an edge record explicitly stores its edge-tensor label. Every record occupies bits,
including nullary vertices and zero labels. Validation checks label ranges, arities,
and a permutation of all edge ends. There are no free stubs; loops and parallel
edges are permitted. The decoder and its round-trip theorem are concrete.
-/

namespace Holant.Complexity

open Computability

abbrev RawEndpoint := ℕ × Bool
abbrev RawVertex := ℕ × List RawEndpoint

/-- A raw closed instance retains both vertex order and each vertex's port order. -/
structure RawClosedNetwork where
  vertices : List RawVertex
  edges : List ℕ
  deriving DecidableEq

namespace RawClosedNetwork

def endpointEncoding : Encoding RawEndpoint Bool :=
  framedProductEncoding encodingNatBool encodingBoolBool

def vertexEncoding : Encoding RawVertex Bool :=
  framedProductEncoding encodingNatBool (framedListEncoding endpointEncoding)

def encoding : Encoding RawClosedNetwork Bool where
  encode r := (framedProductEncoding (framedListEncoding vertexEncoding)
    (framedListEncoding encodingNatBool)).encode (r.vertices, r.edges)
  decode bits := ((framedProductEncoding (framedListEncoding vertexEncoding)
    (framedListEncoding encodingNatBool)).decode bits).map (fun p => ⟨p.1, p.2⟩)
  decode_encode r := by simp

/-- The input-length lower bound is proved for the actual serialization. Nullary
vertices and zero labels cannot be compressed away. -/
theorem counts_le_encoded_length (r : RawClosedNetwork) :
    r.vertices.length + r.edges.length ≤ (encoding.encode r).length := by
  have hv := framedListEncoding_length_lower vertexEncoding r.vertices
  have he := framedListEncoding_length_lower encodingNatBool r.edges
  change r.vertices.length + r.edges.length ≤
    ((framedProductEncoding (framedListEncoding vertexEncoding)
      (framedListEncoding encodingNatBool)).encode (r.vertices, r.edges)).length
  rw [framedProductEncoding_length]
  dsimp only at *
  omega

/-- All actual port occurrences, in vertex order and then port order. -/
def endpoints (r : RawClosedNetwork) : List RawEndpoint := (r.vertices.map Prod.snd).flatten

/-- Canonical list of two distinct ends for each labelled edge. -/
def expectedEndpoints (r : RawClosedNetwork) : List RawEndpoint :=
  (List.ofFn (fun e : Fin r.edges.length => [(e.val, false), (e.val, true)])).flatten

@[simp] theorem expectedEndpoints_length (r : RawClosedNetwork) :
    r.expectedEndpoints.length = r.edges.length * 2 := by
  simp [expectedEndpoints, List.length_flatten, List.map_ofFn, List.sum_ofFn]

/-- Executable closed-instance validation. The total arity function is consulted
only after the signature label range is also checked. -/
def WellFormed (signatureCount edgeLabelCount : ℕ) (arity : ℕ → ℕ) (r : RawClosedNetwork) : Prop :=
  (∀ v : Fin r.vertices.length,
    (r.vertices.get v).1 < signatureCount ∧
      (r.vertices.get v).2.length = arity (r.vertices.get v).1) ∧
  (∀ e : Fin r.edges.length, r.edges.get e < edgeLabelCount) ∧
  r.endpoints.Perm r.expectedEndpoints

instance wellFormedDecidable (signatureCount edgeLabelCount : ℕ) (arity : ℕ → ℕ)
    (r : RawClosedNetwork) : Decidable (r.WellFormed signatureCount edgeLabelCount arity) := by
  unfold WellFormed
  infer_instance

/-- A malformed record is rejected, while well-formed raw records carry their
validation proof forward. This parser performs no classical choice. -/
def validatedEncoding (signatureCount edgeLabelCount : ℕ) (arity : ℕ → ℕ) :
    Encoding { r : RawClosedNetwork // r.WellFormed signatureCount edgeLabelCount arity } Bool where
  encode r := encoding.encode r.val
  decode bits := (encoding.decode bits).bind (fun r =>
    if h : r.WellFormed signatureCount edgeLabelCount arity then some ⟨r, h⟩ else none)
  decode_encode r := by simp [r.property]

theorem validated_counts_le_length (signatureCount edgeLabelCount : ℕ) (arity : ℕ → ℕ)
    (r : { r : RawClosedNetwork // r.WellFormed signatureCount edgeLabelCount arity }) :
    r.val.vertices.length + r.val.edges.length ≤
      ((validatedEncoding signatureCount edgeLabelCount arity).encode r).length :=
  r.val.counts_le_encoded_length

end RawClosedNetwork
end Holant.Complexity
