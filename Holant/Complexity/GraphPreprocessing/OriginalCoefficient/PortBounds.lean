import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.PortCleanup

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.PortLookup
open Computability Holant.Algebraic
variable {s b : ℕ} {arity : ℕ → ℕ}

private theorem drop_bits_le {A : Type} (e : Encoding A Bool) (xs : List A) (n : ℕ) :
    (framedListEncode e (xs.drop n)).length ≤ (framedListEncode e xs).length := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      have h := ih n
      simp only [List.drop_succ_cons, framedListEncode, List.length_cons, List.length_append]
      omega

/-- Copies, original inverse lookup, and all leftover stream cleanup are charged. -/
theorem ticks_le (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) :
    ticks r h p ≤ 27 * ((RawClosedNetwork.encoding.encode r).length + 1)^2 := by
  have ht := NetworkLookup.portTime_le r h p
  have hq := NetworkLookup.query_bits_le r h p
  have hp := drop_bits_le RawClosedNetwork.endpointEncoding (r.vertices.get p.1).2 (p.2.val+1)
  have hv := drop_bits_le RawClosedNetwork.vertexEncoding r.vertices (p.1.val+1)
  have he := NetworkLookup.element_bits_le RawClosedNetwork.vertexEncoding r.vertices
    (r.vertices.get p.1) (List.get_mem _ p.1)
  have hr : (RawClosedNetwork.vertexEncoding.encode (r.vertices.get p.1)).length =
      2 * (encodeNat (r.vertices.get p.1).1).length + 1 +
        (framedListEncode RawClosedNetwork.endpointEncoding (r.vertices.get p.1).2).length :=
    framedProductEncoding_length encodingNatBool (framedListEncoding RawClosedNetwork.endpointEncoding) _
  have hn : (RawClosedNetwork.encoding.encode r).length =
      2 * (framedListEncode RawClosedNetwork.vertexEncoding r.vertices).length + 1 +
        (framedListEncode encodingNatBool r.edges).length :=
    framedProductEncoding_length (framedListEncoding RawClosedNetwork.vertexEncoding) (framedListEncoding encodingNatBool) _
  unfold ticks
  nlinarith

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.PortLookup
