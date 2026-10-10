import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingletonDescriptor

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingleton
open Turing Computability BinaryCompose
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

theorem input_length (x : Input s b arity) :
    ((inputEncoding s b arity).encode x).length =
      2*(RawClosedNetwork.encoding.encode x.val.1.val).length + 2*x.val.2.1.val +
      2*(encodeNat x.val.2.2.1.val).length +
      (RawClosedNetwork.endpointEncoding.encode (x.val.2.2.2.1.val,x.val.2.2.2.2)).length + 3 := by
  change (Holant.Algebraic.frame (RawClosedNetwork.encoding.encode x.val.1.val) ++
    (Holant.Algebraic.frame (List.replicate x.val.2.1.val true) ++
      (Holant.Algebraic.frame (encodeNat x.val.2.2.1.val) ++
        RawClosedNetwork.endpointEncoding.encode (x.val.2.2.2.1.val,x.val.2.2.2.2)))).length = _
  simp only [List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
  omega

/-- All coordinate metadata is bounded by the one original graph's own bits. -/
theorem input_length_le_original (x : Input s b arity) :
    ((inputEncoding s b arity).encode x).length ≤
      6*((RawClosedNetwork.encoding.encode x.val.1.val).length+1) := by
  have hi := x.val.2.1.isLt
  have hv := framedListEncode_length_lower RawClosedNetwork.vertexEncoding x.val.1.val.vertices
  have hr : (RawClosedNetwork.encoding.encode x.val.1.val).length =
      2*(framedListEncode RawClosedNetwork.vertexEncoding x.val.1.val.vertices).length+1+
        (framedListEncode encodingNatBool x.val.1.val.edges).length :=
    framedProductEncoding_length (framedListEncoding RawClosedNetwork.vertexEncoding) (framedListEncoding encodingNatBool) _
  have queryBound (q : Fin x.val.1.val.edges.length × Bool) :
      (RawClosedNetwork.endpointEncoding.encode (q.1.val,q.2)).length ≤
        (RawClosedNetwork.encoding.encode x.val.1.val).length := by
    have h := NetworkLookup.query_bits_le x.val.1.val x.val.1.property (x.val.1.val.lookup x.val.1.property q)
    have he : x.val.1.val.portEndpoint x.val.1.property (x.val.1.val.lookup x.val.1.property q) = (q.1.val,q.2) :=
      congrArg (fun p : Fin x.val.1.val.edges.length × Bool => (p.1.val,p.2))
        (x.val.1.val.route_lookup x.val.1.property q)
    simpa only [he] using h
  have hc := queryBound (x.val.2.2.1,false)
  have hp := queryBound x.val.2.2.2
  simp only [RawClosedNetwork.endpointEncoding,framedProductEncoding_length,encodingNatBool,
    encodingBoolBool,encodeBool,List.length_singleton] at hc
  rw [input_length]
  omega

noncomputable def originalTimePolynomial (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) : Polynomial ℕ :=
  (timePolynomial s b arity a z).comp (6*(Polynomial.X+1))

noncomputable def timed_original (a z : Bool) (x : Input s b arity) :
    TM2OutputsInTime (machine a z).computer ((inputEncoding s b arity).encode x)
      (some (descriptorBits a z x))
      ((originalTimePolynomial s b arity a z).eval (RawClosedNetwork.encoding.encode x.val.1.val).length) where
  steps := (timed a z x).steps
  evals_in_steps := (timed a z x).evals_in_steps
  steps_le_m := by
    have h := natPolynomial_eval_mono (timePolynomial s b arity a z) (input_length_le_original x)
    exact le_trans (timed a z x).steps_le_m (by simpa [originalTimePolynomial] using h)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingleton
