import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroDescriptor

/-! Original raw-input bounds include the actual serialized coordinate metadata.
These are derived from valid original indices, not supplied size certificates. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroDescriptor
open Turing Computability BinaryCompose
variable {s b : ℕ} {arity : ℕ → ℕ}

/-- Both original query coordinates fit linearly within their own raw graph. -/
theorem input_length_le_original (x : Input (s := s) (b := b) (arity := arity)) :
    ((ResidualPinQuery.inputEncoding s b arity).encode x).length ≤
      5 * ((RawClosedNetwork.encoding.encode x.1.val).length+1) := by
  have hi := x.2.1.isLt
  have hv := framedListEncode_length_lower RawClosedNetwork.vertexEncoding x.1.val.vertices
  have hr : (RawClosedNetwork.encoding.encode x.1.val).length =
      2 * (framedListEncode RawClosedNetwork.vertexEncoding x.1.val.vertices).length + 1 +
        (framedListEncode encodingNatBool x.1.val.edges).length :=
    framedProductEncoding_length (framedListEncoding RawClosedNetwork.vertexEncoding) (framedListEncoding encodingNatBool) _
  have hq := NetworkLookup.query_bits_le x.1.val x.1.property (x.1.val.lookup x.1.property (x.2.2,false))
  have he : x.1.val.portEndpoint x.1.property (x.1.val.lookup x.1.property (x.2.2,false)) = (x.2.2.val,false) :=
    congrArg (fun p : Fin x.1.val.edges.length × Bool => (p.1.val,p.2)) (x.1.val.route_lookup x.1.property (x.2.2,false))
  rw [he] at hq
  simp only [RawClosedNetwork.endpointEncoding,framedProductEncoding_length,encodingNatBool,
    encodingBoolBool,encodeBool,List.length_singleton] at hq
  rw [ResidualPinQuery.input_length]
  omega

noncomputable def originalTimePolynomial (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) : Polynomial ℕ :=
  (timePolynomial s b arity a z).comp (5 * (Polynomial.X+1))

/-- The same concrete execution is polynomial in original raw graph bits alone. -/
noncomputable def timed_original (a z : Bool) (x : Input (s := s) (b := b) (arity := arity)) :
    TM2OutputsInTime (machine a z).computer ((ResidualPinQuery.inputEncoding s b arity).encode x)
      (some (descriptorBits a z x))
      ((originalTimePolynomial s b arity a z).eval (RawClosedNetwork.encoding.encode x.1.val).length) where
  steps := (timed a z x).steps
  evals_in_steps := (timed a z x).evals_in_steps
  steps_le_m := by
    have h := natPolynomial_eval_mono (timePolynomial s b arity a z) (input_length_le_original x)
    exact le_trans (timed a z x).steps_le_m (by simpa [originalTimePolynomial] using h)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroDescriptor
