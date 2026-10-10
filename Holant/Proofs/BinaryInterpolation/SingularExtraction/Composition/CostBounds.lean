import Holant.Proofs.BinaryInterpolation.SingularExtraction.Composition.SourceEndpoint


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Composition.CostBounds
open Holant Holant.Tractable Holant.Complexity
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (hs : ¬ CommonOneSided (Set.range (fun i => (⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex))))
variable (u v : Bool → AlgebraicComplex) (hu : u ≠ 0) (hv : v ≠ 0)
variable (hB : Gadget.Realizes (Set.range (fun i => (⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex)))
  .disequality (outerSignature u v))

abbrev U := SourceEndpoint.U G hs u v hu hv hB
abbrev V := SourceEndpoint.V G hs u v hu hv hB
abbrev endpoint := SourceEndpoint.canonicalControlled G hs u v hu hv hB
abbrev Q := (endpoint G hs u v hu hv hB).queryBound
def A : Polynomial ℕ := (endpoint G hs u v hu hv hB).targetOutput.bound.comp (Q G hs u v hu hv hB)
def D : Polynomial ℕ := (CanonicalOracle.decodeComputes G).outputBound.bound.comp (A G hs u v hu hv hB)
def E : Polynomial ℕ :=
  (OriginalField.embedComputes G u v (U G hs u v hu hv hB) (V G hs u v hu hv hB)).outputBound.bound.comp
    (D G hs u v hu hv hB)
abbrev O := (endpoint G hs u v hu hv hB).sourceOutputBound.bound

abbrev inputLength (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :=
  ((FieldReduction.inputEncoding (s:=s) (arity:=arity)).encode r).length
abbrev query := SourceEndpoint.query G hs u v hu hv hB
abbrev answer (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) := CanonicalOracle.value G (query G hs u v hu hv hB r)
abbrev decoded (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :=
  (CanonicalOracle.fieldEquiv G).symm (answer G hs u v hu hv hB r)
abbrev embedded (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :=
  OriginalField.embedding G u v (U G hs u v hu hv hB) (V G hs u v hu hv hB) (decoded G hs u v hu hv hB r)

theorem query_length (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    ((FieldReduction.queryEncoding (s:=s) (arity:=arity)).encode (query G hs u v hu hv hB r)).length ≤
      (Q G hs u v hu hv hB).eval (inputLength r) :=
  FieldReduction.query_length
    (OriginalTarget.original G u v (U G hs u v hu hv hB) (V G hs u v hu hv hB))
    (OriginalTarget.left G u v (U G hs u v hu hv hB) (V G hs u v hu hv hB))
    (OriginalTarget.right G u v (U G hs u v hu hv hB) (V G hs u v hu hv hB))
    (OriginalTarget.leftMacro G u v (U G hs u v hu hv hB) (V G hs u v hu hv hB))
    (OriginalTarget.rightMacro G u v (U G hs u v hu hv hB) (V G hs u v hu hv hB)) r

theorem answer_length (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    ((CanonicalOracle.encoding G).encode (answer G hs u v hu hv hB r)).length ≤
      (A G hs u v hu hv hB).eval (inputLength r) := by
  apply le_trans ((endpoint G hs u v hu hv hB).targetOutput.length_le (query G hs u v hu hv hB r))
  simpa only [A,Polynomial.eval_comp] using natPolynomial_eval_mono
    (endpoint G hs u v hu hv hB).targetOutput.bound (query_length G hs u v hu hv hB r)

theorem decoded_length (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    ((OriginalField.encoding G).encode (decoded G hs u v hu hv hB r)).length ≤
      (D G hs u v hu hv hB).eval (inputLength r) := by
  apply le_trans ((CanonicalOracle.decodeComputes G).outputBound.length_le (answer G hs u v hu hv hB r))
  simpa only [D,Polynomial.eval_comp] using natPolynomial_eval_mono
    (CanonicalOracle.decodeComputes G).outputBound.bound (answer_length G hs u v hu hv hB r)

theorem embedded_length (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    ((CommonField.presentation G u v (U G hs u v hu hv hB) (V G hs u v hu hv hB)).encoding.encode
      (embedded G hs u v hu hv hB r)).length ≤ (E G hs u v hu hv hB).eval (inputLength r) := by
  apply le_trans ((OriginalField.embedComputes G u v (U G hs u v hu hv hB)
    (V G hs u v hu hv hB)).outputBound.length_le (decoded G hs u v hu hv hB r))
  simpa only [E,Polynomial.eval_comp] using natPolynomial_eval_mono
    (OriginalField.embedComputes G u v (U G hs u v hu hv hB) (V G hs u v hu hv hB)).outputBound.bound
    (decoded_length G hs u v hu hv hB r)

theorem output_length (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    ((SourceCodec.encoding G u v).encode (SourceCodec.value G u v r)).length ≤
      (O G hs u v hu hv hB).eval (inputLength r) :=
  (endpoint G hs u v hu hv hB).sourceOutputBound.length_le r

def budget : Polynomial ℕ :=
  (endpoint G hs u v hu hv hB).reduction.time + SourceEndpoint.canonicalPrimitive G hs u v hu hv hB +
    Q G hs u v hu hv hB + A G hs u v hu hv hB + D G hs u v hu hv hB +
    E G hs u v hu hv hB + O G hs u v hu hv hB + 1

/-- A single polynomial of the original raw input bytes bounds all actual
serialized words at this codec boundary. The additional first two summands
also dominate the time and primitive certificate in canonical_execution. -/
theorem word_bounds (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    ((FieldReduction.queryEncoding (s:=s) (arity:=arity)).encode (query G hs u v hu hv hB r)).length ≤
      (budget G hs u v hu hv hB).eval (inputLength r) ∧
    ((CanonicalOracle.encoding G).encode (answer G hs u v hu hv hB r)).length ≤
      (budget G hs u v hu hv hB).eval (inputLength r) ∧
    ((OriginalField.encoding G).encode (decoded G hs u v hu hv hB r)).length ≤
      (budget G hs u v hu hv hB).eval (inputLength r) ∧
    ((CommonField.presentation G u v (U G hs u v hu hv hB) (V G hs u v hu hv hB)).encoding.encode
      (embedded G hs u v hu hv hB r)).length ≤ (budget G hs u v hu hv hB).eval (inputLength r) ∧
    ((SourceCodec.encoding G u v).encode (SourceCodec.value G u v r)).length ≤
      (budget G hs u v hu hv hB).eval (inputLength r) := by
  have hq := query_length G hs u v hu hv hB r
  have ha := answer_length G hs u v hu hv hB r
  have hd := decoded_length G hs u v hu hv hB r
  have he := embedded_length G hs u v hu hv hB r
  have ho := output_length G hs u v hu hv hB r
  simp only [budget,Polynomial.eval_add,Polynomial.eval_one]
  omega

theorem execution_budget (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (FieldReduction.queryEncoding (s:=s) (arity:=arity)) (CanonicalOracle.encoding G)
      (CanonicalOracle.value G) oracle) (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    ∃ t ≤ (budget G hs u v hu hv hB).eval (inputLength r),
      OracleBatch.RunsTrace (endpoint G hs u v hu hv hB).reduction.machine oracle
        ((endpoint G hs u v hu hv hB).reduction.machine.init
          ((FieldReduction.inputEncoding (s:=s) (arity:=arity)).encode r))
        ((endpoint G hs u v hu hv hB).reduction.machine.output
          ((SourceCodec.encoding G u v).encode (SourceCodec.value G u v r))) t
        [(FieldReduction.queryEncoding (s:=s) (arity:=arity)).encode (query G hs u v hu hv hB r)] ∧
      OracleBatch.primitiveCount (endpoint G hs u v hu hv hB).reduction.machine oracle
        ((endpoint G hs u v hu hv hB).reduction.machine.init
          ((FieldReduction.inputEncoding (s:=s) (arity:=arity)).encode r)) t ≤
        (budget G hs u v hu hv hB).eval (inputLength r) := by
  obtain ⟨t,ht,hr,_,hp⟩ := SourceEndpoint.canonical_execution G hs u v hu hv hB oracle ho r
  -- Normalize only the two certificate indices. The endpoint and input
  -- encodings below are literally the producers used by canonical_execution.
  change t ≤ (endpoint G hs u v hu hv hB).reduction.time.eval (inputLength r) at ht
  change OracleBatch.primitiveCount (endpoint G hs u v hu hv hB).reduction.machine oracle
    ((endpoint G hs u v hu hv hB).reduction.machine.init
      ((FieldReduction.inputEncoding (s:=s) (arity:=arity)).encode r)) t ≤
    (SourceEndpoint.canonicalPrimitive G hs u v hu hv hB).eval (inputLength r) at hp
  refine ⟨t,?_,hr,?_⟩ <;> simp only [budget,Polynomial.eval_add,Polynomial.eval_one] <;> omega

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Composition.CostBounds
