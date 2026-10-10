import Holant.Proofs.BinaryInterpolation.SingularExtraction.Composition.SourceCodec
import Holant.Proofs.BinaryInterpolation.SingularExtraction.Composition.CanonicalOracle
import Holant.Proofs.BinaryInterpolation.SingularExtraction.SourceReduction


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Composition.SourceEndpoint
open Holant Holant.Tractable Holant.Complexity
open Holant.Complexity.UniversalPairReduction.ThreeQuery
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (hs : ¬ CommonOneSided (Set.range (fun i => (⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex))))
variable (u v : Bool → AlgebraicComplex) (hu : u ≠ 0) (hv : v ≠ 0)
variable (hB : Gadget.Realizes (Set.range (fun i => (⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex)))
  .disequality (outerSignature u v))

abbrev U := SourceReduction.leftMacro G hs u v hu hv hB
abbrev V := SourceReduction.rightMacro G hs u v hu hv hB
abbrev inputEncoding := FieldReduction.inputEncoding (s:=s) (arity:=arity)
abbrev queryEncoding := FieldReduction.queryEncoding (s:=s) (arity:=arity)
abbrev query := OriginalTarget.query G u v (U G hs u v hu hv hB) (V G hs u v hu hv hB)

/-- The old source machine upgraded directly by its actual trace. -/
def commonControlled : LengthControlledOracleReduction
    (inputEncoding (s:=s) (arity:=arity)) (SourceReduction.outputEncoding G hs u v hu hv hB)
    (queryEncoding (s:=s) (arity:=arity)) (OriginalField.encoding G)
    (SourceReduction.sourceValue G hs u v hu hv hB) (OriginalField.value G) :=
  OriginalTarget.controlled G u v (U G hs u v hu hv hB) (V G hs u v hu hv hB)

/-- The central composition implementation, retained for integration callers
that want the common-field source codec of the previous source capstone. -/
def inlinedReduction : PolyTimeOracleReduction
    (inputEncoding (s:=s) (arity:=arity)) (SourceReduction.outputEncoding G hs u v hu hv hB)
    (queryEncoding (s:=s) (arity:=arity)) (OriginalField.encoding G)
    (SourceReduction.sourceValue G hs u v hu hv hB) (OriginalField.value G) :=
  OriginalTarget.inlinedReduction G u v (U G hs u v hu hv hB) (V G hs u v hu hv hB)

/-- Main endpoint: exact original-family oracle, exact literal source-family
answer, actual reachable-query control suitable for the central inliner. -/
def controlled : LengthControlledOracleReduction
    (inputEncoding (s:=s) (arity:=arity)) (SourceCodec.encoding G u v)
    (queryEncoding (s:=s) (arity:=arity)) (OriginalField.encoding G)
    (SourceCodec.value G u v) (OriginalField.value G) :=
  SourceCodec.controlled G u v (U G hs u v hu hv hB) (V G hs u v hu hv hB)

abbrev reduction := (controlled G hs u v hu hv hB).reduction
abbrev sourceOutput := (controlled G hs u v hu hv hB).sourceOutputBound
abbrev timePolynomial := (reduction G hs u v hu hv hB).time
abbrev primitivePolynomial := SourceCodec.primitivePolynomial G u v
  (U G hs u v hu hv hB) (V G hs u v hu hv hB)
abbrev queryPolynomial := (controlled G hs u v hu hv hB).queryBound
def answerPolynomial : Polynomial ℕ :=
  (controlled G hs u v hu hv hB).targetOutput.bound.comp (queryPolynomial G hs u v hu hv hB)

theorem source_exact (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    (SourceCodec.value G u v r : AlgebraicComplex) =
      (r.val.realize r.property (SourceCodec.signatures G u v)
        (fun _ => Signature.disequality)).denote Fin.elim0 := SourceCodec.value_exact G u v r

theorem target_exact (q : ExactSignatureTables.Input s 1 arity) :
    (OriginalField.value G q : AlgebraicComplex) =
      (q.val.realize q.property G (fun _ => Signature.disequality)).denote Fin.elim0 :=
  OriginalField.value_exact G q

/-- Identical incidence serialization: no macro, residue, field-presentation
certificate, or encoding adapter is attached to the oracle query word. -/
theorem query_bytes (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    (queryEncoding (s:=s) (arity:=arity)).encode (query G hs u v hu hv hB r) =
      RawClosedNetwork.encoding.encode (query G hs u v hu hv hB r).val := rfl

theorem execution (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity)) (OriginalField.encoding G)
      (OriginalField.value G) oracle) (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    ∃ t ≤ (timePolynomial G hs u v hu hv hB).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length,
      OracleBatch.RunsTrace (reduction G hs u v hu hv hB).machine oracle
        ((reduction G hs u v hu hv hB).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r))
        ((reduction G hs u v hu hv hB).machine.output ((SourceCodec.encoding G u v).encode (SourceCodec.value G u v r))) t
        [(queryEncoding (s:=s) (arity:=arity)).encode (query G hs u v hu hv hB r)] ∧
      queryCount (reduction G hs u v hu hv hB).machine oracle
        ((reduction G hs u v hu hv hB).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t = 1 ∧
      OracleBatch.primitiveCount (reduction G hs u v hu hv hB).machine oracle
        ((reduction G hs u v hu hv hB).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t ≤
        (primitivePolynomial G hs u v hu hv hB).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length :=
  SourceCodec.execution G u v (U G hs u v hu hv hB) (V G hs u v hu hv hB) oracle ho r

/-- Arbitrary reachable query times, not merely times before a supplied bound. -/
theorem encountered_answer (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity)) (OriginalField.encoding G)
      (OriginalField.value G) oracle) (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) (t : ℕ)
    (c : (reduction G hs u v hu hv hB).machine.Cfg)
    (hr : (reduction G hs u v hu hv hB).machine.run oracle
      ((inputEncoding (s:=s) (arity:=arity)).encode r) t = some c)
    (hq : (reduction G hs u v hu hv hB).machine.IsQuery c) :
    (oracle (c.stk (reduction G hs u v hu hv hB).machine.queryStack)).length ≤
      (answerPolynomial G hs u v hu hv hB).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length :=
  (controlled G hs u v hu hv hB).answer_length_le oracle ho r t c hr hq

/-- Preferred central endpoint. This is literally BinaryOriginalTarget's
original complex-family oracle codec, not only an isomorphic field codec. -/
def canonicalControlled : LengthControlledOracleReduction
    (inputEncoding (s:=s) (arity:=arity)) (SourceCodec.encoding G u v)
    (queryEncoding (s:=s) (arity:=arity)) (CanonicalOracle.encoding G)
    (SourceCodec.value G u v) (CanonicalOracle.value G) :=
  CanonicalOracle.controlled G u v (U G hs u v hu hv hB) (V G hs u v hu hv hB)

abbrev canonicalReduction := (canonicalControlled G hs u v hu hv hB).reduction
abbrev canonicalInlinedReduction := CanonicalOracle.inlinedReduction G u v
  (U G hs u v hu hv hB) (V G hs u v hu hv hB)
abbrev canonicalSourceOutput := (canonicalControlled G hs u v hu hv hB).sourceOutputBound
abbrev canonicalPrimitive := CanonicalOracle.primitiveBound G u v
  (U G hs u v hu hv hB) (V G hs u v hu hv hB)

theorem canonical_execution (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity)) (CanonicalOracle.encoding G)
      (CanonicalOracle.value G) oracle) (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    ∃ t ≤ (canonicalReduction G hs u v hu hv hB).time.eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length,
      OracleBatch.RunsTrace (canonicalReduction G hs u v hu hv hB).machine oracle
        ((canonicalReduction G hs u v hu hv hB).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r))
        ((canonicalReduction G hs u v hu hv hB).machine.output
          ((SourceCodec.encoding G u v).encode (SourceCodec.value G u v r))) t
        [(queryEncoding (s:=s) (arity:=arity)).encode (query G hs u v hu hv hB r)] ∧
      queryCount (canonicalReduction G hs u v hu hv hB).machine oracle
        ((canonicalReduction G hs u v hu hv hB).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t = 1 ∧
      OracleBatch.primitiveCount (canonicalReduction G hs u v hu hv hB).machine oracle
        ((canonicalReduction G hs u v hu hv hB).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t ≤
        (canonicalPrimitive G hs u v hu hv hB).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length :=
  CanonicalOracle.execution G u v (U G hs u v hu hv hB) (V G hs u v hu hv hB) oracle ho r

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Composition.SourceEndpoint
