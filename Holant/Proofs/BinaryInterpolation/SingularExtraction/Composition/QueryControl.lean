import Holant.Proofs.BinaryInterpolation.SingularExtraction.FieldReduction
import Holant.Proofs.Algorithms.TraceQueryControl


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Composition.QueryControl
open Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
variable {K : Type} [Field K] [Algebra ℚ K] {n s : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K n) (G : (i : Fin s) → Signature K (arity i.val))
variable (u v : Bool → K) (U : PowerMacro G u) (V : PowerMacro G v)

theorem reachable_query (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (FieldReduction.queryEncoding (s:=s) (arity:=arity)) F.encoding
      ((FieldReduction.targetTables F G).evaluate F) oracle)
    (r : FieldReduction.Input (s:=s) (arity:=arity)) (t : ℕ)
    (c : (FieldReduction.reduction F G u v U V).machine.Cfg)
    (hr : (FieldReduction.reduction F G u v U V).machine.run oracle
      ((FieldReduction.inputEncoding (s:=s) (arity:=arity)).encode r) t = some c)
    (hq : (FieldReduction.reduction F G u v U V).machine.IsQuery c) :
    c.stk (FieldReduction.reduction F G u v U V).machine.queryStack =
      (FieldReduction.queryEncoding (s:=s) (arity:=arity)).encode (FieldReduction.query G u v U V r) := by
  obtain ⟨N,_,htrace⟩ := FieldReduction.run_trace F G u v U V oracle ho r
  have hm := TraceQueryControl.transcript_member htrace t c hr hq
  simpa only [List.mem_singleton] using hm

def controlled : LengthControlledOracleReduction
    (FieldReduction.inputEncoding (s:=s) (arity:=arity)) F.encoding
    (FieldReduction.queryEncoding (s:=s) (arity:=arity)) F.encoding
    (FieldReduction.sourceValue G u v) ((FieldReduction.targetTables F G).evaluate F) where
  reduction := FieldReduction.reduction F G u v U V
  targetOutput := (FieldReduction.targetTables F G).outputBound F
  queryBound := FieldReduction.queryPolynomial G u v U V
  safeQuery oracle ho r t c hr hq := by
    have he := reachable_query F G u v U V oracle ho r t c hr hq
    refine ⟨FieldReduction.query G u v U V r,he,?_⟩
    rw [he]
    exact FieldReduction.query_length G u v U V r

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Composition.QueryControl
