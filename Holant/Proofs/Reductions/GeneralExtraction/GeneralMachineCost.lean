import Holant.Proofs.Reductions.GeneralExtraction.GeneralFieldReduction


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralFieldReduction
open Holant.Algebraic Holant.Complexity Computability BinaryCompose
open Holant.Complexity.UniversalPairReduction.ThreeQuery
open GeneralPowerExposure
variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K d) (G : (i : Fin s) → Signature K (arity i.val))
variable (f : Signature K (arity s)) (P : PowerMacro G f)

def primitivePolynomial : Polynomial ℕ :=
  Polynomial.C (reduction F G f P).machine.primitiveBudget * timePolynomial F G f P

theorem run_cost (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity)) F.encoding
      ((targetTables F G).evaluate F) oracle) (r : Input (s:=s) (arity:=arity)) :
    ∃ t ≤ (timePolynomial F G f P).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length,
      (fun c => c.bind ((reduction F G f P).machine.step oracle))^[t]
        (some ((reduction F G f P).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r))) =
        some ((reduction F G f P).machine.output (F.encoding.encode (sourceValue G f r))) ∧
      queryCount (reduction F G f P).machine oracle
        ((reduction F G f P).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t = 1 ∧
      OracleBatch.primitiveCount (reduction F G f P).machine oracle
        ((reduction F G f P).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t ≤
        (primitivePolynomial F G f P).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length := by
  have h := OracleBatch.reduction_query_count (preComputes F G f P) (postComputes F G f P)
      ((targetTables F G).outputBound F) oracle ho r
  rw [← recovery F G f P r] at h
  simp only [pre,List.length_cons,List.length_nil] at h
  exact h

def queryPolynomial : Polynomial ℕ := (queryComputes G f P).outputBound.bound
def answerPolynomial : Polynomial ℕ := ((targetTables F G).outputBound F).bound.comp (queryPolynomial G f P)

theorem query_length (r : Input (s:=s) (arity:=arity)) :
    ((queryEncoding (s:=s) (arity:=arity)).encode (query G f P r)).length ≤
      (queryPolynomial G f P).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length :=
  (queryComputes G f P).outputBound.length_le r

theorem answer_length (r : Input (s:=s) (arity:=arity)) :
    (F.encoding.encode ((targetTables F G).evaluate F (query G f P r))).length ≤
      (answerPolynomial F G f P).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length := by
  apply le_trans (((targetTables F G).outputBound F).length_le (query G f P r))
  simpa only [answerPolynomial, Polynomial.eval_comp] using
    natPolynomial_eval_mono ((targetTables F G).outputBound F).bound (query_length G f P r)

def budget : Polynomial ℕ := timePolynomial F G f P + primitivePolynomial F G f P +
  queryPolynomial G f P + answerPolynomial F G f P + 1

end Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralFieldReduction
