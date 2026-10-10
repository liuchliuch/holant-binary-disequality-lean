import Holant.Proofs.Reductions.RootPreprocessing.FieldTransport
import Holant.Proofs.Algorithms.TraceQueryControl


noncomputable section
namespace Holant.LocalDrafts.Hardness.RootPreprocessing
open Holant.Tractable
set_option backward.isDefEq.respectTransparency false
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open FixedGadgetSubstitution.Compiler RawClosedNetwork
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open FactorSaturation
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (hI : RetainsIdentity (Set.range (fun i => (⟨a i.val,G i⟩ : AnySignature AlgebraicComplex))))

def pre (r : Input (s:=s) (a:=a)) : List (TargetInput G) × sourceField G := ([query G r],context G r)
def preComputes : Computes (sourceEncoding (s:=s) (a:=a))
    (OracleBatch.contextEncoding (OriginalCodec.encoding (roots G hI)) (sourcePresentation G).encoding)
    (pre G) :=
  pairComputes (fixedListComputes (sourceEncoding (s:=s) (a:=a))
    (OriginalCodec.encoding (roots G hI)) (fun r (_ : Unit) => query G r)
      (fun _ => queryComputes G) [()]) (contextComputes G)

def post (p : List (retainedField G) × sourceField G) : sourceField G :=
  p.2 * embedding G (p.1.getD 0 0)
def postComputes : Computes
    (OracleBatch.contextEncoding (OriginalCodec.presentation (roots G hI)).encoding
      (sourcePresentation G).encoding) (sourcePresentation G).encoding (post G) := by
  let answer := ((Wiring.firstComputes (framedListEncoding (retainedPresentation G).encoding)
    (sourcePresentation G).encoding).andThen (getDComputes (retainedPresentation G).encoding 0 0)).andThen
      (embeddingComputes G)
  let factor := Wiring.secondComputes (framedListEncoding (retainedPresentation G).encoding)
    (sourcePresentation G).encoding
  exact (pairComputes factor answer).andThen (Concrete.fieldMultiplication (sourcePresentation G))

theorem recovery (r : Input (s:=s) (a:=a)) :
    sourceValue G r = post G (OracleBatch.answers (OriginalCodec.value (roots G hI)) (pre G r)) :=
  field_recovery G r

def controlled : LengthControlledOracleReduction
    (sourceEncoding (s:=s) (a:=a)) (sourcePresentation G).encoding
    (OriginalCodec.encoding (roots G hI)) (OriginalCodec.presentation (roots G hI)).encoding
    (sourceValue G) (OriginalCodec.value (roots G hI)) := by
  have he : sourceValue G = fun r =>
      post G (OracleBatch.answers (OriginalCodec.value (roots G hI)) (pre G r)) := funext (recovery G hI)
  rw [he]
  exact TraceQueryControl.controlledBatch (preComputes G hI) (postComputes G hI)
    ((GeneralExtraction.GeneralOriginalTarget.originalTables (targetTable G)).outputBound (retainedPresentation G))

def reduction := (controlled G hI).reduction

theorem zero_query (r : Input (s:=s) (a:=a)) (h : ¬ Clean G r.val) :
    pre G r = ([emptyQuery G],0) := by simp [pre,query_zero G r h,context,h]

include hI in
/-- The oracle is still called on a VALID empty graph, whose value is one;
the stored zero correction annihilates the answer. No oracle value is assumed. -/
theorem zero_recovery (r : Input (s:=s) (a:=a)) (h : ¬ Clean G r.val) :
    sourceValue G r = 0 := by
  rw [recovery G hI,zero_query G r h]
  simp [post,OracleBatch.answers]

theorem run_cost (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (OriginalCodec.encoding (roots G hI))
      (OriginalCodec.presentation (roots G hI)).encoding (OriginalCodec.value (roots G hI)) oracle)
    (r : Input (s:=s) (a:=a)) :
    ∃ n ≤ (reduction G hI).time.eval ((sourceEncoding (s:=s) (a:=a)).encode r).length,
      (fun c => c.bind ((reduction G hI).machine.step oracle))^[n]
        (some ((reduction G hI).machine.init ((sourceEncoding (s:=s) (a:=a)).encode r))) =
        some ((reduction G hI).machine.output ((sourcePresentation G).encoding.encode (sourceValue G r))) ∧
      OracleBatch.primitiveCount (reduction G hI).machine oracle
        ((reduction G hI).machine.init ((sourceEncoding (s:=s) (a:=a)).encode r)) n ≤
        (reduction G hI).machine.primitiveBudget *
          (reduction G hI).time.eval ((sourceEncoding (s:=s) (a:=a)).encode r).length := by
  let run := (reduction G hI).correct oracle ho r
  refine ⟨run.steps,run.steps_le_m,run.evals_in_steps,?_⟩
  exact (OracleBatch.primitiveCount_le (reduction G hI).machine oracle
    ((reduction G hI).machine.init ((sourceEncoding (s:=s) (a:=a)).encode r)) run.steps).trans
      (Nat.mul_le_mul_left (reduction G hI).machine.primitiveBudget run.steps_le_m)

theorem query_bit_bound (r : Input (s:=s) (a:=a)) :
    ((OriginalCodec.encoding (roots G hI)).encode (query G r)).length ≤
      (queryComputes G).outputBound.bound.eval ((sourceEncoding (s:=s) (a:=a)).encode r).length :=
  (queryComputes G).outputBound.length_le r

end Holant.LocalDrafts.Hardness.RootPreprocessing
