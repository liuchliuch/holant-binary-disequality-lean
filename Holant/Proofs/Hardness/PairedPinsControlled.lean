import Holant.Proofs.Hardness.PairedPinsValidated
import Holant.Proofs.Algorithms.ControlledReduction
import Holant.Complexity.EncodedHolantOutputSize

/-! Same-field controlled reduction for the actual balanced-pin rewrite.
Source and target answer bytes use exactly the same fixed presentation F.
Their tables are internally computed from the original G,P,Q,E coefficients.
The target's output-length bound is derived on every validated target graph.
No correct evaluator, reduction, answer or runtime bound is supplied.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PairedPinsControlled
open Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open PairedPinsRaw PairedPinsSemantics
namespace V
export PairedPinsValidated (Input inputEncoding targetEncoding query computes)
end V

variable {K : Type} [Field K] [Algebra ℚ K] {d s b : ℕ} {a : ℕ → ℕ}
variable (F : FixedField K d) (G : (i : Fin s) → Signature K (a i.val))
variable (P Q : Bool → K) (E : Fin b → Kernel K)

def sourceTables : ExactSignatureTables d (s+2) b (sourceArity s a) where
  vertex i x := F.decode.symm (sourceSignatures G P Q i x)
  edge i x y := F.decode.symm (E i x y)

def targetTables : ExactSignatureTables d (s+1) b (targetArity s a) where
  vertex i x := F.decode.symm (targetSignatures G P Q i x)
  edge i x y := F.decode.symm (E i x y)

def sourceInput (r : V.Input s b a) : ExactSignatureTables.Input (s+2) b (sourceArity s a) :=
  ⟨r.val,r.property.1⟩

def sourceValue (r : V.Input s b a) : K :=
  (sourceTables F G P Q E).evaluate F (sourceInput r)

abbrev targetValue := (targetTables F G P Q E).evaluate F

/-- The full coefficient interpretation follows the literal graph sum proof,
including all zero terms, arbitrary unary weights and every actual edge end. -/
theorem query_value (r : V.Input s b a) :
    targetValue F G P Q E (V.query r)=sourceValue F G P Q E r := by
  simp only [sourceValue,targetValue,ExactSignatureTables.evaluate_eq_decoded,
    sourceTables,targetTables,LinearEquiv.apply_symm_apply]
  exact denote_preserved r.property.1 r.property.2 G P Q E

/-- Both the actual raw programme and same-field identity answer programme
are installed, including target query validation and answer-copy time. -/
def controlled : LengthControlledOracleReduction (V.inputEncoding s b a) F.encoding
    (V.targetEncoding s b a) F.encoding (sourceValue F G P Q E) (targetValue F G P Q E) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq (V.computes s b a)
    (identityComputes F.encoding) ((targetTables F G P Q E).outputBound F)
    (sourceValue F G P Q E) (fun r => (query_value F G P Q E r).symm)

def outputs (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (V.targetEncoding s b a) F.encoding (targetValue F G P Q E) oracle)
    (r : V.Input s b a) :
    (controlled F G P Q E).reduction.machine.OutputsInTime oracle ((V.inputEncoding s b a).encode r)
      (F.encoding.encode (sourceValue F G P Q E r))
      ((controlled F G P Q E).reduction.time.eval ((V.inputEncoding s b a).encode r).length) :=
  (controlled F G P Q E).reduction.correct oracle ho r

theorem query_parses (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (V.targetEncoding s b a) F.encoding (targetValue F G P Q E) oracle)
    (r : V.Input s b a) (t : ℕ) (z : (controlled F G P Q E).reduction.machine.Cfg)
    (hr : (controlled F G P Q E).reduction.machine.run oracle ((V.inputEncoding s b a).encode r) t=some z)
    (hq : (controlled F G P Q E).reduction.machine.IsQuery z) :
    ∃ q : ExactSignatureTables.Input (s+1) b (targetArity s a),
      z.stk (controlled F G P Q E).reduction.machine.queryStack=(V.targetEncoding s b a).encode q ∧
      (V.targetEncoding s b a).decode
        (z.stk (controlled F G P Q E).reduction.machine.queryStack)=some q := by
  obtain ⟨q,hword,_⟩ := (controlled F G P Q E).safeQuery oracle ho r t z hr hq
  refine ⟨q,hword,?_⟩
  rw [hword]
  exact (V.targetEncoding s b a).decode_encode q

/-- The generic controlled contract supplies an every-prefix bound, including
actual received oracle-answer storage, without inspecting the program table. -/
theorem prefix_storage (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (V.targetEncoding s b a) F.encoding (targetValue F G P Q E) oracle)
    (r : V.Input s b a) (t : ℕ)
    (z : (controlled F G P Q E).reduction.machine.Cfg)
    (hr : (controlled F G P Q E).reduction.machine.run oracle ((V.inputEncoding s b a).encode r) t=some z) :
    stackSize z.stk ≤ ((V.inputEncoding s b a).encode r).length + t *
      ((controlled F G P Q E).reduction.machine.primitiveBudget +
        ((controlled F G P Q E).targetOutput.bound.comp
          (controlled F G P Q E).queryBound).eval ((V.inputEncoding s b a).encode r).length) :=
  (controlled F G P Q E).run_stackSize_le oracle ho r t z hr

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PairedPinsControlled
