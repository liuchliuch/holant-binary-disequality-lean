import Holant.Proofs.Hardness.GeneralEOPairedCSPUnused
import Holant.Proofs.Algorithms.TraceQueryControl
import Holant.Complexity.FixedFieldMachines.ScalarPower.Correction

/-! End-to-end length-controlled original-label/native-X oracle programme.
The graph writer and unused-variable counter are actual Boolean-stack
programmes; the postprocessor multiplies by 2^unused in the same fixed field.
The support-cover premise is explicit, and no CSP-hardness backend is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPNative
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GeneralEOPairedCSPRaw
namespace P
export GeneralEOPairedCSPValidated (query queryComputes)
end P
namespace U
export GeneralEOPairedCSPUnused (unused unusedComputes unused_eq)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {arity : ℕ→ℕ}
variable (F : FixedField K d) (G : (i : Fin s)→Signature K (arity i.val))
variable (label : Fin s) (p : OrientedPerfectPairing (arity label.val))

abbrev TargetInput := GeneralEOPairedCSPRecords.TargetInput (s:=s) (arity:=arity)
abbrev targetEncoding := RawClosedNetwork.validatedEncoding s 1 arity

def tables : ExactSignatureTables d s 1 arity where
  vertex i x := F.decode.symm (G i x)
  edge _ x y := F.decode.symm (Signature.disequality x y)

def targetValue : TargetInput (s:=s) (arity:=arity)→K := (tables F G).evaluate F

def sourceValue (r : Input p.count) : K :=
  value p (GeneralEOPairedCSPCycles.compress p (G label)) r.val

theorem target_semantics (q : TargetInput (s:=s) (arity:=arity)) : targetValue F G q=
    (q.val.realize q.property G (fun _=>Signature.disequality)).denote Fin.elim0 := by
  simp only [targetValue,ExactSignatureTables.evaluate_eq_decoded,tables,LinearEquiv.apply_symm_apply]

theorem query_value (hf : GeneralEOPairedCSPCycles.Covers p (G label)) (r : Input p.count) :
    sourceValue G label p r=targetValue F G (P.query label p r)*(2:K)^U.unused r.val := by
  rw [sourceValue,value_scope p _ r.val r.property,
    GeneralEOPairedCSPRecords.query_value label p G hf,target_semantics,U.unused_eq p r]
  exact mul_comm _ _

def unusedComputes (count : ℕ) : Computes (inputEncoding count) unary (fun r=>U.unused r.val) :=
  recode U.unusedComputes Subtype.val (fun _=>rfl) (fun _=>rfl)

def preprocessing (r : Input p.count) : List (TargetInput (s:=s) (arity:=arity))×ℕ :=
  ([P.query label p r],U.unused r.val)

def pre : Computes (inputEncoding p.count)
    (OracleBatch.contextEncoding (targetEncoding (s:=s) (arity:=arity)) unary)
    (preprocessing label p) :=
  pairComputes (Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access.list₁
    (targetEncoding (s:=s) (arity:=arity)) (P.queryComputes label p)) (unusedComputes p.count)

def post : Computes (OracleBatch.contextEncoding F.encoding unary) F.encoding
    (fun a : List K×ℕ=>a.1.getD 0 0*(2:K)^a.2) := by
  let power : Computes (pairEncoding F.encoding unary) F.encoding
      (fun a : K×ℕ=>a.1*(2:K)^a.2) :=
    congrComputes (ScalarPower.multiplyPower F (F.decode.symm (2:K))) (fun _=>by simp)
  exact (pairComputes
    ((Wiring.firstComputes (framedListEncoding F.encoding) unary).andThen
      (FixedGadgetSubstitution.Compiler.getDComputes F.encoding 0 0))
    (Wiring.secondComputes (framedListEncoding F.encoding) unary)).andThen power

/-- One physically written query, same-field answer correction, and a proved
polynomial bound on every target query and target answer length. -/
def controlled (hf : GeneralEOPairedCSPCycles.Covers p (G label)) :
    LengthControlledOracleReduction (inputEncoding p.count) F.encoding
      (targetEncoding (s:=s) (arity:=arity)) F.encoding
      (sourceValue G label p) (targetValue F G) := by
  let reduction := Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch
    (pre label p) (post F) ((tables F G).outputBound F)
  refine {
    reduction := {
      machine := reduction.reduction.machine
      time := reduction.reduction.time
      correct := ?_ }
    targetOutput := reduction.targetOutput
    queryBound := reduction.queryBound
    safeQuery := reduction.safeQuery }
  intro oracle ho r
  rw [query_value F G label p hf r]
  simpa only [preprocessing,OracleBatch.answers,List.map_cons,List.map_nil,
    List.getD_cons_zero,targetValue] using reduction.reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPNative
