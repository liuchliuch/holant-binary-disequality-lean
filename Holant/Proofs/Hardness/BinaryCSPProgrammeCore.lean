import Holant.Proofs.Counting.RawGraphMachine.Access
import Holant.Proofs.Tractability.AffineMachine.WireLists
import Holant.Complexity.FixedFieldMachines.PrimitiveCost

/-! A literal finite binary-constraint tape. The unary variable declaration
retains unused variables, including in the empty constraint instance. Edge and
sign addresses are ordinary binary integers. All programmes below are finite
Boolean-stack machines with their own completed executions and clocks. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeCore
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

structure Raw where
  «variables» : ℕ
  edges : List (ℕ × ℕ)
  signs : List ℕ
  deriving DecidableEq, Repr

def Raw.WellFormed (r : Raw) : Prop :=
  (∀ e ∈ r.edges, e.1 < r.variables ∧ e.2 < r.variables) ∧
  ∀ v ∈ r.signs, v < r.variables

abbrev unary := UnaryBinary.unaryEncoding
abbrev edgeEncoding := pairEncoding encodingNatBool encodingNatBool
abbrev edgesEncoding := framedListEncoding edgeEncoding
abbrev signsEncoding := framedListEncoding encodingNatBool
abbrev fieldsEncoding := pairEncoding unary (pairEncoding edgesEncoding signsEncoding)

def Raw.fields (r : Raw) : ℕ × (List (ℕ × ℕ) × List ℕ) :=
  (r.variables, r.edges, r.signs)

def ofFields (p : ℕ × (List (ℕ × ℕ) × List ℕ)) : Raw := ⟨p.1,p.2.1,p.2.2⟩

def encoding : Encoding Raw Bool where
  encode r := fieldsEncoding.encode r.fields
  decode bits := ofFields <$> fieldsEncoding.decode bits
  decode_encode r := by rw [fieldsEncoding.decode_encode]; rfl

def fieldsComputes : Computes encoding fieldsEncoding Raw.fields :=
  recode (identityComputes fieldsEncoding) Raw.fields (fun _ => rfl) (fun _ => rfl)

def variablesComputes : Computes encoding unary Raw.variables :=
  fieldsComputes.andThen (Wiring.firstComputes unary (pairEncoding edgesEncoding signsEncoding))

def listsComputes : Computes encoding (pairEncoding edgesEncoding signsEncoding)
    (fun r => (r.edges,r.signs)) :=
  fieldsComputes.andThen (Wiring.secondComputes unary (pairEncoding edgesEncoding signsEncoding))

def edgesComputes : Computes encoding edgesEncoding Raw.edges :=
  listsComputes.andThen (Wiring.firstComputes edgesEncoding signsEncoding)

def signsComputes : Computes encoding signsEncoding Raw.signs :=
  listsComputes.andThen (Wiring.secondComputes edgesEncoding signsEncoding)

def edgeCountComputes : Computes encoding unary (fun r => r.edges.length) :=
  edgesComputes.andThen (Holant.LocalDrafts.Tractability.AffineMachine.WireLists.lengthComputes edgeEncoding)

def signCountComputes : Computes encoding unary (fun r => r.signs.length) :=
  signsComputes.andThen (Holant.LocalDrafts.Tractability.AffineMachine.WireLists.lengthComputes encodingNatBool)

/-- Serialize the three actual fields, including both list terminators. -/
def assemble {A : Type} {e : Encoding A Bool} {v : A → ℕ}
    {es : A → List (ℕ × ℕ)} {ss : A → List ℕ}
    (wv : Computes e unary v) (we : Computes e edgesEncoding es)
    (ws : Computes e signsEncoding ss) :
    Computes e encoding (fun a => (⟨v a,es a,ss a⟩ : Raw)) :=
  recode (pairComputes wv (pairComputes we ws)) id (fun _ => rfl) (fun _ => rfl)

/-- All prefixes, including ones before any output is available, incur only
the explicitly budgeted primitive fees of the same programme. -/
theorem prefix_primitive_bound {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → B} (w : Computes ea eb f) (a : A) (t : ℕ)
    (ht : t ≤ w.time.eval (ea.encode a).length) :
    primitiveCost w.machine t (some (initList w.machine.computer (ea.encode a))) ≤
      (primitivePolynomial w).eval (ea.encode a).length := by
  exact (primitiveCost_le _ _ _).trans (by
    simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
      Nat.mul_le_mul_right w.machine.primitiveBudget ht)

theorem prefix_storage_bound {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → B} (w : Computes ea eb f) (a : A) (t : ℕ) (cfg : w.machine.Config)
    (hr : (fun q => q.bind w.machine.computer.step)^[t]
      (some (initList w.machine.computer (ea.encode a))) = some cfg)
    (ht : t ≤ w.time.eval (ea.encode a).length) :
    stackSize cfg.stk ≤ w.outputBound.bound.eval (ea.encode a).length := by
  have h := w.machine.run_size_le (initList w.machine.computer (ea.encode a)) cfg t hr
  rw [Machine.size_init] at h
  exact h.trans (by
    simpa only [Computes.outputBound,Polynomial.eval_add,Polynomial.eval_X,
      Polynomial.eval_mul,Polynomial.eval_C] using
      Nat.add_le_add_left (Nat.mul_le_mul_right w.machine.primitiveBudget ht) (ea.encode a).length)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeCore
