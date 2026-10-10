import Holant.Proofs.Hardness.PairedPinsRaw
import Holant.Proofs.Tractability.AffineMachine.AccessPrograms

/-!
# Physical complementary-pin pairing compiler

The original graph is parsed as its literal framed raw-record word. Three
actual scans keep old rows and collect the two pin endpoint lists. A unary
length/range program drives ordered two-endpoint emission; each dynamic getD
is an existing physical lookup with default padding. Edge records are copied
unchanged. No graph function or list callback is installed as a primitive.

This module supplies the TOTAL raw-record machine. Its interpretation as a
validated pin-merging reduction additionally needs PairedPinsSemantics, and
does not follow merely from this compiler's time theorem.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PairedPinsCompiler
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open PairedPinsRaw
set_option backward.isDefEq.respectTransparency false

abbrev rowEncoding := RawClosedNetwork.vertexEncoding
abbrev endpointEncoding := RawClosedNetwork.endpointEncoding
abbrev rowsEncoding := framedListEncoding rowEncoding
abbrev portsEncoding := framedListEncoding endpointEncoding
abbrev edgesEncoding := framedListEncoding encodingNatBool
abbrev rawEncoding := RawClosedNetwork.encoding
abbrev cellEncoding := pairEncoding rawEncoding UnaryBinary.unaryEncoding

private theorem filter_rows {A : Type} (p : A → Bool) (xs : List A) :
    xs.flatMap (fun x => if p x then [x] else [])=xs.filter p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp,ih]

private theorem filter_ports (p : RawVertex → Bool) (xs : List RawVertex) :
    xs.flatMap (fun x => if p x then x.2 else [])=(xs.filter p).flatMap Prod.snd := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp,ih]

def rowsComputes : Computes rawEncoding rowsEncoding (fun r => r.vertices) :=
  recode (Wiring.firstComputes rowsEncoding edgesEncoding)
    (fun r => (r.vertices,r.edges)) (fun _ => rfl) (fun _ => rfl)

def edgesComputes : Computes rawEncoding edgesEncoding (fun r => r.edges) :=
  recode (Wiring.secondComputes rowsEncoding edgesEncoding)
    (fun r => (r.vertices,r.edges)) (fun _ => rfl) (fun _ => rfl)

def labelComputes : Computes rowEncoding encodingNatBool (fun r => r.1) :=
  recode (Wiring.firstComputes encodingNatBool portsEncoding)
    id (fun _ => rfl) (fun _ => rfl)

def portsComputes : Computes rowEncoding portsEncoding (fun r => r.2) :=
  recode (Wiring.secondComputes encodingNatBool portsEncoding)
    id (fun _ => rfl) (fun _ => rfl)

def oldTest (s : ℕ) : Computes rowEncoding encodingBoolBool (fun r => decide (r.1<s)) :=
  (pairComputes labelComputes (constantComputes rowEncoding encodingNatBool s)).andThen
    Endpoints.lessComputes

def pinTest (s : ℕ) (b : Bool) :
    Computes rowEncoding encodingBoolBool (fun r => decide (r.1=s+b.toNat)) :=
  (pairComputes labelComputes (constantComputes rowEncoding encodingNatBool (s+b.toNat))).andThen
    Endpoints.equalComputes

def singletonRow : Computes rowEncoding rowsEncoding (fun r => [r]) :=
  fixedListComputes rowEncoding rowEncoding (fun r (_ : Fin 1) => r)
    (fun _ => identityComputes rowEncoding) [0]

def keepOld (s : ℕ) : Computes rowEncoding rowsEncoding
    (fun r => if r.1<s then [r] else []) :=
  congrComputes (ifComputes (oldTest s) singletonRow (constantComputes rowEncoding rowsEncoding []))
    (fun r => by simp)

def keepPins (s : ℕ) (b : Bool) : Computes rowEncoding portsEncoding
    (fun r => if r.1=s+b.toNat then r.2 else []) :=
  congrComputes (ifComputes (pinTest s b) portsComputes
    (constantComputes rowEncoding portsEncoding [])) (fun r => by simp)

def oldRowsComputes (s : ℕ) : Computes rawEncoding rowsEncoding (oldRows s) :=
  congrComputes (rowsComputes.andThen
    (AccessPrograms.flatMap rowEncoding rowEncoding _ (keepOld s)))
    (fun r => by simpa [oldRows] using
      filter_rows (fun row : RawVertex => decide (row.1<s)) r.vertices)

def pinsComputes (s : ℕ) (b : Bool) : Computes rawEncoding portsEncoding (pins s b) :=
  congrComputes (rowsComputes.andThen
    (AccessPrograms.flatMap rowEncoding endpointEncoding _ (keepPins s b)))
    (fun r => by simpa [pins] using
      filter_ports (fun row : RawVertex => decide (row.1=s+b.toNat)) r.vertices)

def pinCountComputes (s : ℕ) (b : Bool) : Computes rawEncoding UnaryBinary.unaryEncoding
    (fun r => (pins s b r).length) :=
  (pinsComputes s b).andThen (WireLists.lengthComputes endpointEncoding)

def contextComputes : Computes cellEncoding rawEncoding (fun x => x.1) :=
  Wiring.firstComputes rawEncoding UnaryBinary.unaryEncoding

def indexComputes : Computes cellEncoding UnaryBinary.unaryEncoding (fun x => x.2) :=
  Wiring.secondComputes rawEncoding UnaryBinary.unaryEncoding

def endpointComputes (s : ℕ) (b : Bool) : Computes cellEncoding endpointEncoding
    (fun x => (pins s b x.1).getD x.2 (0,false)) :=
  AccessPrograms.get endpointEncoding (0,false)
    (contextComputes.andThen (pinsComputes s b)) indexComputes

def pairedPortsComputes (s : ℕ) : Computes cellEncoding portsEncoding
    (fun x => [(pins s false x.1).getD x.2 (0,false),
      (pins s true x.1).getD x.2 (0,false)]) := by
  let cell (x : RawClosedNetwork × ℕ) (b : Bool) := (pins s b x.1).getD x.2 (0,false)
  exact fixedListComputes cellEncoding endpointEncoding cell
    (fun b => endpointComputes s b) [false,true]

def pairedRowComputes (s : ℕ) : Computes cellEncoding rowEncoding
    (fun x => pairedRow s x.1 x.2) :=
  recode (pairComputes (constantComputes cellEncoding encodingNatBool s)
    (pairedPortsComputes s)) id (fun _ => rfl) (fun _ => rfl)

def pairedRowsComputes (s : ℕ) : Computes rawEncoding rowsEncoding (pairedRows s) :=
  WireLists.tabulate rawEncoding rowEncoding (fun r => (pins s false r).length)
    (pinCountComputes s false) (pairedRow s) (pairedRowComputes s)

def verticesComputes (s : ℕ) : Computes rawEncoding rowsEncoding (fun r => (raw s r).vertices) :=
  (pairComputes (oldRowsComputes s) (pairedRowsComputes s)).andThen (WireLists.append rowEncoding)

/-- The whole literal finite programme; the same old edge word follows the
new vertex word. This compiler needs no balancedness or correctness premise. -/
def computes (s : ℕ) : Computes rawEncoding rawEncoding (raw s) :=
  recode (pairComputes (verticesComputes s) edgesComputes)
    id (fun _ => rfl) (fun _ => rfl)

def outputs (s : ℕ) (r : RawClosedNetwork) :
    TM2OutputsInTime (computes s).machine.computer (rawEncoding.encode r)
      (some (rawEncoding.encode (raw s r)))
      ((computes s).time.eval (rawEncoding.encode r).length) :=
  (computes s).outputs r

theorem output_parses (s : ℕ) (r : RawClosedNetwork) :
    rawEncoding.decode (rawEncoding.encode (raw s r))=some (raw s r) :=
  rawEncoding.decode_encode (raw s r)

theorem output_length (s : ℕ) (r : RawClosedNetwork) :
    (rawEncoding.encode (raw s r)).length ≤
      (computes s).outputBound.bound.eval (rawEncoding.encode r).length :=
  (computes s).outputBound.length_le r

theorem primitive_cost (s : ℕ) (r : RawClosedNetwork) :
    primitiveCost (computes s).machine ((computes s).outputs r).steps
      (some (initList (computes s).machine.computer (rawEncoding.encode r))) ≤
      (primitivePolynomial (computes s)).eval (rawEncoding.encode r).length :=
  computes_primitive_cost (computes s) r

/-- Every physical compiler stack is charged, including list frames, copied
contexts, range cells and default-padding work in dynamic lookups. -/
theorem prefix_storage (s : ℕ) (r : RawClosedNetwork) (t : ℕ)
    (ht : t ≤ ((computes s).outputs r).steps) (z : (computes s).machine.Config)
    (hr : (fun q => q.bind (computes s).machine.computer.step)^[t]
      (some (initList (computes s).machine.computer (rawEncoding.encode r)))=some z) :
    stackSize z.stk ≤ (rawEncoding.encode r).length+
      (computes s).time.eval (rawEncoding.encode r).length*(computes s).machine.primitiveBudget := by
  have hs := (computes s).machine.run_size_le _ z t hr
  rw [Machine.size_init] at hs
  exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _
    (ht.trans ((computes s).outputs r).steps_le_m)) _)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PairedPinsCompiler
