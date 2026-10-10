import Holant.Proofs.Counting.RawGraphMachine.Access


noncomputable section
namespace Holant.LocalDrafts.CountingHardness.RawGraphMachine
open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open VerifierCompiler.Stateful VerifierCompiler.Stateful.CapacityFrontend

abbrev endpointEncoding := RawClosedNetwork.endpointEncoding
abbrev envEncoding := framedListEncoding endpointEncoding
abbrev vertexEncoding := RawClosedNetwork.vertexEncoding
abbrev verticesEncoding := framedListEncoding vertexEncoding
def memoryEncoding : Encoding Memory Bool :=
  pairEncoding envEncoding (pairEncoding Access.unary verticesEncoding)
def workEncoding : Encoding Work Bool := pairEncoding Circuit.codeEncoding memoryEncoding

namespace Stages
variable {A : Type} {ea : Encoding A Bool}

def env : Computes memoryEncoding envEncoding (fun s => s.1) :=
  Wiring.firstComputes envEncoding (pairEncoding Access.unary verticesEncoding)
def rest := Wiring.secondComputes envEncoding (pairEncoding Access.unary verticesEncoding)
def offset : Computes memoryEncoding Access.unary (fun s => s.2.1) :=
  rest.andThen (Wiring.firstComputes Access.unary verticesEncoding)
def vertices : Computes memoryEncoding verticesEncoding (fun s => s.2.2) :=
  rest.andThen (Wiring.secondComputes Access.unary verticesEncoding)

def plus (k : ℕ) {f : A → ℕ} (w : Computes ea Access.unary f) :
    Computes ea Access.unary (fun a => f a + k) :=
  (pairComputes w (constantComputes ea Access.unary k)).andThen Unary.addComputes

def fresh (k : ℕ) (sign : Bool) {f : A → ℕ} (w : Computes ea Access.unary f) :
    Computes ea endpointEncoding (fun a => (f a + k, sign)) :=
  recode (pairComputes ((plus k w).andThen UnaryBinary.computes)
    (constantComputes ea encodingBoolBool sign)) id (fun _ => rfl) (fun _ => rfl)

def vertex {label : A → ℕ} {ports : A → List RawEndpoint}
    (wl : Computes ea encodingNatBool label) (wp : Computes ea envEncoding ports) :
    Computes ea vertexEncoding (fun a => (label a, ports a)) :=
  recode (pairComputes wl wp) id (fun _ => rfl) (fun _ => rfl)

def constantEncoding := pairEncoding encodingBoolBool memoryEncoding
def constantComputes : Computes constantEncoding memoryEncoding (fun p => constant p.1 p.2) := by
  let b := Wiring.firstComputes encodingBoolBool memoryEncoding
  let s := Wiring.secondComputes encodingBoolBool memoryEncoding
  let o := s.andThen offset
  let label := ifComputes b (FixedFieldMachines.constantComputes constantEncoding encodingNatBool 2)
    (FixedFieldMachines.constantComputes constantEncoding encodingNatBool 1)
  let row := vertex label (Access.list₁ endpointEncoding (fresh 0 false o))
  let emitted := Access.list₁ vertexEncoding row
  let nextEnv := (pairComputes (fresh 0 true o) (s.andThen env)).andThen (Access.cons endpointEncoding)
  let nextRows := (pairComputes (s.andThen vertices) emitted).andThen (ListAccess.appendComputes vertexEncoding)
  exact congrComputes (pairComputes nextEnv (pairComputes (plus 1 o) nextRows))
    (fun p => by simp [constant])

def nandEncoding := pairEncoding memoryEncoding (pairEncoding encodingNatBool encodingNatBool)

def nandComputes : Computes nandEncoding memoryEncoding (fun p => nand p.2.1 p.2.2 p.1) := by
  let s := Wiring.firstComputes memoryEncoding (pairEncoding encodingNatBool encodingNatBool)
  let refs := Wiring.secondComputes memoryEncoding (pairEncoding encodingNatBool encodingNatBool)
  let a := refs.andThen (Wiring.firstComputes encodingNatBool encodingNatBool)
  let b := refs.andThen (Wiring.secondComputes encodingNatBool encodingNatBool)
  let oldEnv := s.andThen env
  let o := s.andThen offset
  let e₁ := (pairComputes oldEnv (pairComputes a (fresh 0 true o))).andThen
    (Access.update endpointEncoding (0, false))
  let e₂ := (pairComputes e₁ (pairComputes b (fresh 2 true o))).andThen
    (Access.update endpointEncoding (0, false))
  let first := (pairComputes oldEnv a).andThen (Access.lookup endpointEncoding (0, false))
  -- This is a call on the actual returned e₁ word, not a read from oldEnv.
  let second := (pairComputes e₁ b).andThen (Access.lookup endpointEncoding (0, false))
  let copyLabel := FixedFieldMachines.constantComputes nandEncoding encodingNatBool 3
  let row₁ := vertex copyLabel
    (Access.list₃ endpointEncoding first (fresh 0 false o) (fresh 1 false o))
  let row₂ := vertex copyLabel
    (Access.list₃ endpointEncoding second (fresh 2 false o) (fresh 3 false o))
  let row₃ := vertex (FixedFieldMachines.constantComputes nandEncoding encodingNatBool 4)
    (Access.list₃ endpointEncoding (fresh 1 true o) (fresh 3 true o) (fresh 4 false o))
  let emitted := Access.list₃ vertexEncoding row₁ row₂ row₃
  let nextEnv := (pairComputes (fresh 4 true o) e₂).andThen (Access.cons endpointEncoding)
  let nextRows := (pairComputes (s.andThen vertices) emitted).andThen (ListAccess.appendComputes vertexEncoding)
  exact congrComputes (pairComputes nextEnv (pairComputes (plus 5 o) nextRows))
    (fun p => by simp [nand])

def gateEncoding := pairEncoding memoryEncoding Circuit.rowEncoding
def gateComputes : Computes gateEncoding memoryEncoding (fun p => gate p.1 p.2) := by
  let s := Wiring.firstComputes memoryEncoding Circuit.rowEncoding
  let r := Wiring.secondComputes memoryEncoding Circuit.rowEncoding
  let tag := r.andThen (Wiring.firstComputes encodingNatBool (pairEncoding encodingNatBool encodingNatBool))
  let refs := r.andThen (Wiring.secondComputes encodingNatBool (pairEncoding encodingNatBool encodingNatBool))
  let test := (pairComputes tag (FixedFieldMachines.constantComputes gateEncoding encodingNatBool 2)).andThen
    Endpoints.lessComputes
  let b := (pairComputes tag (FixedFieldMachines.constantComputes gateEncoding encodingNatBool 1)).andThen
    Endpoints.equalComputes
  let yes := (pairComputes b s).andThen constantComputes
  let no := (pairComputes s refs).andThen nandComputes
  exact congrComputes (ifComputes test yes no) (fun p => by simp [gate])

def code : Computes workEncoding Circuit.codeEncoding (fun s => s.1) :=
  Wiring.firstComputes Circuit.codeEncoding memoryEncoding
def memory : Computes workEncoding memoryEncoding (fun s => s.2) :=
  Wiring.secondComputes Circuit.codeEncoding memoryEncoding
def rows := code.andThen (Wiring.firstComputes (framedListEncoding Circuit.rowEncoding) encodingNatBool)
def output := code.andThen (Wiring.secondComputes (framedListEncoding Circuit.rowEncoding) encodingNatBool)

def advanceComputes : Computes workEncoding workEncoding advance := by
  let count := rows.andThen (Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Indexed.countComputes Circuit.rowEncoding)
  let empty := (pairComputes count (FixedFieldMachines.constantComputes workEncoding Access.unary 0)).andThen
    Unary.equalComputes
  let head := (pairComputes rows (FixedFieldMachines.constantComputes workEncoding Access.unary 0)).andThen
    (ListAccess.getDComputes Circuit.rowEncoding (0, 0, 0))
  let tail := rows.andThen (Access.tail Circuit.rowEncoding (0, 0, 0))
  let next := pairComputes (pairComputes tail output) ((pairComputes memory head).andThen gateComputes)
  refine congrComputes (ifComputes empty (identityComputes workEncoding) next) ?_
  intro s
  rcases s with ⟨⟨rs, out⟩, mem⟩
  cases rs <;> simp [advance]

def initialComputes : Computes CircuitInstance.codeEncoding workEncoding initial := by
  let base := CircuitInstance.codeEncoding
  let slots := Wiring.firstComputes (framedListEncoding encodingBoolBool) Circuit.codeEncoding
  let c := Wiring.secondComputes (framedListEncoding encodingBoolBool) Circuit.codeEncoding
  let count := slots.andThen (Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Indexed.countComputes encodingBoolBool)
  let idx := Wiring.secondComputes base Access.unary
  let pending := ListAccess.rangeComputes base endpointEncoding (fun x => x.1.length) count
    (fun p => (p.2, true)) (congrComputes (fresh 0 true idx) (fun _ => by simp))
  let free := vertex (FixedFieldMachines.constantComputes (pairEncoding base Access.unary) encodingNatBool 0)
    (Access.list₁ endpointEncoding (fresh 0 false idx))
  let initialRows := ListAccess.rangeComputes base vertexEncoding (fun x => x.1.length) count _ free
  exact congrComputes (pairComputes c (pairComputes pending (pairComputes count initialRows)))
    (fun x => by simp [initial])

def resultComputes : Computes workEncoding RawClosedNetwork.encoding result := by
  let es := memory.andThen env
  let o := memory.andThen offset
  let pre := memory.andThen vertices
  let base := workEncoding
  let context := Wiring.firstComputes base Access.unary
  let idx := Wiring.secondComputes base Access.unary
  let same := (pairComputes (idx.andThen UnaryBinary.computes) (context.andThen output)).andThen
    Endpoints.equalComputes
  let label := ifComputes same
    (FixedFieldMachines.constantComputes (pairEncoding base Access.unary) encodingNatBool 2)
    (FixedFieldMachines.constantComputes (pairEncoding base Access.unary) encodingNatBool 0)
  let p := (pairComputes (context.andThen es) idx).andThen (ListAccess.getDComputes endpointEncoding (0, false))
  let row := vertex label (Access.list₁ endpointEncoding p)
  let capRows := ListAccess.rangeComputes base vertexEncoding (fun s => s.2.1.length)
    (es.andThen (Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Indexed.countComputes endpointEncoding)) _ row
  let allRows := (pairComputes pre capRows).andThen (ListAccess.appendComputes vertexEncoding)
  let edges := o.andThen (ListAccess.replicateComputes encodingNatBool 0)
  exact recode (pairComputes allRows edges) id (fun _ => rfl)
    (fun s => by simp [result, finish, caps]; rfl)

end Stages
end Holant.LocalDrafts.CountingHardness.RawGraphMachine
