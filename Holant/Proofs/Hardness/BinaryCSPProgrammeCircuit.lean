import Holant.Proofs.Hardness.BinaryCSPProgrammeCircuitBlocks

/-! Original accepted circuit bytes to the exact signed binary CSP tape.
Independent physical prefix scans/tabulations emit every gate and output cap;
the existing static-code theorem identifies the resulting flat graph exactly. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeCircuit
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open BinaryCSPProgrammeCore FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.RemoteWork.CountingBridge
namespace A
export BinaryCSPProgrammeCircuitAccess (rowsEncoding pairNat tagComputes startComputes resolveComputes)
end A
namespace B
export BinaryCSPProgrammeCircuitBlocks (rowsEncoding inputEncoding pinEncoding pinComputes nandComputes)
end B
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate flatten append getD lengthComputes succComputes)
export Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access (list₁)
end W
namespace G
export BinaryThreeSupportCodeGraph (start resolve blockAt staticRows compile compile_exact)
end G
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

abbrev Input := ℕ × Circuit.Code
abbrev inputEncoding := pairEncoding unary Circuit.codeEncoding
abbrev atEncoding := pairEncoding inputEncoding unary

def input (c : CircuitInstance) : Input := (c.inputs,c.circuit.code)

def inputComputes : Computes CircuitInstance.encoding inputEncoding input := by
  let rawFields : Computes CircuitInstance.encoding CircuitInstance.codeEncoding
      (fun c => (List.replicate c.inputs false,c.circuit.code)) :=
    recode (identityComputes CircuitInstance.codeEncoding)
      (fun c => (List.replicate c.inputs false,c.circuit.code)) (fun _ => rfl) (fun _ => rfl)
  let fields := recode rawFields id (fun _ => rfl) (fun _ => rfl)
  exact congrComputes (fields.andThen (leftMapComputes Circuit.codeEncoding
    (W.lengthComputes encodingBoolBool))) (fun c => by simp [input])

def inputs : Computes inputEncoding unary Prod.fst := Wiring.firstComputes unary Circuit.codeEncoding
def code : Computes inputEncoding Circuit.codeEncoding Prod.snd := Wiring.secondComputes unary Circuit.codeEncoding
def codeFields : Computes Circuit.codeEncoding (pairEncoding A.rowsEncoding encodingNatBool) id :=
  recode (identityComputes (pairEncoding A.rowsEncoding encodingNatBool)) id (fun _ => rfl) (fun _ => rfl)
def rows : Computes inputEncoding A.rowsEncoding (fun p => p.2.1) :=
  (code.andThen codeFields).andThen (Wiring.firstComputes A.rowsEncoding encodingNatBool)
def output : Computes inputEncoding encodingNatBool (fun p => p.2.2) :=
  (code.andThen codeFields).andThen (Wiring.secondComputes A.rowsEncoding encodingNatBool)
def count : Computes inputEncoding unary (fun p => p.2.1.length) := rows.andThen (W.lengthComputes Circuit.rowEncoding)

def startInput : Computes atEncoding BinaryCSPProgrammeCircuitAccess.startEncoding
    (fun x => ((x.1.2.1,x.1.1),x.2)) :=
  pairComputes (pairComputes ((Wiring.firstComputes inputEncoding unary).andThen rows)
    ((Wiring.firstComputes inputEncoding unary).andThen inputs)) (Wiring.secondComputes inputEncoding unary)

def atStart : Computes atEncoding unary (fun x => G.start x.1.2.1 x.1.1 x.2) := startInput.andThen A.startComputes
def atRow : Computes atEncoding Circuit.rowEncoding (fun x => x.1.2.1.getD x.2 (0,(0,0))) :=
  (pairComputes ((Wiring.firstComputes inputEncoding unary).andThen rows)
    (Wiring.secondComputes inputEncoding unary)).andThen (W.getD Circuit.rowEncoding (0,(0,0)))

def rowRefs : Computes Circuit.rowEncoding A.pairNat Prod.snd :=
  recode (Wiring.secondComputes encodingNatBool A.pairNat) id (fun _ => rfl) (fun _ => rfl)

def atReference (side : Bool) : Computes atEncoding encodingNatBool
    (fun x => G.resolve x.1.2.1 id x.1.1 x.2
      (if side then (x.1.2.1.getD x.2 (0,(0,0))).2.2 else (x.1.2.1.getD x.2 (0,(0,0))).2.1)) := by
  let refs := atRow.andThen rowRefs
  cases side with
  | false => exact (pairComputes startInput (refs.andThen (Wiring.firstComputes encodingNatBool encodingNatBool))).andThen A.resolveComputes
  | true => exact (pairComputes startInput (refs.andThen (Wiring.secondComputes encodingNatBool encodingNatBool))).andThen A.resolveComputes

def blockAtComputes : Computes atEncoding B.rowsEncoding
    (fun x => G.blockAt x.1.2.1 id x.1.1 x.2) := by
  let tag := atRow.andThen A.tagComputes
  let test := (pairComputes tag (constantComputes atEncoding encodingNatBool 2)).andThen Endpoints.lessComputes
  let bit := (pairComputes tag (constantComputes atEncoding encodingNatBool 1)).andThen Endpoints.equalComputes
  let yes := (pairComputes bit atStart).andThen B.pinComputes
  let no := (pairComputes (pairComputes (atReference false) (atReference true)) atStart).andThen B.nandComputes
  exact congrComputes (ifComputes test yes no)
    (fun x => by simp [G.blockAt,BinaryThreeSupportCodeGraph.block])

def endStart : Computes inputEncoding unary (fun p => G.start p.2.1 p.1 p.2.1.length) :=
  (pairComputes (identityComputes inputEncoding) count).andThen atStart
def endAddress : Computes inputEncoding encodingNatBool
    (fun p => G.resolve p.2.1 id p.1 p.2.1.length p.2.2) :=
  (pairComputes ((pairComputes (identityComputes inputEncoding) count).andThen startInput) output).andThen A.resolveComputes

def raw (p : Input) : Raw :=
  ⟨G.start p.2.1 p.1 p.2.1.length+1,
    (G.staticRows p.2.1 p.2.2 id p.1).1,(G.staticRows p.2.1 p.2.2 id p.1).2⟩

def rawComputes : Computes inputEncoding encoding raw := by
  let chunksE := W.tabulate inputEncoding edgesEncoding (fun p => p.2.1.length) count
    (fun p t => (G.blockAt p.2.1 id p.1 t).1)
    (blockAtComputes.andThen (Wiring.firstComputes edgesEncoding signsEncoding))
  let chunksS := W.tabulate inputEncoding signsEncoding (fun p => p.2.1.length) count
    (fun p t => (G.blockAt p.2.1 id p.1 t).2)
    (blockAtComputes.andThen (Wiring.secondComputes edgesEncoding signsEncoding))
  let lastEdge := W.list₁ edgeEncoding (pairComputes (endStart.andThen UnaryBinary.computes) endAddress)
  let lastSign := W.list₁ encodingNatBool (endStart.andThen UnaryBinary.computes)
  exact assemble (endStart.andThen W.succComputes)
    ((pairComputes (chunksE.andThen (W.flatten edgeEncoding)) lastEdge).andThen (W.append edgeEncoding))
    ((pairComputes (chunksS.andThen (W.flatten encodingNatBool)) lastSign).andThen (W.append encodingNatBool))

/-- No circuit compiler or time bound is supplied: this is the composition of
the literal parser/projection, prefix, row and final serialization machines. -/
def computes : Computes CircuitInstance.encoding encoding BinaryThreeSupportGraph.compile :=
  congrComputes (inputComputes.andThen rawComputes) (fun c => G.compile_exact c)

def polyTime : PolyTime CircuitInstance.encoding encoding BinaryThreeSupportGraph.compile := computes.toPolyTime

theorem all_prefix_fees (c : CircuitInstance) (t : ℕ)
    (ht : t≤computes.time.eval (CircuitInstance.encoding.encode c).length) :
    primitiveCost computes.machine t (some (initList computes.machine.computer (CircuitInstance.encoding.encode c)))≤
      (primitivePolynomial computes).eval (CircuitInstance.encoding.encode c).length :=
  BinaryCSPProgrammeCore.prefix_primitive_bound computes c t ht

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeCircuit
