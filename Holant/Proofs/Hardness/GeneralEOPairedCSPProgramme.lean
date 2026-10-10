import Holant.Proofs.Hardness.GeneralEOPairedCSPRaw
import Holant.Proofs.Hardness.BinaryCSPProgrammeScan

/-! A genuine finite Boolean-stack writer for arbitrary fixed paired arity.
Every row/edge/address is emitted by composed physical programs. The fixed
pairing is compiled into finite control; no incidence certificate is input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPProgramme
open Turing Computability Holant Holant.Tractable Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing GeneralEOPairedCSPRaw
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate replicate)
end W
namespace A
export Holant.LocalDrafts.Tractability.AffineMachine.AccessPrograms (unaryAdd)
export Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access (cons)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

variable {n : ℕ} (p : OrientedPerfectPairing n)

def portList : List (ℕ×Bool) := List.ofFn fun k : Fin n=>
  ((p.ports.symm k).1.val,(p.ports.symm k).2)

def port (r : Raw) (v : ℕ) (q : ℕ×Bool) : RawEndpoint :=
  (if q.2 then BinaryCSPProgrammeScan.next (r.addresses,v*p.count+q.1)
    else v*p.count+q.1,q.2)

def row (label : ℕ) (r : Raw) (v : ℕ) : RawVertex :=
  (label,(portList p).map (port p r v))

def raw (label : ℕ) (r : Raw) : RawClosedNetwork :=
  ⟨(List.range r.constraints).map (row p label r),List.replicate (r.constraints*p.count) 0⟩

abbrev rowEncoding := pairEncoding encoding unary
abbrev portsEncoding := framedListEncoding RawClosedNetwork.endpointEncoding

def slotComputes (j : ℕ) : Computes rowEncoding unary (fun x=>x.2*p.count+j) :=
  (pairComputes
    ((pairComputes (Wiring.secondComputes encoding unary)
      (constantComputes rowEncoding unary p.count)).andThen
        BinaryInterpolation.WeightCompiler.multiplyUnaryComputes)
    (constantComputes rowEncoding unary j)).andThen A.unaryAdd

def nextComputes (j : ℕ) : Computes rowEncoding unary
    (fun x=>BinaryCSPProgrammeScan.next (x.1.addresses,x.2*p.count+j)) :=
  (pairComputes ((Wiring.firstComputes encoding unary).andThen addressesComputes)
    (slotComputes p j)).andThen BinaryCSPProgrammeScan.nextComputes

def portComputes (q : ℕ×Bool) : Computes rowEncoding RawClosedNetwork.endpointEncoding
    (fun x=>port p x.1 x.2 q) := by
  rcases q with ⟨j,b⟩
  cases b with
  | false => exact recode (pairComputes ((slotComputes p j).andThen UnaryBinary.computes)
      (constantComputes rowEncoding encodingBoolBool false)) id (fun _=>rfl) (fun _=>rfl)
  | true => exact recode (pairComputes ((nextComputes p j).andThen UnaryBinary.computes)
      (constantComputes rowEncoding encodingBoolBool true)) id (fun _=>rfl) (fun _=>rfl)

def portsComputes (ports : List (ℕ×Bool)) : Computes rowEncoding portsEncoding
    (fun x=>ports.map (port p x.1 x.2)) :=
  match ports with
  | [] => constantComputes rowEncoding portsEncoding []
  | q::qs => (pairComputes (portComputes p q) (portsComputes qs)).andThen
      (A.cons RawClosedNetwork.endpointEncoding)

def rowComputes (label : ℕ) : Computes rowEncoding RawClosedNetwork.vertexEncoding
    (fun x=>row p label x.1 x.2) :=
  recode (pairComputes (constantComputes rowEncoding encodingNatBool label)
    (portsComputes p (portList p))) id (fun _=>rfl) (fun _=>rfl)

def edgeCountComputes : Computes encoding unary (fun r=>r.constraints*p.count) :=
  (pairComputes constraintsComputes (constantComputes encoding unary p.count)).andThen
    BinaryInterpolation.WeightCompiler.multiplyUnaryComputes

def rawComputes (label : ℕ) : Computes encoding RawClosedNetwork.encoding (raw p label) := by
  let vertices := W.tabulate encoding RawClosedNetwork.vertexEncoding Raw.constraints
    constraintsComputes (row p label) (rowComputes p label)
  let edges := (edgeCountComputes p).andThen (W.replicate encodingNatBool 0)
  exact recode (pairComputes vertices edges) id (fun _=>rfl) (fun _=>rfl)

def polyTime (label : ℕ) : PolyTime encoding RawClosedNetwork.encoding (raw p label) :=
  (rawComputes p label).toPolyTime

theorem raw_counts (label : ℕ) (r : Raw) :
    (raw p label r).vertices.length=r.constraints ∧
      (raw p label r).edges.length=r.constraints*p.count := by simp [raw]

theorem output_bound (label : ℕ) (r : Raw) :
    (RawClosedNetwork.encoding.encode (raw p label r)).length≤
      (rawComputes p label).outputBound.bound.eval (encoding.encode r).length :=
  (rawComputes p label).outputBound.length_le r

theorem primitive_bound (label : ℕ) (r : Raw) :
    primitiveCost (rawComputes p label).machine ((rawComputes p label).outputs r).steps
      (some (initList (rawComputes p label).machine.computer (encoding.encode r)))≤
      (primitivePolynomial (rawComputes p label)).eval (encoding.encode r).length :=
  computes_primitive_cost (rawComputes p label) r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPProgramme
