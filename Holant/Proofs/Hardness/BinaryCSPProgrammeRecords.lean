import Holant.Proofs.Hardness.BinaryCSPProgrammeScan
import Holant.Proofs.Hardness.EOBinaryPlaneScanNat
import Holant.Proofs.Hardness.EOBinaryPlaneRecords

/-! The physical original-M/native-X row writer. Each binary row emits one
original quaternary row with the fixed ordered opposite-port convention.
Successors are computed from the entire original occurrence list on tape. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeRecords
open Turing Computability Holant Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open BinaryCSPProgrammeCore
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate replicate)
end W
namespace A
export Holant.LocalDrafts.Tractability.AffineMachine.AccessPrograms (flatMap unaryAdd)
export Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access (cons list₁ list₃)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

def addresses (r : Raw) : List ℕ := r.edges.flatMap (fun e => [e.1,e.2])

def addressesComputes : Computes encoding BinaryCSPProgrammeScan.addressesEncoding addresses :=
  edgesComputes.andThen (A.flatMap edgeEncoding encodingNatBool (fun e => [e.1,e.2])
    ((pairComputes (Wiring.firstComputes encodingNatBool encodingNatBool)
      (A.list₁ encodingNatBool (Wiring.secondComputes encodingNatBool encodingNatBool))).andThen
        (A.cons encodingNatBool)))

@[simp] theorem addresses_length (r : Raw) : (addresses r).length=r.edges.length*2 := by
  simp [addresses,List.length_flatMap,List.sum_replicate]

def row (r : Raw) (v : ℕ) : RawVertex :=
  (0,[(v*2,false),(BinaryCSPProgrammeScan.next (addresses r,v*2),true),
    (v*2+1,false),(BinaryCSPProgrammeScan.next (addresses r,v*2+1),true)])

def raw (r : Raw) : RawClosedNetwork :=
  ⟨(List.range r.edges.length).map (row r),List.replicate (r.edges.length*2) 0⟩

abbrev rowEncoding := pairEncoding encoding unary
abbrev portsEncoding := framedListEncoding RawClosedNetwork.endpointEncoding

def slotComputes (j : ℕ) : Computes rowEncoding unary (fun x => x.2*2+j) :=
  (pairComputes
    ((pairComputes (Wiring.secondComputes encoding unary) (constantComputes rowEncoding unary 2)).andThen
      BinaryInterpolation.WeightCompiler.multiplyUnaryComputes)
    (constantComputes rowEncoding unary j)).andThen A.unaryAdd

def nextComputes (j : ℕ) : Computes rowEncoding unary
    (fun x => BinaryCSPProgrammeScan.next (addresses x.1,x.2*2+j)) :=
  (pairComputes ((Wiring.firstComputes encoding unary).andThen addressesComputes) (slotComputes j)).andThen
    BinaryCSPProgrammeScan.nextComputes

def portComputes (j : ℕ) (positive : Bool) : Computes rowEncoding RawClosedNetwork.endpointEncoding
    (fun x => (if positive then BinaryCSPProgrammeScan.next (addresses x.1,x.2*2+j) else x.2*2+j,positive)) := by
  cases positive with
  | false => exact recode (pairComputes ((slotComputes j).andThen UnaryBinary.computes)
      (constantComputes rowEncoding encodingBoolBool false)) id (fun _ => rfl) (fun _ => rfl)
  | true => exact recode (pairComputes ((nextComputes j).andThen UnaryBinary.computes)
      (constantComputes rowEncoding encodingBoolBool true)) id (fun _ => rfl) (fun _ => rfl)

def rowComputes : Computes rowEncoding RawClosedNetwork.vertexEncoding (fun x => row x.1 x.2) := by
  let ports := (pairComputes (portComputes 0 false)
    (A.list₃ RawClosedNetwork.endpointEncoding (portComputes 0 true) (portComputes 1 false)
      (portComputes 1 true))).andThen (A.cons RawClosedNetwork.endpointEncoding)
  exact recode (pairComputes (constantComputes rowEncoding encodingNatBool 0) ports)
    id (fun _ => rfl) (fun x => by simp only [row,Nat.add_zero]; rfl)

def rawComputes : Computes encoding RawClosedNetwork.encoding raw := by
  let vertices := W.tabulate encoding RawClosedNetwork.vertexEncoding (fun r => r.edges.length)
    edgeCountComputes row rowComputes
  let n := (pairComputes edgeCountComputes (constantComputes encoding unary 2)).andThen
    BinaryInterpolation.WeightCompiler.multiplyUnaryComputes
  let edges := n.andThen (W.replicate encodingNatBool 0)
  exact recode (pairComputes vertices edges) id (fun _ => rfl) (fun _ => rfl)

def polyTime : PolyTime encoding RawClosedNetwork.encoding raw := rawComputes.toPolyTime

@[simp] theorem raw_vertices_length (r : Raw) : (raw r).vertices.length=r.edges.length := by simp [raw]
@[simp] theorem raw_edges (r : Raw) : (raw r).edges=List.replicate (r.edges.length*2) 0 := rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeRecords
