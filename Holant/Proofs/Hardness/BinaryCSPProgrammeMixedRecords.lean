import Holant.Proofs.Hardness.BinaryCSPProgrammeRecords

/-! A per-row polarity bit swaps the first two original incidence ports.
The successor scan and edge tape are the same physical occurrence-cycle
writer; no flipped signature is added to the palette. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeMixedRecords
open Turing Computability Holant Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open BinaryCSPProgrammeCore
open UniversalPairReduction.SmoothingCompiler
namespace R
export BinaryCSPProgrammeRecords (addresses addressesComputes portComputes row rowComputes)
end R
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate replicate getD)
end W
namespace A
export Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access (cons list₃)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

abbrev Input := Raw×List Bool
abbrev polaritiesEncoding := framedListEncoding encodingBoolBool
abbrev inputEncoding := pairEncoding encoding polaritiesEncoding
abbrev rowEncoding := pairEncoding inputEncoding unary

def row (a : Input) (v : ℕ) : RawVertex :=
  if a.2.getD v false then
    (0,[(BinaryCSPProgrammeScan.next (R.addresses a.1,v*2),true),(v*2,false),
      (v*2+1,false),(BinaryCSPProgrammeScan.next (R.addresses a.1,v*2+1),true)])
  else R.row a.1 v

def raw (a : Input) : RawClosedNetwork :=
  ⟨(List.range a.1.edges.length).map (row a),List.replicate (a.1.edges.length*2) 0⟩

def input : Computes inputEncoding encoding Prod.fst := Wiring.firstComputes encoding polaritiesEncoding
def atInput : Computes rowEncoding inputEncoding Prod.fst := Wiring.firstComputes inputEncoding unary
def atIndex : Computes rowEncoding unary Prod.snd := Wiring.secondComputes inputEncoding unary
def oldRow : Computes rowEncoding BinaryCSPProgrammeRecords.rowEncoding (fun x=>(x.1.1,x.2)) :=
  pairComputes (atInput.andThen input) atIndex

def atPolarity : Computes rowEncoding encodingBoolBool (fun x=>x.1.2.getD x.2 false) :=
  (pairComputes (atInput.andThen (Wiring.secondComputes encoding polaritiesEncoding)) atIndex).andThen
    (W.getD encodingBoolBool false)

def reversedRow : Computes rowEncoding RawClosedNetwork.vertexEncoding
    (fun x=>(0,[(BinaryCSPProgrammeScan.next (R.addresses x.1.1,x.2*2),true),(x.2*2,false),
      (x.2*2+1,false),(BinaryCSPProgrammeScan.next (R.addresses x.1.1,x.2*2+1),true)])) := by
  let port := fun j b=>oldRow.andThen (R.portComputes j b)
  let ports := (pairComputes (port 0 true)
    (A.list₃ RawClosedNetwork.endpointEncoding (port 0 false) (port 1 false) (port 1 true))).andThen
      (A.cons RawClosedNetwork.endpointEncoding)
  exact recode (pairComputes (constantComputes rowEncoding encodingNatBool 0) ports)
    id (fun _=>rfl) (fun _=>by simp only [Nat.add_zero]; rfl)

def rowComputes : Computes rowEncoding RawClosedNetwork.vertexEncoding (fun x=>row x.1 x.2) :=
  ifComputes atPolarity reversedRow (oldRow.andThen R.rowComputes)

def rawComputes : Computes inputEncoding RawClosedNetwork.encoding raw := by
  let count := input.andThen edgeCountComputes
  let vertices := W.tabulate inputEncoding RawClosedNetwork.vertexEncoding (fun a=>a.1.edges.length)
    count row rowComputes
  let n := (pairComputes count (constantComputes inputEncoding unary 2)).andThen
    BinaryInterpolation.WeightCompiler.multiplyUnaryComputes
  let edges := n.andThen (W.replicate encodingNatBool 0)
  exact recode (pairComputes vertices edges) id (fun _=>rfl) (fun _=>rfl)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeMixedRecords
