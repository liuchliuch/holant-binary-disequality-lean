import Holant.Proofs.Hardness.GeneralEOPairedCSPFamilyRaw
import Holant.Proofs.Hardness.GeneralEOPairedCSPProgramme
import Holant.Proofs.Hardness.BinaryCSPProgrammeCircuitAccess
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Prefix

/-! Physical mixed-family row writer. Finite control contains all original
pairings; input labels select the actual fixed row programme. All row offsets
are calculated by scanning unary pair-count tokens of preceding labels. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPFamilyProgramme
open Turing Computability Holant Holant.Tractable Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing GeneralEOPairedCSPFamilyRaw
open FixedGadgetSubstitution.Compiler
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate replicate mapComputes lengthComputes getD)
end W
namespace A
export Holant.LocalDrafts.Tractability.AffineMachine.AccessPrograms (unaryAdd)
export Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access (cons)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

variable {s : ℕ} {arity : ℕ→ℕ} (P : (i : Fin s)→OrientedPerfectPairing (arity i.val))

abbrev rowEncoding (s : ℕ) := pairEncoding (encoding s) unary
abbrev countsEncoding := framedListEncoding unary
abbrev portsEncoding := framedListEncoding RawClosedNetwork.endpointEncoding

def port (r : Raw s) (v : ℕ) (q : ℕ×Bool) : RawEndpoint :=
  (if q.2 then BinaryCSPProgrammeScan.next (r.addresses,r.offset P v+q.1)
    else r.offset P v+q.1,q.2)

def rowFor (i : Fin s) (r : Raw s) (v : ℕ) : RawVertex :=
  (i.val,(GeneralEOPairedCSPProgramme.portList (P i)).map (port P r v))

def row (r : Raw s) (v : ℕ) : RawVertex :=
  ((List.finRange s).map (fun i=>rowFor P i r v)).getD ((r.labels.map Fin.val).getD v 0) (0,[])

def raw (r : Raw s) : RawClosedNetwork :=
  ⟨(List.range r.labels.length).map (row P r),List.replicate (r.edgeCount P) 0⟩

def labelRecodeComputes {B : Type} (e : Encoding B Bool) (f : Fin s→B) :
    Computes (labelEncoding s) e f :=
  FiniteRecode.computes (labelEncoding s) e f s.size
    (SignatureLabel.binaryFinEncoding_length_le s)

def countListComputes : Computes (encoding s) countsEncoding
    (fun r=>r.labels.map (fun i=>(P i).count)) :=
  labelsComputes.andThen (W.mapComputes (labelEncoding s) unary (fun i=>(P i).count)
    (labelRecodeComputes unary (fun i=>(P i).count)))

def sumComputes : Computes countsEncoding unary List.sum := by
  let run := Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Indexed.flatMapComputes
    unary (fun n=>List.replicate n true) (encodeComputes unary)
  exact recode run id (fun _=>rfl) (fun xs=>by
    change xs.flatMap (fun n=>List.replicate n true)=List.replicate xs.sum true
    simpa using flatMap_tokens xs id)

def offsetComputes : Computes (rowEncoding s) unary (fun x=>x.1.offset P x.2) :=
  ((pairComputes ((Wiring.firstComputes (encoding s) unary).andThen (countListComputes P))
    (Wiring.secondComputes (encoding s) unary)).andThen
      (BinaryCSPProgrammeCircuitAccess.takeComputes unary 0)).andThen sumComputes

def slotComputes (j : ℕ) : Computes (rowEncoding s) unary (fun x=>x.1.offset P x.2+j) :=
  (pairComputes (offsetComputes P) (constantComputes (rowEncoding s) unary j)).andThen A.unaryAdd

def nextComputes (j : ℕ) : Computes (rowEncoding s) unary
    (fun x=>BinaryCSPProgrammeScan.next (x.1.addresses,x.1.offset P x.2+j)) :=
  (pairComputes ((Wiring.firstComputes (encoding s) unary).andThen addressesComputes)
    (slotComputes P j)).andThen BinaryCSPProgrammeScan.nextComputes

def portComputes (q : ℕ×Bool) : Computes (rowEncoding s) RawClosedNetwork.endpointEncoding
    (fun x=>port P x.1 x.2 q) := by
  rcases q with ⟨j,b⟩
  cases b with
  | false => exact recode (pairComputes ((slotComputes P j).andThen UnaryBinary.computes)
      (constantComputes (rowEncoding s) encodingBoolBool false)) id (fun _=>rfl) (fun _=>rfl)
  | true => exact recode (pairComputes ((nextComputes P j).andThen UnaryBinary.computes)
      (constantComputes (rowEncoding s) encodingBoolBool true)) id (fun _=>rfl) (fun _=>rfl)

def portsComputes (ports : List (ℕ×Bool)) : Computes (rowEncoding s) portsEncoding
    (fun x=>ports.map (port P x.1 x.2)) :=
  match ports with
  | [] => constantComputes (rowEncoding s) portsEncoding []
  | q::qs => (pairComputes (portComputes P q) (portsComputes qs)).andThen
      (A.cons RawClosedNetwork.endpointEncoding)

def rowForComputes (i : Fin s) : Computes (rowEncoding s) RawClosedNetwork.vertexEncoding
    (fun x=>rowFor P i x.1 x.2) :=
  recode (pairComputes (constantComputes (rowEncoding s) encodingNatBool i.val)
    (portsComputes P (GeneralEOPairedCSPProgramme.portList (P i)))) id (fun _=>rfl) (fun _=>rfl)

def labelIndexComputes : Computes (rowEncoding s) unary
    (fun x=>(x.1.labels.map Fin.val).getD x.2 0) :=
  (pairComputes (((Wiring.firstComputes (encoding s) unary).andThen labelsComputes).andThen
    (W.mapComputes (labelEncoding s) unary Fin.val (labelRecodeComputes unary Fin.val)))
    (Wiring.secondComputes (encoding s) unary)).andThen (W.getD unary 0)

def rowComputes : Computes (rowEncoding s) RawClosedNetwork.vertexEncoding (fun x=>row P x.1 x.2) :=
  (pairComputes (fixedListComputes (rowEncoding s) RawClosedNetwork.vertexEncoding
    (fun x i=>rowFor P i x.1 x.2) (rowForComputes P) (List.finRange s))
    labelIndexComputes).andThen (W.getD RawClosedNetwork.vertexEncoding (0,[]))

def edgeCountComputes : Computes (encoding s) unary (fun r=>r.edgeCount P) :=
  (countListComputes P).andThen sumComputes

def rawComputes : Computes (encoding s) RawClosedNetwork.encoding (raw P) := by
  let vertices := W.tabulate (encoding s) RawClosedNetwork.vertexEncoding
    (fun r=>r.labels.length) (labelsComputes.andThen (W.lengthComputes (labelEncoding s)))
    (row P) (rowComputes P)
  let edges := (edgeCountComputes P).andThen (W.replicate encodingNatBool 0)
  exact recode (pairComputes vertices edges) id (fun _=>rfl) (fun _=>rfl)

def polyTime : PolyTime (encoding s) RawClosedNetwork.encoding (raw P) := (rawComputes P).toPolyTime

theorem raw_counts (r : Raw s) : (raw P r).vertices.length=r.labels.length ∧
    (raw P r).edges.length=r.edgeCount P := by simp [raw]

theorem output_bound (r : Raw s) :
    (RawClosedNetwork.encoding.encode (raw P r)).length≤
      (rawComputes P).outputBound.bound.eval ((encoding s).encode r).length :=
  (rawComputes P).outputBound.length_le r

theorem primitive_bound (r : Raw s) :
    primitiveCost (rawComputes P).machine ((rawComputes P).outputs r).steps
      (some (initList (rawComputes P).machine.computer ((encoding s).encode r)))≤
      (primitivePolynomial (rawComputes P)).eval ((encoding s).encode r).length :=
  computes_primitive_cost (rawComputes P) r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPFamilyProgramme
