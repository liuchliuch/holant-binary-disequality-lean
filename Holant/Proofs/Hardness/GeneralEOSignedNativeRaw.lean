import Holant.Proofs.Hardness.GeneralEOSignedNativeDecoded
import Holant.Proofs.Hardness.GeneralEOSignedParityProgram
import Holant.Proofs.Hardness.GeneralEOPairedCSPFamilyProgramme

/-! Parse actual validated native-network rows into their parity links.
Binary endpoint addresses are bounded by the physically counted edge list before
unary conversion. Every ordered row and pair is emitted, including self links. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedNativeRaw
open Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.OneHot.StackProgram.GraphLabelEncoding
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
namespace N
export GeneralEOSignedNativeParity (port links link)
end N
namespace Pr
export GeneralEOSignedParityProgram (Input inputEncoding rawInputEncoding natLinkEncoding fields links_encode tabulate)
end Pr
namespace C
export FixedGadgetSubstitution.Compiler
  (Input Query queryEncoding sourceComputes indexComputes originalRowComputes sourceLabel labelRecodeComputes edgeCountComputes vertexCountComputes)
end C
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (getD flatten)
end W
namespace A
export Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access (boundedUnary)
end A
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
abbrev unary := UnaryBinary.unaryEncoding
variable {s : ℕ} {arity : ℕ → ℕ}
variable (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))
abbrev Input := C.Input s 1 arity
abbrev inputEncoding := RawClosedNetwork.validatedEncoding s 1 arity
abbrev Query := C.Query s 1 arity
abbrev queryEncoding := C.queryEncoding s 1 arity

def rowPairing (r : Input (s:=s) (arity:=arity)) (v : Fin r.val.vertices.length) :
    OrientedPerfectPairing ((r.val.shape r.property).arity v) :=
  P (r.val.signatureLabel r.property v)

def parsed (r : Input (s:=s) (arity:=arity)) : Pr.Input :=
  ⟨r.val.edges.length,N.links (r.val.shape r.property) (rowPairing P r)⟩

def endpoint (x : Query (s:=s) (arity:=arity)) (k : ℕ) : ℕ × Bool :=
  let q := (x.1.val.vertices.get x.2).2.getD k (0,false)
  (min x.1.val.edges.length q.1,q.2)

def rawLink (i : Fin s) (x : Query (s:=s) (arity:=arity)) (j : Fin (P i).count) :
    (ℕ × ℕ) × Bool :=
  let a := endpoint x ((P i).ports (j,false)).val
  let b := endpoint x ((P i).ports (j,true)).val
  ((a.1,b.1),Bool.xor true (Bool.xor a.2 b.2))

def row (x : Query (s:=s) (arity:=arity)) : List ((ℕ × ℕ) × Bool) :=
  List.ofFn (rawLink P (C.sourceLabel s 1 arity x) x)

def rawLinks (r : Input (s:=s) (arity:=arity)) : List ((ℕ × ℕ) × Bool) :=
  (List.finRange r.val.vertices.length).flatMap (fun v => row P ⟨r,v⟩)

theorem native_port (r : Input (s:=s) (arity:=arity)) (v : Fin r.val.vertices.length)
    (k : Fin (arity (r.val.vertices.get v).1)) :
    N.port (r.val.shape r.property) v k = r.val.route r.property ⟨v,k⟩ := rfl

theorem endpoint_native (x : Query (s:=s) (arity:=arity))
    (k : Fin (arity (x.1.val.vertices.get x.2).1)) :
    endpoint x k.val =
      ((N.port (x.1.val.shape x.1.property) x.2 k).1.val,
        (N.port (x.1.val.shape x.1.property) x.2 k).2) := by
  rw [native_port]
  have hk : k.val < (x.1.val.vertices.get x.2).2.length := by
    rw [(x.1.property.1 x.2).2]
    exact k.isLt
  have hb := x.1.val.portEndpoint_bound x.1.property ⟨x.2,k⟩
  simp only [RawClosedNetwork.portEndpoint,List.get_eq_getElem,Fin.val_cast] at hb
  simp only [endpoint,List.getD_eq_getElem _ _ hk,RawClosedNetwork.route,
    RawClosedNetwork.portEndpoint,List.get_eq_getElem,Fin.val_cast]
  simp only [List.get_eq_getElem] at hk
  rw [List.getD_eq_getElem _ _ hk,Nat.min_eq_right (Nat.le_of_lt hb)]

theorem rawLinks_eq (r : Input (s:=s) (arity:=arity)) :
    rawLinks P r=(Pr.fields (parsed P r)).2 := by
  simp only [rawLinks,Pr.fields,parsed,N.links,List.map_flatMap]
  apply List.flatMap_congr
  intro v hv
  simp only [row,List.map_ofFn]
  congr 1
  funext j
  simp only [rawLink,N.link,rowPairing,C.sourceLabel,RawClosedNetwork.signatureLabel]
  rw [endpoint_native,endpoint_native]
  rfl

def rawEndpointComputes (k : ℕ) : Computes (queryEncoding (s:=s) (arity:=arity))
    RawClosedNetwork.endpointEncoding (fun x => (x.1.val.vertices.get x.2).2.getD k (0,false)) :=
  (pairComputes ((C.originalRowComputes s 1 arity).andThen
    (recode (Wiring.secondComputes encodingNatBool (framedListEncoding RawClosedNetwork.endpointEncoding))
      id (fun _ => rfl) (fun _ => rfl)))
    (constantComputes (queryEncoding (s:=s) (arity:=arity)) unary k)).andThen
    (W.getD RawClosedNetwork.endpointEncoding (0,false))

def endpointComputes (k : ℕ) : Computes (queryEncoding (s:=s) (arity:=arity))
    (pairEncoding unary encodingBoolBool) (fun x => endpoint x k) := by
  let ep := rawEndpointComputes (s:=s) (arity:=arity) k
  let num := ep.andThen (recode (Wiring.firstComputes encodingNatBool encodingBoolBool)
    id (fun _ => rfl) (fun _ => rfl))
  let bit := ep.andThen (recode (Wiring.secondComputes encodingNatBool encodingBoolBool)
    id (fun _ => rfl) (fun _ => rfl))
  exact pairComputes ((pairComputes ((C.sourceComputes s 1 arity).andThen
    (C.edgeCountComputes s 1 arity)) num).andThen A.boundedUnary) bit

def parityComputes : Computes (pairEncoding encodingBoolBool encodingBoolBool) encodingBoolBool
    (fun p => Bool.xor true (Bool.xor p.1 p.2)) :=
  FiniteRecode.computes (pairEncoding encodingBoolBool encodingBoolBool) encodingBoolBool
    (fun p => Bool.xor true (Bool.xor p.1 p.2)) 5
    (fun p => by rcases p with ⟨a,b⟩; cases a <;> cases b <;> decide)

def rawLinkComputes (i : Fin s) (j : Fin (P i).count) :
    Computes (queryEncoding (s:=s) (arity:=arity)) Pr.natLinkEncoding (fun x => rawLink P i x j) := by
  let a := endpointComputes (s:=s) (arity:=arity) ((P i).ports (j,false)).val
  let b := endpointComputes (s:=s) (arity:=arity) ((P i).ports (j,true)).val
  exact pairComputes
    (pairComputes (a.andThen (Wiring.firstComputes unary encodingBoolBool))
      (b.andThen (Wiring.firstComputes unary encodingBoolBool)))
    ((pairComputes (a.andThen (Wiring.secondComputes unary encodingBoolBool))
      (b.andThen (Wiring.secondComputes unary encodingBoolBool))).andThen parityComputes)

def rowForComputes (i : Fin s) :
    Computes (queryEncoding (s:=s) (arity:=arity)) (framedListEncoding Pr.natLinkEncoding)
      (fun x => List.ofFn (rawLink P i x)) :=
  congrComputes (fixedListComputes (queryEncoding (s:=s) (arity:=arity)) Pr.natLinkEncoding
    (fun x j => rawLink P i x j) (rawLinkComputes P i) (List.finRange (P i).count))
    (fun x => by apply List.ext_getElem <;> simp)

def rowComputes : Computes (queryEncoding (s:=s) (arity:=arity))
    (framedListEncoding Pr.natLinkEncoding) (row P) :=
  chooseComputes (queryEncoding (s:=s) (arity:=arity)) (framedListEncoding Pr.natLinkEncoding) s
    (C.sourceLabel s 1 arity) (fun x i => List.ofFn (rawLink P i x))
    (C.labelRecodeComputes s 1 arity unary Fin.val) (rowForComputes P)

def rawLinksComputes : Computes (inputEncoding (s:=s) (arity:=arity))
    (framedListEncoding Pr.natLinkEncoding) (rawLinks P) :=
  congrComputes ((Pr.tabulate (inputEncoding (s:=s) (arity:=arity))
    (framedListEncoding Pr.natLinkEncoding) (fun r => r.val.vertices.length)
    (C.vertexCountComputes s 1 arity) (fun r v => row P ⟨r,v⟩) (rowComputes P)).andThen
    (W.flatten Pr.natLinkEncoding)) (fun _ => by simp [rawLinks,List.flatMap_def])

/-- Physical parser into the bounded parity programme input. The source is
exactly the original validated network encoding; it supplies no graph advice. -/
def parsedComputes : Computes (inputEncoding (s:=s) (arity:=arity)) Pr.inputEncoding (parsed P) :=
  recode (pairComputes (C.edgeCountComputes s 1 arity) (rawLinksComputes P)) id (fun _ => rfl)
    (fun r => by
      change (Pr.rawInputEncoding).encode (r.val.edges.length,rawLinks P r)=_
      rw [rawLinks_eq]
      simp only [Pr.rawInputEncoding,pairEncoding_encode,Pr.inputEncoding,sigmaEncoding,
        Pr.fields,Pr.links_encode]
      rfl)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedNativeRaw
