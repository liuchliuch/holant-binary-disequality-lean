import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ChainCompilerRecords
import Holant.Complexity.BinaryInterpolation.Chains.Compiler.Occurrence

/-! A finite Boolean machine emits the four ordered ports of every chain
copy from unary k, unary copy index, the boundary list, and a binary offset. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerLocalRows
open Holant.Complexity Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution RawClosedNetwork
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
namespace B
export Holant.Complexity.BinaryInterpolation.Chains.Compiler
  (LocalInput localEncoding RowInput rowEncoding contextComputes indexComputes lengthComputes
   placementComputes offsetComputes successorComputes)
end B
namespace R
export GlobalCloseCompletionComplementQ4ChainCompilerRecords (explicitRow explicitTemplate incoming outgoing)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096
set_option Elab.async false

abbrev LocalInput:=B.LocalInput
abbrev localEncoding:=B.localEncoding
abbrev RowInput:=B.RowInput
abbrev rowEncoding:=B.rowEncoding

def incoming (channel : Bool) (x : RowInput) : RawEndpoint:=
  if x.2=0 then x.1.2.2.getD (if channel then 1 else 0) (0,false)
  else (x.1.2.1+2*(x.1.1-x.2)+(if channel then 0 else 1),true)
def outgoing (channel : Bool) (x : RowInput) : RawEndpoint:=
  if x.2=x.1.1 then x.1.2.2.getD (if channel then 3 else 2) (0,false)
  else (x.1.2.1+2*(x.1.1-1-x.2)+(if channel then 0 else 1),false)
def placedRow (label : ℕ) (x : RowInput) : RawVertex:=
  (label,if x.2=0 then [incoming false x,incoming true x,outgoing false x,outgoing true x]
    else [outgoing false x,outgoing true x,incoming false x,incoming true x])

theorem incoming_eq (channel : Bool) (x : RowInput) : incoming channel x=
    Template.placeEndpoint x.1.2.1 x.1.2.2 (R.incoming x.1.1 x.2 channel) := by
  cases channel <;> by_cases h : x.2=0 <;>
    simp [incoming,R.incoming,Template.placeEndpoint,h,Nat.add_assoc]

theorem outgoing_eq (channel : Bool) (x : RowInput) : outgoing channel x=
    Template.placeEndpoint x.1.2.1 x.1.2.2 (R.outgoing x.1.1 x.2 channel) := by
  cases channel <;> by_cases h : x.2=x.1.1 <;>
    simp [outgoing,R.outgoing,Template.placeEndpoint,h,Nat.add_assoc]

theorem placedRow_eq (label : ℕ) (x : RowInput) : placedRow label x=
    (label,(R.explicitRow label x.1.1 x.2).2.map (Template.placeEndpoint x.1.2.1 x.1.2.2)) := by
  unfold placedRow R.explicitRow
  split_ifs <;> simp only [List.map_cons,List.map_nil,incoming_eq,outgoing_eq]

def freshComputes (delta : RowInput→ℕ) (w : Computes rowEncoding encodingNatBool delta)
    (shift : ℕ) (side : Bool) :
    Computes rowEncoding endpointEncoding (fun x=>(x.1.2.1+2*delta x+shift,side)) := by
  let twice := (pairComputes (constantComputes rowEncoding encodingNatBool 2) w).andThen
    Holant.Complexity.BinaryInterpolation.Chains.Compiler.Occurrence.multiplyComputes
  let edge := (pairComputes ((pairComputes B.offsetComputes twice).andThen addComputes)
    (constantComputes rowEncoding encodingNatBool shift)).andThen addComputes
  exact recode (pairComputes edge (constantComputes rowEncoding encodingBoolBool side)) id
    (fun _=>rfl) (fun _=>rfl)

def firstComputes : Computes rowEncoding encodingBoolBool (fun x=>decide (x.2=0)) :=
  (pairComputes B.indexComputes (constantComputes rowEncoding encodingNatBool 0)).andThen Endpoints.equalComputes

def incomingComputes (channel : Bool) : Computes rowEncoding endpointEncoding (incoming channel) := by
  let difference := (pairComputes B.lengthComputes B.indexComputes).andThen Endpoints.subtractComputes
  exact congrComputes (ifComputes firstComputes
    (B.placementComputes.andThen (boundaryComputes (if channel then 1 else 0)))
    (freshComputes _ difference (if channel then 0 else 1) true)) (fun x=>by simp [incoming])

def outgoingComputes (channel : Bool) : Computes rowEncoding endpointEncoding (outgoing channel) := by
  let test := (pairComputes B.indexComputes B.lengthComputes).andThen Endpoints.equalComputes
  let previous := (pairComputes B.lengthComputes (constantComputes rowEncoding encodingNatBool 1)).andThen
    Endpoints.subtractComputes
  let difference := (pairComputes previous B.indexComputes).andThen Endpoints.subtractComputes
  exact congrComputes (ifComputes test
    (B.placementComputes.andThen (boundaryComputes (if channel then 3 else 2)))
    (freshComputes _ difference (if channel then 0 else 1) false)) (fun x=>by simp [outgoing])

def port (first : Bool) (x : RowInput) (i : Fin 4) : RawEndpoint:=
  if first then ![incoming false x,incoming true x,outgoing false x,outgoing true x] i
  else ![outgoing false x,outgoing true x,incoming false x,incoming true x] i

def portComputes (first : Bool) : (i : Fin 4)→Computes rowEncoding endpointEncoding (fun x=>port first x i) := by
  cases first
  · exact Fin.cases (outgoingComputes false) (Fin.cases (outgoingComputes true)
      (Fin.cases (incomingComputes false) (Fin.cases (incomingComputes true) (fun i=>Fin.elim0 i))))
  · exact Fin.cases (incomingComputes false) (Fin.cases (incomingComputes true)
      (Fin.cases (outgoingComputes false) (Fin.cases (outgoingComputes true) (fun i=>Fin.elim0 i))))

def portsComputes (first : Bool) : Computes rowEncoding (framedListEncoding endpointEncoding)
    (fun x=>([0,1,2,3] : List (Fin 4)).map (port first x)) :=
  fixedListComputes rowEncoding endpointEncoding (port first) (portComputes first) [0,1,2,3]

def rowComputes (label : ℕ) : Computes rowEncoding vertexEncoding (placedRow label) := by
  exact recode (pairComputes (constantComputes rowEncoding encodingNatBool label)
    (ifComputes firstComputes (portsComputes true) (portsComputes false))) id
    (fun _=>rfl) (fun x=>by by_cases h : x.2=0 <;> simp [port,placedRow,h] <;> rfl)

def placedRows (label : ℕ) (x : LocalInput) : List RawVertex:=
  (List.range (x.1+1)).map (fun i=>placedRow label (x,i))

def rowsComputes (label : ℕ) : Computes localEncoding (framedListEncoding vertexEncoding) (placedRows label) := by
  let prepare := pairComputes (identityComputes localEncoding)
    (((Wiring.firstComputes UnaryBinary.unaryEncoding placementEncoding).andThen B.successorComputes).andThen
      ComponentSelection.UnaryRange.computes)
  exact prepare.andThen (mapListComputes localEncoding UnaryBinary.unaryEncoding vertexEncoding
    (fun x i=>placedRow label (x,i)) (rowComputes label))

theorem placedRows_eq (label edge : ℕ) (x : LocalInput) : placedRows label x=
    (R.explicitTemplate label edge x.1).placeVertices x.2.1 x.2.2 := by
  simp only [placedRows,R.explicitTemplate,Template.placeVertices,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro i _
  exact placedRow_eq label (x,i)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerLocalRows
end
