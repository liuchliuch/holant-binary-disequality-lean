import Holant.Proofs.Algorithms.TransformRecognition.OriginalAddressTablesMachine
import Holant.Proofs.Algorithms.TransformRecognition.OriginalAffineBranchMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineBranchMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Templates := List EncodedTable.Data × EncodedTable.Data
abbrev Input := OriginalFamilyPackingMachine.Input × Templates
abbrev templateListEncoding := framedListEncoding EncodedTable.encoding
abbrev templatesEncoding := pairEncoding templateListEncoding EncodedTable.encoding
abbrev encoding := pairEncoding OriginalFamilyPackingMachine.encoding templatesEncoding
def emptyTemplate : EncodedTable.Data := (0,[],0,[],[])
def imaginary (r : Input) : ℕ := OriginalFamilyPackingMachine.base r.1+(OriginalFamilyPackingMachine.original r.1).length
def vertexBlock (r : Input) (i : ℕ) : RationalAffineRowsMachine.Block :=
  (5+i,r.2.1.getD i emptyTemplate,
    OriginalAddressTablesMachine.table (r.1.1,OriginalFamilyPackingMachine.parameterCount r.1,i))
def edgeBlock (r : Input) : RationalAffineEdgeRowsMachine.Block :=
  (5+r.1.1.length,r.2.2,
    (OriginalAddressTablesMachine.table
      (r.1.1,OriginalFamilyPackingMachine.parameterCount r.1,r.1.1.length)).map Prod.snd)
def bodyInput (r : Input) : RationalAffineBodyMachine.Input :=
  (OriginalFamilyPackingMachine.width r.1,imaginary r,imaginary r+1,imaginary r+2,
    (List.range r.1.1.length).map (vertexBlock r),edgeBlock r)
def request (r : Input) : OriginalAffineBranchMachine.Input :=
  (OriginalFamilyPackingMachine.roots r.1,OriginalFamilyPackingMachine.addresses r.1,bodyInput r)

noncomputable section
def source := Wiring.firstComputes OriginalFamilyPackingMachine.encoding templatesEncoding
def family := source.andThen OriginalFamilyPackingMachine.family
def templates := Wiring.secondComputes OriginalFamilyPackingMachine.encoding templatesEncoding
def vertexTemplates := templates.andThen (Wiring.firstComputes templateListEncoding EncodedTable.encoding)
def edgeTemplate := templates.andThen (Wiring.secondComputes templateListEncoding EncodedTable.encoding)
def familyCount := (family.andThen (WireLists.lengthComputes OriginalFamilyPackingMachine.vertexEncoding)).andThen
  GraphPreprocessing.UnaryBinary.computes
def parameters := source.andThen OriginalFamilyPackingMachine.parameters
def imaginaryComputes : Computes encoding encodingNatBool imaginary :=
  (pairComputes (source.andThen OriginalFamilyPackingMachine.baseComputes)
    (source.andThen OriginalFamilyPackingMachine.originalsCount)).andThen RationalInputMachine.Programs.add

def vertexCell : Executes (pairEncoding encoding encodingNatBool) RationalAffineRowsMachine.blockEncoding
    (fun p : Input × ℕ => vertexBlock p.1 p.2) := by
  let ctx := Wiring.firstComputes encoding encodingNatBool
  let i := Wiring.secondComputes encoding encodingNatBool
  let scalar := (pairComputes (constantComputes _ encodingNatBool 5) i).andThen RationalInputMachine.Programs.add
  let template := (Executes.ofComputes (pairComputes (ctx.andThen vertexTemplates) i)).comp
    (NegativeCertificateMachine.Lists.lookup EncodedTable.encoding emptyTemplate)
  let tableInput := pairComputes (ctx.andThen family) (pairComputes (ctx.andThen parameters) i)
  let table := (Executes.ofComputes tableInput).comp OriginalAddressTablesMachine.executes
  exact (Executes.ofComputes scalar).pair (template.pair table)

def verticesExecutes : Executes encoding (framedListEncoding RationalAffineRowsMachine.blockEncoding)
    (fun r : Input => (List.range r.1.1.length).map (vertexBlock r)) :=
  NegativeCertificateMachine.Lists.map encoding encodingNatBool RationalAffineRowsMachine.blockEncoding
    ((Executes.ofComputes familyCount).comp RationalInputMachine.Programs.range) vertexBlock vertexCell

def edgeExecutes : Executes encoding RationalAffineEdgeRowsMachine.blockEncoding edgeBlock := by
  let scalar := (pairComputes (constantComputes encoding encodingNatBool 5) familyCount).andThen
    RationalInputMachine.Programs.add
  let table := (Executes.ofComputes (pairComputes family (pairComputes parameters familyCount))).comp
    OriginalAddressTablesMachine.executes
  let addressList := table.comp (Executes.ofComputes
    (WireLists.mapComputes RationalTensorMachine.rowEncoding encodingNatBool Prod.snd
      (Wiring.secondComputes RationalTensorMachine.wordEncoding encodingNatBool)))
  exact (Executes.ofComputes scalar).pair ((Executes.ofComputes edgeTemplate).pair addressList)

def bodyExecutes : Executes encoding RationalAffineBodyMachine.encoding bodyInput := by
  let width := Executes.ofComputes (source.andThen OriginalFamilyPackingMachine.widthComputes)
  let imag := Executes.ofComputes imaginaryComputes
  let sqrt := Executes.ofComputes (imaginaryComputes.andThen RationalInputMachine.Programs.successor)
  let eighth := Executes.ofComputes
    ((pairComputes imaginaryComputes (constantComputes encoding encodingNatBool 2)).andThen
      RationalInputMachine.Programs.add)
  exact width.pair (imag.pair (sqrt.pair (eighth.pair (verticesExecutes.pair edgeExecutes))))

def prepare : Executes encoding OriginalAffineBranchMachine.encoding request :=
  (Executes.ofComputes (source.andThen OriginalFamilyPackingMachine.rootsComputes)).pair
    (((Executes.ofComputes source).comp OriginalFamilyPackingMachine.addressesExecutes).pair bodyExecutes)

def machine := prepare.machine.compose OriginalAffineBranchMachine.machine

/-- Ordinary composition of the generated branch input with its actual run.
This helper is not a termination theorem; the final typed-source theorem must
derive the second run from original representation validity and catalogue
correspondence. Neither that proof nor a bound is a machine input. -/
def compose_output (r : Input) (b : Bool) (bound : ℕ)
    (run : TM2OutputsInTime OriginalAffineBranchMachine.machine.computer
      (OriginalAffineBranchMachine.encoding.encode (request r))
      (some (encodingBoolBool.encode b)) bound) :
    TM2OutputsInTime machine.computer (encoding.encode r) (some (encodingBoolBool.encode b))
      (prepare.cost r+2*((OriginalAffineBranchMachine.encoding.encode (request r)).length+1)+bound) :=
  Machine.compose_correct _ _ _ _ _ _ _ (prepare.outputs r) run
end
end Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineBranchMachine
