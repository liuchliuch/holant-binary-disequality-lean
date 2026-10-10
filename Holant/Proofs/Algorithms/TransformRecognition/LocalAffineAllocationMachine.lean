import Holant.Proofs.Algorithms.TransformRecognition.RawLocalAffineEnumeration
import Holant.Proofs.Algorithms.TransformRecognition.OriginalAllocatedPackingMachine
import Holant.Proofs.Algorithms.TransformRecognition.OriginalCatalogueMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.LocalAffineAllocationMachine
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open CommonFieldMachine (Executes)

abbrev Family := OriginalCatalogueMachine.Family
abbrev Input := Family × (ℕ × RawLocalAffineEnumeration.Candidate)
abbrev tailEncoding := pairEncoding encodingNatBool RawLocalAffineEnumeration.candidateEncoding
abbrev encoding := pairEncoding OriginalCatalogueMachine.familyEncoding tailEncoding
abbrev cellEncoding := pairEncoding encoding encodingNatBool

def emptyChoice : RawLocalAffineEnumeration.Choice := (false,(0,[],0,[],[]))
def entries (xs : Family) : ℕ := (OriginalCatalogueMachine.catalogue xs).length
def count (xs : Family) : ℕ := entries xs+entries xs
def key (r : Input) (j : ℕ) : OriginalCatalogueMachine.Key :=
  (OriginalCatalogueMachine.atVertex r.1 r.2.1).getD j (r.2.1,[])
def record (r : Input) (j : ℕ) : RationalLocalAffineRowsMachine.Record :=
  let k := key r j
  let c := r.2.2.getD j emptyChoice
  (k.2,c.1,OriginalCatalogueMachine.address (0,OriginalCatalogueMachine.catalogue r.1,k),
    OriginalCatalogueMachine.address (entries r.1,OriginalCatalogueMachine.catalogue r.1,k),c.2)
def records (r : Input) : List RationalLocalAffineRowsMachine.Record :=
  (List.range (OriginalCatalogueMachine.atVertex r.1 r.2.1).length).map (record r)

noncomputable section

def entriesExecutes : Executes OriginalCatalogueMachine.familyEncoding encodingNatBool entries :=
  OriginalCatalogueMachine.executes.comp (Executes.ofComputes
    ((WireLists.lengthComputes OriginalCatalogueMachine.keyEncoding).andThen UnaryBinary.computes))

def countExecutes : Executes OriginalCatalogueMachine.familyEncoding encodingNatBool count :=
  (entriesExecutes.pair entriesExecutes).comp (Executes.ofComputes RationalInputMachine.Programs.add)

def family := Wiring.firstComputes OriginalCatalogueMachine.familyEncoding tailEncoding
def tail := Wiring.secondComputes OriginalCatalogueMachine.familyEncoding tailEncoding
def slot := tail.andThen (Wiring.firstComputes encodingNatBool RawLocalAffineEnumeration.candidateEncoding)
def candidate := tail.andThen (Wiring.secondComputes encodingNatBool RawLocalAffineEnumeration.candidateEncoding)
def keys : Executes encoding OriginalCatalogueMachine.keysEncoding
    (fun r : Input => OriginalCatalogueMachine.atVertex r.1 r.2.1) :=
  (Executes.ofComputes (pairComputes family slot)).comp OriginalCatalogueMachine.vertexExecutes

def recordExecutes : Executes cellEncoding RationalLocalAffineRowsMachine.recordEncoding
    (fun p : Input × ℕ => record p.1 p.2) := by
  let context := Wiring.firstComputes encoding encodingNatBool
  let j := Wiring.secondComputes encoding encodingNatBool
  let words := (Executes.ofComputes context).comp keys
  -- List.lookup has a fixed default; the generated range always reads a
  -- present key. Use a fixed default in the implementation via the source
  -- slot label stored separately, then restore that label in the record.
  let wordList := words.comp (Executes.ofComputes
    (WireLists.mapComputes OriginalCatalogueMachine.keyEncoding RationalTensorMachine.wordEncoding Prod.snd
      (Wiring.secondComputes encodingNatBool RationalTensorMachine.wordEncoding)))
  let word := (wordList.pair (Executes.ofComputes j)).comp
    (NegativeCertificateMachine.Lists.lookup RationalTensorMachine.wordEncoding [])
  let keyProgram := (Executes.ofComputes (context.andThen slot)).pair word
  let code := (Executes.ofComputes (pairComputes (context.andThen candidate) j)).comp
    (NegativeCertificateMachine.Lists.lookup RawLocalAffineEnumeration.choiceEncoding emptyChoice)
  let cat := (Executes.ofComputes (context.andThen family)).comp OriginalCatalogueMachine.executes
  let n := (Executes.ofComputes (context.andThen family)).comp entriesExecutes
  let zero := Executes.ofComputes (constantComputes cellEncoding encodingNatBool 0)
  let scale := (zero.pair (cat.pair keyProgram)).comp
    (Executes.ofComputes OriginalCatalogueMachine.addressComputes)
  let inverse := (n.pair (cat.pair keyProgram)).comp
    (Executes.ofComputes OriginalCatalogueMachine.addressComputes)
  let mask := code.comp (Executes.ofComputes (Wiring.firstComputes encodingBoolBool EncodedTable.encoding))
  let template := code.comp (Executes.ofComputes (Wiring.secondComputes encodingBoolBool EncodedTable.encoding))
  refine (word.pair (mask.pair (scale.pair (inverse.pair template)))).congr ?_
  intro p
  have hk : key p.1 p.2 = (p.1.2.1,
      ((OriginalCatalogueMachine.atVertex p.1.1 p.1.2.1).map Prod.snd).getD p.2 []) := by
    unfold key OriginalCatalogueMachine.atVertex
    simp only [List.map_map,Function.comp_def,List.map_id']
    exact List.getD_map _ [] (fun x => (p.1.2.1,x))
  simp only [record,hk,Function.comp_def]

def executes : Executes encoding RationalLocalAffineRowsMachine.recordsEncoding records :=
  NegativeCertificateMachine.Lists.map encoding encodingNatBool RationalLocalAffineRowsMachine.recordEncoding
    ((keys.comp (Executes.ofComputes
      ((WireLists.lengthComputes OriginalCatalogueMachine.keyEncoding).andThen UnaryBinary.computes))).comp
        RationalInputMachine.Programs.range)
    record recordExecutes
end
end Holant.LocalDrafts.MainChain.TransformRecognition.LocalAffineAllocationMachine
