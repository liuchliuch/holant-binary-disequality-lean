import Holant.Proofs.Algorithms.TransformRecognition.OriginalCatalogueMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalAddressTablesMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Input := OriginalCatalogueMachine.Family × (ℕ × ℕ)
abbrev indicesEncoding := pairEncoding encodingNatBool encodingNatBool
abbrev encoding := pairEncoding OriginalCatalogueMachine.familyEncoding indicesEncoding
abbrev Context := ℕ × List OriginalCatalogueMachine.Key
abbrev contextEncoding := pairEncoding encodingNatBool OriginalCatalogueMachine.keysEncoding
def table (r : Input) : List RationalTensorMachine.Row :=
  (OriginalCatalogueMachine.atVertex r.1 r.2.2).map (fun k =>
    (k.2,OriginalCatalogueMachine.address (r.2.1,OriginalCatalogueMachine.catalogue r.1,k)))

noncomputable section
def cell : Executes (pairEncoding contextEncoding OriginalCatalogueMachine.keyEncoding)
    RationalTensorMachine.rowEncoding
    (fun p : Context × OriginalCatalogueMachine.Key =>
      (p.2.2,OriginalCatalogueMachine.address (p.1.1,p.1.2,p.2))) := by
  let ctx := Wiring.firstComputes contextEncoding OriginalCatalogueMachine.keyEncoding
  let key := Wiring.secondComputes contextEncoding OriginalCatalogueMachine.keyEncoding
  let q := ctx.andThen (Wiring.firstComputes encodingNatBool OriginalCatalogueMachine.keysEncoding)
  let keys := ctx.andThen (Wiring.secondComputes encodingNatBool OriginalCatalogueMachine.keysEncoding)
  let word := key.andThen (Wiring.secondComputes encodingNatBool RationalTensorMachine.wordEncoding)
  exact Executes.ofComputes (pairComputes word
    ((pairComputes q (pairComputes keys key)).andThen OriginalCatalogueMachine.addressComputes))

def executes : Executes encoding RationalTensorMachine.tableEncoding table := by
  let family := Wiring.firstComputes OriginalCatalogueMachine.familyEncoding indicesEncoding
  let indices := Wiring.secondComputes OriginalCatalogueMachine.familyEncoding indicesEncoding
  let q := indices.andThen (Wiring.firstComputes encodingNatBool encodingNatBool)
  let vertex := indices.andThen (Wiring.secondComputes encodingNatBool encodingNatBool)
  let keys := (Executes.ofComputes family).comp OriginalCatalogueMachine.executes
  let context := (Executes.ofComputes q).pair keys
  let selected := (Executes.ofComputes (pairComputes family vertex)).comp OriginalCatalogueMachine.vertexExecutes
  exact (context.pair selected).comp (Executes.mapList contextEncoding
    OriginalCatalogueMachine.keyEncoding RationalTensorMachine.rowEncoding
    (fun c k => (k.2,OriginalCatalogueMachine.address (c.1,c.2,k))) cell)

def outputs (r : Input) : TM2OutputsInTime executes.machine.computer
    (encoding.encode r) (some (RationalTensorMachine.tableEncoding.encode (table r)))
    (executes.cost r) := executes.outputs r
theorem primitive_bound (r : Input) :
    primitiveCost executes.machine (executes.outputs r).steps
      (some (initList executes.machine.computer (encoding.encode r))) ≤
        executes.cost r * executes.machine.primitiveBudget := executes.primitive_bound r
end

theorem words_preserved (r : Input) :
    (table r).map Prod.fst = (OriginalCatalogueMachine.atVertex r.1 r.2.2).map Prod.snd := by
  simp only [table,List.map_map,Function.comp_def]
theorem addresses_bounded (r : Input) (k : OriginalCatalogueMachine.Key)
    (hk : k ∈ OriginalCatalogueMachine.atVertex r.1 r.2.2) (hi : r.2.2 < r.1.length+1) :
    OriginalCatalogueMachine.address (r.2.1,OriginalCatalogueMachine.catalogue r.1,k) <
      5+r.2.1+(OriginalCatalogueMachine.catalogue r.1).length := by
  apply OriginalCatalogueMachine.address_present
  exact List.mem_flatMap.mpr ⟨r.2.2,List.mem_range.mpr hi,hk⟩
end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalAddressTablesMachine
