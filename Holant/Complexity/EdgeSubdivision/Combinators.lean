import Holant.Complexity.EdgeSubdivision.Raw
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Template
import Holant.Complexity.GraphPreprocessing.FiniteRecode

/-! Real Boolean-machine record maps for edge subdivision. Only the Boolean
orientation uses finite recoding; all unbounded natural indices use the proved
binary arithmetic programs, and unbounded lists use the context-flat-map loop. -/
namespace Holant.Complexity.EdgeSubdivision.Compiler
open Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient RawClosedNetwork
open Holant.OneHot.StackProgram.GraphLabelEncoding
open FixedGadgetSubstitution.Compiler
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

noncomputable def boolNatComputes : Computes encodingBoolBool encodingNatBool
    (fun b => if b then 1 else 0) :=
  FiniteRecode.computes encodingBoolBool encodingNatBool _ 1
    (by intro b; cases b <;> decide)

noncomputable def endpointFirst : Computes endpointEncoding encodingNatBool Prod.fst :=
  recode (Wiring.firstComputes encodingNatBool encodingBoolBool) id
    (fun _ => rfl) (fun _ => rfl)
noncomputable def endpointSecond : Computes endpointEncoding encodingBoolBool Prod.snd :=
  recode (Wiring.secondComputes encodingNatBool encodingBoolBool) id
    (fun _ => rfl) (fun _ => rfl)

noncomputable def outsideComputes : Computes endpointEncoding endpointEncoding outside :=
  recode (pairComputes
    ((pairComputes (endpointFirst.andThen doublingComputes)
      (endpointSecond.andThen boolNatComputes)).andThen
        FixedGadgetSubstitution.Compiler.addComputes)
    endpointSecond) id (fun _ => rfl) (fun _ => rfl)

noncomputable def insideEndpointComputes (b : Bool) :
    Computes encodingNatBool endpointEncoding
      (fun e => (2*e+(if b then 1 else 0),!b)) :=
  recode (pairComputes
    ((pairComputes doublingComputes
      (constantComputes encodingNatBool encodingNatBool (if b then 1 else 0))).andThen
        FixedGadgetSubstitution.Compiler.addComputes)
    (constantComputes encodingNatBool encodingBoolBool (!b)))
    id (fun _ => rfl) (fun _ => rfl)

noncomputable def insideComputes : Computes encodingNatBool
    (framedListEncoding endpointEncoding) inside :=
  congrComputes (fixedListComputes encodingNatBool endpointEncoding
    (fun e b => (2*e+(if b then 1 else 0),!b)) insideEndpointComputes [false,true])
    (fun _ => by simp [inside])

noncomputable def mapComputes {A B : Type} (ea : Encoding A Bool) (eb : Encoding B Bool)
    (f : A → B) (w : Computes ea eb f) :
    Computes (framedListEncoding ea) (framedListEncoding eb) (List.map f) := by
  let provider : Computes (sigmaEncoding Frame.wordEncoding (fun _ => ea)) Frame.wordEncoding
      (fun x => entry eb (f x.2)) :=
    recode (((Wiring.secondComputes Frame.wordEncoding ea).andThen w).andThen
      (entryComputes eb)) (fun x => (x.1,x.2)) (fun _ => rfl) (fun _ => rfl)
  let prepare : Computes (framedListEncoding ea)
      (ContextFlatMap.inputEncoding Frame.wordEncoding (fun _ => ea))
      (fun xs => (⟨[],xs⟩ : Σ _ : List Bool,List A)) :=
    recode (pairComputes (constantComputes (framedListEncoding ea) Frame.wordEncoding [])
      (identityComputes (framedListEncoding ea))) id (fun _ => rfl) (fun _ => rfl)
  let body := prepare.andThen
    (ContextFlatMap.computes Frame.wordEncoding (fun _ => ea) (fun x => entry eb (f x.2)) provider)
  exact recode (joinComputes body
    (constantComputes (framedListEncoding ea) Frame.wordEncoding [false]))
    id (fun _ => rfl) (fun xs => by
      have h := entries_append_encode eb (xs.map f) []
      simpa only [ContextFlatMap.value,entries,List.flatMap_map,Function.comp_def,
        List.append_nil,framedListEncode,framedListEncoding,Frame.wordEncoding,id_eq] using h)

noncomputable def oldVertexComputes : Computes vertexEncoding vertexEncoding oldVertex :=
  recode (pairComputes
    (Wiring.firstComputes encodingNatBool (framedListEncoding endpointEncoding))
    ((Wiring.secondComputes encodingNatBool (framedListEncoding endpointEncoding)).andThen
      (mapComputes endpointEncoding endpointEncoding outside outsideComputes)))
    id (fun _ => rfl) (fun _ => rfl)

end Holant.Complexity.EdgeSubdivision.Compiler
