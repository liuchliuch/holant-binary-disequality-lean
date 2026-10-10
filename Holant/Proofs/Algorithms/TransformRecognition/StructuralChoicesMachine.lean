import Holant.Proofs.Algorithms.TransformRecognition.StructuralListMachine
import Holant.Proofs.AlgebraicRecognition.PositiveCertificateMachine.RightFold


namespace Holant.LocalDrafts.MainChain.TransformRecognition.StructuralChoicesMachine
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open ComplexIsolation.RootSearchDriver (cross mem_cross)
variable {A : Type} (e : Encoding A Bool)

abbrev listEncoding := framedListEncoding e
abbrev familyEncoding := framedListEncoding (listEncoding e)
def prependChoices (xs : List A) (rest : List (List A)) : List (List A) :=
  (cross xs rest).map (fun p => p.1::p.2)
def product (choices : List (List A)) : List (List A) := choices.foldr prependChoices [[]]

theorem mem_product_iff (cs : List (List A)) (ts : List A) :
    ts ∈ product cs ↔ List.Forall₂ (fun c t => t ∈ c) cs ts := by
  constructor
  · intro h
    induction cs generalizing ts with
    | nil =>
      have he : ts=[] := by simpa only [product,List.foldr_nil,List.mem_singleton] using h
      subst ts
      exact .nil
    | cons c cs ih =>
      obtain ⟨⟨t,rest⟩,hp,rfl⟩ := List.mem_map.mp h
      obtain ⟨ht,hr⟩ := mem_cross.mp hp
      exact .cons ht (ih rest hr)
  · intro h
    induction h with
    | nil => simp [product]
    | @cons c t cs ts hc ht ih =>
      exact List.mem_map.mpr ⟨(t,ts),mem_cross.mpr ⟨hc,ih⟩,rfl⟩

noncomputable section
def prependComputes : Computes (pairEncoding (listEncoding e) (familyEncoding e)) (familyEncoding e)
    (fun p => prependChoices p.1 p.2) :=
  (ComplexIsolation.RootSearchDriver.crossComputes e (listEncoding e)).andThen
    (WireLists.mapComputes (pairEncoding e (listEncoding e)) (listEncoding e)
      (fun p => p.1::p.2) (StructuralListMachine.consComputes e))

def executes : Executes (familyEncoding e) (familyEncoding e) product := by
  let prepare := Executes.ofComputes (pairComputes (constantComputes (familyEncoding e) encodingBoolBool false)
    (pairComputes (identityComputes (familyEncoding e)) (constantComputes (familyEncoding e) (familyEncoding e) [[]])))
  let body := Executes.ofComputes
    ((Wiring.secondComputes encodingBoolBool (pairEncoding (listEncoding e) (familyEncoding e))).andThen
      (prependComputes e))
  exact prepare.comp (PositiveCertificateMachine.RightFold.executes encodingBoolBool
    (listEncoding e) (familyEncoding e) (fun _ => prependChoices) [] body)
end
end Holant.LocalDrafts.MainChain.TransformRecognition.StructuralChoicesMachine
