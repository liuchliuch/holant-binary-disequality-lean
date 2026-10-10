import Holant.Proofs.Traversal.ArityTwo.ActionTableCompiler
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawComponentLabel


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.RawSeedSelection
open Holant Holant.Complexity Computability
open BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (s b : ℕ) (arity : ℕ → ℕ)
abbrev Query := RawRootReach.Input s b arity
abbrev encoding := RawRootReach.inputEncoding s b arity
abbrev Scan := Σ x : Query s b arity, Fin x.1.val.vertices.length
def scanEncoding := sigmaEncoding (encoding s b arity)
  (fun x => OccurrenceLabel.unaryPortEncoding x.1.val.vertices.length)

def contextComputes : Computes (scanEncoding s b arity) (encoding s b arity) Sigma.fst :=
  recode (Wiring.firstComputes (encoding s b arity) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)

def indexComputes : Computes (scanEncoding s b arity) UnaryBinary.unaryEncoding (fun x => x.2.val) :=
  recode (Wiring.secondComputes (encoding s b arity) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)

def candidateQuery (x : Scan s b arity) : Query s b arity := ⟨x.1.1,x.2⟩

def candidateComputes : Computes (scanEncoding s b arity) (encoding s b arity) (candidateQuery s b arity) :=
  recode (pairComputes
    ((contextComputes s b arity).andThen (sourceComputes s b arity))
    (indexComputes s b arity)) id (fun _ => rfl) (fun _ => rfl)

def eligible (x : Scan s b arity) : Bool :=
  decide ((x.1.1.val.graph x.1.1.property).label x.2 = x.1.2) &&
    decide (PortWalk.degree (arity := arity) x.1.1.val x.2 = 1)

def andComputes : Computes (pairEncoding encodingBoolBool encodingBoolBool) encodingBoolBool
    (fun x => x.1 && x.2) :=
  FiniteRecode.computes _ _ _ 4 (fun x => by rcases x with ⟨a,b⟩; cases a <;> cases b <;> decide)

def eligibleComputes : Computes (scanEncoding s b arity) encodingBoolBool (eligible s b arity) :=
  congrComputes ((pairComputes
    ((pairComputes
      ((candidateComputes s b arity).andThen (RawComponentLabel.computes s b arity))
      ((contextComputes s b arity).andThen (FixedGadgetSubstitution.Compiler.indexComputes s b arity))).andThen
        (equalComputes UnaryBinary.unaryEncoding))
    ((candidateComputes s b arity).andThen
      (labelRecodeComputes s b arity encodingBoolBool (fun i => decide (arity i.val = 1))))).andThen andComputes)
    (fun x => by simp [eligible,RawComponentLabel.value,candidateQuery,PortWalk.degree,
      sourceLabel,Fin.ext_iff])

def chunk (x : Scan s b arity) :=
  if eligible s b arity x then entry UnaryBinary.unaryEncoding x.2.val else []

def chunkComputes : Computes (scanEncoding s b arity) Frame.wordEncoding (chunk s b arity) :=
  ifComputes (eligibleComputes s b arity)
    ((indexComputes s b arity).andThen (entryComputes UnaryBinary.unaryEncoding))
    (constantComputes (scanEncoding s b arity) Frame.wordEncoding [])

def candidates (x : Query s b arity) :=
  (List.finRange x.1.val.vertices.length).filter (fun v => eligible s b arity ⟨x,v⟩)

def selected (x : Query s b arity) : Fin x.1.val.vertices.length :=
  (candidates s b arity x).head?.getD x.2

def prepare : Computes (encoding s b arity)
    (ContextFlatMap.inputEncoding (encoding s b arity)
      (fun x => OccurrenceLabel.unaryPortEncoding x.1.val.vertices.length))
    (fun x => ⟨x,List.finRange x.1.val.vertices.length⟩) :=
  recode (pairComputes (identityComputes (encoding s b arity))
    (((sourceComputes s b arity).andThen (vertexCountComputes s b arity)).andThen
      ComponentSelection.UnaryRange.computes)) id (fun _ => rfl) (fun x => by
        change Holant.Algebraic.frame _ ++ framedListEncode UnaryBinary.unaryEncoding (List.range _) = _
        rw [← finRange_values,finListEncoding]
        rfl)

theorem chunk_word (x : Query s b arity) :
    (List.finRange x.1.val.vertices.length).flatMap (fun v => chunk s b arity ⟨x,v⟩) =
      entries UnaryBinary.unaryEncoding ((candidates s b arity x).map Fin.val) := by
  have aux (vs : List (Fin x.1.val.vertices.length)) :
      vs.flatMap (fun v => chunk s b arity ⟨x,v⟩) = entries UnaryBinary.unaryEncoding
        ((vs.filter (fun v => eligible s b arity ⟨x,v⟩)).map Fin.val) := by
    induction vs with
    | nil => rfl
    | cons v vs ih =>
      simp only [chunk, entries] at ih
      cases he : eligible s b arity ⟨x,v⟩ <;> simp [chunk,he,entries,ih]
  exact aux _

def choicesComputes : Computes (encoding s b arity) (framedListEncoding UnaryBinary.unaryEncoding)
    (fun x => (candidates s b arity x).map Fin.val ++ [x.2.val]) := by
  let scanned := (prepare s b arity).andThen
    (ContextFlatMap.computes (encoding s b arity)
      (fun x => OccurrenceLabel.unaryPortEncoding x.1.val.vertices.length)
      (chunk s b arity) (chunkComputes s b arity))
  let fallback := joinComputes
    ((FixedGadgetSubstitution.Compiler.indexComputes s b arity).andThen (entryComputes UnaryBinary.unaryEncoding))
    (constantComputes (encoding s b arity) Frame.wordEncoding [false])
  refine recode (joinComputes scanned fallback) id (fun _ => rfl) ?_
  intro x
  dsimp only [Frame.wordEncoding,ContextFlatMap.value,Function.comp_apply,id_eq]
  rw [chunk_word]
  exact entries_append_encode UnaryBinary.unaryEncoding _ [x.2.val]

def selectedComputes : Computes (encoding s b arity) UnaryBinary.unaryEncoding
    (fun x => (selected s b arity x).val) :=
  congrComputes ((choicesComputes s b arity).andThen (getDComputes UnaryBinary.unaryEncoding 0 0))
    (fun x => by cases hc : candidates s b arity x <;> simp [selected,hc])

def value (x : Query s b arity) : Query s b arity := ⟨x.1,selected s b arity x⟩
def computes : Computes (encoding s b arity) (encoding s b arity) (value s b arity) :=
  recode (pairComputes (sourceComputes s b arity) (selectedComputes s b arity))
    id (fun _ => rfl) (fun _ => rfl)

theorem candidates_original (x : Query s b arity) : candidates s b arity x =
    ((x.1.val.graph x.1.property).componentVertices x.2).filter
      (fun v => decide (PortWalk.degree (arity := arity) x.1.val v = 1)) := by
  simp [candidates,eligible,Holant.OneHot.Computable.Graph.componentVertices,List.filter_filter,
    Bool.and_comm]

theorem selected_original (x : Query s b arity) : selected s b arity x =
    (((x.1.val.graph x.1.property).componentVertices x.2).find?
      (fun v => decide (PortWalk.degree (arity := arity) x.1.val v = 1))).getD x.2 := by
  have aux {B : Type} (P : B → Bool) (xs : List B) : (xs.filter P).head? = xs.find? P := by
    induction xs with
    | nil => rfl
    | cons y ys ih => cases hp : P y <;> simp [List.find?,hp,ih]
  rw [selected,candidates_original,aux]

theorem primitive_bound (x : Query s b arity) :
    let w := computes s b arity
    primitiveCost w.machine (w.outputs x).steps
      (some (Turing.initList w.machine.computer ((encoding s b arity).encode x))) ≤
        (primitivePolynomial w).eval ((encoding s b arity).encode x).length :=
  computes_primitive_cost (computes s b arity) x

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.RawSeedSelection
