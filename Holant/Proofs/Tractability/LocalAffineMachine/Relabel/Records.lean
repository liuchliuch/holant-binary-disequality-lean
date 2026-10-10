import Holant.Proofs.Tractability.LocalAffineMachine.Relabel.LocalWords


namespace Holant.LocalDrafts.Tractability.LocalAffineMachine.Relabel.Records

open Computability Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
noncomputable section
variable {s b : ℕ} {arity : ℕ → ℕ}

def vertexEncoding := pairEncoding WordLookup.wordEncoding RawClosedNetwork.vertexEncoding
def vertexCandidate (x : List Bool × RawVertex) (i : Fin s) : ℕ :=
  Catalogue.vertexCode (⟨i, LocalWords.sample (arity i.val) (x.1, x.2.2)⟩ : Catalogue.V (s := s) (arity := arity))
def vertexLabel (x : List Bool × RawVertex) : ℕ :=
  FiniteDispatch.select (fun x : List Bool × RawVertex => x.2.1)
    (vertexCandidate (arity := arity)) (fun _ => 0) (List.finRange s) x
def vertex (x : List Bool × RawVertex) : RawVertex := (vertexLabel (s := s) (arity := arity) x, x.2.2)

theorem vertex_label (x : List Bool × RawVertex) (h : x.2.1 < s) :
    vertexLabel (s := s) (arity := arity) x = vertexCandidate (arity := arity) x ⟨x.2.1, h⟩ :=
  FiniteDispatch.select_at _ _ _ _ _ (by simp) x rfl

noncomputable def vertexCandidateComputes (i : Fin s) :
    Computes vertexEncoding encodingNatBool (fun x => vertexCandidate (arity := arity) x i) := by
  let word := Wiring.firstComputes WordLookup.wordEncoding RawClosedNetwork.vertexEncoding
  let row := Wiring.secondComputes WordLookup.wordEncoding RawClosedNetwork.vertexEncoding
  let ports : Computes vertexEncoding LocalWords.portsEncoding (fun x => x.2.2) :=
    row.andThen (recode (Wiring.secondComputes encodingNatBool LocalWords.portsEncoding)
      id (fun _ => rfl) (fun _ => rfl))
  exact ((pairComputes word ports).andThen (LocalWords.sampleComputes (arity i.val))).andThen
    (FiniteRecode.computes (LocalWords.fixedEncoding (arity i.val)) encodingNatBool
      (fun w => Catalogue.vertexCode (⟨i, w⟩ : Catalogue.V (s := s) (arity := arity))) (4 * arity i.val + 1)
      (fun w => le_of_eq (LocalWords.fixed_length _ w)))

def vertexComputes : Computes vertexEncoding RawClosedNetwork.vertexEncoding (vertex (s := s) (arity := arity)) := by
  let row := Wiring.secondComputes WordLookup.wordEncoding RawClosedNetwork.vertexEncoding
  let label : Computes vertexEncoding encodingNatBool (fun x => x.2.1) :=
    row.andThen (recode (Wiring.firstComputes encodingNatBool LocalWords.portsEncoding)
      id (fun _ => rfl) (fun _ => rfl))
  let selected := FiniteDispatch.computes vertexEncoding encodingNatBool _ (vertexCandidate (arity := arity)) (fun _ => 0)
    label vertexCandidateComputes (constantComputes vertexEncoding encodingNatBool 0) (List.finRange s)
  let ports := row.andThen (recode (Wiring.secondComputes encodingNatBool LocalWords.portsEncoding)
    id (fun _ => rfl) (fun _ => rfl))
  exact recode (pairComputes selected ports) id (fun _ => rfl) (fun _ => rfl)

abbrev EdgeInput := List Bool × (ℕ × ℕ)
def edgeEncoding := pairEncoding WordLookup.wordEncoding (pairEncoding encodingNatBool encodingNatBool)
def edgeCandidate (x : EdgeInput) (i : Fin b) : ℕ := Catalogue.edgeCode (i, LocalWords.edgeSample (x.1, x.2.2))
def edge (x : EdgeInput) : ℕ :=
  FiniteDispatch.select (fun x : EdgeInput => x.2.1) edgeCandidate (fun _ => 0) (List.finRange b) x

theorem edge_label (x : EdgeInput) (h : x.2.1 < b) :
    edge (b := b) x = edgeCandidate x ⟨x.2.1, h⟩ :=
  FiniteDispatch.select_at _ _ _ _ _ (by simp) x rfl

def edgeCandidateComputes (i : Fin b) : Computes edgeEncoding encodingNatBool (fun x => edgeCandidate x i) := by
  let word := Wiring.firstComputes WordLookup.wordEncoding (pairEncoding encodingNatBool encodingNatBool)
  let index := (Wiring.secondComputes WordLookup.wordEncoding (pairEncoding encodingNatBool encodingNatBool)).andThen
    (Wiring.secondComputes encodingNatBool encodingNatBool)
  exact ((pairComputes word index).andThen LocalWords.edgeComputes).andThen
    (FiniteRecode.computes (LocalWords.fixedEncoding 2) encodingNatBool (fun w => Catalogue.edgeCode (i, w)) 9
      (fun w => le_of_eq (LocalWords.fixed_length 2 w)))

def edgeComputes : Computes edgeEncoding encodingNatBool (edge (b := b)) := by
  let label := (Wiring.secondComputes WordLookup.wordEncoding (pairEncoding encodingNatBool encodingNatBool)).andThen
    (Wiring.firstComputes encodingNatBool encodingNatBool)
  exact FiniteDispatch.computes edgeEncoding encodingNatBool _ edgeCandidate (fun _ => 0)
    label edgeCandidateComputes (constantComputes edgeEncoding encodingNatBool 0) (List.finRange b)

end
end Holant.LocalDrafts.Tractability.LocalAffineMachine.Relabel.Records
