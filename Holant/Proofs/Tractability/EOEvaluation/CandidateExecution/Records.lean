import Holant.Proofs.Tractability.EOEvaluation.CandidateExecution.Responses


namespace Holant.LocalDrafts.Tractability.EOEvaluation.CandidateExecution.Records
open Computability Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing AffineMachine LocalAffineMachine.Relabel FixedGadgetSubstitution.Compiler
open scoped BigOperators
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ}

def candidate (x : Responses.LocalInput (s := s) (arity := arity)) (i : Fin s) :
    Catalogue.Label (s := s) (arity := arity) :=
  ⟨i, PairingTemplates.select (Responses.mask (arity i.val) x)⟩
def label (x : Responses.LocalInput (s := s) (arity := arity)) : ℕ :=
  FiniteDispatch.select (fun x => x.2.2.1) (fun x i => Catalogue.code (candidate x i))
    (fun _ => 0) (List.finRange s) x
def vertex (x : Responses.LocalInput (s := s) (arity := arity)) : RawVertex := (label x, x.2.2.2)

theorem label_valid (x : Responses.LocalInput (s := s) (arity := arity)) (h : x.2.2.1 < s) :
    label x = Catalogue.code (candidate x ⟨x.2.2.1, h⟩) :=
  FiniteDispatch.select_at _ _ _ _ _ (by simp) x rfl

def labelComputes : Computes (Responses.localEncoding (s := s) (arity := arity)) encodingNatBool label := by
  let row := (Wiring.secondComputes (Responses.inputEncoding (s := s) (arity := arity)) RawColumns.vertexEncoding).andThen
    (Wiring.secondComputes UnaryBinary.unaryEncoding RawClosedNetwork.vertexEncoding)
  let key := row.andThen (recode (Wiring.firstComputes encodingNatBool
    (framedListEncoding RawClosedNetwork.endpointEncoding)) id (fun _ => rfl) (fun _ => rfl))
  let branch (i : Fin s) := ((Responses.maskComputes (s := s) (arity := arity) (arity i.val)).andThen
    (PairingTemplates.computes (arity i.val))).andThen
      (FiniteRecode.computes (PairingTemplates.outputEncoding (arity i.val)) encodingNatBool
        (fun p => Catalogue.code (⟨i, p⟩ : Catalogue.Label (s := s) (arity := arity)))
        (∑ p : Option (PairingTemplates.Label (arity i.val)),
          ((PairingTemplates.outputEncoding (arity i.val)).encode p).length)
        (fun p => Finset.single_le_sum
          (fun q _ => Nat.zero_le ((PairingTemplates.outputEncoding (arity i.val)).encode q).length)
          (Finset.mem_univ p)))
  exact FiniteDispatch.computes (Responses.localEncoding (s := s) (arity := arity)) encodingNatBool _ _ _ key branch
    (constantComputes (Responses.localEncoding (s := s) (arity := arity)) encodingNatBool 0) (List.finRange s)

def computes : Computes (Responses.localEncoding (s := s) (arity := arity)) RawClosedNetwork.vertexEncoding vertex := by
  let row := (Wiring.secondComputes (Responses.inputEncoding (s := s) (arity := arity)) RawColumns.vertexEncoding).andThen
    (Wiring.secondComputes UnaryBinary.unaryEncoding RawClosedNetwork.vertexEncoding)
  let ports := row.andThen (recode (Wiring.secondComputes encodingNatBool
    (framedListEncoding RawClosedNetwork.endpointEncoding)) id (fun _ => rfl) (fun _ => rfl))
  exact recode (pairComputes labelComputes ports) id (fun _ => rfl) (fun _ => rfl)

theorem true_candidate (D : Source.Family s arity) (r : Source.Input (s := s) (arity := arity))
    (v : Fin r.val.vertices.length) :
    candidate ((r, Responses.truth D r), v.val, r.val.vertices.get v) (r.val.signatureLabel r.property v) =
      ⟨r.val.signatureLabel r.property v, some (CandidatePairing.label D r v)⟩ := by
  have hmask := Responses.mask_truth D r v
  have hselect := congrArg
    (PairingTemplates.select (n := arity (r.val.vertices.get v).1)) hmask
  have hselected := hselect.trans (CandidatePairing.label_spec D r v).1
  exact congrArg
    (fun p : Option (PairingTemplates.Label (arity (r.val.signatureLabel r.property v).val)) =>
      (⟨r.val.signatureLabel r.property v, p⟩ : Catalogue.Label (s := s) (arity := arity))) hselected

end
end Holant.LocalDrafts.Tractability.EOEvaluation.CandidateExecution.Records
