import Holant.Proofs.Tractability.EOEvaluation.PairLift


namespace Holant.LocalDrafts.Tractability.EOEvaluation.CandidatePairing
open Holant Holant.Tractable Holant.Complexity Source Relaxation PairingTemplates Distribution
open scoped BigOperators
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ} (D : Family s arity)
variable (r : Input (s := s) (arity := arity))

def mask (v : Fin (network D r).shape.vertices) : Mask ((network D r).shape.arity v) := by
  classical
  exact fun i => decide (Candidate (network D r) v ((Fintype.equivFin (Word _)).symm i))

theorem mask_entry (v : Fin (network D r).shape.vertices) (x : Word ((network D r).shape.arity v)) :
    entry (mask D r v) x = true ↔ Candidate (network D r) v x := by
  classical
  simp [entry, mask]

theorem even_arity (v : Fin (network D r).shape.vertices) : ∃ d, (network D r).shape.arity v = 2 * d :=
  (D.tract.2.1 _ (Source.member D (r.val.signatureLabel r.property v))).1

theorem good (v : Fin (network D r).shape.vertices) : Good (mask D r v) := by
  obtain ⟨sign, _, H, _⟩ := shared_conditions D
  refine ⟨?_, ?_⟩
  · intro x hx
    exact (H r).central v x (candidate_support _ ((mask_entry D r v x).mp hx))
  · intro a b c ha hb hc
    exact (mask_entry D r v _).mpr (candidates_closed D r v a b c
      ((mask_entry D r v a).mp ha) ((mask_entry D r v b).mp hb) ((mask_entry D r v c).mp hc))

def label (v : Fin (network D r).shape.vertices) : Label ((network D r).shape.arity v) :=
  Classical.choose (select_complete (even_arity D r v) (mask D r v) (good D r v))

theorem label_spec (v : Fin (network D r).shape.vertices) :
    select (mask D r v) = some (label D r v) ∧ Covers (mask D r v) (decode (label D r v)) :=
  Classical.choose_spec (select_complete (even_arity D r v) (mask D r v) (good D r v))

def pairing (v : Fin (network D r).shape.vertices) : OrientedPerfectPairing ((network D r).shape.arity v) :=
  ⟨(network D r).shape.arity v / 2, decode (label D r v)⟩

theorem covers (v : Fin (network D r).shape.vertices) (x : Word ((network D r).shape.arity v))
    (hx : Candidate (network D r) v x) : PairLift.Compatible (pairing D r v) x :=
  (label_spec D r v).2 x ((mask_entry D r v x).mpr hx)

def paired : Network AlgebraicComplex 0 where
  shape := (network D r).shape
  vertex v := PairLift.restrict (pairing D r v) ((network D r).vertex v)
  edge := (network D r).edge

theorem assignmentTerm_eq (z : (Fin (network D r).shape.edges × Bool) → Bool) :
    (paired D r).assignmentTerm Fin.elim0 z = (network D r).assignmentTerm Fin.elim0 z := by
  classical
  by_cases h : ∀ v, PairLift.Compatible (pairing D r v) ((network D r).shape.assignment Fin.elim0 z v)
  · simp only [Network.assignmentTerm, paired, PairLift.restrict, if_pos (h _)]
    rfl
  · obtain ⟨v, hv⟩ := not_forall.mp h
    have hold : (network D r).assignmentTerm Fin.elim0 z = 0 := by
      by_contra hz
      exact hv (covers D r v _ (effective_candidate _ (native D r) z hz v))
    have hp : (∏ u, (paired D r).vertex u ((paired D r).shape.assignment Fin.elim0 z u)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      simp [paired, PairLift.restrict, hv]
    rw [hold]
    simp [Network.assignmentTerm, hp]

theorem denote_eq : (paired D r).denote Fin.elim0 = (network D r).denote Fin.elim0 := by
  change (∑ z, (paired D r).assignmentTerm Fin.elim0 z) = ∑ z, (network D r).assignmentTerm Fin.elim0 z
  exact Finset.sum_congr rfl (fun z _ => assignmentTerm_eq D r z)

theorem shared_class : ∃ C : EOClass, ∀ v, C.Holds ((paired D r).vertex v) := by
  obtain ⟨_, C, _, hp⟩ := shared_conditions D
  refine ⟨C, ?_⟩
  intro v
  exact PairLift.class_lift (pairing D r v) C
    (hp (r.val.signatureLabel r.property v) (pairing D r v))

end
end Holant.LocalDrafts.Tractability.EOEvaluation.CandidatePairing
