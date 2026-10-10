import Holant.Proofs.Tractability.EOEvaluation.Restriction
import Holant.Complexity.ClosedNetworkSemantics


namespace Holant.LocalDrafts.Tractability.EOEvaluation.Source
open Holant.Tractable Holant.Complexity Distribution Relaxation
open scoped BigOperators
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ}

def signatureSet (f : (i : Fin s) → Signature AlgebraicComplex (arity i.val)) :
    SignatureFamily AlgebraicComplex := Set.range (fun i => (⟨arity i.val, f i⟩ : AnySignature AlgebraicComplex))

structure Family (s : ℕ) (arity : ℕ → ℕ) where
  signatures : (i : Fin s) → Signature AlgebraicComplex (arity i.val)
  preprocessed : Preprocessed (signatureSet signatures)
  tract : EOTract (signatureSet signatures)

abbrev Input := { r : RawClosedNetwork // r.WellFormed s 1 arity }
def inputEncoding := RawClosedNetwork.validatedEncoding s 1 arity
variable (D : Family s arity)

def network (r : Input (s := s) (arity := arity)) : Network AlgebraicComplex 0 :=
  r.val.realize r.property D.signatures (fun _ => Signature.disequality)

theorem native (r : Input (s := s) (arity := arity)) :
    ∀ e, (network D r).edge e = Signature.disequality := fun _ => rfl

theorem member (i : Fin s) : (⟨arity i.val, D.signatures i⟩ : AnySignature AlgebraicComplex) ∈
    signatureSet D.signatures := ⟨i, rfl⟩

/-- The same sign and class govern every occurrence in every input graph. -/
theorem shared_conditions : ∃ sign : EOSign, ∃ C : EOClass,
    (∀ r : Input (s := s) (arity := arity), Cubic.Conditions (network D r) sign) ∧
    (∀ i : Fin s, ∀ p : OrientedPerfectPairing (arity i.val), C.Holds (p.restrict (D.signatures i))) := by
  obtain ⟨sign, C, hq, hp⟩ := D.tract.2.2
  refine ⟨sign, C, ?_, ?_⟩
  · intro r
    refine ⟨?_, ?_⟩
    · intro v a ha
      have hc := (D.tract.2.1 _ (member D (r.val.signatureLabel r.property v))).2
      apply (Holant.charge_eq_zero_iff a).mpr
      by_contra hn
      exact ha (hc a hn)
    · intro v a b c ha hb hc
      exact hq _ (member D (r.val.signatureLabel r.property v)) a b c ha hb hc
  · intro i p; exact hp _ (member D i) p

theorem candidates_closed (r : Input (s := s) (arity := arity))
    (v : Fin (network D r).shape.vertices) (a b c : Word ((network D r).shape.arity v))
    (ha : Candidate (network D r) v a) (hb : Candidate (network D r) v b)
    (hc : Candidate (network D r) v c) : Candidate (network D r) v (tripleXor a b c) := by
  obtain ⟨sign, _, H, _⟩ := shared_conditions D
  exact CandidateClosure.candidate_triple _ sign (H r) v a b c ha hb hc

theorem candidate_restriction_value (r : Input (s := s) (arity := arity)) :
    (Restriction.network (network D r)).denote Fin.elim0 = (network D r).denote Fin.elim0 :=
  Restriction.denote_eq _ (native D r)

theorem infeasible_value (r : Input (s := s) (arity := arity))
    (h : ¬ ∃ w : Weights (network D r), Feasible (network D r) w) :
    (network D r).denote Fin.elim0 = 0 := Relaxation.infeasible_zero _ (native D r) h

/-- Number of LP variables: all local truth-table entries, never global
assignments. The family constant is independent of graph size. -/
def localBudget (s : ℕ) (arity : ℕ → ℕ) := ∑ i : Fin s, 2 ^ arity i.val
abbrev Coordinate (r : Input (s := s) (arity := arity)) :=
  Σ v : Fin r.val.vertices.length, Word (arity (r.val.vertices.get v).1)

theorem coordinate_count (r : Input (s := s) (arity := arity)) :
    Fintype.card (Coordinate r) = ∑ v : Fin r.val.vertices.length, 2 ^ arity (r.val.vertices.get v).1 := by
  simp [Coordinate, Fintype.card_sigma, Fintype.card_fun]

theorem coordinate_bound (r : Input (s := s) (arity := arity)) :
    Fintype.card (Coordinate r) ≤
      localBudget s arity * (RawClosedNetwork.encoding.encode r.val).length := by
  rw [coordinate_count]
  have each (v : Fin r.val.vertices.length) :
      2 ^ arity (r.val.vertices.get v).1 ≤ localBudget s arity := by
    change 2 ^ arity (r.val.signatureLabel r.property v).val ≤
      ∑ i : Fin s, 2 ^ arity i.val
    exact Finset.single_le_sum (fun i _ => Nat.zero_le (2 ^ arity i.val))
      (Finset.mem_univ (r.val.signatureLabel r.property v))
  have hc := r.val.counts_le_encoded_length
  calc
    _ ≤ ∑ _ : Fin r.val.vertices.length, localBudget s arity := Finset.sum_le_sum (fun v _ => each v)
    _ = localBudget s arity * r.val.vertices.length := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

end
end Holant.LocalDrafts.Tractability.EOEvaluation.Source
