import Holant.Proofs.Tractability.EOEvaluation.CandidateClosure


namespace Holant.LocalDrafts.Tractability.EOEvaluation.Restriction
open Holant.Tractable Distribution Relaxation
open scoped BigOperators
noncomputable section
variable (G : Network AlgebraicComplex 0)

def network : Network AlgebraicComplex 0 := by
  classical
  exact {
    shape := G.shape
    vertex := fun v a => if Candidate G v a then G.vertex v a else 0
    edge := G.edge }

theorem support_iff (v : Fin G.shape.vertices) (a : Word (G.shape.arity v)) :
    (network G).vertex v a ≠ 0 ↔ Candidate G v a := by
  classical
  change (if Candidate G v a then G.vertex v a else 0) ≠ 0 ↔ Candidate G v a
  by_cases h : Candidate G v a
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => candidate_support G h⟩
  · rw [if_neg h]
    exact ⟨fun hn => False.elim (hn rfl), fun hc => False.elim (h hc)⟩

theorem assignmentTerm_eq (hX : ∀ e, G.edge e = Signature.disequality)
    (z : (Fin G.shape.edges × Bool) → Bool) :
    (network G).assignmentTerm Fin.elim0 z = G.assignmentTerm Fin.elim0 z := by
  classical
  by_cases h : ∀ v, Candidate G v (G.shape.assignment Fin.elim0 z v)
  · have hvertex (v : Fin G.shape.vertices) :
        (network G).vertex v ((network G).shape.assignment Fin.elim0 z v) =
          G.vertex v (G.shape.assignment Fin.elim0 z v) := by
      change (if Candidate G v (G.shape.assignment Fin.elim0 z v)
        then G.vertex v (G.shape.assignment Fin.elim0 z v) else 0) =
          G.vertex v (G.shape.assignment Fin.elim0 z v)
      exact if_pos (h v)
    have hp : (∏ v : Fin G.shape.vertices,
        (network G).vertex v ((network G).shape.assignment Fin.elim0 z v)) =
          ∏ v : Fin G.shape.vertices, G.vertex v (G.shape.assignment Fin.elim0 z v) :=
      Finset.prod_congr rfl (fun v _ => hvertex v)
    change (∏ v : Fin G.shape.vertices,
        (network G).vertex v ((network G).shape.assignment Fin.elim0 z v)) *
          (∏ e : Fin G.shape.edges, G.edge e (z (e, false)) (z (e, true))) =
        (∏ v : Fin G.shape.vertices, G.vertex v (G.shape.assignment Fin.elim0 z v)) *
          (∏ e : Fin G.shape.edges, G.edge e (z (e, false)) (z (e, true)))
    exact congrArg (fun t : AlgebraicComplex =>
      t * ∏ e : Fin G.shape.edges, G.edge e (z (e, false)) (z (e, true))) hp
  · obtain ⟨v, hv⟩ := not_forall.mp h
    have hnew : (network G).assignmentTerm Fin.elim0 z = 0 := by
      have hp : (∏ u, (network G).vertex u ((network G).shape.assignment Fin.elim0 z u)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ v)
        change (if Candidate G v (G.shape.assignment Fin.elim0 z v)
          then G.vertex v (G.shape.assignment Fin.elim0 z v) else 0) = 0
        exact if_neg hv
      unfold Network.assignmentTerm
      rw [hp, zero_mul]
    have hold : G.assignmentTerm Fin.elim0 z = 0 := by
      by_contra hz
      exact hv (effective_candidate G hX z hz v)
    rw [hnew, hold]

theorem denote_eq (hX : ∀ e, G.edge e = Signature.disequality) :
    (network G).denote Fin.elim0 = G.denote Fin.elim0 := by
  change (∑ z, (network G).assignmentTerm Fin.elim0 z) = ∑ z, G.assignmentTerm Fin.elim0 z
  exact Finset.sum_congr rfl (fun z _ => assignmentTerm_eq G hX z)

theorem support_triple (sign : EOSign) (H : Cubic.Conditions G sign)
    (v : Fin G.shape.vertices) (a b c : Word (G.shape.arity v))
    (ha : (network G).vertex v a ≠ 0) (hb : (network G).vertex v b ≠ 0)
    (hc : (network G).vertex v c ≠ 0) : (network G).vertex v (tripleXor a b c) ≠ 0 :=
  (support_iff G v _).mpr (CandidateClosure.candidate_triple G sign H v a b c
    ((support_iff G v a).mp ha) ((support_iff G v b).mp hb) ((support_iff G v c).mp hc))

end
end Holant.LocalDrafts.Tractability.EOEvaluation.Restriction
