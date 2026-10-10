import Holant.Proofs.Tractability.EOEvaluation.Distribution


namespace Holant.LocalDrafts.Tractability.EOEvaluation.Relaxation
open Holant.Tractable Distribution
open scoped BigOperators
noncomputable section
variable (G : Network AlgebraicComplex 0)

abbrev Weights := (v : Fin G.shape.vertices) → Mass (G.shape.arity v)
def endpointMean (w : Weights G) (q : Fin G.shape.edges × Bool) : ℚ :=
  let p := G.shape.closedPorts.symm q
  mean (w p.1) p.2

structure Feasible (w : Weights G) : Prop where
  nonneg : ∀ v a, 0 ≤ w v a
  total : ∀ v, ∑ a, w v a = 1
  offSupport : ∀ v a, G.vertex v a = 0 → w v a = 0
  edge : ∀ e, endpointMean G w (e, false) + endpointMean G w (e, true) = 0

/-- Positive-coordinate feasibility, not a chosen optimal solution. Over
rationals this is precisely the positivity decision needed by the algorithm. -/
def Candidate (v : Fin G.shape.vertices) (a : Word (G.shape.arity v)) : Prop :=
  ∃ w : Weights G, Feasible G w ∧ 0 < w v a

theorem candidate_support {v : Fin G.shape.vertices} {a : Word (G.shape.arity v)}
    (h : Candidate G v a) : G.vertex v a ≠ 0 := by
  obtain ⟨w, hw, hp⟩ := h
  intro hz
  rw [hw.offSupport v a hz] at hp
  exact lt_irrefl _ hp

def dirac (z : (Fin G.shape.edges × Bool) → Bool) : Weights G :=
  fun v a => if a = G.shape.assignment Fin.elim0 z v then 1 else 0

theorem dirac_mean (z : (Fin G.shape.edges × Bool) → Bool) (q : Fin G.shape.edges × Bool) :
    endpointMean G (dirac G z) q = spin (z q) := by
  simp [endpointMean, mean, dirac, NetworkShape.assignment_closed]

theorem effective_feasible (hX : ∀ e, G.edge e = Signature.disequality)
    (z : (Fin G.shape.edges × Bool) → Bool) (hz : G.assignmentTerm Fin.elim0 z ≠ 0) :
    Feasible G (dirac G z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v a; dsimp [dirac]; split_ifs <;> norm_num
  · intro v; simp [dirac]
  · intro v a ha
    have hn := G.vertex_ne_zero_of_assignmentTerm_ne_zero Fin.elim0 z hz v
    have hne : a ≠ G.shape.assignment Fin.elim0 z v := by intro h; subst a; exact hn ha
    simp [dirac, hne]
  · intro e
    have he := G.edge_ne_zero_of_assignmentTerm_ne_zero Fin.elim0 z hz e
    rw [hX e] at he
    rw [dirac_mean, dirac_mean]
    cases h0 : z (e, false) <;> cases h1 : z (e, true) <;>
      simp_all [Signature.disequality, spin]

theorem effective_candidate (hX : ∀ e, G.edge e = Signature.disequality)
    (z : (Fin G.shape.edges × Bool) → Bool) (hz : G.assignmentTerm Fin.elim0 z ≠ 0)
    (v : Fin G.shape.vertices) : Candidate G v (G.shape.assignment Fin.elim0 z v) :=
  ⟨dirac G z, effective_feasible G hX z hz, by simp [dirac]⟩

theorem infeasible_zero (hX : ∀ e, G.edge e = Signature.disequality)
    (h : ¬ ∃ w : Weights G, Feasible G w) : G.denote Fin.elim0 = 0 := by
  change (∑ z, G.assignmentTerm Fin.elim0 z) = 0
  apply Finset.sum_eq_zero; intro z _
  by_contra hz
  exact h ⟨dirac G z, effective_feasible G hX z hz⟩

def average (a b c : Weights G) : Weights G := fun v x => (a v x + b v x + c v x) / 3

theorem mean_average (a b c : Weights G) (q : Fin G.shape.edges × Bool) :
    endpointMean G (average G a b c) q =
      (endpointMean G a q + endpointMean G b q + endpointMean G c q) / 3 := by
  simp only [endpointMean, mean, average, add_div, add_mul, div_mul_eq_mul_div,
    Finset.sum_add_distrib, ← Finset.sum_div]

theorem average_feasible {a b c : Weights G}
    (ha : Feasible G a) (hb : Feasible G b) (hc : Feasible G c) :
    Feasible G (average G a b c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v x; exact div_nonneg (add_nonneg (add_nonneg (ha.nonneg v x) (hb.nonneg v x)) (hc.nonneg v x)) (by norm_num)
  · intro v
    norm_num [average, ← Finset.sum_div, Finset.sum_add_distrib, ha.total, hb.total, hc.total]
  · intro v x hx; simp [average, ha.offSupport v x hx, hb.offSupport v x hx, hc.offSupport v x hx]
  · intro e
    rw [mean_average, mean_average]
    have h1 := ha.edge e; have h2 := hb.edge e; have h3 := hc.edge e
    linarith

/-- The cancellation uses the actual port bijection, so self-loops and
parallel edges require no simple-graph assumption. -/
theorem cubic_conservation {w : Weights G} (hw : Feasible G w) :
    (∑ v, ∑ j, mean (w v) j ^ 3) = 0 := by
  have hi := G.shape.sum_closedPorts (fun q => endpointMean G w q ^ 3)
  have he (e : Fin G.shape.edges) :
      endpointMean G w (e, false) ^ 3 + endpointMean G w (e, true) ^ 3 = 0 := by
    have h := hw.edge e
    have h' : endpointMean G w (e, true) = -endpointMean G w (e, false) := by linarith
    rw [h']; ring
  have hi' : (∑ v, ∑ j, mean (w v) j ^ 3) =
      ∑ q : Fin G.shape.edges × Bool, endpointMean G w q ^ 3 := by
    have hp (v : Fin G.shape.vertices) (j : Fin (G.shape.arity v)) :
        endpointMean G w (G.shape.closedPorts ⟨v, j⟩) = mean (w v) j :=
      congrArg
        (fun p : Σ v : Fin G.shape.vertices, Fin (G.shape.arity v) => mean (w p.1) p.2)
        (G.shape.closedPorts.symm_apply_apply ⟨v, j⟩)
    calc
      (∑ v, ∑ j, mean (w v) j ^ 3) =
          ∑ v, ∑ j, endpointMean G w (G.shape.closedPorts ⟨v, j⟩) ^ 3 := by
        apply Finset.sum_congr rfl
        intro v _
        apply Finset.sum_congr rfl
        intro j _
        exact congrArg (fun t : ℚ => t ^ 3) (hp v j).symm
      _ = _ := hi
  apply hi'.trans
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero; intro e _
  simpa only [Fintype.sum_bool, add_comm] using he e

end
end Holant.LocalDrafts.Tractability.EOEvaluation.Relaxation
