import Holant.Proofs.Tractability.EOEvaluation.Source


namespace Holant.LocalDrafts.Tractability.EOEvaluation.LinearSystem
open Holant.Tractable Distribution Relaxation
open scoped BigOperators
noncomputable section
variable (G : Network AlgebraicComplex 0)

abbrev Column := Σ v : Fin G.shape.vertices, Word (G.shape.arity v)
abbrev Row := Fin G.shape.vertices ⊕ (Fin G.shape.edges ⊕ Column G)

def spinZ (b : Bool) : ℤ := if b then 1 else -1
theorem cast_spinZ (b : Bool) : (spinZ b : ℚ) = spin b := by cases b <;> rfl

def portColumn (p : Σ v : Fin G.shape.vertices, Fin (G.shape.arity v)) (i : Column G) : ℤ :=
  if h : p.1 = i.1 then spinZ (i.2 (Fin.cast (congrArg G.shape.arity h) p.2)) else 0
def endpointColumn (q : Fin G.shape.edges × Bool) (i : Column G) : ℤ :=
  portColumn G (G.shape.closedPorts.symm q) i

def coefficient : Row G → Column G → ℤ
  | .inl v, i => if i.1 = v then 1 else 0
  | .inr (.inl e), i => endpointColumn G (e, false) i + endpointColumn G (e, true) i
  | .inr (.inr c), i => if G.vertex c.1 c.2 = 0 ∧ i = c then 1 else 0

def rhs : Row G → ℤ
  | .inl _ => 1
  | .inr _ => 0

def equations (w : Weights G) : Prop :=
  ∀ r, (∑ i : Column G, (coefficient G r i : ℚ) * w i.1 i.2) = rhs G r

theorem port_inner (w : Weights G) (p : Σ v : Fin G.shape.vertices, Fin (G.shape.arity v)) :
    (∑ i : Column G, (portColumn G p i : ℚ) * w i.1 i.2) = mean (w p.1) p.2 := by
  classical
  rcases p with ⟨v, j⟩
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ x : Word (G.shape.arity v),
        (portColumn G ⟨v,j⟩ ⟨v,x⟩ : ℚ) * w v x := by
      apply Finset.sum_eq_single v
      · intro u _ huv
        apply Finset.sum_eq_zero
        intro x _
        simp only [portColumn,dif_neg (Ne.symm huv),Int.cast_zero,zero_mul]
      · intro hv
        exact (hv (Finset.mem_univ v)).elim
    _ = mean (w v) j := by
      have hp (x : Word (G.shape.arity v)) :
          portColumn G ⟨v,j⟩ ⟨v,x⟩ = spinZ (x j) := by
        simp [portColumn]
      simp only [hp,cast_spinZ,mean,mul_comm]

theorem endpoint_inner (w : Weights G) (q : Fin G.shape.edges × Bool) :
    (∑ i : Column G, (endpointColumn G q i : ℚ) * w i.1 i.2) = endpointMean G w q :=
  port_inner G w (G.shape.closedPorts.symm q)

theorem equations_iff (w : Weights G) : equations G w ↔
    (∀ v, ∑ a, w v a = 1) ∧
    (∀ v a, G.vertex v a = 0 → w v a = 0) ∧
    (∀ e, endpointMean G w (e, false) + endpointMean G w (e, true) = 0) := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro v
      have hv := h (.inl v)
      simpa [coefficient, rhs, Fintype.sum_sigma] using hv
    · intro v a ha
      have hv := h (.inr (.inr ⟨v, a⟩))
      simpa [coefficient, rhs, ha] using hv
    · intro e
      have he := h (.inr (.inl e))
      simpa only [coefficient, rhs, Int.cast_zero, Int.cast_add, add_mul,
        Finset.sum_add_distrib, endpoint_inner] using he
  · rintro ⟨hv, hz, he⟩ r
    rcases r with v | e | c
    · simpa [coefficient, rhs, Fintype.sum_sigma] using hv v
    · simpa only [coefficient, rhs, Int.cast_zero, Int.cast_add, add_mul,
        Finset.sum_add_distrib, endpoint_inner] using he e
    · by_cases hc : G.vertex c.1 c.2 = 0
      · simpa [coefficient, rhs, hc] using hz c.1 c.2 hc
      · simp [coefficient, rhs, hc]

theorem feasible_iff (w : Weights G) : Feasible G w ↔
    (∀ i : Column G, 0 ≤ w i.1 i.2) ∧ equations G w := by
  rw [equations_iff]
  constructor
  · intro hw; exact ⟨fun i => hw.nonneg i.1 i.2, hw.total, hw.offSupport, hw.edge⟩
  · rintro ⟨hn, ht, hs, he⟩; exact ⟨fun v a => hn ⟨v, a⟩, ht, hs, he⟩

theorem portColumn_range (p : Σ v : Fin G.shape.vertices, Fin (G.shape.arity v)) (i : Column G) :
    -1 ≤ portColumn G p i ∧ portColumn G p i ≤ 1 := by
  dsimp [portColumn]
  split_ifs <;> simp [spinZ] <;> split_ifs <;> norm_num

theorem coefficient_range (r : Row G) (i : Column G) :
    -2 ≤ coefficient G r i ∧ coefficient G r i ≤ 2 := by
  rcases r with v | e | c
  · simp only [coefficient]; split_ifs <;> norm_num
  · have h0 := portColumn_range G (G.shape.closedPorts.symm (e, false)) i
    have h1 := portColumn_range G (G.shape.closedPorts.symm (e, true)) i
    dsimp [coefficient, endpointColumn]; omega
  · simp only [coefficient]; split_ifs <;> norm_num

theorem row_count : Fintype.card (Row G) = G.shape.vertices + G.shape.edges + Fintype.card (Column G) := by
  simp [Row, Fintype.card_sum, Nat.add_assoc]

end
end Holant.LocalDrafts.Tractability.EOEvaluation.LinearSystem
