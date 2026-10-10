import Holant.OneHot.Computable.Evaluation.Conditioning

/-! Executed original surplus-edge selection and two actual conditioned-tree programs. -/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot.Computable.Evaluation

open Holant.OneHot.Decomposition

variable {n m : ℕ} {endpoint : Fin m → Bool → Fin n} {root : Fin n}
variable (t : RootedSpanning endpoint root)

/-- Scan original edge IDs against all computed original parent edges. -/
def surplusEdges : Finset (Fin m) :=
  Finset.univ.filter (fun e => ∀ u : {u : Fin n // u ≠ root}, t.parentEdge u ≠ e)

@[simp] theorem mem_surplusEdges (e : Fin m) :
    e ∈ surplusEdges t ↔ e ∉ Set.range t.parentEdge := by
  simp [surplusEdges, Set.mem_range]

theorem surplusEdges_nonempty (hc : m = n) : (surplusEdges t).Nonempty := by
  classical
  let e := t.chooseSurplus (by simpa only [Fintype.card_fin] using hc)
  exact ⟨e.1, (mem_surplusEdges t e.1).mpr e.2⟩

/-- Choose the least original surplus ID by actual finite scanning. -/
def surplusEdge (hc : m = n) : t.Surplus :=
  ⟨(surplusEdges t).min' (surplusEdges_nonempty t hc),
    (mem_surplusEdges t _).mp (Finset.min'_mem _ _)⟩

end Holant.OneHot.Computable.Evaluation

namespace Holant.Network

open OneHot OneHot.Computable.Evaluation OneHot.Decomposition

variable {K : Type*} [CommSemiring K] (N : Network K 0)
variable {root : Fin N.shape.vertices} (t : RootedSpanning N.shape.endpoint root)

omit [CommSemiring K] in
/-- Original selected parents prove residual connectivity after actual deletion. -/
theorem executableCondition_connected (e : t.Surplus) (a b : Bool) (v : Fin N.shape.vertices) :
    Relation.EqvGen (Link (N.asFinite.executableConditionEdge e.1 a b).endpoint) root v := by
  rw [FiniteNetwork.executableConditionEdge_eq]
  exact N.asFinite.conditionEdge_connected t e a b v

/-- Both deleted occurrences are conditioned inside the actual local labels. -/
def executableConditionedProgram (e : t.Surplus) (a b : Bool) : Arithmetic K K :=
  (N.asFinite.executableConditionEdge e.1 a b).computedTreeProgram root
    (N.executableCondition_connected t e a b)

theorem executableConditionedProgram_spec (e : t.Surplus) (a b : Bool)
    (hcycle : N.shape.edges = N.shape.vertices)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    (N.executableConditionedProgram t e a b).run =
      ((N.asFinite.conditionEdge e.1 a b).denote Fin.elim0,
        3 * N.shape.vertices + 5 * Fintype.card (FiniteNetwork.RemainingEdge e.1) - 1) := by
  have ht : Fintype.card (FiniteNetwork.RemainingEdge e.1) + 1 = Fintype.card (Fin N.shape.vertices) := by
    have hp : 0 < N.shape.edges := Nat.lt_of_le_of_lt (Nat.zero_le e.1.val) e.1.isLt
    simp only [FiniteNetwork.RemainingEdge, Fintype.card_subtype_compl,
      Fintype.card_unique, Fintype.card_fin]
    omega
  have hn := (N.asFinite.executableConditionEdge e.1 a b).computedTreeProgram_spec root
    (N.executableCondition_connected t e a b)
    ht
    (by
      intro v
      rw [FiniteNetwork.executableConditionEdge_eq]
      exact N.asFinite.conditionEdge_oneHot e.1 a b hf v)
    (fun d => hX d.1)
  have hd := congrArg (fun M : FiniteNetwork K (Fin N.shape.vertices) (FiniteNetwork.RemainingEdge e.1) 0 =>
      M.denote Fin.elim0) (N.asFinite.executableConditionEdge_eq e.1 a b)
  rw [hd] at hn
  unfold executableConditionedProgram
  convert! hn using 1
  congr! 3
  simp only [Fintype.card_fin]

/-- Two executed residual-tree programs and exactly one addition. -/
def executableSpanningUnicycleProgram (e : t.Surplus) : Arithmetic K K := do
  let x ← N.executableConditionedProgram t e false true
  let y ← N.executableConditionedProgram t e true false
  Arithmetic.addOp x y

theorem executableSpanningUnicycleProgram_spec (e : t.Surplus)
    (hcycle : N.shape.edges = N.shape.vertices)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    (N.executableSpanningUnicycleProgram t e).run =
      (N.denote Fin.elim0, 6 * N.shape.vertices + 10 * N.shape.edges - 11) := by
  rw [executableSpanningUnicycleProgram]
  simp only [bind, Arithmetic.run_bind,
    N.executableConditionedProgram_spec t e false true hcycle hf hX,
    N.executableConditionedProgram_spec t e true false hcycle hf hX, Arithmetic.run_addOp]
  have hn := N.asFinite.denote_eq_two_conditionEdge e.1 (hX e.1) Fin.elim0
  rw [N.denote_asFinite] at hn
  apply Prod.ext
  · convert! hn.symm using 1
    congr! 3
  · have he : Fintype.card (FiniteNetwork.RemainingEdge e.1) = N.shape.edges - 1 := by
      simp [FiniteNetwork.RemainingEdge, Fintype.card_subtype_compl]
    have hv : 0 < N.shape.vertices := Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
    dsimp only
    omega

/-- Original incidence, computed parents and computed surplus ID determine the
whole program; no spanning tree or surplus edge is supplied as input. -/
def computedUnicycleProgram (root : Fin N.shape.vertices)
    (hc : N.incidenceGraph.Connected root) (hcycle : N.shape.edges = N.shape.vertices) : Arithmetic K K :=
  let t := N.computedSpanning root hc
  N.executableSpanningUnicycleProgram t (surplusEdge t hcycle)

theorem computedUnicycleProgram_spec (root : Fin N.shape.vertices)
    (hc : N.incidenceGraph.Connected root) (hcycle : N.shape.edges = N.shape.vertices)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    (N.computedUnicycleProgram root hc hcycle).run =
      (N.denote Fin.elim0, 6 * N.shape.vertices + 10 * N.shape.edges - 11) :=
  N.executableSpanningUnicycleProgram_spec (N.computedSpanning root hc)
    (surplusEdge (N.computedSpanning root hc) hcycle) hcycle hf hX

end Holant.Network
