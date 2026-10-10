import Holant.OneHot.Decomposition.UnicycleEvaluation
import Holant.OneHot.Density

/-!
# Arithmetic evaluation of every connected one-hot component

Density is tested on the actual original component. The remaining cases are
proved to be a tree or a unicycle and evaluated by genuine extracted graphs.
Only semiring instructions in the resulting program are counted; effective
preprocessing and machine-level bit complexity remain separate obligations.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.FiniteNetwork

open OneHot OneHot.Decomposition

variable {K V E : Type*} [Fintype V] [Fintype E] [CommSemiring K]
variable (N : FiniteNetwork K V E 0)

open scoped Classical

/-- The density obstruction applies to arbitrary finite-index presentations. -/
theorem denote_zero_of_dense
    (dense : Fintype.card V < Fintype.card E)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) : N.denote = 0 := by
  have hn := Network.denote_native_oneHot_of_dense N.toNetwork.shape N.toNetwork.vertex
    (fun v => hf ((Fintype.equivFin V).symm v)) dense
  have he : N.toNetwork.denote =
      (Network.mk N.toNetwork.shape N.toNetwork.vertex (fun _ => Signature.disequality)).denote := by
    apply Network.denote_congr
    · intro v x
      rfl
    · intro e a b
      exact congrFun₂ (hX ((Fintype.equivFin E).symm e)) a b
  rw [← N.denote_toNetwork]
  exact he.trans hn

omit [CommSemiring K] in
/-- The remaining sparse non-tree case has exactly equal original edge/vertex
counts. This follows from extracted connectivity, not an input certificate. -/
theorem equal_card_of_sparse_not_tree (root : V)
    (connected : ∀ v, Relation.EqvGen (Link N.endpoint) root v)
    (sparse : ¬Fintype.card V < Fintype.card E)
    (notTree : ¬Fintype.card E + 1 = Fintype.card V) :
    Fintype.card E = Fintype.card V := by
  have h := (extractRootedSpanning N.endpoint root connected).vertices_le_edges_add_one
  omega

/-- An actual arithmetic program for the connected original input. -/
noncomputable def connectedProgram (root : V)
    (connected : ∀ v, Relation.EqvGen (Link N.endpoint) root v) : Arithmetic K K :=
  if dense : Fintype.card V < Fintype.card E then .pure 0
  else if tree : Fintype.card E + 1 = Fintype.card V then
    N.connectedTreeProgram root connected
  else N.unicycleProgram root connected (N.equal_card_of_sparse_not_tree root connected dense tree)

/-- Exact original denotation and a uniform linear semiring-instruction bound. -/
theorem connectedProgram_spec (root : V)
    (connected : ∀ v, Relation.EqvGen (Link N.endpoint) root v)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    (N.connectedProgram root connected).run.1 = N.denote Fin.elim0 ∧
      (N.connectedProgram root connected).run.2 ≤ 10 * (Fintype.card V + Fintype.card E) := by
  unfold connectedProgram
  split
  · rename_i dense
    simp only [Arithmetic.run_pure]
    rw [N.denote_zero_of_dense dense hf hX]
    simp
  · rename_i sparse
    split
    · rename_i tree
      rw [N.connectedTreeProgram_spec root connected tree hf hX]
      simp only
      constructor
      · trivial
      · omega
    · rename_i notTree
      rw [N.unicycleProgram_spec root connected
        (N.equal_card_of_sparse_not_tree root connected sparse notTree) hf hX]
      simp only
      constructor
      · trivial
      · omega

end Holant.FiniteNetwork
