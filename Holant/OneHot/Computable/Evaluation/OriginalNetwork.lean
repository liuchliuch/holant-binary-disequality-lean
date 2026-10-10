import Holant.OneHot.Computable.Evaluation.FiniteTree

/-!
# Executable original-port tree evaluation

All runtime coefficients below are read from the actual input Network. The
proved finite-index construction replaces the old classical child enumeration.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.Network

open OneHot OneHot.Decomposition OneHot.Computable.Evaluation

variable {K : Type*} [CommSemiring K] (N : Network K 0)
variable {root : Fin N.shape.vertices} (t : RootedSpanning N.shape.endpoint root)

/-- Read the actual child-end port using decidable finite vertex equality. -/
def executableParent (v : Fin N.shape.vertices) : K :=
  if h : v = root then 0 else
    N.occurrenceCoefficient (N.shape.closedPorts.symm (t.parentEnd ⟨v, h⟩))

/-- The other end of the same original edge retains its original local port. -/
def executableChild (u : {v : Fin N.shape.vertices // v ≠ root}) : K :=
  N.occurrenceCoefficient (N.shape.closedPorts.symm
    ((t.parentEnd u).1, !(t.parentEnd u).2))

@[simp] theorem executableParent_eq : N.executableParent t = N.treeParent t := by
  funext v
  unfold executableParent treeParent
  split <;> rfl

omit [CommSemiring K] in
@[simp] theorem executableChild_eq : N.executableChild t = N.treeChild t := rfl

/-- Compiles when the input network and computed parent table compile. No
classical enumeration or choice is called by this definition. -/
def executableTree (maxDepth : ℕ) : Tree K :=
  tree t N.treeZero (N.executableParent t) (N.executableChild t) maxDepth

/-- Both orientations' coefficients are exactly their original ordered ports. -/
theorem executable_coefficients (u : {v : Fin N.shape.vertices // v ≠ root}) :
    N.executableParent t u.1 =
      N.vertex (N.shape.closedPorts.symm (t.parentEnd u)).1
        (fun j => decide (j = (N.shape.closedPorts.symm (t.parentEnd u)).2)) ∧
    N.executableChild t u =
      N.vertex (N.shape.closedPorts.symm ((t.parentEnd u).1, !(t.parentEnd u).2)).1
        (fun j => decide (j =
          (N.shape.closedPorts.symm ((t.parentEnd u).1, !(t.parentEnd u).2)).2)) := by
  simp only [executableParent, dite_eq_right u.2, executableChild, occurrenceCoefficient, and_self]

omit [CommSemiring K] in
/-- Every selected child edge has exactly its original two incident vertices. -/
theorem executable_child_incidence (v : Fin N.shape.vertices) (u : Child t v) :
    N.shape.endpoint (t.parentEnd ⟨u.1, u.2.1⟩).1 (t.parentEnd ⟨u.1, u.2.1⟩).2 = u.1 ∧
    N.shape.endpoint (t.parentEnd ⟨u.1, u.2.1⟩).1 (!(t.parentEnd ⟨u.1, u.2.1⟩).2) = v := by
  refine ⟨t.child_endpoint _, ?_⟩
  simpa only [parent, dite_eq_right u.2.1] using u.2.2

/-- Exact original-network sum and exact arithmetic count for the executable
construction. Connectivity/parent extraction is supplied by the executable graph
module below; no supplied recursive tree or port relabeling is assumed here. -/
theorem executableTree_program_spec (maxDepth : ℕ)
    (bound : ∀ u, t.depth u ≤ maxDepth)
    (htree : N.shape.edges + 1 = N.shape.vertices)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    (N.executableTree t maxDepth).closedProgram.run =
      (N.denote Fin.elim0, 3 * N.shape.vertices + 5 * N.shape.edges - 1) := by
  have hs := tree_spec t N.treeZero (N.executableParent t) (N.executableChild t) maxDepth bound
  rw [N.executableParent_eq t, N.executableChild_eq t] at hs
  have old := N.extractedTree_program_spec t htree hf hX
  rw [closedProgram_run] at old
  rw [closedProgram_run]
  have hv : (N.executableTree t maxDepth).eval = (N.extractedTree t).eval := by
    simpa only [executableTree, executableParent_eq, executableChild_eq, extractedTree] using hs.1
  have hn : (N.executableTree t maxDepth).vertices = N.shape.vertices := by
    simpa only [executableTree, executableParent_eq, executableChild_eq] using hs.2.1
  have he : (N.executableTree t maxDepth).edges = N.shape.edges := by
    have hh : (N.executableTree t maxDepth).edges + 1 = N.shape.vertices := by
      simpa only [executableTree, executableParent_eq, executableChild_eq] using hs.2.2
    omega
  rw [hv, hn, he]
  have ho := congrArg (fun p : K × ℕ => p.1) old
  exact Prod.ext ho rfl

end Holant.Network
