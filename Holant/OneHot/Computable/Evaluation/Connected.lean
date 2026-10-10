import Holant.OneHot.Computable.Evaluation.Unicycle
import Holant.OneHot.Decomposition.ConnectedEvaluation

/-! Executable density/tree/unicycle branching on the original connected input. -/

namespace Holant.Network

open OneHot OneHot.Decomposition

variable {K : Type*} [CommSemiring K] (N : Network K 0)

omit [CommSemiring K] in
theorem computed_cycle_count (root : Fin N.shape.vertices)
    (hc : N.incidenceGraph.Connected root)
    (hd : ¬N.shape.vertices < N.shape.edges)
    (ht : ¬N.shape.edges + 1 = N.shape.vertices) : N.shape.edges = N.shape.vertices := by
  have hh := (N.computedSpanning root hc).vertices_le_edges_add_one
  simp only [Fintype.card_fin] at hh
  omega

/-- Every branch is executed on actual original record counts. -/
def computedConnectedProgram (root : Fin N.shape.vertices)
    (hc : N.incidenceGraph.Connected root) : Arithmetic K K :=
  if hd : N.shape.vertices < N.shape.edges then .pure 0
  else if ht : N.shape.edges + 1 = N.shape.vertices then N.computedTreeProgram root hc
  else N.computedUnicycleProgram root hc (N.computed_cycle_count root hc hd ht)

theorem computedConnectedProgram_spec (root : Fin N.shape.vertices)
    (hc : N.incidenceGraph.Connected root)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    (N.computedConnectedProgram root hc).run.1 = N.denote Fin.elim0 ∧
    (N.computedConnectedProgram root hc).run.2 ≤ 10 * (N.shape.vertices + N.shape.edges) := by
  unfold computedConnectedProgram
  split
  · rename_i hd
    have hn := N.asFinite.denote_zero_of_dense (by simpa only [Fintype.card_fin] using hd) hf hX
    rw [N.denote_asFinite] at hn
    simp only [Arithmetic.run_pure, hn, Pi.zero_apply]
    exact ⟨trivial, Nat.zero_le _⟩
  · rename_i hd
    split
    · rename_i ht
      rw [N.computedTreeProgram_spec root hc ht hf hX]
      exact ⟨rfl, by omega⟩
    · rename_i ht
      rw [N.computedUnicycleProgram_spec root hc (N.computed_cycle_count root hc hd ht) hf hX]
      exact ⟨rfl, by omega⟩

/-- A finite check supplies all connectedness evidence; empty/disconnected inputs
are deferred to the component-product layer. -/
def compileConnected : Option (Arithmetic K K) :=
  if hn : 0 < N.shape.vertices then
    let root : Fin N.shape.vertices := ⟨0, hn⟩
    if hc : N.incidenceGraph.Connected root then some (N.computedConnectedProgram root hc)
    else none
  else none

theorem compileConnected_spec
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality)
    (p : Arithmetic K K) (hp : N.compileConnected = some p) :
    p.run.1 = N.denote Fin.elim0 ∧ p.run.2 ≤ 10 * (N.shape.vertices + N.shape.edges) := by
  unfold compileConnected at hp
  split at hp
  · dsimp only at hp
    split at hp
    · cases Option.some.inj hp
      exact N.computedConnectedProgram_spec _ _ hf hX
    · contradiction
  · contradiction

end Holant.Network

namespace Holant.OneHot.Computable.Evaluation

open Holant.Complexity

/-- Real encoded data to the general connected one-hot arithmetic compiler. -/
def compileConnectedBits {K : Type*} [CommSemiring K] (s b : ℕ) (arity : ℕ → ℕ)
    (signatures : (i : Fin s) → Holant.Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) (bits : List Bool) : Option (Arithmetic K K) :=
  ((RawClosedNetwork.validatedEncoding s b arity).decode bits).bind fun r =>
    (r.1.executableRealize r.2 signatures kernels).compileConnected

theorem compileConnectedBits_encode {K : Type*} [CommSemiring K] {s b : ℕ} {arity : ℕ → ℕ}
    (signatures : (i : Fin s) → Holant.Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) (r : RawClosedNetwork)
    (h : r.WellFormed s b arity) :
    compileConnectedBits s b arity signatures kernels (RawClosedNetwork.encoding.encode r) =
      (r.executableRealize h signatures kernels).compileConnected := by
  unfold compileConnectedBits
  have hd := (RawClosedNetwork.validatedEncoding s b arity).decode_encode ⟨r, h⟩
  change (RawClosedNetwork.validatedEncoding s b arity).decode
    (RawClosedNetwork.encoding.encode r) = some ⟨r, h⟩ at hd
  rw [hd]
  rfl

end Holant.OneHot.Computable.Evaluation
