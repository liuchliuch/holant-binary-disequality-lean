import Holant.VertexGadget
import Holant.EdgeBox

/-!
Actual finite-gadget realizability, separate from polynomial-time oracle access.
The resource test applies only to ordinary tensor vertices. Structural default
edges, including isolated edge boxes, are not extra supplied signatures.
-/

namespace Holant

abbrev AnySignature (K : Type*) := Σ n, Signature K n
abbrev SignatureFamily (K : Type*) := Set (AnySignature K)

namespace OpenNetwork

variable {K : Type*} {n : ℕ}

def Uses (N : OpenNetwork K n) (F : SignatureFamily K) : Prop :=
  ∀ v, (⟨N.shape.arity v, N.vertex v⟩ : AnySignature K) ∈ F

def HasDefaultEdges (N : OpenNetwork K n) (W : EdgeKind) : Prop := ∀ e, N.edge e = W

end OpenNetwork

namespace Gadget

variable {K : Type*} [CommSemiring K] {n : ℕ}

/-- An actual finite open network, with exact boundary entries and port order. -/
def Realizes (F : SignatureFamily K) (W : EdgeKind) (f : Signature K n) : Prop :=
  ∃ N : OpenNetwork K n, N.Uses F ∧ N.HasDefaultEdges W ∧ N.tensor = f

/-- Projective realizability records the nonzero scalar rather than discarding it. -/
def RealizesUpTo (F : SignatureFamily K) (W : EdgeKind) (f : Signature K n) : Prop :=
  ∃ c : K, c ≠ 0 ∧ Realizes F W (fun x => c * f x)

theorem Realizes.mono {F G : SignatureFamily K} {W : EdgeKind} {f : Signature K n}
    (h : Realizes F W f) (hFG : F ⊆ G) : Realizes G W f := by
  obtain ⟨N, hN, hW, hf⟩ := h
  exact ⟨N, fun v => hFG (hN v), hW, hf⟩

/-- A supplied signature is directly realized by one genuine vertex. -/
theorem realizes_of_mem (F : SignatureFamily K) (W : EdgeKind) (f : Signature K n)
    (hf : (⟨n, f⟩ : AnySignature K) ∈ F) : Realizes F W f := by
  refine ⟨OpenNetwork.singleVertex f, ?_, ?_, OpenNetwork.tensor_vertex f⟩
  · intro v
    exact hf
  · intro e
    exact Fin.elim0 e

/-- The two-port structural primitive is the default kernel, even with no resources. -/
theorem realizes_edgeBox (F : SignatureFamily K) (W : EdgeKind) :
    Realizes F W (fun x : Fin 2 → Bool => W.value (x 0) (x 1)) := by
  refine ⟨OpenNetwork.edgeBox W, ?_, ?_, ?_⟩
  · intro v
    exact Fin.elim0 v
  · intro e
    rfl
  · funext x
    exact OpenNetwork.tensor_edgeBox W x

end Gadget
end Holant
