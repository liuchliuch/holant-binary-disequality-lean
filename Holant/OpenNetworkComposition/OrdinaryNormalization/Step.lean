import Holant.OpenNetworkComposition.OrdinaryNormalization.Wire
import Holant.OpenNetworkComposition.FreeOrdinaryTensor

/-! Replace one free boundary stub by the ordinary I-X-I wire. Every old
vertex and local port is retained, and the corrected tensor is unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.OrdinaryNormalization
variable {K V F E : Type*} {n : ℕ} [CommSemiring K]

/-- One genuine ordinary port of the fixed wire, used as its attaching port. -/
def wireAttach : Σv,Fin ((wire (K := K)).shape.arity v) :=
  Classical.choose (wire_boundary_ordinary (K := K) 1)

theorem wireAttach_boundary : (wire (K := K)).shape.boundary 1=.inl wireAttach :=
  Classical.choose_spec (wire_boundary_ordinary (K := K) 1)

/-- Only the selected free endpoint is removed. Its old opposite endpoint,
including another free endpoint, survives in the actual disjoint splice. -/
abbrev step (N : FiniteNetwork K V F E n) (f : F) :
    FiniteNetwork K (V ⊕ WireVertices) (FiniteShape.CutFree f ⊕ WireFree)
      (FreeOrdinary.JoinEdges (ER := WireEdges) N.shape f) n :=
  FreeOrdinary.network N wire f (N.shape.freeBoundary f) wireAttach
    (N.shape.free_boundary f) wireAttach_boundary

theorem step_native (N : FiniteNetwork K V F E n) (f : F)
    (he : ∀e,N.edge e=.disequality) :
    ∀e,(step N f).edge e=.disequality :=
  FreeOrdinary.network_edges_native _ _ _ _ _ _ _ he wire_native

theorem step_uses (N : FiniteNetwork K V F E n) (f : F) (family : SignatureFamily K)
    (hv : ∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family)
    (hI : (⟨2,identitySignature (K := K)⟩ : AnySignature K)∈family) :
    ∀v,(⟨(step N f).shape.arity v,(step N f).vertex v⟩ : AnySignature K)∈family := by
  rintro (v|v)
  · exact hv v
  · exact wire_uses family hI v

/-- This is literal equality of each original dependent label, so no
replacement, rescaling, or change in its local ordered ports occurs. -/
theorem step_original_label (N : FiniteNetwork K V F E n) (f : F) (v : V) :
    (⟨(step N f).shape.arity (.inl v),(step N f).vertex (.inl v)⟩ : AnySignature K)=
      ⟨N.shape.arity v,N.vertex v⟩ := rfl

/-- Every newly introduced occurrence is the literal I signature. -/
theorem step_new_label (N : FiniteNetwork K V F E n) (f : F) (v : WireVertices) :
    (⟨(step N f).shape.arity (.inr v),(step N f).vertex (.inr v)⟩ : AnySignature K)=
      ⟨2,identitySignature (K := K)⟩ := by
  cases v <;> rfl

variable [Fintype V] [Fintype F] [Fintype E]

/-- The native-X boundary correction is accounted for exactly, including
when the selected stub belongs to an isolated free/free edge box. -/
theorem step_tensor (N : FiniteNetwork K V F E n) (f : F)
    (he : ∀e,N.edge e=.disequality) : (step N f).tensor=N.tensor := by
  rw [step,FreeOrdinary.network_tensor _ _ _ _ _ _ _ he wire_native]
  exact splice_wire N.tensor (N.shape.freeBoundary f)

/-- Each actual splice removes exactly one free boundary occurrence. -/
theorem step_free_card_lt (f : F) :
    Fintype.card (FiniteShape.CutFree f ⊕ WireFree)<Fintype.card F := by
  classical
  simpa [WireFree] using
    (Fintype.card_subtype_lt (x := f) (p := fun g : F => g≠f) (not_not.mpr rfl))

end Holant.OpenNetworkComposition.OrdinaryNormalization
