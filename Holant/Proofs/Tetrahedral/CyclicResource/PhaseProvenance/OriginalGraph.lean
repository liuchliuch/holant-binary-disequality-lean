import Holant.Proofs.Tetrahedral.CyclicResource.PhaseProvenance.CurrentEndpoint
import Holant.NetworkAlgebra


namespace Holant.LocalDrafts.TetrahedralCompletion.CyclicResource.PhaseProvenance
open Holant Holant.LocalDrafts.MainChain RingHomRealization
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {L : Type*} [Field L]

theorem mapAny_injective (φ : L →+* ℂ) : Function.Injective (mapAny φ) := by
  rintro ⟨n,f⟩ ⟨m,g⟩ he
  have hn : n = m := congrArg Sigma.fst he
  subst m
  have hf : RingHomRealization.mapSignature φ f = RingHomRealization.mapSignature φ g :=
    eq_of_heq (Sigma.mk.inj_iff.mp he).2
  exact congrArg (fun t : Signature L n => (⟨n,t⟩ : AnySignature L))
    (RingHomDescent.signature_injective φ hf)

variable (φ : L →+* ℂ) {F : SignatureFamily L} {n : ℕ}
variable (M : Network ℂ n)
variable (hM : ∀ v, (⟨M.shape.arity v,M.vertex v⟩ : AnySignature ℂ) ∈ mapFamily φ F)

def originalGraph : Network L n where
  shape := M.shape
  vertex v := (RingHomDescent.vertex_preimage φ (M.vertex v) (hM v)).choose
  edge _ := Signature.disequality

theorem originalGraph_labels (v : Fin M.shape.vertices) :
    (⟨(originalGraph φ M hM).shape.arity v,(originalGraph φ M hM).vertex v⟩ :
      AnySignature L) ∈ F :=
  (RingHomDescent.vertex_preimage φ (M.vertex v) (hM v)).choose_spec.1

theorem originalGraph_native (e : Fin M.shape.edges) :
    (originalGraph φ M hM).edge e = Signature.disequality := rfl

theorem originalGraph_map (hX : ∀ e, M.edge e = Signature.disequality) :
    (originalGraph φ M hM).map φ = M := by
  have hv : (fun v => RingHomRealization.mapSignature φ
      ((originalGraph φ M hM).vertex v)) = M.vertex := by
    funext v
    exact (RingHomDescent.vertex_preimage φ (M.vertex v) (hM v)).choose_spec.2
  have he : (fun _ : Fin M.shape.edges => fun a b =>
      φ (Signature.disequality a b)) = M.edge := by
    funext e a b
    rw [hX e]
    cases a <;> cases b <;> simp [Signature.disequality]
  change {
    shape := M.shape
    vertex := fun v => RingHomRealization.mapSignature φ ((originalGraph φ M hM).vertex v)
    edge := fun _ a b => φ (Signature.disequality a b)} = M
  exact congrArg₂ (fun v e => (⟨M.shape,v,e⟩ : Network ℂ n)) hv he

/-- Literal label equality is reflected by the field embedding. In
particular a different original four-ary label cannot acquire a q charge. -/
theorem originalGraph_count (q : Signature L 4)
    (hX : ∀ e, M.edge e = Signature.disequality) :
    (∑ v : Fin (originalGraph φ M hM).shape.vertices,
      if (⟨(originalGraph φ M hM).shape.arity v,(originalGraph φ M hM).vertex v⟩ :
        AnySignature L) = ⟨4,q⟩ then 1 else 0) =
      occurrences (RingHomRealization.mapSignature φ q) M := by
  classical
  trans occurrences (RingHomRealization.mapSignature φ q) ((originalGraph φ M hM).map φ)
  · unfold occurrences
    apply Finset.sum_congr rfl
    intro v _
    have he : mapAny φ
        (⟨(originalGraph φ M hM).shape.arity v,(originalGraph φ M hM).vertex v⟩ : AnySignature L) =
        mapAny φ (⟨4,q⟩ : AnySignature L) ↔
        (⟨(originalGraph φ M hM).shape.arity v,(originalGraph φ M hM).vertex v⟩ : AnySignature L) =
        ⟨4,q⟩ := (mapAny_injective φ).eq_iff
    change (if (⟨(originalGraph φ M hM).shape.arity v,(originalGraph φ M hM).vertex v⟩ :
      AnySignature L) = ⟨4,q⟩ then (1 : ℕ) else 0) =
      if mapAny φ (⟨(originalGraph φ M hM).shape.arity v,(originalGraph φ M hM).vertex v⟩ :
        AnySignature L) = mapAny φ (⟨4,q⟩ : AnySignature L) then 1 else 0
    simp only [he]
  · exact congrArg (occurrences (RingHomRealization.mapSignature φ q))
      (originalGraph_map φ M hM hX)

/-- The source certificate scalar remains in the equality for this SAME
graph. No assumption that the analytic target or scalar lies in L is needed.
The actual output over L is the originalGraph's own denote. -/
theorem originalGraph_value {g : Signature ℂ n} {c : ℂ}
    (hX : ∀ e, M.edge e = Signature.disequality) (he : M.denote = c • g) :
    RingHomRealization.mapSignature φ (originalGraph φ M hM).denote = c • g := by
  calc
    RingHomRealization.mapSignature φ (originalGraph φ M hM).denote =
        ((originalGraph φ M hM).map φ).denote := by
      funext x
      exact (Network.denote_map φ _ x).symm
    _ = M.denote := congrArg Network.denote (originalGraph_map φ M hM hX)
    _ = c • g := he

theorem originalGraph_actual :
    Gadget.Realizes F .disequality (originalGraph φ M hM).denote :=
  Gadget.realizes_network _ F .disequality (originalGraph_labels φ M hM)
    (originalGraph_native φ M hM)

end
end Holant.LocalDrafts.TetrahedralCompletion.CyclicResource.PhaseProvenance
