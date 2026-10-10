import Holant.ReedMuller.WeightTwoIntegration.ExceptionalPhysical
import Holant.ReedMuller.WeightTwoIntegration.ExceptionalDressing
import Holant.ReedMuller.WeightTwoIntegration.ExceptionalDeterminant

/-! Constant-size, literal native-X realization of the six-port exception. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open scoped BigOperators
open CoefficientAtlas ExceptionalTopology
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def TwoSixPortCopies {V E : Type*} [Fintype V] (N : FiniteNetwork ℂ V E 4)
    (q : Signature ℂ 6) : Prop :=
  Fintype.card {v : V // N.arity v = 6} = 2 ∧
    ∀ v, N.arity v = 6 → HEq (N.vertex v) q

theorem physicalNetwork_two_copies {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (q : Signature ℂ 6) :
    TwoSixPortCopies (physicalNetwork d B q) q := by
  constructor
  · change Fintype.card {v : Bool ⊕ Fin 4 //
      (match v with | .inl _ => 6 | .inr _ => 2) = 6} = 2
    decide
  · rintro (b|e) hv
    · rfl
    · change (2 : ℕ) = 6 at hv
      omega

theorem dressedNetwork_two_copies {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (q : Signature ℂ 6) (c : ℂ) :
    TwoSixPortCopies (ExceptionalDressing.attachI (physicalNetwork d B q) c) q := by
  constructor
  · change Fintype.card {v : (Bool ⊕ Fin 4) ⊕ Unit //
      (match v with | .inl (.inl _) => 6 | .inl (.inr _) => 2 | .inr _ => 2) = 6} = 2
    decide
  · rintro ((b|e)|u) hv
    · rfl
    · change (2 : ℕ) = 6 at hv
      omega
    · change (2 : ℕ) = 6 at hv
      omega

theorem two_copies_toNetwork {V E : Type*} [Fintype V] [Fintype E]
    (N : FiniteNetwork ℂ V E 4) (q : Signature ℂ 6) (h : TwoSixPortCopies N q) :
    Fintype.card {v : Fin N.toNetwork.shape.vertices // N.toNetwork.shape.arity v = 6} = 2 ∧
      ∀ v, N.toNetwork.shape.arity v = 6 → HEq (N.toNetwork.vertex v) q := by
  constructor
  · calc
      _ = Fintype.card {v : V // N.arity v = 6} :=
        Fintype.card_congr (Equiv.subtypeEquiv (Fintype.equivFin V).symm (fun _ => Iff.rfl))
      _ = 2 := h.1
  · intro v hv
    exact h.2 ((Fintype.equivFin V).symm v) hv

theorem physicalNetwork_uses {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (q : Signature ℂ 6)
    (hq : (⟨6,q⟩ : AnySignature ℂ) ∈ family) :
    ∀ v, (⟨(physicalNetwork d B q).arity v,(physicalNetwork d B q).vertex v⟩ :
      AnySignature ℂ) ∈ family := by
  rintro (b|e)
  · exact hq
  · exact B.available (linkSigns d e)

theorem uses_toNetwork {V E : Type*} [Fintype V] [Fintype E]
    (N : FiniteNetwork ℂ V E 4) (family : SignatureFamily ℂ)
    (h : ∀ v, (⟨N.arity v,N.vertex v⟩ : AnySignature ℂ) ∈ family) :
    ∀ v, (⟨N.toNetwork.shape.arity v,N.toNetwork.vertex v⟩ : AnySignature ℂ) ∈ family :=
  fun v => h ((Fintype.equivFin V).symm v)

/-- Complete six-port exceptional alternative: an actual graph with at most
seven genuine vertices and nine native X edges. Exactly two vertices are the
original six-port q. All remaining vertices are the fixed binary resources.
No Walsh matrix or normalized logical tensor is a supplied resource. -/
theorem exceptional_two_copy_even4 {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (q : Signature ℂ 6)
    (hqmem : (⟨6,q⟩ : AnySignature ℂ) ∈ family) (c : ℂ) (hc : c ≠ 0)
    (hq : q = fun x => c * Signature.coordinateAction (fun _ => walshKernel) (paired d.h) x) :
    ∃ N : Network ℂ 4, ∃ s : ℂ,
      s ≠ 0 ∧ N.denote = (fun x => s * even4 x) ∧
      N.shape.vertices ≤ 7 ∧ N.shape.edges ≤ 9 ∧
      Fintype.card {v : Fin N.shape.vertices // N.shape.arity v = 6} = 2 ∧
      (∀ v, N.shape.arity v = 6 → HEq (N.vertex v) q) ∧
      (∀ v, (⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ) ∈ family) ∧
      (∀ e, N.edge e = Signature.disequality) := by
  have hs : physicalScale d B c * (2 * d.coefficient) ≠ 0 :=
    mul_ne_zero (physicalScale_ne_zero d B c hc)
      (mul_ne_zero (by norm_num) d.coefficient_ne_zero)
  have hu := physicalNetwork_uses d B q hqmem
  rcases d.sigma_sign with hσ | hσ
  · refine ⟨(physicalNetwork d B q).toNetwork,physicalScale d B c * (2 * d.coefficient),
      hs,?_,?_,?_,?_,?_,uses_toNetwork _ _ hu,?_⟩
    · rw [FiniteNetwork.denote_toNetwork,physicalNetwork_denote d B q c hq,
        exceptional_reconstruction_even d hσ]
      funext x
      ring
    · rw [physicalNetwork_vertices]
      omega
    · rw [physicalNetwork_edges]
      omega
    · exact (two_copies_toNetwork _ q (physicalNetwork_two_copies d B q)).1
    · exact (two_copies_toNetwork _ q (physicalNetwork_two_copies d B q)).2
    · intro e
      rfl
  · let N := ExceptionalDressing.attachI (physicalNetwork d B q) (B.scale false)
    have hN : ∀ v, (⟨N.arity v,N.vertex v⟩ : AnySignature ℂ) ∈ family := by
      rintro (v|u)
      · exact hu v
      · exact B.available false
    refine ⟨N.toNetwork,B.scale false * (physicalScale d B c * (2 * d.coefficient)),
      mul_ne_zero (B.nonzero false) hs,?_,?_,?_,?_,?_,uses_toNetwork _ _ hN,?_⟩
    · rw [FiniteNetwork.denote_toNetwork]
      change (ExceptionalDressing.attachI (physicalNetwork d B q) (B.scale false)).denote = _
      rw [ExceptionalDressing.denote_attachI,physicalNetwork_denote d B q c hq,
        exceptional_reconstruction_odd d hσ]
      funext x
      dsimp only
      rw [flipFirst_twice]
      ring
    · change (ExceptionalDressing.attachI _ _).toNetwork.shape.vertices ≤ 7
      rw [ExceptionalDressing.vertex_count]
      norm_num
    · change (ExceptionalDressing.attachI _ _).toNetwork.shape.edges ≤ 9
      rw [ExceptionalDressing.edge_count]
      norm_num
    · exact (two_copies_toNetwork _ q (dressedNetwork_two_copies d B q (B.scale false))).1
    · exact (two_copies_toNetwork _ q (dressedNetwork_two_copies d B q (B.scale false))).2
    · intro e
      change N.edge _ = _
      generalize (Fintype.equivFin ((Fin 4 × Bool) ⊕ Unit)).symm e = w
      cases w <;> rfl

theorem exceptional_realizes_even4 {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (q : Signature ℂ 6)
    (hqmem : (⟨6,q⟩ : AnySignature ℂ) ∈ family) (c : ℂ) (hc : c ≠ 0)
    (hq : q = fun x => c * Signature.coordinateAction (fun _ => walshKernel) (paired d.h) x) :
    Gadget.RealizesUpTo family .disequality even4 := by
  obtain ⟨N,s,hs,hden,_,_,_,_,hv,he⟩ := exceptional_two_copy_even4 d B q hqmem c hc hq
  refine ⟨s,hs,?_⟩
  rw [← hden]
  exact Gadget.realizes_network N family .disequality hv he

end Holant.ReedMuller.WeightTwoIntegration
