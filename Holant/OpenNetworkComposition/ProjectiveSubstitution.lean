import Holant.OpenNetworkComposition.ProjectiveSubstitutionPorts
import Holant.NetworkGluing.Finite

/-! Substitution of arbitrary actual open gadgets into an ordinary native-X
macro network. Actual free stubs are allowed. The result is projective because
closing a wire-only circle contributes its proved nonzero factor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.OpenNetworkComposition.ProjectiveSubstitution
open Holant.Certificates.MatchingContractionClosure
universe u v w z
variable {K : Type u} [Field K]

/-- Simultaneous closure of the actual disjoint original port pairs. -/
theorem Actual.closeCollection {P : Type v} [Fintype P] [DecidableEq P]
    {Q : Type w} {E : Type z} [Fintype E] [DecidableEq E]
    {family : SignatureFamily K} {f : Tensor K P} (hf : Actual family f)
    (p : CollectionPorts P Q E) (htwo : (2:K)≠0) :
    Actual family (contractCollection p (fun _ => Signature.disequality) f) := by
  classical
  have aux : ∀ k : ℕ, ∀ (E : Type z) [Fintype E] [DecidableEq E], Fintype.card E=k →
      ∀ (P : Type v) [Fintype P] [DecidableEq P] (Q : Type w),
      ∀ p : CollectionPorts P Q E, ∀ f : Tensor K P,
      Actual family f → Actual family (contractCollection p (fun _ => Signature.disequality) f) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro E _ _ hk P _ _ Q p f hf
      rcases isEmpty_or_nonempty E with hE | hE
      · let : IsEmpty E := hE
        rw [contractCollection_empty]
        exact hf.reindex (emptyBoundary p).symm
      · obtain ⟨e⟩ := hE
        rw [contractCollection_step p (fun _ => Signature.disequality) f e]
        have hl : Fintype.card (OtherEdges e)<k := by rw [←hk]; exact otherEdges_card_lt e
        exact ih _ hl (OtherEdges e) rfl _ Q (collectionTailPorts p e) _
          (hf.contractPair _ _ (collection_pair_distinct p e) htwo)
  exact aux _ E rfl P Q p f hf

/-- A pair of endpoint bits and a function on endpoint occurrences carry the
same complete assignment data, including loop and parallel-edge occurrences. -/
def endpointAssignments (E : Type*) : (E → Bool × Bool) ≃ ((E × Bool) → Bool) where
  toFun y q := if q.2 then (y q.1).2 else (y q.1).1
  invFun z e := (z (e,false),z (e,true))
  left_inv y := by funext e; rfl
  right_inv z := by funext q; rcases q with ⟨e,b⟩; cases b <;> rfl

/-- The simultaneous original-port contraction is the ordinary macro's exact
finite sum, with the vertex product and every original native edge retained. -/
theorem network_eq_collection {n : ℕ} (N : Network K n)
    (he : ∀ e,N.edge e=Signature.disequality) :
    N.denote=contractCollection N.shape.ports.symm (fun _ => Signature.disequality)
      (fun x : (Σ v,Fin (N.shape.arity v)) → Bool => ∏ v,N.vertex v (fun i => x ⟨v,i⟩)) := by
  classical
  funext x
  unfold Network.denote contractCollection
  symm
  apply Fintype.sum_equiv (endpointAssignments (Fin N.shape.edges))
  intro y
  have ha (v : Fin N.shape.vertices) :
      (fun i => collectionAssignment N.shape.ports.symm x y ⟨v,i⟩)=
        N.shape.assignment x (endpointAssignments (Fin N.shape.edges) y) v := by
    funext i
    unfold collectionAssignment NetworkShape.assignment
    simp only [Equiv.symm_symm]
    cases N.shape.ports ⟨v,i⟩ with
    | inl j => rfl
    | inr e => rfl
  simp only [ha,he,kernelProduct,endpointAssignments]
  exact mul_comm _ _

end Holant.OpenNetworkComposition.ProjectiveSubstitution

namespace Holant.OpenNetworkComposition
variable {K : Type*} [Field K] {n : ℕ}

/-- Substitute arbitrary actual gadgets into an ordinary finite native-X macro.
All original realization multipliers and every deleted wire-circle multiplier
are composed by the actual tensor and contraction theorems. No exact arbitrary
self-gluing theorem or additional scalar resource is assumed. -/
theorem realizesUpTo_network (family : SignatureFamily K) (N : Network K n)
    (hv : ∀ v,Gadget.RealizesUpTo family .disequality (N.vertex v))
    (he : ∀ e,N.edge e=Signature.disequality) (htwo : (2:K)≠0) :
    Gadget.RealizesUpTo family .disequality N.denote := by
  rw [ProjectiveSubstitution.network_eq_collection N he]
  exact ((ProjectiveSubstitution.Actual.vertexProduct family N.shape.vertices
    N.shape.arity N.vertex hv).closeCollection N.shape.ports.symm htwo).realizesUpTo

/-- Exact actual vertex realizations are valid inputs; the macro output still
records the possible nonzero wire-circle correction projectively. -/
theorem realizes_network_upTo (family : SignatureFamily K) (N : Network K n)
    (hv : ∀ v,Gadget.Realizes family .disequality (N.vertex v))
    (he : ∀ e,N.edge e=Signature.disequality) (htwo : (2:K)≠0) :
    Gadget.RealizesUpTo family .disequality N.denote := by
  apply realizesUpTo_network family N _ he htwo
  intro v
  exact ⟨1,one_ne_zero,by simpa using hv v⟩

/-- The same substitution result before enumerating finite vertex/edge sets. -/
theorem realizesUpTo_finiteNetwork {V E : Type*} [Fintype V] [Fintype E]
    (family : SignatureFamily K) (N : Holant.FiniteNetwork K V E n)
    (hv : ∀ v,Gadget.RealizesUpTo family .disequality (N.vertex v))
    (he : ∀ e,N.edge e=Signature.disequality) (htwo : (2:K)≠0) :
    Gadget.RealizesUpTo family .disequality N.denote := by
  rw [←Holant.FiniteNetwork.denote_toNetwork]
  exact realizesUpTo_network family N.toNetwork
    (fun v => hv ((Fintype.equivFin V).symm v))
    (fun e => he ((Fintype.equivFin E).symm e)) htwo

theorem realizes_finiteNetwork_upTo {V E : Type*} [Fintype V] [Fintype E]
    (family : SignatureFamily K) (N : Holant.FiniteNetwork K V E n)
    (hv : ∀ v,Gadget.Realizes family .disequality (N.vertex v))
    (he : ∀ e,N.edge e=Signature.disequality) (htwo : (2:K)≠0) :
    Gadget.RealizesUpTo family .disequality N.denote := by
  apply realizesUpTo_finiteNetwork family N _ he htwo
  intro v
  exact ⟨1,one_ne_zero,by simpa using hv v⟩

end Holant.OpenNetworkComposition
