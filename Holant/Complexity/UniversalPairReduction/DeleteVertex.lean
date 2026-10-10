import Holant.Complexity.UniversalPairReduction.RawHole
import Holant.OpenNetworkComposition.Semantics
import Holant.Complexity.ClosedNetworkSerialize
import Mathlib.Logic.Equiv.Sum

/-! Actual open-network deletion of a binary occurrence. All original edges
remain, including an edge joining the deleted vertex to itself. Its two old
ports become the two ordered free stubs, so raw and corrected tensors remain
distinct. No equality vertex or wire-circle quotient is introduced. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Holant.Complexity.UniversalPairReduction.DeleteVertex
open OpenNetworkComposition
open scoped BigOperators
variable {K : Type*} (N : Network K 0) (v : Fin N.shape.vertices)
variable (h : N.shape.arity v=2)

abbrev Vertices := {u : Fin N.shape.vertices // u≠v}
abbrev OldPorts := Σu : Fin N.shape.vertices,Fin (N.shape.arity u)
abbrev NewPorts := Ports (Vertices N v) (Fin 2) (fun u => N.shape.arity u.val)

/-- Partition the original port set into surviving occurrences and the two
marked occurrences. This is a bijection even in the self-loop case. -/
def portEquiv : OldPorts N ≃ NewPorts N v :=
  (Equiv.sumCompl (fun p : OldPorts N => p.1=v)).symm.trans
    ((Equiv.sumCongr ((Equiv.sigmaSubtype v).trans (finCongr h))
      (Equiv.subtypeSigmaEquiv (fun u => Fin (N.shape.arity u)) (fun u => u≠v))).trans
      (Equiv.sumComm _ _))

theorem port_marked (j : Fin 2) :
    portEquiv N v h ⟨v,Fin.cast h.symm j⟩ = .inr j := by
  simp [portEquiv,Equiv.sumCompl,Equiv.sigmaSubtype]

theorem port_other (u : Vertices N v) (i : Fin (N.shape.arity u.val)) :
    portEquiv N v h ⟨u.val,i⟩ = .inl ⟨u,i⟩ := by
  simp [portEquiv,Equiv.sumCompl,u.property,Equiv.subtypeSigmaEquiv]

abbrev endsEquiv : (Fin N.shape.edges × Bool) ≃ NewPorts N v :=
  (ClosedLabelling.closedPortEquiv N.shape).symm.trans (portEquiv N v h)

/-- The full remaining network with two ordered paired free boundary stubs. -/
def network : OpenNetworkComposition.FiniteNetwork K (Vertices N v) (Fin 2)
    (Fin N.shape.edges) 2 where
  shape := {
    arity u := N.shape.arity u.val
    boundary := ⟨Sum.inr,Sum.inr_injective⟩
    ends := (endsEquiv N v h).toEmbedding
    ordinary_boundary_iff_unpaired := by
      intro p
      constructor
      · rintro ⟨j,hj⟩
        cases hj
      · intro hn
        exact False.elim (hn ⟨(endsEquiv N v h).symm (.inl p),
          (endsEquiv N v h).apply_symm_apply _⟩)
    freeBoundary := id
    free_boundary _ := rfl
    freeEdge j := (endsEquiv N v h).symm (.inr j)
    free_paired j := (endsEquiv N v h).apply_symm_apply _ }
  vertex u := N.vertex u.val
  edge _ := .disequality

/-- Retained vertices have exactly their original labels and arities. -/
theorem uses (family : SignatureFamily K)
    (hv : ∀u,u≠v → (⟨N.shape.arity u,N.vertex u⟩ : AnySignature K)∈family)
    (u : Vertices N v) :
    (⟨(network N v h).shape.arity u,(network N v h).vertex u⟩ : AnySignature K)∈family :=
  hv u.val u.property

variable [CommSemiring K]

theorem assigned_port (z : NewPorts N v → Bool) (u : Fin N.shape.vertices)
    (i : Fin (N.shape.arity u)) :
    N.shape.assignment Fin.elim0 (fun e => z (endsEquiv N v h e)) u i =
      z (portEquiv N v h ⟨u,i⟩) := by
  unfold NetworkShape.assignment
  cases hp : N.shape.ports ⟨u,i⟩ with
  | inl j => exact Fin.elim0 j
  | inr e =>
    have he : ClosedLabelling.closedPortEquiv N.shape ⟨u,i⟩=e := by
      simp [ClosedLabelling.closedPortEquiv,hp,RawClosedNetwork.closedEndsEquiv]
    change z (endsEquiv N v h e)=_
    rw [←he]
    simp [endsEquiv]

/-- Every assignment on the deleted open network still sees the original
edge factors exactly once; the erased vertex is its only omitted factor. -/
theorem weight_eq (he : ∀e,N.edge e=Signature.disequality) (z : NewPorts N v → Bool) :
    (network N v h).weight z = holeWeight N v (fun e => z (endsEquiv N v h e)) := by
  unfold OpenNetworkComposition.FiniteNetwork.weight holeWeight
  apply congrArg₂ (·*·)
  · change (∏u : Vertices N v,N.vertex u.val (fun i => z (.inl ⟨u,i⟩))) =
      ∏u ∈ Finset.univ.erase v,N.vertex u
        (N.shape.assignment Fin.elim0 (fun e => z (endsEquiv N v h e)) u)
    rw [Finset.prod_subtype (p:=fun u => u≠v) (Finset.univ.erase v) (by simp)]
    apply Finset.prod_congr rfl
    intro u _
    congr 1
    funext i
    rw [assigned_port,port_other]
  · apply Finset.prod_congr rfl
    intro e _
    simp [network,he,EdgeKind.value]

def assignments : (NewPorts N v → Bool) ≃ ((Fin N.shape.edges × Bool) → Bool) where
  toFun z e := z (endsEquiv N v h e)
  invFun z p := z ((endsEquiv N v h).symm p)
  left_inv z := by funext p; simp
  right_inv z := by funext e; simp

private theorem sum_instances {A : Type*} (I J : Fintype A) (f g : A → K)
    (heq : ∀a,f a=g a) :
    (@Finset.univ A I).sum f=(@Finset.univ A J).sum g := by
  have hij : I=J := Subsingleton.elim _ _
  cases hij
  exact Finset.sum_congr rfl (fun a _ => heq a)

/-- Exact raw boundary table, before the manuscript's X correction. -/
theorem raw_eq (he : ∀e,N.edge e=Signature.disequality) (x : Fin 2 → Bool) :
    (network N v h).raw x = rawHole N v (fun i => x (Fin.cast h i)) := by
  classical
  unfold rawHole
  rw [←(assignments N v h).sum_comp]
  unfold OpenNetworkComposition.FiniteNetwork.raw
  apply sum_instances
  intro z
  change (if ∀j,z (.inr j)=x j then (network N v h).weight z else 0) =
    if N.shape.assignment Fin.elim0 (fun e => z (endsEquiv N v h e)) v =
      (fun i => x (Fin.cast h i)) then holeWeight N v (fun e => z (endsEquiv N v h e)) else 0
  rw [weight_eq N v h he]
  congr 1
  apply propext
  change (∀j,z (.inr j)=x j) ↔ _
  constructor
  · intro hz
    funext i
    rw [assigned_port]
    have hi : i=Fin.cast h.symm (Fin.cast h i) := by simp
    rw [hi,port_marked]
    exact hz _
  · intro hz j
    have hj := congrFun hz (Fin.cast h.symm j)
    rw [assigned_port,port_marked] at hj
    simpa using hj

/-- Native-X correction complements the two free-stub coordinates. -/
theorem tensor_eq (he : ∀e,N.edge e=Signature.disequality) (x : Fin 2 → Bool) :
    (network N v h).tensor x = rawHole N v (fun i => !(x (Fin.cast h i))) := by
  have hk : (network N v h).boundaryKernel = fun _ => (Signature.disequality : Kernel K) := rfl
  unfold OpenNetworkComposition.FiniteNetwork.tensor
  rw [hk]
  unfold Signature.coordinateAction
  have hp (y : Fin 2 → Bool) :
      (∏ j,Signature.disequality (K:=K) (x j) (y j)) =
        if (fun j => !(x j))=y then 1 else 0 := by
    convert Signature.prod_equality (K:=K) (fun j => !(x j)) y using 1
    apply Finset.prod_congr rfl
    intro j _
    cases x j <;> cases y j <;> rfl
  simp only [hp]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  exact raw_eq N v h he (fun j => !(x j))

/-- The corrected boundary tensor is an actual original-family binary. -/
theorem realizes (family : SignatureFamily K)
    (hv : ∀u,u≠v → (⟨N.shape.arity u,N.vertex u⟩ : AnySignature K)∈family) :
    Gadget.Realizes family .disequality (network N v h).tensor :=
  OpenNetworkComposition.FiniteNetwork.realizes (network N v h) family .disequality
    (uses N v h family hv) (fun _ => rfl)

/-- In the all-symmetric branch, the actual corrected deleted network supplies
precisely the witness needed to deduce symmetry of the raw table. This covers
a marked self-loop without representing its later closure as a gadget. -/
theorem raw_symmetric (family : SignatureFamily K)
    (hv : ∀u,u≠v → (⟨N.shape.arity u,N.vertex u⟩ : AnySignature K)∈family)
    (he : ∀e,N.edge e=Signature.disequality)
    (hs : ∀f : Signature K 2,Gadget.Realizes family .disequality f →
      f ![false,true]=f ![true,false]) :
    (binaryRaw N v h).Symmetric := by
  have hh := hs (network N v h).tensor (realizes N v h family hv)
  rw [tensor_eq N v h he,tensor_eq N v h he] at hh
  have hf (a b : Bool) : (fun i => !((![a,b] : Fin 2 → Bool) (Fin.cast h i))) =
      (fun i => (![!a,!b] : Fin 2 → Bool) (Fin.cast h i)) := by
    funext i
    generalize Fin.cast h i=j
    fin_cases j <;> rfl
  simp only [hf,Bool.not_false,Bool.not_true] at hh
  exact hh.symm

end Holant.Complexity.UniversalPairReduction.DeleteVertex
