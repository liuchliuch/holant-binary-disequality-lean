import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralExposeEdgeGraph

/-! Exact conditioned-partition semantics of the exposed Eq4 edge. Equality
at the two new ports is enforced physically, and the retained edge bit is
conditioned to their common value without any multiplicative correction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralExposeEdgeValue
open Holant Holant.Complexity Holant.Tractable
open OrdinaryNegativeCubicGadgets
open scoped BigOperators
namespace P
export NoXGeneralExposeEdgeGraph (Vertices Edges arity ports finite graph old_route new_route)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

section General
variable {K V E : Type} [CommSemiring K] [Fintype V] [Fintype E] [DecidableEq E] {n : ℕ}
theorem ordinary (N : FiniteNetwork K V E n) (native : ∀e,N.edge e=Signature.equality) (x : Fin n→Bool) :
    N.denote x=∑c : E→Bool,∏v,N.vertex v (fun i=>Sum.elim x (fun p=>c p.1) (N.ports ⟨v,i⟩)) := by
  classical
  have expand : N.denote x=∑z : (E×Bool)→Bool,
      (∏v,N.vertex v (fun i=>Sum.elim x z (N.ports ⟨v,i⟩)))*
      ∏e,N.edge e (z (e,false)) (z (e,true)) := by
    unfold FiniteNetwork.denote
    have sums {A : Type} (I J : Fintype A) (f : A→K) :
        (@Finset.univ A I).sum f=(@Finset.univ A J).sum f := by
      cases Subsingleton.elim I J
      rfl
    exact sums _ _ _
  rw [expand]
  rw [←Equiv.sum_comp (Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.EqualityTree.doubled E).symm]
  simp only [Fintype.sum_prod_type]
  simp_rw [native]
  have he (a b : E→Bool) : (∏e,Signature.equality (K:=K) (a e) (b e))=if a=b then 1 else 0 := by
    simp only [Signature.equality,Fintype.prod_boole,←funext_iff]
  simp only [Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.EqualityTree.doubled,
    Equiv.coe_fn_symm_mk,Bool.false_eq_true,ite_false,ite_true,he]
  simp
end General

variable {K : Type} [Field K] {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (N : Macro H 0)
variable (eqLabel : Fin s)
variable (eqLiteral : (⟨a eqLabel.val,H eqLabel⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (edge : Fin N.network.shape.edges)

def words : ((P.Edges H N)→Bool) ≃ ((Fin N.network.shape.edges→Bool)×Bool) where
  toFun c:=(fun e=>c (.inl e),c (.inr ()))
  invFun p:=Sum.elim p.1 (fun _=>p.2)
  left_inv c:=by funext e;cases e with | inl _=>rfl | inr u=>cases u;rfl
  right_inv _:=rfl

def oldWeight (c : Fin N.network.shape.edges→Bool) : K :=
  ∏v,N.network.vertex v (N.network.shape.assignment Fin.elim0 (fun p=>c p.1) v)

def word (c : Fin N.network.shape.edges→Bool) (b : Bool) (x : Fin 2→Bool)
    (v : Fin N.network.shape.vertices) : Fin (N.network.shape.arity v)→Bool :=
  fun i=>Sum.elim x (fun p=>Sum.elim c (fun _=>b) p.1) (P.ports H N edge ⟨.inl v,i⟩)

theorem old_word (c : Fin N.network.shape.edges→Bool) (b : Bool) (x : Fin 2→Bool) (same : b=c edge)
    (v : Fin N.network.shape.vertices) : word H N edge c b x v=
      N.network.shape.assignment Fin.elim0 (fun p=>c p.1) v := by
  funext i
  rw [word]
  erw [P.old_route H N edge ⟨v,i⟩,ClosedLabelling.closed_assignment]
  split_ifs with h
  · simp only [Sum.elim_inr]
    rw [h]
    exact same
  · rfl

theorem equality_value (x : Fin 2→Bool) (c b : Bool) :
    Holant.EightVertex.ProductAnchor.equalityFour (K:=K) ![x 0,x 1,c,b]=
      if x 0=x 1 ∧ c=x 0 ∧ b=x 0 then 1 else 0 := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases c <;> cases b <;>
    simp [Holant.EightVertex.ProductAnchor.equalityFour,Fin.forall_fin_succ]

theorem vertex_product (c : Fin N.network.shape.edges→Bool) (b : Bool) (x : Fin 2→Bool) :
    (∏v : P.Vertices H N,(P.finite H N edge).vertex v
      (fun i=>Sum.elim x (fun p=>Sum.elim c (fun _=>b) p.1) ((P.finite H N edge).ports ⟨v,i⟩)))=
      (∏v,N.network.vertex v (word H N edge c b x v))*
        (if x 0=x 1 ∧ c edge=x 0 ∧ b=x 0 then 1 else 0) := by
  rw [Fintype.prod_sum_type]
  simp only [Fintype.prod_unique]
  congr 1
  have he : (fun i=>Sum.elim x (fun p=>Sum.elim c (fun _=>b) p.1)
      ((P.finite H N edge).ports ⟨.inr (),i⟩))=![x 0,x 1,c edge,b] := by
    funext i
    change Sum.elim x (fun p=>Sum.elim c (fun _=>b) p.1) (P.ports H N edge ⟨.inr (),i⟩)=_
    erw [P.new_route]
    fin_cases i <;> rfl
  change Holant.EightVertex.ProductAnchor.equalityFour _=_
  rw [he,equality_value]

theorem value (x : Fin 2→Bool) : (P.graph H N eqLabel eqLiteral edge).network.denote x=
    if x 0=x 1 then ∑c : Fin N.network.shape.edges→Bool,
      if c edge=x 0 then oldWeight H N c else 0 else 0 := by
  classical
  rw [P.graph,FiniteNetwork.denote_toNetwork,ordinary _ (fun _=>rfl)]
  rw [←Equiv.sum_comp (words H N).symm,Fintype.sum_prod_type]
  simp only [words,Equiv.coe_fn_symm_mk]
  simp_rw [vertex_product]
  by_cases same : x 0=x 1
  · rw [ite_eq_left same]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : c edge=x 0
    · rw [ite_eq_left hc]
      have h0 : (∏v,N.network.vertex v (word H N edge c (x 0) x v))=oldWeight H N c := by
        simp_rw [old_word H N edge c (x 0) x hc.symm]
        rfl
      cases hx : x 0 <;> simp_all
    · simp [hc]
  · simp [same]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralExposeEdgeValue
end
