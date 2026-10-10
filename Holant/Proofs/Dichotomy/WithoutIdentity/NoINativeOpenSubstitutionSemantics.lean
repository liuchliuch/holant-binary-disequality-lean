import Holant.NetworkGluing.Finite
import Holant.Complexity.ClosedNetworkSemantics
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! Exact physical substitution for arbitrary-boundary networks. Every copy of a
fixed gadget has its own vertex and internal-edge occurrences; original edges
retain their original orientation and may be loops or parallel edges. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoINativeOpenSubstitutionSemantics
open scoped BigOperators
variable {K : Type*} [CommSemiring K]
variable {m : ℕ}
variable (N : Network K m) (G : (v : Fin N.shape.vertices) → Network K (N.shape.arity v))

abbrev Vertices := Σv : Fin N.shape.vertices, Fin (G v).shape.vertices
abbrev InternalEdges := Σv : Fin N.shape.vertices, Fin (G v).shape.edges
abbrev Edges := Fin N.shape.edges ⊕ InternalEdges N G

/-- Explicit wiring retains every outer boundary port. -/
def ports : (Σv : Vertices N G, Fin ((G v.1).shape.arity v.2)) ≃
    (Fin m ⊕ (Edges N G × Bool)) :=
  (Equiv.sigmaAssoc (fun v i => Fin ((G v).shape.arity i))) |>.trans
    ((Equiv.sigmaCongrRight fun v => (G v).shape.ports).trans
      ((Equiv.sigmaSumDistrib (fun v => Fin (N.shape.arity v))
        (fun v => Fin (G v).shape.edges × Bool)).trans
        ((Equiv.sumCongr N.shape.ports
          (Equiv.sigmaProdDistrib (fun v => Fin (G v).shape.edges) Bool).symm).trans
          ((Equiv.sumAssoc (Fin m) (Fin N.shape.edges × Bool)
            (InternalEdges N G × Bool)).trans
            (Equiv.sumCongr (Equiv.refl _)
              (Equiv.sumProdDistrib (Fin N.shape.edges) (InternalEdges N G) Bool).symm)))))

/-- Literal substitution as an ordinary finite network; no scalar vertex is added. -/
def network : Holant.FiniteNetwork K (Vertices N G) (Edges N G) m where
  arity v := (G v.1).shape.arity v.2
  ports := ports N G
  vertex v := (G v.1).vertex v.2
  edge := Sum.elim N.edge (fun e => (G e.1).edge e.2)

/-- All old and all per-copy internal assignments are independent. -/
def assignmentEquiv : ((Edges N G × Bool) → Bool) ≃
    (((Fin N.shape.edges × Bool) → Bool) ×
      ((v : Fin N.shape.vertices) → (Fin (G v).shape.edges × Bool) → Bool)) where
  toFun z := (fun q => z (.inl q.1,q.2), fun v q => z (.inr ⟨v,q.1⟩,q.2))
  invFun z q := match q.1 with
    | .inl e => z.1 (e,q.2)
    | .inr e => z.2 e.1 (e.2,q.2)
  left_inv z := by funext q; rcases q with ⟨e,b⟩; cases e <;> rfl
  right_inv z := by rcases z with ⟨a,b⟩; rfl

 theorem vertex_assignment (x : Fin m → Bool) (z : (Edges N G × Bool) → Bool) (v : Fin N.shape.vertices)
    (i : Fin (G v).shape.vertices) :
    (fun j => Sum.elim x z ((network N G).ports ⟨⟨v,i⟩,j⟩)) =
      (G v).shape.assignment
        (N.shape.assignment x ((assignmentEquiv N G z).1) v)
        ((assignmentEquiv N G z).2 v) i := by
  funext j
  dsimp [network,ports,NetworkShape.assignment]
  cases h : (G v).shape.ports ⟨i,j⟩ with
  | inr e =>
    simp [Equiv.sigmaAssoc,Equiv.sigmaSumDistrib,Equiv.sigmaProdDistrib,
      Equiv.sumProdDistrib,assignmentEquiv,h,Equiv.sumAssoc]
  | inl p =>
    cases hN : N.shape.ports ⟨v,p⟩ with
    | inl q =>
      simp [Equiv.sigmaAssoc,Equiv.sigmaSumDistrib,Equiv.sigmaProdDistrib,
        Equiv.sumAssoc,Equiv.sumProdDistrib,assignmentEquiv,h,hN,NetworkShape.assignment]
    | inr e =>
      simp [Equiv.sigmaAssoc,Equiv.sigmaSumDistrib,Equiv.sigmaProdDistrib,
        Equiv.sumProdDistrib,assignmentEquiv,h,hN,Equiv.sumAssoc,
        NetworkShape.assignment,Prod.map]

/-- The exact factorization of one physical assignment into old and local edges. -/
 theorem weight (x : Fin m → Bool) (z : (Edges N G × Bool) → Bool) :
    (∏ v : Vertices N G, (network N G).vertex v
      (fun j => Sum.elim x z ((network N G).ports ⟨v,j⟩))) *
      (∏ e : Edges N G, (network N G).edge e (z (e,false)) (z (e,true))) =
    (∏ v, ((∏ i, (G v).vertex i ((G v).shape.assignment
      (N.shape.assignment x ((assignmentEquiv N G z).1) v)
        ((assignmentEquiv N G z).2 v) i)) *
      ∏ e, (G v).edge e (((assignmentEquiv N G z).2 v) (e,false))
        (((assignmentEquiv N G z).2 v) (e,true)))) *
      ∏ e, N.edge e (((assignmentEquiv N G z).1) (e,false))
        (((assignmentEquiv N G z).1) (e,true)) := by
  simp only [Fintype.prod_sigma,vertex_assignment,Fintype.prod_sum_type,
    Finset.prod_mul_distrib]
  dsimp [network,assignmentEquiv]
  ring

/-- Actual finite partition-function substitution, before choosing an encoding. -/
 theorem denote (x : Fin m → Bool) : (network N G).denote x =
    (Network.mk N.shape (fun v => (G v).denote) N.edge).denote x := by
  classical
  letI : DecidableEq (Edges N G) := Classical.decEq _
  unfold Holant.FiniteNetwork.denote
  simp_rw [weight N G x]
  let W := fun z : (((Fin N.shape.edges × Bool) → Bool) ×
      ((v : Fin N.shape.vertices) → (Fin (G v).shape.edges × Bool) → Bool)) =>
    (∏ v, ((∏ i, (G v).vertex i ((G v).shape.assignment
      (N.shape.assignment x z.1 v) (z.2 v) i)) *
      ∏ e, (G v).edge e (z.2 v (e,false)) (z.2 v (e,true)))) *
      ∏ e, N.edge e (z.1 (e,false)) (z.1 (e,true))
  change (∑ z, W (assignmentEquiv N G z)) = _
  rw [(assignmentEquiv N G).sum_comp W]
  simp only [Fintype.sum_prod_type]
  change (∑ old, ∑ inner, W (old,inner)) = _
  unfold Network.denote
  apply Finset.sum_congr rfl
  intro old _
  dsimp [W]
  rw [← Finset.sum_mul]
  congr 1
  exact (Fintype.prod_sum (fun v z =>
    (∏ i, (G v).vertex i ((G v).shape.assignment
      (N.shape.assignment x old v) z i)) *
      ∏ e, (G v).edge e (z (e,false)) (z (e,true)))).symm

/-- Every projective normalization is retained multiplicatively. -/
 theorem denote_scaled (x : Fin m → Bool) (c : Fin N.shape.vertices → K)
    (hc : ∀ v, (G v).denote = c v • N.vertex v) :
    (network N G).denote x = (∏ v,c v) * N.denote x := by
  rw [denote]
  have hfun : (fun v => (G v).denote) = (fun v => c v • N.vertex v) := funext hc
  rw [hfun]
  change (∑ z, (∏ v, c v * N.vertex v (N.shape.assignment x z v)) *
    ∏ e, N.edge e (z (e,false)) (z (e,true))) = _
  simp_rw [Finset.prod_mul_distrib]
  unfold Network.denote
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact mul_assoc _ _ _

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoINativeOpenSubstitutionSemantics

