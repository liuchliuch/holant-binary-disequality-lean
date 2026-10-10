import Holant.NetworkGluing.Finite
import Holant.Complexity.ClosedNetworkSemantics
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! Exact edge subdivision in the original ordered-port network model. Each
old edge becomes two edges with one binary vertex between them. -/
noncomputable section
namespace Holant.Complexity.EdgeSubdivision.Finite
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [CommSemiring K]
variable (N : Network K 0)
abbrev E := Fin N.shape.edges
abbrev V := Fin N.shape.vertices ⊕ E N

def halfEnds (E : Type*) : ((E×Bool) ⊕ (E×Bool)) ≃ ((E×Bool)×Bool) where
  toFun := Sum.elim (fun q => (q,q.2)) (fun q => (q,!q.2))
  invFun q := if q.2=q.1.2 then .inl q.1 else .inr q.1
  left_inv q := by rcases q with ⟨e,b⟩|⟨e,b⟩ <;> cases b <;> rfl
  right_inv q := by rcases q with ⟨⟨e,b⟩,c⟩; cases b <;> cases c <;> rfl

def arity : V N → ℕ := Sum.elim N.shape.arity (fun _ => 2)

def ports : (Σ v : V N, Fin (arity N v)) ≃ (Fin 0 ⊕ ((E N×Bool)×Bool)) :=
  (Equiv.sumSigmaDistrib (fun v => Fin (arity N v))).trans
    ((Equiv.sumCongr
      (N.shape.ports.trans (RawClosedNetwork.closedEndsEquiv N.shape.edges).symm)
      ((Equiv.sigmaEquivProd (E N) (Fin 2)).trans
        (Equiv.prodCongr (Equiv.refl _) finTwoEquiv))).trans
      ((halfEnds (E N)).trans (Equiv.emptySum (Fin 0) _).symm))

def network (binary : E N → Bool → Bool → K) (wire : Bool → Bool → K) :
    Holant.FiniteNetwork K (V N) (E N×Bool) 0 where
  arity := arity N
  ports := ports N
  vertex := fun v => match v with
    | .inl v => N.vertex v
    | .inr e => fun x => binary e (x (0 : Fin 2)) (x (1 : Fin 2))
  edge _ := wire

def assignmentEquiv : (((E N×Bool)×Bool) → Bool) ≃
    (((E N×Bool) → Bool) × (E N → Bool×Bool)) where
  toFun z := (fun q => z (q,q.2),fun e => (z ((e,false),true),z ((e,true),false)))
  invFun z q := if q.2=q.1.2 then z.1 q.1 else
    if q.1.2 then (z.2 q.1.1).2 else (z.2 q.1.1).1
  left_inv z := by funext q; rcases q with ⟨⟨e,b⟩,c⟩; cases b <;> cases c <;> rfl
  right_inv z := by
    rcases z with ⟨a,b⟩
    apply Prod.ext
    · funext q; rcases q with ⟨e,c⟩; cases c <;> rfl
    · funext e; rfl

theorem old_assignment (z : ((E N×Bool)×Bool) → Bool)
    (v : Fin N.shape.vertices) :
    (fun i => Sum.elim Fin.elim0 z (ports N ⟨.inl v,i⟩)) =
      N.shape.assignment Fin.elim0 ((assignmentEquiv N z).1) v := by
  funext i
  cases h : N.shape.ports ⟨v,i⟩ with
  | inl q => exact Fin.elim0 q
  | inr q =>
    simp [ports,arity,Equiv.sumSigmaDistrib,RawClosedNetwork.closedEndsEquiv,
      halfEnds,Equiv.emptySum,NetworkShape.assignment,assignmentEquiv,h]

theorem new_assignment (z : ((E N×Bool)×Bool) → Bool) (e : E N) (i : Fin 2) :
    Sum.elim Fin.elim0 z (ports N ⟨.inr e,i⟩) =
      if finTwoEquiv i then ((assignmentEquiv N z).2 e).2
      else ((assignmentEquiv N z).2 e).1 := by
  fin_cases i <;>
    simp [ports,arity,Equiv.sumSigmaDistrib,Equiv.sigmaEquivProd,halfEnds,
      Equiv.emptySum,assignmentEquiv,finTwoEquiv]

theorem weight (binary : E N → Bool → Bool → K) (wire : Bool → Bool → K)
    (z : ((E N×Bool)×Bool) → Bool) :
    (∏ v : V N, (network N binary wire).vertex v
      (fun i => Sum.elim Fin.elim0 z (ports N ⟨v,i⟩))) *
      (∏ e : E N×Bool, wire (z (e,false)) (z (e,true))) =
    (∏ v, N.vertex v (N.shape.assignment Fin.elim0 ((assignmentEquiv N z).1) v)) *
      ∏ e, wire (((assignmentEquiv N z).1) (e,false)) (((assignmentEquiv N z).2 e).1) *
        binary e (((assignmentEquiv N z).2 e).1) (((assignmentEquiv N z).2 e).2) *
        wire (((assignmentEquiv N z).2 e).2) (((assignmentEquiv N z).1) (e,true)) := by
  rw [Fintype.prod_sum_type]
  simp only [network,old_assignment,new_assignment,finTwoEquiv,Fin.reduceFinMk,
    Bool.false_eq_true,if_false,if_true]
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_bool]
  simp only [Finset.prod_mul_distrib]
  dsimp [assignmentEquiv]
  ring

theorem denote (binary : E N → Bool → Bool → K) (wire : Bool → Bool → K)
    (hfuse : ∀ e a b, (∑ uv : Bool×Bool,
      wire a uv.1 * binary e uv.1 uv.2 * wire uv.2 b) = N.edge e a b) :
      (network N binary wire).denote Fin.elim0 = N.denote Fin.elim0 := by
  classical
  letI : DecidableEq (E N×Bool) := Classical.decEq _
  unfold Holant.FiniteNetwork.denote
  change (∑ z : ((E N×Bool)×Bool) → Bool,
    (∏ v : V N, (network N binary wire).vertex v
      (fun i => Sum.elim Fin.elim0 z (ports N ⟨v,i⟩))) *
      (∏ e : E N×Bool, wire (z (e,false)) (z (e,true)))) = _
  simp_rw [weight N binary wire]
  let W := fun z : (((E N×Bool) → Bool) × (E N → Bool×Bool)) =>
    (∏ v, N.vertex v (N.shape.assignment Fin.elim0 z.1 v)) *
      ∏ e, wire (z.1 (e,false)) (z.2 e).1 * binary e (z.2 e).1 (z.2 e).2 *
        wire (z.2 e).2 (z.1 (e,true))
  change (∑ z, W (assignmentEquiv N z)) = _
  rw [(assignmentEquiv N).sum_comp W]
  simp only [Fintype.sum_prod_type]
  unfold Network.denote
  apply Finset.sum_congr (by ext x; simp)
  intro old _
  dsimp [W]
  rw [←Finset.mul_sum]
  congr 1
  calc
    _ = ∏ e, ∑ uv : Bool×Bool,
        wire (old (e,false)) uv.1 * binary e uv.1 uv.2 * wire uv.2 (old (e,true)) :=
      (Fintype.prod_sum (fun e (uv : Bool×Bool) =>
        wire (old (e,false)) uv.1 * binary e uv.1 uv.2 * wire uv.2 (old (e,true)))).symm
    _ = _ := by simp_rw [hfuse]

end Holant.Complexity.EdgeSubdivision.Finite
