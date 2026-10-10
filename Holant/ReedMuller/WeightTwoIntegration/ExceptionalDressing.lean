import Holant.ReedMuller.WeightTwoIntegration.ExceptionalLinks
import Holant.ReedMuller.WeightTwoIntegration.ExceptionalReconstruction

/-! An actual one-port X action: attach a supplied scalar-I binary by one
native X edge. Its scalar, one added vertex, and one added edge are retained. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalDressing
variable {V E : Type*} [Fintype V] [Fintype E]

def attachPorts : (Fin 4 ⊕ (E × Bool)) ⊕ Fin 2 ≃
    Fin 4 ⊕ ((E ⊕ Unit) × Bool) where
  toFun
    | .inl (.inl i) => if i = 0 then .inr (.inr (),false) else .inl i
    | .inl (.inr (e,b)) => .inr (.inl e,b)
    | .inr j => if j = 0 then .inl 0 else .inr (.inr (),true)
  invFun
    | .inl i => if i = 0 then .inr 0 else .inl (.inl i)
    | .inr (.inl e,b) => .inl (.inr (e,b))
    | .inr (.inr (),false) => .inl (.inl 0)
    | .inr (.inr (),true) => .inr 1
  left_inv := by
    rintro ((i|⟨e,b⟩)|j)
    · fin_cases i <;> rfl
    · rfl
    · fin_cases j <;> rfl
  right_inv := by
    rintro (i|⟨e|u,b⟩)
    · fin_cases i <;> rfl
    · rfl
    · cases u; cases b <;> rfl

def unitPorts : (Σ _ : Unit, Fin 2) ≃ Fin 2 where
  toFun p := p.2
  invFun i := ⟨(),i⟩
  left_inv := by rintro ⟨⟨⟩,i⟩; rfl
  right_inv := by intro i; rfl

def attachI (N : FiniteNetwork ℂ V E 4) (c : ℂ) :
    FiniteNetwork ℂ (V ⊕ Unit) (E ⊕ Unit) 4 where
  arity := fun v => match v with | .inl v => N.arity v | .inr _ => 2
  ports := (Equiv.sumSigmaDistrib (fun v : V ⊕ Unit => Fin (match v with | .inl v => N.arity v | .inr _ => 2))).trans
    ((Equiv.sumCongr N.ports unitPorts).trans attachPorts)
  vertex
    | .inl v => N.vertex v
    | .inr _ => fun x => c * Signature.equality (x (0 : Fin 2)) (x (1 : Fin 2))
  edge
    | .inl e => N.edge e
    | .inr _ => Signature.disequality

def attachAssignments : (((E ⊕ Unit) × Bool) → Bool) ≃
    ((E × Bool → Bool) × Bool × Bool) where
  toFun z := (fun p => z (.inl p.1,p.2),z (.inr (),false),z (.inr (),true))
  invFun p q := match q with
    | (.inl e,b) => p.1 (e,b)
    | (.inr (),false) => p.2.1
    | (.inr (),true) => p.2.2
  left_inv := by intro z; funext q; rcases q with ⟨e|⟨⟩,b⟩; rfl; cases b <;> rfl
  right_inv := by rintro ⟨z,a,b⟩; rfl

def replaceFirst (x : Fin 4 → Bool) (a : Bool) : Fin 4 → Bool := ![a,x 1,x 2,x 3]

theorem denote_attachI (N : FiniteNetwork ℂ V E 4) (c : ℂ) :
    (attachI N c).denote = fun x => c * N.denote (flipFirst x) := by
  classical
  let : DecidableEq (E ⊕ Unit) := Classical.decEq _
  funext x
  simp only [FiniteNetwork.denote]
  rw [← (attachAssignments (E := E)).symm.sum_comp,Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  have ha (z : E × Bool → Bool) (a b : Bool) (v : V) (i : Fin (N.arity v)) :
      Sum.elim x (attachAssignments.symm (z,a,b)) ((attachI N c).ports ⟨.inl v,i⟩) =
        Sum.elim (replaceFirst x a) z (N.ports ⟨v,i⟩) := by
    change Sum.elim x _ (attachPorts (.inl (N.ports ⟨v,i⟩))) = _
    cases hp : N.ports ⟨v,i⟩ with
    | inl j => fin_cases j <;> rfl
    | inr e => rfl
  have hv (z : E × Bool → Bool) (a b : Bool) (v : V) :
      (attachI N c).vertex (.inl v) (fun i =>
        Sum.elim x (attachAssignments.symm (z,a,b)) ((attachI N c).ports ⟨.inl v,i⟩)) =
      N.vertex v (fun i => Sum.elim (replaceFirst x a) z (N.ports ⟨v,i⟩)) := by
    exact congrArg (N.vertex v) (funext (ha z a b v))
  have hb (z : E × Bool → Bool) (a b : Bool) :
      (attachI N c).vertex (.inr ()) (fun i =>
        Sum.elim x (attachAssignments.symm (z,a,b)) ((attachI N c).ports ⟨.inr (),i⟩)) =
      c * Signature.equality (x 0) b := rfl
  simp only [Fintype.prod_sum_type,Fintype.prod_unique,hv,hb]
  change (∑ z : E × Bool → Bool, ∑ a : Bool, ∑ b : Bool,
    ((∏ v, N.vertex v (fun i => Sum.elim (replaceFirst x a) z (N.ports ⟨v,i⟩))) *
      (c * Signature.equality (x 0) b)) *
      ((∏ e, N.edge e (z (e,false)) (z (e,true))) * Signature.disequality a b)) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  cases h0 : x 0 <;>
    simp [Signature.equality,Signature.disequality,replaceFirst,flipFirst,h0] <;> ring

theorem vertex_count (N : FiniteNetwork ℂ V E 4) (c : ℂ) :
    (attachI N c).toNetwork.shape.vertices = Fintype.card V + 1 := by
  simp [FiniteNetwork.toNetwork]

theorem edge_count (N : FiniteNetwork ℂ V E 4) (c : ℂ) :
    (attachI N c).toNetwork.shape.edges = Fintype.card E + 1 := by
  simp [FiniteNetwork.toNetwork]

theorem realizes_attachI (N : FiniteNetwork ℂ V E 4) (c : ℂ)
    (family : SignatureFamily ℂ)
    (hv : ∀ v, (⟨N.arity v,N.vertex v⟩ : AnySignature ℂ) ∈ family)
    (he : ∀ e, N.edge e = Signature.disequality)
    (hc : (⟨2,fun x => c * Signature.equality (x (0 : Fin 2)) (x (1 : Fin 2))⟩ : AnySignature ℂ) ∈ family) :
    Gadget.Realizes family .disequality (attachI N c).denote := by
  rw [← FiniteNetwork.denote_toNetwork]
  apply Gadget.realizes_network
  · intro v
    change (⟨(attachI N c).arity _,(attachI N c).vertex _⟩ : AnySignature ℂ) ∈ family
    generalize (Fintype.equivFin (V ⊕ Unit)).symm v = w
    cases w with
    | inl v => exact hv v
    | inr u => exact hc
  · intro e
    change (attachI N c).edge _ = _
    generalize (Fintype.equivFin (E ⊕ Unit)).symm e = w
    cases w with
    | inl e => exact he e
    | inr u => rfl

end ExceptionalDressing
end Holant.ReedMuller.WeightTwoIntegration
