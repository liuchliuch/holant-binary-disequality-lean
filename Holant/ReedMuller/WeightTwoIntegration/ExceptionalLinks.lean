import Holant.ReedMuller.WeightTwoIntegration.ExceptionalTransport
import Holant.NetworkAsGadget

/-! Subdivide every link into a real binary vertex between two native X edges.
The construction records every occurrence and the exact count of vertices. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalLinks
variable {V E : Type*} [Fintype V] [Fintype E] {n : ℕ}

def binaryPort : Fin 2 ≃ Bool where
  toFun i := decide (i = 1)
  invFun b := if b then 1 else 0
  left_inv := by decide
  right_inv := by decide

abbrev subdividedArity (N : FiniteNetwork ℂ V E n) : V ⊕ E → ℕ :=
  fun v => match v with | .inl v => N.arity v | .inr _ => 2

def splitPorts : (Fin n ⊕ (E × Bool)) ⊕ (E × Bool) ≃
    Fin n ⊕ ((E × Bool) × Bool) where
  toFun
    | .inl (.inl i) => .inl i
    | .inl (.inr e) => .inr (e,false)
    | .inr e => .inr (e,true)
  invFun
    | .inl i => .inl (.inl i)
    | .inr (e,false) => .inl (.inr e)
    | .inr (e,true) => .inr e
  left_inv := by rintro ((i|e)|e) <;> rfl
  right_inv := by rintro (i|⟨e,b⟩); rfl; cases b <;> rfl

def binaryPorts : (Σ _ : E, Fin 2) ≃ E × Bool where
  toFun p := (p.1,binaryPort p.2)
  invFun p := ⟨p.1,binaryPort.symm p.2⟩
  left_inv := by rintro ⟨e,i⟩; simp
  right_inv := by rintro ⟨e,b⟩; simp

def subdivide (N : FiniteNetwork ℂ V E n) (C : E → Kernel ℂ) :
    FiniteNetwork ℂ (V ⊕ E) (E × Bool) n where
  arity := subdividedArity N
  ports := (Equiv.sumSigmaDistrib (fun v => Fin (subdividedArity N v))).trans
    ((Equiv.sumCongr N.ports binaryPorts).trans splitPorts)
  vertex
    | .inl v => N.vertex v
    | .inr e => fun x => C e (x (0 : Fin 2)) (x (1 : Fin 2))
  edge := fun _ => Signature.disequality

def splitAssignments : (((E × Bool) × Bool) → Bool) ≃
    ((E × Bool → Bool) × (E × Bool → Bool)) where
  toFun z := (fun e => z (e,false),fun e => z (e,true))
  invFun p q := if q.2 then p.2 q.1 else p.1 q.1
  left_inv := by intro z; funext q; rcases q with ⟨e,b⟩; cases b <;> rfl
  right_inv := by rintro ⟨z,t⟩; rfl

theorem sum_binary_links [DecidableEq (E × Bool)] (C : E → Kernel ℂ) (z : E × Bool → Bool) :
    (∑ t : E × Bool → Bool,
      (∏ e, C e (t (e,false)) (t (e,true))) *
        ∏ e : E × Bool, Signature.disequality (z e) (t e)) =
      ∏ e, Kernel.mul (Kernel.mul Signature.disequality (C e))
        Signature.disequality (z (e,false)) (z (e,true)) := by
  simp only [Fintype.prod_prod_type,Fintype.prod_bool]
  simp_rw [← Finset.prod_mul_distrib]
  rw [ExceptionalTransport.sum_halfEdge_products (fun e a b =>
    C e a b * (Signature.disequality (z (e,true)) b * Signature.disequality (z (e,false)) a))]
  apply Finset.prod_congr rfl
  intro e _
  cases z (e,false) <;> cases z (e,true) <;>
    simp [Kernel.mul,Signature.disequality]

/-- Exact contraction of real binary vertices with their two native-X attachments. -/
theorem denote_subdivide (N : FiniteNetwork ℂ V E n) (C : E → Kernel ℂ) :
    (subdivide N C).denote =
      ({ N with edge := fun e => Kernel.mul (Kernel.mul Signature.disequality (C e)) Signature.disequality }).denote := by
  classical
  let : DecidableEq (E × Bool) := Classical.decEq _
  funext x
  simp only [FiniteNetwork.denote]
  rw [← (splitAssignments (E := E)).symm.sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr (by ext; simp)
  intro z _
  have ha (t : E × Bool → Bool) (v : V) (i : Fin (N.arity v)) :
      Sum.elim x (splitAssignments.symm (z,t)) ((subdivide N C).ports ⟨.inl v,i⟩) =
        Sum.elim x z (N.ports ⟨v,i⟩) := by
    change Sum.elim x _ (splitPorts (.inl (N.ports ⟨v,i⟩))) = _
    cases N.ports ⟨v,i⟩ <;> rfl
  have hv (t : E × Bool → Bool) (v : V) :
      (subdivide N C).vertex (.inl v) (fun i =>
        Sum.elim x (splitAssignments.symm (z,t)) ((subdivide N C).ports ⟨.inl v,i⟩)) =
      N.vertex v (fun i => Sum.elim x z (N.ports ⟨v,i⟩)) := by
    exact congrArg (N.vertex v) (funext (ha t v))
  have hb (t : E × Bool → Bool) (e : E) :
      (subdivide N C).vertex (.inr e) (fun i =>
        Sum.elim x (splitAssignments.symm (z,t)) ((subdivide N C).ports ⟨.inr e,i⟩)) =
      C e (t (e,false)) (t (e,true)) := rfl
  simp only [Fintype.prod_sum_type,hv,hb]
  change (∑ t : E × Bool → Bool,
      ((∏ v, N.vertex v (fun i => Sum.elim x z (N.ports ⟨v,i⟩))) *
        ∏ e, C e (t (e,false)) (t (e,true))) *
          ∏ e : E × Bool, Signature.disequality (z e) (t e)) = _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum,sum_binary_links C z]

theorem vertex_count (N : FiniteNetwork ℂ V E n) (C : E → Kernel ℂ) :
    (subdivide N C).toNetwork.shape.vertices = Fintype.card V + Fintype.card E := by
  simp [FiniteNetwork.toNetwork]

theorem edge_count (N : FiniteNetwork ℂ V E n) (C : E → Kernel ℂ) :
    (subdivide N C).toNetwork.shape.edges = 2 * Fintype.card E := by
  simp [FiniteNetwork.toNetwork,Nat.mul_comm]

theorem realizes_subdivide (N : FiniteNetwork ℂ V E n) (C : E → Kernel ℂ)
    (family : SignatureFamily ℂ)
    (hv : ∀ v, (⟨N.arity v,N.vertex v⟩ : AnySignature ℂ) ∈ family)
    (hC : ∀ e, (⟨2,fun x => C e (x (0 : Fin 2)) (x (1 : Fin 2))⟩ : AnySignature ℂ) ∈ family) :
    Gadget.Realizes family .disequality (subdivide N C).denote := by
  rw [← FiniteNetwork.denote_toNetwork]
  apply Gadget.realizes_network
  · intro v
    change (⟨(subdivide N C).arity _,(subdivide N C).vertex _⟩ : AnySignature ℂ) ∈ family
    generalize (Fintype.equivFin (V ⊕ E)).symm v = w
    cases w with
    | inl v => exact hv v
    | inr e => exact hC e
  · intro e
    rfl

end ExceptionalLinks
end Holant.ReedMuller.WeightTwoIntegration
