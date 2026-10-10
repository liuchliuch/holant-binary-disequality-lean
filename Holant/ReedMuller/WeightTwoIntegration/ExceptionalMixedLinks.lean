import Holant.ReedMuller.WeightTwoIntegration.ExceptionalOriginalPorts

/-! Native X links need no X resource vertex. Only an I link is subdivided,
using one literal I vertex and its two native-X attachments. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalMixedLinks
variable {V E : Type*} [Fintype V] [Fintype E] {n : ℕ}

abbrev XLinks (m : E → Bool) := {e : E // m e = true}
abbrev ILinks (m : E → Bool) := {e : E // m e ≠ true}
abbrev Edges (m : E → Bool) := XLinks m ⊕ (ILinks m × Bool)

abbrev arity (N : FiniteNetwork ℂ V E n) (m : E → Bool) : V ⊕ ILinks m → ℕ :=
  fun v => match v with | .inl v => N.arity v | .inr _ => 2

def splitPorts (m : E → Bool) :
    (Fin n ⊕ (E × Bool)) ⊕ (ILinks m × Bool) ≃ Fin n ⊕ (Edges m × Bool) where
  toFun
    | .inl (.inl i) => .inl i
    | .inl (.inr (e,b)) => if h : m e = true then .inr (.inl ⟨e,h⟩,b)
        else .inr (.inr (⟨e,h⟩,b),false)
    | .inr (e,b) => .inr (.inr (e,b),true)
  invFun
    | .inl i => .inl (.inl i)
    | .inr (.inl e,b) => .inl (.inr (e.val,b))
    | .inr (.inr (e,b),false) => .inl (.inr (e.val,b))
    | .inr (.inr (e,b),true) => .inr (e,b)
  left_inv := by
    rintro ((i|⟨e,b⟩)|⟨e,b⟩)
    · rfl
    · by_cases h : m e = true <;> simp [h]
    · rfl
  right_inv := by
    rintro (i|⟨e|⟨e,b⟩,a⟩)
    · rfl
    · simp [e.property]
    · cases a <;> simp [e.property]

def network (N : FiniteNetwork ℂ V E n) (m : E → Bool) :
    FiniteNetwork ℂ (V ⊕ ILinks m) (Edges m) n where
  arity := arity N m
  ports := (Equiv.sumSigmaDistrib (fun v => Fin (arity N m v))).trans
    ((Equiv.sumCongr N.ports ExceptionalLinks.binaryPorts).trans (splitPorts m))
  vertex
    | .inl v => N.vertex v
    | .inr _ => fun x => Signature.equality (x (0 : Fin 2)) (x (1 : Fin 2))
  edge := fun _ => Signature.disequality

def assignments (m : E → Bool) : (Edges m × Bool → Bool) ≃
    ((E × Bool → Bool) × (ILinks m × Bool → Bool)) where
  toFun w :=
    (fun q => if h : m q.1 = true then w (.inl ⟨q.1,h⟩,q.2)
      else w (.inr (⟨q.1,h⟩,q.2),false),
     fun q => w (.inr q,true))
  invFun p q := match q with
    | (.inl e,b) => p.1 (e.val,b)
    | (.inr (e,b),false) => p.1 (e.val,b)
    | (.inr (e,b),true) => p.2 (e,b)
  left_inv := by
    intro w
    funext q
    rcases q with ⟨e|⟨e,b⟩,a⟩
    · simp [e.property]
    · cases a <;> simp [e.property]
  right_inv := by
    rintro ⟨z,t⟩
    apply Prod.ext
    · funext q
      by_cases h : m q.1 = true <;> simp [h]
    · rfl

theorem kernel_product (m : E → Bool) (z : E × Bool → Bool) :
    (∏ e : XLinks m, Signature.disequality (z (e.val,false)) (z (e.val,true))) *
      (∏ e : ILinks m, Signature.equality (z (e.val,false)) (z (e.val,true))) =
      ∏ e, actualKernel (m e) (z (e,false)) (z (e,true)) := by
  rw [← (Equiv.sumCompl (fun e => m e = true)).prod_comp]
  rw [Fintype.prod_sum_type]
  congr 1
  · apply Finset.prod_congr rfl
    intro e _
    simp [actualKernel,e.property]
  · apply Finset.prod_congr rfl
    intro e _
    simp [actualKernel,e.property]

/-- Exact semantics, including the native X links with no intervening vertex. -/
theorem denote_network (N : FiniteNetwork ℂ V E n) (m : E → Bool) :
    (network N m).denote = ({N with edge := fun e => actualKernel (m e)}).denote := by
  classical
  let : DecidableEq (Edges m) := Classical.decEq _
  funext x
  simp only [FiniteNetwork.denote]
  rw [← (assignments m).symm.sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr (by ext; simp)
  intro z _
  have ha (t : ILinks m × Bool → Bool) (v : V) (i : Fin (N.arity v)) :
      Sum.elim x ((assignments m).symm (z,t)) ((network N m).ports ⟨.inl v,i⟩) =
      Sum.elim x z (N.ports ⟨v,i⟩) := by
    change Sum.elim x _ (splitPorts m (.inl (N.ports ⟨v,i⟩))) = _
    cases hp : N.ports ⟨v,i⟩ with
    | inl j => rfl
    | inr e => by_cases h : m e.1 = true <;> simp [splitPorts,assignments,h]
  have hv (t : ILinks m × Bool → Bool) (v : V) :
      (network N m).vertex (.inl v) (fun i =>
        Sum.elim x ((assignments m).symm (z,t)) ((network N m).ports ⟨.inl v,i⟩)) =
      N.vertex v (fun i => Sum.elim x z (N.ports ⟨v,i⟩)) :=
    congrArg (N.vertex v) (funext (ha t v))
  have hb (t : ILinks m × Bool → Bool) (e : ILinks m) :
      (network N m).vertex (.inr e) (fun i =>
        Sum.elim x ((assignments m).symm (z,t)) ((network N m).ports ⟨.inr e,i⟩)) =
      Signature.equality (t (e,false)) (t (e,true)) := rfl
  simp only [Fintype.prod_sum_type,hv,hb]
  change (∑ t : ILinks m × Bool → Bool,
    ((∏ v, N.vertex v (fun i => Sum.elim x z (N.ports ⟨v,i⟩))) *
      ∏ e : ILinks m, Signature.equality (t (e,false)) (t (e,true))) *
      ((∏ e : XLinks m, Signature.disequality (z (e.val,false)) (z (e.val,true))) *
        ∏ e : ILinks m × Bool, Signature.disequality (z (e.1.val,e.2)) (t e))) = _
  calc
    _ = (∏ v, N.vertex v (fun i => Sum.elim x z (N.ports ⟨v,i⟩))) *
        (∏ e : XLinks m, Signature.disequality (z (e.val,false)) (z (e.val,true))) *
        (∑ t : ILinks m × Bool → Bool,
          (∏ e, Signature.equality (t (e,false)) (t (e,true))) *
            ∏ e : ILinks m × Bool, Signature.disequality (z (e.1.val,e.2)) (t e)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = _ := by
      rw [ExceptionalLinks.sum_binary_links (fun _ : ILinks m => Signature.equality)
        (fun e : ILinks m × Bool => z (e.1.val,e.2))]
      simp only [Kernel.mul_equality,Kernel.disequality_mul_disequality]
      rw [mul_assoc,kernel_product]

theorem vertex_count (N : FiniteNetwork ℂ V E n) (m : E → Bool) :
    (network N m).toNetwork.shape.vertices = Fintype.card V + Fintype.card (ILinks m) := by
  simp [FiniteNetwork.toNetwork]

theorem edge_count (N : FiniteNetwork ℂ V E n) (m : E → Bool) :
    (network N m).toNetwork.shape.edges = Fintype.card E + Fintype.card (ILinks m) := by
  have h := Fintype.card_congr (Equiv.sumCompl (fun e => m e = true))
  simp only [Fintype.card_sum] at h
  simp only [FiniteNetwork.toNetwork,Edges,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool]
  change Fintype.card (XLinks m) + Fintype.card (ILinks m) * 2 = _
  change Fintype.card (XLinks m) + Fintype.card (ILinks m) = Fintype.card E at h
  omega

theorem iLinks_card_le (m : E → Bool) : Fintype.card (ILinks m) ≤ Fintype.card E :=
  Fintype.card_le_of_injective Subtype.val Subtype.val_injective

end ExceptionalMixedLinks
end Holant.ReedMuller.WeightTwoIntegration
