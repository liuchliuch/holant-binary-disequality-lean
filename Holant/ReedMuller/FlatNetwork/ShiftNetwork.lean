import Holant.ReedMuller.FlatNetwork.GenerationNetworkBasic
import Holant.NetworkGluing.Finite
import Holant.OrdinaryNetwork

/-! Actual affine shifts: one retained ordinary I vertex on each boundary,
with I/X chosen by the shift bit. All exposed ports remain ordinary. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace GenerationNetwork
variable {n : ℕ}

def shiftPorts (E : Type*) (n : ℕ) :
    ((Fin n ⊕ (E × Bool)) ⊕ (Fin n × Bool)) ≃ (Fin n ⊕ ((E ⊕ Fin n) × Bool)) where
  toFun
    | .inl (.inl i) => .inr (.inr i,false)
    | .inl (.inr (e,b)) => .inr (.inl e,b)
    | .inr (i,false) => .inl i
    | .inr (i,true) => .inr (.inr i,true)
  invFun
    | .inl i => .inr (i,false)
    | .inr (.inl e,b) => .inl (.inr (e,b))
    | .inr (.inr i,false) => .inl (.inl i)
    | .inr (.inr i,true) => .inr (i,true)
  left_inv := by
    rintro ((i | ⟨e,b⟩) | ⟨i,b⟩)
    · rfl
    · rfl
    · cases b <;> rfl
  right_inv := by
    rintro (i | ⟨e|i,b⟩)
    · rfl
    · rfl
    · cases b <;> rfl

def shiftVertexPorts (N : Network ℂ n) :
    (Σ v : Fin N.shape.vertices ⊕ Fin n,Fin (Sum.elim N.shape.arity (fun _ => 2) v)) ≃
      ((Σ v : Fin N.shape.vertices,Fin (N.shape.arity v)) ⊕ (Fin n × Bool)) where
  toFun
    | ⟨.inl v,i⟩ => .inl ⟨v,i⟩
    | ⟨.inr j,i⟩ => .inr (j,finTwoEquiv i)
  invFun
    | .inl ⟨v,i⟩ => ⟨.inl v,i⟩
    | .inr (j,b) => ⟨.inr j,finTwoEquiv.symm b⟩
  left_inv := by rintro ⟨v|j,i⟩;rfl;simp
  right_inv := by rintro (⟨v,i⟩ | ⟨j,b⟩);rfl;simp

def shiftFinite (N : Network ℂ n) (a : BinaryVector n) :
    FiniteNetwork ℂ (Fin N.shape.vertices ⊕ Fin n) (Fin N.shape.edges ⊕ Fin n) n where
  arity := Sum.elim N.shape.arity (fun _ => 2)
  ports := (shiftVertexPorts N).trans
    ((Equiv.sumCongr N.shape.ports (Equiv.refl _)).trans (shiftPorts _ n))
  vertex
    | .inl v => N.vertex v
    | .inr _ => fun x => Signature.equality (x (0 : Fin 2)) (x (1 : Fin 2))
  edge := Sum.elim N.edge (fun i => parityKernel (a i))

def shift (N : Network ℂ n) (a : BinaryVector n) : Network ℂ n := (shiftFinite N a).toNetwork

@[simp] theorem shift_vertices (N : Network ℂ n) (a : BinaryVector n) :
    (shift N a).shape.vertices=N.shape.vertices+n := by simp [shift,FiniteNetwork.toNetwork]
@[simp] theorem shift_edges (N : Network ℂ n) (a : BinaryVector n) :
    (shift N a).shape.edges=N.shape.edges+n := by simp [shift,FiniteNetwork.toNetwork]

theorem allowed_shift (N : Network ℂ n) (a : BinaryVector n) (hN : Allowed N) : Allowed (shift N a) := by
  have hv : ∀ v,(⟨(shiftFinite N a).arity v,(shiftFinite N a).vertex v⟩ : AnySignature ℂ)=
      ⟨2,fun x => Signature.equality (x 0) (x 1)⟩ ∨
      (⟨(shiftFinite N a).arity v,(shiftFinite N a).vertex v⟩ : AnySignature ℂ)=⟨8,rmCore⟩ := by
    rintro (v|i)
    · exact hN.1 v
    · exact Or.inl rfl
  have he : ∀ e,(shiftFinite N a).edge e=Signature.equality ∨ (shiftFinite N a).edge e=Signature.disequality := by
    rintro (e|i)
    · exact hN.2 e
    · change parityKernel (a i)=Signature.equality ∨ parityKernel (a i)=Signature.disequality
      generalize a i=eta
      fin_cases eta
      · exact Or.inl parityKernel_zero
      · exact Or.inr parityKernel_one
  exact ⟨fun v => hv ((Fintype.equivFin (Fin N.shape.vertices ⊕ Fin n)).symm v),
    fun e => he ((Fintype.equivFin (Fin N.shape.edges ⊕ Fin n)).symm e)⟩

def shiftWord (a : BinaryVector n) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if a i=0 then x i else !(x i)

theorem vector_shiftWord (a : BinaryVector n) (x : Fin n → Bool) :
    vectorWord (shiftWord a x)=vectorWord x-a := by
  funext i
  have h : ∀ c : ZMod 2,∀ b : Bool,
      boolEquiv (if c=0 then b else !b)=boolEquiv b-c := by decide
  exact h (a i) (x i)

theorem parityKernel_shift (c : ZMod 2) (b x : Bool) :
    parityKernel c b x=(Signature.equality b (if c=0 then x else !x) : ℂ) := by
  fin_cases c <;> cases b <;> cases x <;>
    norm_num [parityKernel_zero,parityKernel_one,Signature.equality,Signature.disequality]

theorem shift_kernel_product (a : BinaryVector n) (b x : Fin n → Bool) :
    (∏ i,parityKernel (a i) (b i) (x i))=if b=shiftWord a x then 1 else 0 := by
  simp only [parityKernel_shift]
  exact Signature.prod_equality b (shiftWord a x)

def shiftAssignments (E : Type*) (n : ℕ) :
    (((E ⊕ Fin n) × Bool) → Bool) ≃
      (((E × Bool) → Bool) × ((Fin n → Bool) × (Fin n → Bool))) :=
  (Network.tensorAssignments E (Fin n)).trans
    (Equiv.prodCongr (Equiv.refl _) (halfEdgeAssignmentsEquiv n))

theorem denote_shift (N : Network ℂ n) (a : BinaryVector n) (x : Fin n → Bool) :
    (shift N a).denote x=N.denote (shiftWord a x) := by
  let : DecidableEq (Fin N.shape.edges ⊕ Fin n) := Classical.decEq _
  rw [shift,FiniteNetwork.denote_toNetwork]
  unfold FiniteNetwork.denote
  change (∑ z : ((Fin N.shape.edges ⊕ Fin n) × Bool) → Bool,
    (∏ v,(shiftFinite N a).vertex v (fun i => Sum.elim x z ((shiftFinite N a).ports ⟨v,i⟩)))*
      ∏ e,(shiftFinite N a).edge e (z (e,false)) (z (e,true)))=_
  rw [←(shiftAssignments (Fin N.shape.edges) n).symm.sum_comp]
  simp only [Fintype.sum_prod_type,Fintype.prod_sum_type]
  have ho (z : (Fin N.shape.edges × Bool) → Bool) (b c : Fin n → Bool) (v : Fin N.shape.vertices) :
      (fun i => Sum.elim x ((shiftAssignments _ n).symm (z,b,c)) ((shiftFinite N a).ports ⟨.inl v,i⟩))=
        N.shape.assignment b z v := by
    funext i
    dsimp [shiftFinite,shiftVertexPorts,NetworkShape.assignment]
    cases hp : N.shape.ports ⟨v,i⟩ <;>
      simp [shiftPorts,shiftAssignments,Network.tensorAssignments,halfEdgeAssignmentsEquiv,hp]
  have hn (z : (Fin N.shape.edges × Bool) → Bool) (b c : Fin n → Bool) (j : Fin n) :
      (shiftFinite N a).vertex (.inr j)
        (fun i => Sum.elim x ((shiftAssignments _ n).symm (z,b,c)) ((shiftFinite N a).ports ⟨.inr j,i⟩))=
        Signature.equality (x j) (c j) := by
    simp [shiftFinite,shiftVertexPorts,shiftPorts,shiftAssignments,Network.tensorAssignments,halfEdgeAssignmentsEquiv,finTwoEquiv]
  have he (z : (Fin N.shape.edges × Bool) → Bool) (b c : Fin n → Bool) :
      (∏ e : Fin N.shape.edges,(shiftFinite N a).edge (.inl e)
        ((shiftAssignments _ n).symm (z,b,c) (.inl e,false))
        ((shiftAssignments _ n).symm (z,b,c) (.inl e,true)))*
      (∏ i : Fin n,(shiftFinite N a).edge (.inr i)
        ((shiftAssignments _ n).symm (z,b,c) (.inr i,false))
        ((shiftAssignments _ n).symm (z,b,c) (.inr i,true)))=
      (∏ e,N.edge e (z (e,false)) (z (e,true)))*(∏ i,parityKernel (a i) (b i) (c i)) := rfl
  simp only [ho,hn,he,Signature.prod_equality]
  change (∑ z : (Fin N.shape.edges × Bool) → Bool,∑ b : Fin n → Bool,∑ c : Fin n → Bool,
      ((∏ v,N.vertex v (N.shape.assignment b z v))*(if x=c then 1 else 0))*
        ((∏ e,N.edge e (z (e,false)) (z (e,true)))*(∏ i,parityKernel (a i) (b i) (c i))))=_
  simp only [mul_ite,ite_mul,mul_one,mul_zero,zero_mul]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,shift_kernel_product]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rfl

/-- The true graph realizes the translated coset, with scalar exactly one. -/
theorem denote_shift_flat (N : Network ℂ n) (D : BinaryCode n)
    (hN : N.denote=flatSignature 1 0 D) (a : BinaryVector n) :
    (shift N a).denote=flatSignature 1 a D := by
  funext x
  rw [denote_shift,hN,flat_zero_value]
  rw [vector_shiftWord]
  rfl

end GenerationNetwork
end
end Holant.ReedMuller.FlatNetwork
