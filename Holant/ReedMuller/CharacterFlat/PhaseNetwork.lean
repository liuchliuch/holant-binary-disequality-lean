import Holant.ReedMuller.CharacterFlat.Bell
import Holant.ReedMuller.FlatNetwork.SourceNative

/-! Actual ordered Bell attachments on every original boundary port. The first
port of each Bell vertex is exposed, and its second port is joined to the old
boundary by a native X edge. Thus B_{1,l}X gives the literal diagonal sign. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace PhaseNetwork
open GenerationNetwork
variable {n : ℕ}

def coefficients (ell : Character n) : BinaryVector n :=
  fun i => ell (fun j => if i=j then 1 else 0)

theorem character_expansion (ell : Character n) (x : BinaryVector n) :
    ell x=∑ i,coefficients ell i*x i := by
  simpa only [coefficients,smul_eq_mul,mul_comm] using ell.pi_apply_eq_sum_univ x

theorem sign_finite_sum {ι : Type*} (s : Finset ι) (a : ι → ZMod 2) :
    sign (∑ i ∈ s,a i)=∏ i ∈ s,sign (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi,Finset.prod_insert hi,sign_add,ih]

theorem sign_character (ell : Character n) (x : Fin n → Bool) :
    sign (ell (vectorWord x))=∏ i,sign (coefficients ell i*bit (x i)) := by
  rw [character_expansion,sign_finite_sum]
  rfl

def finite (N : Network ℂ n) (l : BinaryVector n) :
    FiniteNetwork ℂ (Fin N.shape.vertices ⊕ Fin n) (Fin N.shape.edges ⊕ Fin n) n where
  arity := Sum.elim N.shape.arity (fun _ => 2)
  ports := (shiftVertexPorts N).trans
    ((Equiv.sumCongr N.shape.ports (Equiv.refl _)).trans (shiftPorts _ n))
  vertex
    | .inl v => N.vertex v
    | .inr i => bellSignature 1 (l i)
  edge := Sum.elim N.edge (fun _ => Signature.disequality)

def attach (N : Network ℂ n) (l : BinaryVector n) : Network ℂ n := (finite N l).toNetwork

@[simp] theorem attach_vertices (N : Network ℂ n) (l : BinaryVector n) :
    (attach N l).shape.vertices=N.shape.vertices+n := by simp [attach,FiniteNetwork.toNetwork]
@[simp] theorem attach_edges (N : Network ℂ n) (l : BinaryVector n) :
    (attach N l).shape.edges=N.shape.edges+n := by simp [attach,FiniteNetwork.toNetwork]

theorem attach_native (N : Network ℂ n) (l : BinaryVector n)
    (hN : ∀ e,N.edge e=Signature.disequality) :
    ∀ e,(attach N l).edge e=Signature.disequality := by
  intro e
  change (finite N l).edge ((Fintype.equivFin (Fin N.shape.edges ⊕ Fin n)).symm e)=_
  cases (Fintype.equivFin (Fin N.shape.edges ⊕ Fin n)).symm e with
  | inl e => exact hN e
  | inr i => rfl

private theorem prod_disequality {ι : Type*} [Fintype ι] (a b : ι → Bool) :
    (∏ i,(Signature.disequality (a i) (b i) : ℂ))=
      if b=(fun i => !(a i)) then 1 else 0 := by
  simp only [Signature.disequality,Fintype.prod_boole]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    exact Bool.eq_not_iff.mpr (Ne.symm (h i))
  · intro h i
    exact Ne.symm (Bool.eq_not_iff.mp (congrFun h i))

private theorem bell_complement (l : ZMod 2) (x b : Bool) :
    bellKernel 1 l x (!b)=sign (l*bit x)*Signature.equality x b := by
  rw [bellKernel,parityKernel_one]
  cases x <;> cases b <;> rfl

theorem denote_attach (N : Network ℂ n) (l : BinaryVector n) (x : Fin n → Bool) :
    (attach N l).denote x=(∏ i,sign (l i*bit (x i)))*N.denote x := by
  let : DecidableEq (Fin N.shape.edges ⊕ Fin n) := Classical.decEq _
  rw [attach,FiniteNetwork.denote_toNetwork]
  unfold FiniteNetwork.denote
  change (∑ z : ((Fin N.shape.edges ⊕ Fin n) × Bool) → Bool,
    (∏ v,(finite N l).vertex v (fun i => Sum.elim x z ((finite N l).ports ⟨v,i⟩)))*
      ∏ e,(finite N l).edge e (z (e,false)) (z (e,true)))=_
  rw [←(shiftAssignments (Fin N.shape.edges) n).symm.sum_comp]
  simp only [Fintype.sum_prod_type,Fintype.prod_sum_type]
  have ho (z : (Fin N.shape.edges × Bool) → Bool) (b c : Fin n → Bool) (v : Fin N.shape.vertices) :
      (fun i => Sum.elim x ((shiftAssignments _ n).symm (z,b,c)) ((finite N l).ports ⟨.inl v,i⟩))=
        N.shape.assignment b z v := by
    funext i
    dsimp [finite,shiftVertexPorts,NetworkShape.assignment]
    cases hp : N.shape.ports ⟨v,i⟩ <;>
      simp [shiftPorts,shiftAssignments,Network.tensorAssignments,halfEdgeAssignmentsEquiv,hp]
  have hn (z : (Fin N.shape.edges × Bool) → Bool) (b c : Fin n → Bool) (j : Fin n) :
      (finite N l).vertex (.inr j)
        (fun i => Sum.elim x ((shiftAssignments _ n).symm (z,b,c)) ((finite N l).ports ⟨.inr j,i⟩))=
        bellKernel 1 (l j) (x j) (c j) := by
    simp [finite,shiftVertexPorts,shiftPorts,shiftAssignments,Network.tensorAssignments,
      halfEdgeAssignmentsEquiv,finTwoEquiv,bellSignature]
  have he (z : (Fin N.shape.edges × Bool) → Bool) (b c : Fin n → Bool) :
      (∏ e : Fin N.shape.edges,(finite N l).edge (.inl e)
        ((shiftAssignments _ n).symm (z,b,c) (.inl e,false))
        ((shiftAssignments _ n).symm (z,b,c) (.inl e,true)))*
      (∏ i : Fin n,(finite N l).edge (.inr i)
        ((shiftAssignments _ n).symm (z,b,c) (.inr i,false))
        ((shiftAssignments _ n).symm (z,b,c) (.inr i,true)))=
      (∏ e,N.edge e (z (e,false)) (z (e,true)))*
        (∏ i,Signature.disequality (b i) (c i)) := rfl
  simp only [ho,hn,he,prod_disequality]
  simp only [mul_ite,ite_mul,mul_one,mul_zero,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [bell_complement,Finset.prod_mul_distrib,Signature.prod_equality]
  simp only [mul_ite,ite_mul,mul_one,mul_zero,zero_mul,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  unfold Network.denote
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  dsimp only [finite]
  ring

theorem denote_attach_character (N : Network ℂ n) (ell : Character n) (x : Fin n → Bool) :
    (attach N (coefficients ell)).denote x=sign (ell (vectorWord x))*N.denote x := by
  rw [denote_attach,sign_character]

theorem denote_attach_flat (N : Network ℂ n) (a : BinaryVector n) (D : BinaryCode n)
    (hN : N.denote=flatSignature 1 a D) (ell : Character n) :
    (attach N (coefficients ell)).denote=signature 1 a D ell := by
  funext x
  rw [denote_attach_character,hN]
  change sign (ell (vectorWord x))*(if vectorWord x-a∈D then 1 else 0)=
    if vectorWord x-a∈D then 1*sign (ell (vectorWord x)) else 0
  split_ifs <;> simp

end PhaseNetwork
end
end Holant.ReedMuller.CharacterFlat
