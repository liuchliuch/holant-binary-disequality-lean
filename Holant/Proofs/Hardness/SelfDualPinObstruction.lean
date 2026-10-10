import Holant.ChargeConservation

/-! An obstruction to a particular local pinning method.
Simultaneous bit complement is an explicit bijection on every full edge-end
assignment of an actual network, including loops and parallel edges. Therefore
self-dual local labels yield a self-dual boundary tensor. Uniform EXACT2_4/native
X cannot realize nonzero scalar times oriented01 as a local gadget. This is not
an obstruction to global oracle reductions or a counterexample to a dichotomy. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.SelfDualPinObstruction
open Holant
open scoped BigOperators

variable {K : Type*} [CommSemiring K]

def flip {ι : Type*} (x : ι → Bool) : ι → Bool := fun i=>!x i

@[simp] theorem flip_flip {ι : Type*} (x : ι → Bool) : flip (flip x)=x := by
  funext i
  exact Bool.not_not (x i)

def flipEquiv (ι : Type*) : (ι → Bool) ≃ (ι → Bool) where
  toFun := flip
  invFun := flip
  left_inv := flip_flip
  right_inv := flip_flip

def SelfDual {n : ℕ} (f : Signature K n) : Prop := ∀x,f (flip x)=f x

theorem assignment_flip {n : ℕ} (s : NetworkShape n) (x : Fin n → Bool)
    (z : (Fin s.edges × Bool) → Bool) (v : Fin s.vertices) :
    s.assignment (flip x) (flip z) v=flip (s.assignment x z v) := by
  funext i
  change Sum.elim (flip x) (flip z) (s.ports ⟨v,i⟩)=!(Sum.elim x z (s.ports ⟨v,i⟩))
  cases s.ports ⟨v,i⟩ <;> rfl

theorem term_flip {n : ℕ} (N : Network K n)
    (hv : ∀v,SelfDual (N.vertex v))
    (he : ∀e a b,N.edge e (!a) (!b)=N.edge e a b)
    (x : Fin n → Bool) (z : (Fin N.shape.edges × Bool) → Bool) :
    N.assignmentTerm (flip x) (flip z)=N.assignmentTerm x z := by
  unfold Network.assignmentTerm
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro v _
    rw [assignment_flip]
    exact hv v _
  · apply Finset.prod_congr rfl
    intro e _
    exact he e _ _

/-- Equality of the complete weighted boundary signature, termwise after an
explicit involutive bijection on actual oriented edge-end assignments. -/
theorem denote_self_dual {n : ℕ} (N : Network K n)
    (hv : ∀v,SelfDual (N.vertex v))
    (he : ∀e a b,N.edge e (!a) (!b)=N.edge e a b) : SelfDual N.denote := by
  intro x
  change (∑z : (Fin N.shape.edges × Bool) → Bool,N.assignmentTerm (flip x) z)=
    ∑z : (Fin N.shape.edges × Bool) → Bool,N.assignmentTerm x z
  apply Fintype.sum_equiv (flipEquiv (Fin N.shape.edges × Bool))
  intro z
  change N.assignmentTerm (flip x) z=N.assignmentTerm x (flip z)
  simpa only [flip_flip] using term_flip N hv he x (flip z)

def exactTwo : Signature K 4 := fun x=>if weight x=2 then 1 else 0

theorem exactTwo_support [Nontrivial K] (x : Fin 4 → Bool) :
    (exactTwo x : K)≠0 ↔ weight x=2 := by
  by_cases h : weight x=2 <;> simp [exactTwo,h]

theorem exactTwo_self_dual : SelfDual (exactTwo : Signature K 4) := by
  intro x
  have hw : weight (flip x)+weight x=4 := weight_compl_add x
  by_cases hx : weight x=2
  · have hf : weight (flip x)=2 := by omega
    simp only [exactTwo,hf,hx,ite_true]
  · have hf : weight (flip x)≠2 := by omega
    simp only [exactTwo,hf,hx,ite_false]

theorem nativeX_self_dual (a b : Bool) :
    (Signature.disequality (!a) (!b) : K)=Signature.disequality a b := by
  cases a <;> cases b <;> rfl

/-- Actual singleton EXACT2_4 labels and actual native-X edge labels imply the
symmetry. The label equality includes each vertex's original arity. -/
theorem exactTwo_network {n : ℕ} (N : Network K n)
    (hv : ∀v,(⟨N.shape.arity v,N.vertex v⟩ : Σm : ℕ,Signature K m)=⟨4,exactTwo⟩)
    (he : ∀e,N.edge e=Signature.disequality) : SelfDual N.denote := by
  apply denote_self_dual N
  · intro v
    have h := congrArg (fun f : Σm : ℕ,Signature K m=>SelfDual f.2) (hv v)
    exact h.mpr exactTwo_self_dual
  · intro e a b
    rw [he e]
    exact nativeX_self_dual a b

def oriented01 : Signature K 2 := fun x=>if x 0=false ∧ x 1=true then 1 else 0

/-- The obstruction excludes arbitrary nonzero local projective normalization,
not merely literal equality with the unscaled pin. -/
theorem no_projective_oriented01 {f : Signature K 2} (hf : SelfDual f)
    (c : K) (hc : c≠0) : f≠c • oriented01 := by
  intro h
  have hs := hf ![false,true]
  rw [h] at hs
  have hz : (0 : K)=c := by
    simpa [oriented01,flip,Pi.smul_apply,smul_eq_mul] using hs
  exact hc hz.symm

theorem exactTwo_no_projective_pin (N : Network K 2)
    (hv : ∀v,(⟨N.shape.arity v,N.vertex v⟩ : Σm : ℕ,Signature K m)=⟨4,exactTwo⟩)
    (he : ∀e,N.edge e=Signature.disequality) (c : K) (hc : c≠0) :
    N.denote≠c • oriented01 := no_projective_oriented01 (exactTwo_network N hv he) c hc

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.SelfDualPinObstruction
