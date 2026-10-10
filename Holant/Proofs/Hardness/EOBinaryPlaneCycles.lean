import Holant.Proofs.Hardness.EOBinaryPlaneCore
import Holant.Proofs.Hardness.LabelledNetwork

/-! An actual native-X graph for binary Boolean constraints. The variables are
cycles of a permutation of the two incidences at each constraint. There are
exactly n original quaternary vertices and 2n structural X edges. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCycles
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace C
export EOBinaryPlaneCore (pairing word compress lift)
end C
set_option backward.isDefEq.respectTransparency false

abbrev Slot (n : ℕ) := Fin (n*2)

def incidence {n : ℕ} (v : Fin n) (j : Fin 2) : Slot n := finProdFinEquiv (v,j)

def split (n : ℕ) : (Σ_v : Fin n,Fin 4) ≃ (Slot n × Bool) :=
  (Equiv.sigmaEquivProd (Fin n) (Fin 4)).trans
    ((Equiv.prodCongr (Equiv.refl _) C.pairing.ports.symm).trans
      ((Equiv.prodAssoc _ _ _).symm.trans
        (Equiv.prodCongr finProdFinEquiv (Equiv.refl _))))

def route {n : ℕ} (next : Equiv.Perm (Slot n)) : Equiv.Perm (Slot n × Bool) where
  toFun p := (if p.2 then next p.1 else p.1,p.2)
  invFun p := (if p.2 then next.symm p.1 else p.1,p.2)
  left_inv := by rintro ⟨p,b⟩; cases b <;> simp
  right_inv := by rintro ⟨p,b⟩; cases b <;> simp

def closedPorts (n : ℕ) : (Slot n × Bool) ≃ (Fin 0 ⊕ (Slot n × Bool)) where
  toFun := Sum.inr
  invFun := Sum.elim Fin.elim0 id
  left_inv := fun _=>rfl
  right_inv := by intro p; cases p with | inl j=>exact Fin.elim0 j | inr p=>rfl

def shape {n : ℕ} (next : Equiv.Perm (Slot n)) : NetworkShape 0 where
  vertices := n
  arity _ := 4
  edges := n*2
  ports := (split n).trans ((route next).trans (closedPorts n))

def network {K : Type*} [Semiring K] {n : ℕ}
    (M : Signature K 4) (next : Equiv.Perm (Slot n)) : Network K 0 where
  shape := shape next
  vertex _ := M
  edge _ := Signature.disequality

def labels {K : Type*} [Semiring K] {n : ℕ}
    (M : Signature K 4) (next : Equiv.Perm (Slot n)) :
    Labelling (network M next).shape 1 1 (fun _=>4) where
  vertex _ := 0
  vertex_arity _ := rfl
  edge _ := 0

theorem counts {K : Type*} [Semiring K] {n : ℕ}
    (M : Signature K 4) (next : Equiv.Perm (Slot n)) :
    (network M next).shape.vertices=n ∧ (network M next).shape.edges=n*2 := ⟨rfl,rfl⟩

theorem native_edges {K : Type*} [Semiring K] {n : ℕ}
    (M : Signature K 4) (next : Equiv.Perm (Slot n)) (e : Fin (network M next).shape.edges) :
    (network M next).edge e=Signature.disequality := rfl

/-- Opposite ends are independent summation variables before the X factors. -/
def assignments (n : ℕ) : ((Slot n × Bool)→Bool) ≃ ((Slot n→Bool)×(Slot n→Bool)) where
  toFun z := (fun e=>z (e,false),fun e=>z (e,true))
  invFun p e := if e.2 then p.2 e.1 else p.1 e.1
  left_inv := by intro z; funext e; rcases e with ⟨e,b⟩; cases b <;> rfl
  right_inv := by intro p; rcases p with ⟨a,b⟩; rfl

theorem assignment_row {n : ℕ} (next : Equiv.Perm (Slot n))
    (z : (Slot n×Bool)→Bool) (v : Fin n) :
    (shape next).assignment Fin.elim0 z v=
      ![z (incidence v 0,false),z (next (incidence v 0),true),
        z (incidence v 1,false),z (next (incidence v 1),true)] := by
  funext i
  fin_cases i <;> rfl

theorem edge_product {K : Type*} [CommSemiring K] {n : ℕ} (a b : Slot n→Bool) :
    (∏e,Signature.disequality (K:=K) (a e) (b e))=
      if b=(fun e=>!(a e)) then 1 else 0 := by
  classical
  by_cases h : b=(fun e=>!(a e))
  · rw [ite_eq_left h,h]
    apply Finset.prod_eq_one
    intro e _
    cases ha : a e <;> simp [Signature.disequality,ha]
  · rw [ite_eq_right h]
    have hh : ∃e,b e≠!(a e) := by simpa only [funext_iff,not_forall] using h
    obtain ⟨e,he⟩ := hh
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    cases ha : a e <;> cases hb : b e <;> simp_all [Signature.disequality]

/-- One bit is retained per native edge; the other end is literally its complement. -/
theorem native_sum {K : Type*} [CommSemiring K] {n : ℕ}
    (M : Signature K 4) (next : Equiv.Perm (Slot n)) :
    (network M next).denote Fin.elim0=
      ∑a : Slot n→Bool, ∏v : Fin n,
        M ![a (incidence v 0),!(a (next (incidence v 0))),
          a (incidence v 1),!(a (next (incidence v 1)))] := by
  classical
  unfold Network.denote
  change (∑z : (Slot n×Bool)→Bool,
    (∏v : Fin n,M ((shape next).assignment Fin.elim0 z v))*
      ∏e : Slot n,Signature.disequality (z (e,false)) (z (e,true)))=_
  rw [←(assignments n).symm.sum_comp,Fintype.sum_prod_type]
  simp only [assignments,Equiv.coe_fn_symm_mk,Bool.false_eq_true,ite_false,ite_true,
    edge_product]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro v _
  rw [assignment_row]
  rfl

def Consistent {n : ℕ} (next : Equiv.Perm (Slot n)) (a : Slot n→Bool) : Prop :=
  ∀e,a (next e)=a e

def weight {K : Type*} [CommSemiring K] {n : ℕ} (f : Signature K 2) (a : Slot n→Bool) : K :=
  ∏v : Fin n,f ![a (incidence v 0),a (incidence v 1)]

/-- The standard binary-CSP value on variables presented by occurrence cycles. -/
def value {K : Type*} [CommSemiring K] {n : ℕ}
    (f : Signature K 2) (next : Equiv.Perm (Slot n)) : K := by
  classical
  exact ∑a : Slot n→Bool,if Consistent next a then weight f a else 0

theorem lift_row {K : Type*} [Zero K] {n : ℕ} (f : Signature K 2)
    (next : Equiv.Perm (Slot n)) (a : Slot n→Bool) (v : Fin n) :
    C.lift f ![a (incidence v 0),!(a (next (incidence v 0))),
      a (incidence v 1),!(a (next (incidence v 1)))]=
    if a (next (incidence v 0))=a (incidence v 0) ∧
      a (next (incidence v 1))=a (incidence v 1)
    then f ![a (incidence v 0),a (incidence v 1)] else 0 := by
  simp [C.lift]

theorem denote_lift {K : Type*} [CommSemiring K] {n : ℕ}
    (f : Signature K 2) (next : Equiv.Perm (Slot n)) :
    (network (C.lift f) next).denote Fin.elim0=value f next := by
  classical
  rw [native_sum]
  unfold value
  apply Finset.sum_congr rfl
  intro a _
  simp only [lift_row]
  by_cases h : Consistent next a
  · rw [ite_eq_left h]
    unfold weight
    apply Finset.prod_congr rfl
    intro v _
    rw [ite_eq_left ⟨h _,h _⟩]
  · rw [ite_eq_right h]
    have hh : ∃e,a (next e)≠a e := by simpa only [Consistent,not_forall] using h
    obtain ⟨e,he⟩ := hh
    let p : Fin n×Fin 2 := finProdFinEquiv.symm e
    have hp : incidence p.1 p.2=e := finProdFinEquiv.apply_symm_apply e
    apply Finset.prod_eq_zero (Finset.mem_univ p.1)
    apply ite_eq_right
    intro hpair
    have hi : p.2=0 ∨ p.2=1 := by omega
    rcases hi with hi|hi
    · exact he (hp ▸ (hi ▸ hpair.1))
    · exact he (hp ▸ (hi ▸ hpair.2))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCycles
