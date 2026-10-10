import Holant.Proofs.Hardness.GeneralCSPUnused
import Holant.Proofs.Tractability.EOEvaluation.PairLift

/-! Arbitrary-arity original-signature occurrence-cycle networks. The whole
support-cover hypothesis is essential: this file does not claim that an
arbitrary opposite-pair restriction is freely available. Every vertex is the
literal original signature, with its original port order, and every edge is X. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPCycles
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {n N : ℕ} (p : OrientedPerfectPairing n)
abbrev Slot := Fin (N*p.count)

def incidence (v : Fin N) (j : Fin p.count) : Slot (N:=N) p := finProdFinEquiv (v,j)

def split : (Σ_v : Fin N,Fin n) ≃ (Slot (N:=N) p × Bool) :=
  (Equiv.sigmaEquivProd (Fin N) (Fin n)).trans
    ((Equiv.prodCongr (Equiv.refl _) p.ports.symm).trans
      ((Equiv.prodAssoc _ _ _).symm.trans
        (Equiv.prodCongr finProdFinEquiv (Equiv.refl _))))

def route {d : ℕ} (next : Equiv.Perm (Fin d)) : Equiv.Perm (Fin d × Bool) where
  toFun q := (if q.2 then next q.1 else q.1,q.2)
  invFun q := (if q.2 then next.symm q.1 else q.1,q.2)
  left_inv := by rintro ⟨q,b⟩; cases b <;> simp
  right_inv := by rintro ⟨q,b⟩; cases b <;> simp

def closedPorts (d : ℕ) : (Fin d × Bool) ≃ (Fin 0 ⊕ (Fin d × Bool)) where
  toFun := Sum.inr
  invFun := Sum.elim Fin.elim0 id
  left_inv := fun _=>rfl
  right_inv := by intro q; cases q with | inl j=>exact Fin.elim0 j | inr q=>rfl

def shape (next : Equiv.Perm (Slot (N:=N) p)) : NetworkShape 0 where
  vertices := N
  arity _ := n
  edges := N*p.count
  ports := (split p).trans ((route next).trans (closedPorts _))

def network {K : Type*} [Semiring K] (f : Signature K n)
    (next : Equiv.Perm (Slot (N:=N) p)) : Network K 0 where
  shape := shape p next
  vertex _ := f
  edge _ := Signature.disequality

/-- Original family labels can be retained, without renaming to a new resource. -/
def labels {s : ℕ} {arity : ℕ→ℕ} (label : Fin s) (ha : arity label.val=n)
    (next : Equiv.Perm (Slot (N:=N) p)) : Labelling (shape p next) s 1 arity where
  vertex _ := label
  vertex_arity _ := ha
  edge _ := 0

theorem counts {K : Type*} [Semiring K] (f : Signature K n)
    (next : Equiv.Perm (Slot (N:=N) p)) :
    (network p f next).shape.vertices=N ∧ (network p f next).shape.edges=N*p.count := ⟨rfl,rfl⟩

theorem original_vertex {K : Type*} [Semiring K] (f : Signature K n)
    (next : Equiv.Perm (Slot (N:=N) p)) (v : Fin N) : (network p f next).vertex v=f := rfl

theorem native_edges {K : Type*} [Semiring K] (f : Signature K n)
    (next : Equiv.Perm (Slot (N:=N) p)) (e : Slot (N:=N) p) :
    (network p f next).edge e=Signature.disequality := rfl

/-- Port order is exactly the given oriented pairing, with the second side
routed to the successor occurrence of the same CSP variable. -/
theorem ordered_port (next : Equiv.Perm (Slot (N:=N) p)) (v : Fin N)
    (j : Fin p.count) (b : Bool) :
    (shape p next).ports ⟨v,p.ports (j,b)⟩=
      Sum.inr (if b then next (incidence p v j) else incidence p v j,b) := by
  simp [shape,split,route,closedPorts,incidence]

def assignments (d : ℕ) : ((Fin d × Bool)→Bool) ≃ ((Fin d→Bool)×(Fin d→Bool)) where
  toFun z := (fun e=>z (e,false),fun e=>z (e,true))
  invFun q e := if e.2 then q.2 e.1 else q.1 e.1
  left_inv := by intro z; funext e; rcases e with ⟨e,b⟩; cases b <;> rfl
  right_inv := by intro q; rcases q with ⟨a,b⟩; rfl

def row (next : Equiv.Perm (Slot (N:=N) p)) (a : Slot (N:=N) p→Bool)
    (v : Fin N) : Fin n→Bool := fun k=>
  let q := p.ports.symm k
  if q.2 then !(a (next (incidence p v q.1))) else a (incidence p v q.1)

@[simp] theorem row_first (next : Equiv.Perm (Slot (N:=N) p))
    (a : Slot (N:=N) p→Bool) (v : Fin N) (j : Fin p.count) :
    row p next a v (p.ports (j,false))=a (incidence p v j) := by simp [row]

@[simp] theorem row_second (next : Equiv.Perm (Slot (N:=N) p))
    (a : Slot (N:=N) p→Bool) (v : Fin N) (j : Fin p.count) :
    row p next a v (p.ports (j,true))= !(a (next (incidence p v j))) := by simp [row]

theorem edge_product {K : Type*} [CommSemiring K] {d : ℕ} (a b : Fin d→Bool) :
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

theorem native_sum {K : Type*} [CommSemiring K] (f : Signature K n)
    (next : Equiv.Perm (Slot (N:=N) p)) :
    (network p f next).denote Fin.elim0=
      ∑a : Slot (N:=N) p→Bool,∏v : Fin N,f (row p next a v) := by
  classical
  unfold Network.denote
  change (∑z : (Slot (N:=N) p×Bool)→Bool,
    (∏v : Fin N,f ((shape p next).assignment Fin.elim0 z v))*
      ∏e : Slot (N:=N) p,Signature.disequality (z (e,false)) (z (e,true)))=_
  rw [←(assignments (N*p.count)).symm.sum_comp,Fintype.sum_prod_type]
  simp only [assignments,Equiv.coe_fn_symm_mk,Bool.false_eq_true,ite_false,ite_true,edge_product]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext k
  obtain ⟨⟨j,b⟩,rfl⟩ := p.ports.surjective k
  unfold NetworkShape.assignment
  rw [ordered_port]
  cases b <;> simp [row]

abbrev Compatible (x : Fin n→Bool) :=
  Holant.LocalDrafts.Tractability.EOEvaluation.PairLift.Compatible p x

def Covers {K : Type*} [Zero K] (f : Signature K n) : Prop :=
  ∀x,f x≠0 → Compatible p x

/-- This generic coefficient-preserving compression specializes definitionally
 to OrientedPerfectPairing.restrict over AlgebraicComplex. -/
def compress {K : Type*} (f : Signature K n) : Signature K p.count := fun z=>f (p.word z)

def Consistent (next : Equiv.Perm (Slot (N:=N) p)) (a : Slot (N:=N) p→Bool) : Prop :=
  ∀s,a (next s)=a s

def weight {K : Type*} [CommSemiring K] (g : Signature K p.count)
    (a : Slot (N:=N) p→Bool) : K := ∏v : Fin N,g (fun j=>a (incidence p v j))

def value {K : Type*} [CommSemiring K] (g : Signature K p.count)
    (next : Equiv.Perm (Slot (N:=N) p)) : K := by
  classical
  exact ∑a : Slot (N:=N) p→Bool,if Consistent p next a then weight p g a else 0

theorem row_compatible (next : Equiv.Perm (Slot (N:=N) p))
    (a : Slot (N:=N) p→Bool) (v : Fin N) :
    Compatible p (row p next a v) ↔ ∀j,a (next (incidence p v j))=a (incidence p v j) := by
  unfold Compatible Holant.LocalDrafts.Tractability.EOEvaluation.PairLift.Compatible
  simp only [row_first,row_second]
  apply forall_congr'
  intro j
  cases a (incidence p v j) <;> cases a (next (incidence p v j)) <;> decide

theorem covered_row {K : Type*} [Zero K] (f : Signature K n) (hf : Covers p f)
    (next : Equiv.Perm (Slot (N:=N) p)) (a : Slot (N:=N) p→Bool) (v : Fin N) :
    f (row p next a v)=
      if ∀j,a (next (incidence p v j))=a (incidence p v j)
      then compress p f (fun j=>a (incidence p v j)) else 0 := by
  classical
  by_cases h : ∀j,a (next (incidence p v j))=a (incidence p v j)
  · rw [ite_eq_left h]
    unfold compress
    congr 1
    funext k
    obtain ⟨⟨j,b⟩,rfl⟩ := p.ports.surjective k
    cases b <;> simp [row,OrientedPerfectPairing.word,h]
  · rw [ite_eq_right h]
    by_contra hn
    exact h ((row_compatible p next a v).mp (hf _ hn))

/-- The original signature, not an assumed available restricted signature,
realizes the compressed CSP on occurrence cycles under whole-support cover. -/
theorem denote_original {K : Type*} [CommSemiring K] (f : Signature K n)
    (hf : Covers p f) (next : Equiv.Perm (Slot (N:=N) p)) :
    (network p f next).denote Fin.elim0=value p (compress p f) next := by
  classical
  rw [native_sum]
  unfold value
  apply Finset.sum_congr rfl
  intro a _
  simp only [covered_row p f hf]
  by_cases h : Consistent p next a
  · rw [ite_eq_left h]
    unfold weight
    apply Finset.prod_congr rfl
    intro v _
    exact ite_eq_left (fun j=>h _)
  · rw [ite_eq_right h]
    obtain ⟨s,hs⟩ := not_forall.mp h
    let q : Fin N×Fin p.count := finProdFinEquiv.symm s
    have hq : incidence p q.1 q.2=s := finProdFinEquiv.apply_symm_apply s
    apply Finset.prod_eq_zero (Finset.mem_univ q.1)
    apply ite_eq_right
    intro hh
    exact hs (hq ▸ hh q.2)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPCycles
