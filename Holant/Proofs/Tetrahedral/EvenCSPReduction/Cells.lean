import Holant.Proofs.Tetrahedral.EvenCSPReduction.EqualityTree
import Holant.Complexity.ClosedNetworkCompleteness
import Mathlib.Algebra.BigOperators.Fin


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
namespace Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Cells
open Holant Holant.Complexity
open scoped BigOperators

structure Cell (d : ℕ) where
  vertices : ℕ
  edges : ℕ
  root : Fin edges
  ports : (Fin d ⊕ (Fin vertices × Fin 4)) ≃ (Fin edges × Bool)
  connected : ∀c : Fin edges → Bool,
    (∀v : Fin vertices,∀j : Fin 4,
      c (ports (.inr (v,j))).1=c (ports (.inr (v,0))).1) →
    ∀e,c e=c root

namespace Cell
variable {d : ℕ} (C : Cell d)

def row (c : Fin C.edges → Bool) (v : Fin C.vertices) : Fin 4 → Bool :=
  fun j => c (C.ports (.inr (v,j))).1
def boundary (c : Fin C.edges → Bool) : Fin d → Bool :=
  fun j => c (C.ports (.inl j)).1

theorem support_iff (c : Fin C.edges → Bool) :
    (∀v,∀j,C.row c v j=C.row c v 0) ↔ ∀e,c e=c C.root := by
  constructor
  · exact C.connected c
  · intro h v j
    exact (h _).trans (h _).symm

theorem boundary_supported (c : Fin C.edges → Bool)
    (h : ∀v,∀j,C.row c v j=C.row c v 0) : ∀j,C.boundary c j=c C.root :=
  fun j => (C.support_iff c).mp h (C.ports (.inl j)).1

/-- The supported physical edge assignments are in bijection with the
two variable bits, even for a declared variable with no occurrences. -/
def supportedBits :
    {c : Fin C.edges → Bool // ∀v,∀j,C.row c v j=C.row c v 0} ≃ Bool where
  toFun c := c.val C.root
  invFun b := ⟨(fun _ => b),(C.support_iff _).mpr (fun _ => rfl)⟩
  left_inv c := Subtype.ext (by
    funext e
    exact ((C.support_iff c.val).mp c.property e).symm)
  right_inv b := rfl

def cast {n : ℕ} (h : d=n) : Cell n := by
  subst n
  exact C

end Cell

def zeroPorts : (Fin 0 ⊕ (Fin 1 × Fin 4)) ≃ (Fin 2 × Bool) where
  toFun := Sum.elim Fin.elim0 (fun q =>
    ClosedLabelling.closedPortEquiv (EqualityTree.zeroGraph (K:=ℕ)).shape ⟨q.1,q.2⟩)
  invFun q := .inr (let p :=
    (ClosedLabelling.closedPortEquiv (EqualityTree.zeroGraph (K:=ℕ)).shape).symm q
    (p.1,p.2))
  left_inv := by
    rintro (j|⟨v,j⟩)
    · exact Fin.elim0 j
    · exact congrArg (fun p : Σ _ : Fin 1,Fin 4 =>
        (Sum.inr (p.1,p.2) : Fin 0 ⊕ (Fin 1 × Fin 4)))
        ((ClosedLabelling.closedPortEquiv (EqualityTree.zeroGraph (K:=ℕ)).shape).symm_apply_apply ⟨v,j⟩)
  right_inv q := by
    simp only [Sum.elim_inr,Sigma.eta,Equiv.apply_symm_apply]

def zero : Cell 0 where
  vertices := 1
  edges := 2
  root := 0
  ports := zeroPorts
  connected := by
    intro c h e
    let p := zeroPorts.symm (e,false)
    let q := zeroPorts.symm (0,false)
    have hp : ∃j : Fin 4,p=.inr (0,j) := by
      cases p with
      | inl j => exact Fin.elim0 j
      | inr a => exact ⟨a.2,congrArg Sum.inr (Prod.ext (Subsingleton.elim _ _) rfl)⟩
    have hq : ∃j : Fin 4,q=.inr (0,j) := by
      cases q with
      | inl j => exact Fin.elim0 j
      | inr a => exact ⟨a.2,congrArg Sum.inr (Prod.ext (Subsingleton.elim _ _) rfl)⟩
    obtain ⟨j,hj⟩ := hp
    obtain ⟨k,hk⟩ := hq
    have he : (zeroPorts (.inr (0,j))).1=e := by
      rw [←hj]
      exact congrArg Prod.fst (zeroPorts.apply_symm_apply (e,false))
    have hr : (zeroPorts (.inr (0,k))).1=0 := by
      rw [←hk]
      exact congrArg Prod.fst (zeroPorts.apply_symm_apply (0,false))
    rw [←he,←hr]
    exact (h 0 j).trans (h 0 k).symm

def twoPorts : (Fin 2 ⊕ (Fin 0 × Fin 4)) ≃ (Fin 1 × Bool) where
  toFun := Sum.elim (fun j => (0,finTwoEquiv j)) (fun q => Fin.elim0 q.1)
  invFun q := .inl (finTwoEquiv.symm q.2)
  left_inv := by
    rintro (j|q)
    · simp
    · exact Fin.elim0 q.1
  right_inv := by
    rintro ⟨e,b⟩
    have he : e=0 := Subsingleton.elim _ _
    subst e
    simp

def two : Cell 2 where
  vertices := 0
  edges := 1
  root := 0
  ports := twoPorts
  connected := fun c _ e => congrArg c (Subsingleton.elim _ _)

/-- Original occurrences are false ends of the outer edges; the actual
Eq4 tree boundary is their true ends. Internal tree orientations are kept. -/
def chainPorts (t : ℕ) :
    (Fin (2*t+4) ⊕ (Fin (t+1) × Fin 4)) ≃ (Fin ((2*t+4)+t) × Bool) where
  toFun
    | .inl j => (finSumFinEquiv (.inl j),false)
    | .inr q => match EqualityTree.ports t ⟨q.1,q.2⟩ with
      | .inl j => (finSumFinEquiv (.inl j),true)
      | .inr (e,b) => (finSumFinEquiv (.inr e),b)
  invFun q := match finSumFinEquiv.symm q.1 with
    | .inl j => if q.2 then
        .inr (let p := (EqualityTree.ports t).symm (.inl j); (p.1,p.2))
      else .inl j
    | .inr e => .inr (let p := (EqualityTree.ports t).symm (.inr (e,q.2)); (p.1,p.2))
  left_inv := by
    rintro (j|⟨v,j⟩)
    · simp only [Equiv.symm_apply_apply,Bool.false_eq_true,if_false]
    · cases hp : EqualityTree.ports t ⟨v,j⟩ with
      | inl k =>
        simp only [hp,Equiv.symm_apply_apply,if_true]
        have h := congrArg (EqualityTree.ports t).symm hp
        simpa only [Equiv.symm_apply_apply] using congrArg
          (fun p : EqualityTree.Ports t => (Sum.inr (p.1,p.2) :
            Fin (2*t+4) ⊕ (Fin (t+1) × Fin 4))) h.symm
      | inr q =>
        simp only [hp,Equiv.symm_apply_apply]
        have h := congrArg (EqualityTree.ports t).symm hp
        simpa only [Equiv.symm_apply_apply] using congrArg
          (fun p : EqualityTree.Ports t => (Sum.inr (p.1,p.2) :
            Fin (2*t+4) ⊕ (Fin (t+1) × Fin 4))) h.symm
  right_inv := by
    rintro ⟨e,b⟩
    obtain ⟨q,rfl⟩ := finSumFinEquiv.surjective e
    cases q with
    | inl j => cases b <;> simp only [Equiv.symm_apply_apply,if_true,if_false,
        Bool.false_eq_true,Bool.true_eq_false,Sigma.eta,Equiv.apply_symm_apply]
    | inr k => simp only [Equiv.symm_apply_apply,Sigma.eta,Equiv.apply_symm_apply]

theorem chain_row (t : ℕ) (c : Fin ((2*t+4)+t) → Bool)
    (v : Fin (t+1)) (j : Fin 4) :
    c ((chainPorts t (.inr (v,j))).1)=
      EqualityTree.bits t (fun k => c (finSumFinEquiv (.inl k)))
        (fun e => c (finSumFinEquiv (.inr e))) v j := by
  simp only [chainPorts,Equiv.coe_fn_mk,EqualityTree.bits,EqualityTree.ports,
    Equiv.ofBijective_apply]
  cases EqualityTree.port t ⟨v,j⟩ <;> rfl

def chain (t : ℕ) : Cell (2*t+4) where
  vertices := t+1
  edges := (2*t+4)+t
  root := finSumFinEquiv (.inl 0)
  ports := chainPorts t
  connected := by
    intro c h e
    have hh := (EqualityTree.support_iff t
      (fun k => c (finSumFinEquiv (.inl k)))
      (fun k => c (finSumFinEquiv (.inr k)))).mp
        (by simpa only [chain_row] using h)
    obtain ⟨q,rfl⟩ := finSumFinEquiv.surjective e
    cases q with
    | inl j => exact hh.1 j
    | inr j => exact hh.2 j

theorem high_degree (d : ℕ) (hd : Even d) (h0 : d≠0) (h2 : d≠2) :
    2*(d/2-2)+4=d := by
  rcases hd with ⟨k,hk⟩
  omega

/-- No cell, layout, pairing or equality tree is a caller argument. -/
def make (d : ℕ) (hd : Even d) : Cell d :=
  if h0 : d=0 then zero.cast h0.symm
  else if h2 : d=2 then two.cast h2.symm
  else (chain (d/2-2)).cast (high_degree d hd h0 h2)

theorem make_counts (d : ℕ) (hd : Even d) :
    (make d hd).vertices=(if d=0 then 1 else if d=2 then 0 else d/2-1) ∧
    (make d hd).edges=(if d=0 then 2 else if d=2 then 1 else d+(d/2-2)) := by
  by_cases h0 : d=0
  · subst d
    simp [make,Cell.cast,zero]
  · by_cases h2 : d=2
    · subst d
      simp [make,Cell.cast,two]
    · have hh := high_degree d hd h0 h2
      have hcast {m n : ℕ} (C : Cell m) (h : m=n) :
          (C.cast h).vertices=C.vertices ∧ (C.cast h).edges=C.edges := by
        subst n
        exact ⟨rfl,rfl⟩
      have hc := hcast (chain (d/2-2)) hh
      simp only [make,dif_neg h0,dif_neg h2,if_neg h0,if_neg h2]
      change ((chain (d/2-2)).cast hh).vertices=_ ∧
        ((chain (d/2-2)).cast hh).edges=_
      rw [hc.1,hc.2]
      change (d/2-2)+1=d/2-1 ∧ (2*(d/2-2)+4)+(d/2-2)=d+(d/2-2)
      omega

theorem make_size (d : ℕ) (hd : Even d) :
    (make d hd).vertices≤d+1 ∧ (make d hd).edges≤2*d+2 := by
  rw [(make_counts d hd).1,(make_counts d hd).2]
  split_ifs <;> omega

end Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Cells
end
