import Holant.Proofs.Hardness.GeneralEOPairedCSPRecords
import Mathlib.Algebra.BigOperators.Fin

/-! Mixed fixed-family occurrence cycles with arbitrary, label-dependent arity.
Each original signature has its own whole-support covering pairing. Literal
original labels and original port order are retained at every mixed vertex. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPFamilyCycles
open Holant Holant.Tractable Holant.Complexity
open scoped BigOperators
namespace C
export GeneralEOPairedCSPCycles (route closedPorts assignments edge_product Compatible Covers compress)
end C
set_option backward.isDefEq.respectTransparency false

variable {s N m : ℕ} {arity : ℕ→ℕ}
variable (P : (i : Fin s)→OrientedPerfectPairing (arity i.val)) (labels : Fin N→Fin s)

def count : ℕ := ∑v : Fin N,(P (labels v)).count
abbrev Slot := Fin (count P labels)

def incidence (v : Fin N) (j : Fin (P (labels v)).count) : Slot P labels := finSigmaFinEquiv ⟨v,j⟩

/-- Cumulative original occurrence address, including zero-length blocks. -/
theorem incidence_val (v : Fin N) (j : Fin (P (labels v)).count) :
    (incidence P labels v j).val=
      (((List.ofFn labels).take v.val).map (fun i=>(P i).count)).sum+j.val := by
  have ht : (List.ofFn labels).take v.val=
      List.ofFn (fun i : Fin v.val=>labels (Fin.castLE v.isLt.le i)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [ht,List.map_ofFn,List.sum_ofFn]
  exact finSigmaFinEquiv_apply (n:=fun v : Fin N=>(P (labels v)).count) ⟨v,j⟩

def split : (Σv : Fin N,Fin (arity (labels v).val)) ≃ (Slot P labels×Bool) :=
  (Equiv.sigmaCongrRight (fun v=>(P (labels v)).ports.symm)).trans
    ((Equiv.sigmaProdDistrib (fun v : Fin N=>Fin (P (labels v)).count) Bool).symm.trans
      (Equiv.prodCongr finSigmaFinEquiv (Equiv.refl Bool)))

def shape (next : Equiv.Perm (Slot P labels)) : NetworkShape 0 where
  vertices := N
  arity v := arity (labels v).val
  edges := count P labels
  ports := (split P labels).trans ((C.route next).trans (C.closedPorts _))

def network {K : Type*} [Semiring K] (G : (i : Fin s)→Signature K (arity i.val))
    (next : Equiv.Perm (Slot P labels)) : Network K 0 where
  shape := shape P labels next
  vertex v := G (labels v)
  edge _ := Signature.disequality

theorem ordered_port (next : Equiv.Perm (Slot P labels)) (v : Fin N)
    (j : Fin (P (labels v)).count) (b : Bool) :
    (shape P labels next).ports ⟨v,(P (labels v)).ports (j,b)⟩=
      Sum.inr (if b then next (incidence P labels v j) else incidence P labels v j,b) := by
  simp [shape,split,C.route,C.closedPorts,incidence]
  rfl

def row (next : Equiv.Perm (Slot P labels)) (a : Slot P labels→Bool) (v : Fin N) :
    Fin (arity (labels v).val)→Bool := fun k=>
  let q := (P (labels v)).ports.symm k
  if q.2 then !(a (next (incidence P labels v q.1))) else a (incidence P labels v q.1)

@[simp] theorem row_first (next : Equiv.Perm (Slot P labels)) (a : Slot P labels→Bool)
    (v : Fin N) (j : Fin (P (labels v)).count) :
    row P labels next a v ((P (labels v)).ports (j,false))=a (incidence P labels v j) := by simp [row]

@[simp] theorem row_second (next : Equiv.Perm (Slot P labels)) (a : Slot P labels→Bool)
    (v : Fin N) (j : Fin (P (labels v)).count) :
    row P labels next a v ((P (labels v)).ports (j,true))= !(a (next (incidence P labels v j))) := by simp [row]

theorem native_sum {K : Type*} [CommSemiring K] (G : (i : Fin s)→Signature K (arity i.val))
    (next : Equiv.Perm (Slot P labels)) :
    (network P labels G next).denote Fin.elim0=
      ∑a : Slot P labels→Bool,∏v : Fin N,G (labels v) (row P labels next a v) := by
  classical
  unfold Network.denote
  change (∑z : (Slot P labels×Bool)→Bool,
    (∏v : Fin N,G (labels v) ((shape P labels next).assignment Fin.elim0 z v))*
      ∏e : Slot P labels,Signature.disequality (z (e,false)) (z (e,true)))=_
  rw [←(C.assignments (count P labels)).symm.sum_comp,Fintype.sum_prod_type]
  simp only [C.assignments,Equiv.coe_fn_symm_mk,Bool.false_eq_true,ite_false,ite_true,C.edge_product]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext k
  obtain ⟨⟨j,b⟩,rfl⟩ := (P (labels v)).ports.surjective k
  unfold NetworkShape.assignment
  rw [ordered_port]
  cases b <;> simp [row]

def Consistent (next : Equiv.Perm (Slot P labels)) (a : Slot P labels→Bool) : Prop :=
  ∀e,a (next e)=a e

def weight {K : Type*} [CommSemiring K] (g : (i : Fin s)→Signature K (P i).count)
    (a : Slot P labels→Bool) : K := ∏v : Fin N,g (labels v) (fun j=>a (incidence P labels v j))

def cycleValue {K : Type*} [CommSemiring K] (g : (i : Fin s)→Signature K (P i).count)
    (next : Equiv.Perm (Slot P labels)) : K := by
  classical
  exact ∑a : Slot P labels→Bool,if Consistent P labels next a then weight P labels g a else 0

theorem row_compatible (next : Equiv.Perm (Slot P labels)) (a : Slot P labels→Bool) (v : Fin N) :
    C.Compatible (P (labels v)) (row P labels next a v) ↔
      ∀j,a (next (incidence P labels v j))=a (incidence P labels v j) := by
  unfold C.Compatible Holant.LocalDrafts.Tractability.EOEvaluation.PairLift.Compatible
  simp only [row_first,row_second]
  apply forall_congr'
  intro j
  cases a (incidence P labels v j) <;> cases a (next (incidence P labels v j)) <;> decide

theorem covered_row {K : Type*} [Zero K] (G : (i : Fin s)→Signature K (arity i.val))
    (hf : ∀i,C.Covers (P i) (G i)) (next : Equiv.Perm (Slot P labels))
    (a : Slot P labels→Bool) (v : Fin N) :
    G (labels v) (row P labels next a v)=
      if ∀j,a (next (incidence P labels v j))=a (incidence P labels v j)
      then C.compress (P (labels v)) (G (labels v)) (fun j=>a (incidence P labels v j)) else 0 := by
  classical
  by_cases h : ∀j,a (next (incidence P labels v j))=a (incidence P labels v j)
  · rw [ite_eq_left h]
    unfold C.compress
    congr 1
    funext k
    obtain ⟨⟨j,b⟩,rfl⟩ := (P (labels v)).ports.surjective k
    cases b <;> simp [row,OrientedPerfectPairing.word,h]
  · rw [ite_eq_right h]
    by_contra hn
    exact h ((row_compatible P labels next a v).mp (hf (labels v) _ hn))

theorem denote_original {K : Type*} [CommSemiring K] (G : (i : Fin s)→Signature K (arity i.val))
    (hf : ∀i,C.Covers (P i) (G i)) (next : Equiv.Perm (Slot P labels)) :
    (network P labels G next).denote Fin.elim0=
      cycleValue P labels (fun i=>C.compress (P i) (G i)) next := by
  classical
  rw [native_sum]
  unfold cycleValue
  apply Finset.sum_congr rfl
  intro a _
  simp only [covered_row P labels G hf]
  by_cases h : Consistent P labels next a
  · rw [ite_eq_left h]
    unfold weight
    apply Finset.prod_congr rfl
    intro v _
    exact ite_eq_left (fun j=>h _)
  · rw [ite_eq_right h]
    obtain ⟨e,he⟩ := not_forall.mp h
    let q : Σv : Fin N,Fin (P (labels v)).count := finSigmaFinEquiv.symm e
    have hq : incidence P labels q.1 q.2=e := finSigmaFinEquiv.apply_symm_apply e
    apply Finset.prod_eq_zero (Finset.mem_univ q.1)
    apply ite_eq_right
    intro hh
    exact he (hq ▸ hh q.2)

def value {K : Type*} [CommSemiring K] (g : (i : Fin s)→Signature K (P i).count)
    (scope : Slot P labels→Fin m) : K :=
  ∑x : Fin m→Bool,∏v : Fin N,g (labels v) (fun j=>x (scope (incidence P labels v j)))

theorem cycle_value {K : Type*} [CommSemiring K] (g : (i : Fin s)→Signature K (P i).count)
    (scope : Slot P labels→Fin m) :
    value P labels g scope=(2:K)^GeneralCSPUnused.unusedCount scope*
      cycleValue P labels g (GeneralEOPairedCSPScan.next scope) := by
  classical
  have hc (a : Slot P labels→Bool) : GeneralCSPUnused.FiberConstant scope a ↔
      Consistent P labels (GeneralEOPairedCSPScan.next scope) a := GeneralEOPairedCSPScan.constant_iff scope a
  have hv : cycleValue P labels g (GeneralEOPairedCSPScan.next scope)=
      ∑a : GeneralCSPUnused.ConsistentAssignment scope,weight P labels g a.val := by
    unfold cycleValue
    simp only [←hc]
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype (p:=GeneralCSPUnused.FiberConstant scope) _
      (by intro a; simp) (weight P labels g)
  rw [hv]
  exact GeneralCSPUnused.assignment_sum scope (weight P labels g)

theorem native_value {K : Type*} [CommSemiring K] (G : (i : Fin s)→Signature K (arity i.val))
    (hf : ∀i,C.Covers (P i) (G i)) (scope : Slot P labels→Fin m) :
    value P labels (fun i=>C.compress (P i) (G i)) scope=
      (2:K)^GeneralCSPUnused.unusedCount scope*
        (network P labels G (GeneralEOPairedCSPScan.next scope)).denote Fin.elim0 := by
  rw [denote_original P labels G hf]
  exact cycle_value P labels _ scope

/-- Original mixed labels, including coincidences and nullary occurrences. -/
def labelling (next : Equiv.Perm (Slot P labels)) : ClosedLabelling (shape P labels next) s 1 arity where
  vertex := labels
  vertex_arity _ := rfl
  edge _ := 0

def query (next : Equiv.Perm (Slot P labels)) :
    GeneralEOPairedCSPRecords.TargetInput (s:=s) (arity:=arity) := (labelling P labels next).validated

def rows (next : Equiv.Perm (Slot P labels)) : List RawVertex :=
  List.ofFn fun v : Fin N=>((labels v).val,List.ofFn fun k : Fin (arity (labels v).val)=>
    let q := (P (labels v)).ports.symm k
    ((if q.2 then next (incidence P labels v q.1) else incidence P labels v q.1).val,q.2))

theorem query_rows (next : Equiv.Perm (Slot P labels)) :
    (query P labels next).val.vertices=rows P labels next := by
  unfold query ClosedLabelling.validated ClosedLabelling.serialize rows
  congr 1

theorem query_edges (next : Equiv.Perm (Slot P labels)) :
    (query P labels next).val.edges=List.replicate (count P labels) 0 := by
  change List.ofFn (fun _ : Fin (count P labels)=>(0 : Fin 1).val)=_
  simp

/-- Each emitted port uses the natural-address successor, in its own original
signature's port order and retaining its original mixed-family label. -/
theorem query_scan_rows (scope : Slot P labels→Fin m) :
    (query P labels (GeneralEOPairedCSPScan.next scope)).val.vertices=
      List.ofFn (fun v : Fin N=>((labels v).val,List.ofFn fun k : Fin (arity (labels v).val)=>
        let q := (P (labels v)).ports.symm k
        (if q.2 then GeneralEOPairedCSPScan.NatScan.next
          (GeneralEOPairedCSPScan.NatScan.addresses scope) (incidence P labels v q.1).val
          else (incidence P labels v q.1).val,q.2))) := by
  rw [query_rows]
  unfold rows
  congr 1
  funext v
  congr 1
  apply congrArg List.ofFn
  funext k
  dsimp only
  rw [GeneralEOPairedCSPScan.NatScan.next_value]
  cases ((P (labels v)).ports.symm k).2 <;> rfl

theorem query_counts (next : Equiv.Perm (Slot P labels)) :
    (query P labels next).val.vertices.length=N ∧
      (query P labels next).val.edges.length=∑v : Fin N,(P (labels v)).count := by
  constructor <;> simp [query,ClosedLabelling.validated,shape,count]

theorem query_value {K : Type*} [CommSemiring K] (G : (i : Fin s)→Signature K (arity i.val))
    (hf : ∀i,C.Covers (P i) (G i)) (scope : Slot P labels→Fin m) :
    value P labels (fun i=>C.compress (P i) (G i)) scope=
      (2:K)^GeneralCSPUnused.unusedCount scope*
        ((query P labels (GeneralEOPairedCSPScan.next scope)).val.realize
          (query P labels (GeneralEOPairedCSPScan.next scope)).property G
          (fun _=>Signature.disequality)).denote Fin.elim0 := by
  rw [(labelling P labels _).denote_serialize]
  exact native_value P labels G hf scope

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPFamilyCycles
