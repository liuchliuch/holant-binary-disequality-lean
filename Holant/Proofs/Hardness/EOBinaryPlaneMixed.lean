import Holant.Proofs.Hardness.EOBinaryPlaneOrient
import Holant.Proofs.Hardness.EOBinaryPlaneRecords
import Holant.Proofs.Hardness.GeneralCSPUnused

/-! Mixed binary factors and literal per-row argument polarity. Pair reversal
changes only the original vertex's ordered incidences. All actual vertices still
carry the original quaternary table and every edge remains native X. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneMixed
open Holant Holant.Complexity
open scoped BigOperators
namespace C
export EOBinaryPlaneCycles (Slot incidence shape assignments assignment_row edge_product Consistent lift_row)
end C
namespace B
export EOBinaryPlaneCore (lift)
end B
namespace F
export EOBinaryPlaneOrient (ports flipWord lift_flip)
end F
namespace U
export GeneralCSPUnused (unusedCount FiberConstant ConsistentAssignment assignment_sum)
end U
set_option backward.isDefEq.respectTransparency false

variable {n m : ℕ}

def networkRows {K : Type*} [Semiring K] (tables : Fin n→Signature K 4)
    (next : Equiv.Perm (C.Slot n)) : Network K 0 where
  shape := C.shape next
  vertex := tables
  edge _ := Signature.disequality

theorem native_rows_sum {K : Type*} [CommSemiring K] (tables : Fin n→Signature K 4)
    (next : Equiv.Perm (C.Slot n)) :
    (networkRows tables next).denote Fin.elim0=
      ∑a : C.Slot n→Bool,∏v : Fin n,tables v
        ![a (C.incidence v 0),!(a (next (C.incidence v 0))),
          a (C.incidence v 1),!(a (next (C.incidence v 1)))] := by
  classical
  unfold Network.denote
  change (∑z : (C.Slot n×Bool)→Bool,
    (∏v : Fin n,tables v ((C.shape next).assignment Fin.elim0 z v))*
      ∏e : C.Slot n,Signature.disequality (z (e,false)) (z (e,true)))=_
  rw [←(C.assignments n).symm.sum_comp,Fintype.sum_prod_type]
  simp only [C.assignments,Equiv.coe_fn_symm_mk,Bool.false_eq_true,ite_false,ite_true,C.edge_product]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro v _
  rw [C.assignment_row]
  rfl

def cycleValue {K : Type*} [CommSemiring K] (f : Fin n→Signature K 2)
    (next : Equiv.Perm (C.Slot n)) : K := by
  classical
  exact ∑a : C.Slot n→Bool,if C.Consistent next a then
    ∏v : Fin n,f v ![a (C.incidence v 0),a (C.incidence v 1)] else 0

theorem denote_rows {K : Type*} [CommSemiring K] (f : Fin n→Signature K 2)
    (next : Equiv.Perm (C.Slot n)) :
    (networkRows (fun v=>B.lift (f v)) next).denote Fin.elim0=cycleValue f next := by
  classical
  rw [native_rows_sum]
  unfold cycleValue
  apply Finset.sum_congr rfl
  intro a _
  simp only [C.lift_row]
  by_cases h : C.Consistent next a
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro v _
    rw [ite_eq_left ⟨h _,h _⟩]
  · rw [ite_eq_right h]
    have hh : ∃e,a (next e)≠a e := by simpa only [C.Consistent,not_forall] using h
    obtain ⟨e,he⟩ := hh
    let p : Fin n×Fin 2 := finProdFinEquiv.symm e
    have hp : C.incidence p.1 p.2=e := finProdFinEquiv.apply_symm_apply e
    apply Finset.prod_eq_zero (Finset.mem_univ p.1)
    apply ite_eq_right
    intro hpair
    have hi : p.2=0 ∨ p.2=1 := by omega
    rcases hi with hi|hi
    · exact he (hp ▸ (hi ▸ hpair.1))
    · exact he (hp ▸ (hi ▸ hpair.2))

def value {K : Type*} [CommSemiring K] (f : Fin n→Signature K 2)
    (scope : C.Slot n→Fin m) : K :=
  ∑x : Fin m→Bool,∏v : Fin n,
    f v ![x (scope (C.incidence v 0)),x (scope (C.incidence v 1))]

theorem value_cycle {K : Type*} [CommSemiring K] (f : Fin n→Signature K 2)
    (scope : C.Slot n→Fin m) :
    value f scope=(2 : K)^U.unusedCount scope*cycleValue f (EOBinaryPlaneScan.next scope) := by
  classical
  have hc (a : C.Slot n→Bool) : U.FiberConstant scope a ↔
      C.Consistent (EOBinaryPlaneScan.next scope) a := by
    constructor
    · intro h s
      exact h _ s (EOBinaryPlaneScan.scope_forward scope s)
    · intro h s t hst
      exact EOBinaryPlaneScan.consistent_fiber scope a h s t hst
  have hcycle : cycleValue f (EOBinaryPlaneScan.next scope)=
      ∑a : U.ConsistentAssignment scope,∏v : Fin n,
        f v ![a.val (C.incidence v 0),a.val (C.incidence v 1)] := by
    unfold cycleValue
    simp only [←hc]
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype (p:=U.FiberConstant scope) _ (by intro a; simp) _
  rw [hcycle]
  exact U.assignment_sum scope (fun a=>∏v : Fin n,f v ![a (C.incidence v 0),a (C.incidence v 1)])

def twistedShape (next : Equiv.Perm (C.Slot n)) (signs : Fin n→Fin 2→Bool) : NetworkShape 0 where
  vertices := n
  arity _ := 4
  edges := n*2
  ports := (Equiv.sigmaCongrRight fun v=>F.ports (signs v)).trans (C.shape next).ports

def twistedNetwork {K : Type*} [Semiring K] (M : Signature K 4)
    (next : Equiv.Perm (C.Slot n)) (signs : Fin n→Fin 2→Bool) : Network K 0 where
  shape := twistedShape next signs
  vertex _ := M
  edge _ := Signature.disequality

theorem twisted_denote {K : Type*} [CommSemiring K] (M : Signature K 4)
    (next : Equiv.Perm (C.Slot n)) (signs : Fin n→Fin 2→Bool) :
    (twistedNetwork M next signs).denote Fin.elim0=
      (networkRows (fun v=>Tensor.reindex (F.ports (signs v)) M) next).denote Fin.elim0 := by
  classical
  unfold Network.denote
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg (fun t=>t*∏e : C.Slot n,Signature.disequality (z (e,false)) (z (e,true)))
  apply Finset.prod_congr rfl
  intro v _
  rfl

theorem twisted_lift {K : Type*} [CommSemiring K] (f : Signature K 2)
    (next : Equiv.Perm (C.Slot n)) (signs : Fin n→Fin 2→Bool) :
    (twistedNetwork (B.lift f) next signs).denote Fin.elim0=
      cycleValue (fun v z=>f (F.flipWord (signs v) z)) next := by
  rw [twisted_denote]
  simp_rw [F.lift_flip]
  exact denote_rows _ _

/-- Ordinary variable assignments, mixed polarities, and all unused variables. -/
theorem native_signed_value {K : Type*} [CommSemiring K] (f : Signature K 2)
    (scope : C.Slot n→Fin m) (signs : Fin n→Fin 2→Bool) :
    value (fun v z=>f (F.flipWord (signs v) z)) scope=
      (2 : K)^U.unusedCount scope*
        (twistedNetwork (B.lift f) (EOBinaryPlaneScan.next scope) signs).denote Fin.elim0 := by
  rw [twisted_lift,value_cycle]

def labels (next : Equiv.Perm (C.Slot n)) (signs : Fin n→Fin 2→Bool) :
    ClosedLabelling (twistedShape next signs) 1 1 (fun _=>4) where
  vertex _ := 0
  vertex_arity _ := rfl
  edge _ := 0

def query (next : Equiv.Perm (C.Slot n)) (signs : Fin n→Fin 2→Bool) :
    Holant.LocalDrafts.Hardness.EightVertexNonexception.Source.TargetInput := (labels next signs).validated

theorem query_counts (next : Equiv.Perm (C.Slot n)) (signs : Fin n→Fin 2→Bool) :
    (query next signs).val.vertices.length=n ∧ (query next signs).val.edges.length=n*2 := by
  constructor <;> simp [query,ClosedLabelling.validated,twistedShape]

theorem query_denote {K : Type*} [CommSemiring K] (M : Signature K 4)
    (next : Equiv.Perm (C.Slot n)) (signs : Fin n→Fin 2→Bool) :
    ((query next signs).val.realize (query next signs).property (fun _=>M)
      (fun _=>Signature.disequality)).denote Fin.elim0=(twistedNetwork M next signs).denote Fin.elim0 :=
  (labels next signs).denote_serialize (fun _=>M) (fun _=>Signature.disequality)

def endpoint (next : Equiv.Perm (C.Slot n)) (v : Fin n) (i : Fin 4) : C.Slot n×Bool :=
  ![(C.incidence v 0,false),(next (C.incidence v 0),true),
    (C.incidence v 1,false),(next (C.incidence v 1),true)] i

theorem endpoint_exact (next : Equiv.Perm (C.Slot n)) (v : Fin n) (i : Fin 4) :
    ClosedLabelling.closedPortEquiv (C.shape next) ⟨v,i⟩=endpoint next v i := by
  fin_cases i <;> rfl

/-- Exact row writer: polarity permutes only the four original incidence slots. -/
theorem query_rows (next : Equiv.Perm (C.Slot n)) (signs : Fin n→Fin 2→Bool) :
    (query next signs).val.vertices=List.ofFn (fun v : Fin n=>(0,
      List.ofFn (fun i : Fin 4=>let p := endpoint next v (F.ports (signs v) i);(p.1.val,p.2)))) := by
  unfold query ClosedLabelling.validated ClosedLabelling.serialize
  apply congrArg List.ofFn
  funext v
  apply Prod.ext
  · rfl
  dsimp only [Prod.snd]
  apply congrArg List.ofFn
  funext i
  change ((ClosedLabelling.closedPortEquiv (C.shape next) ⟨v,F.ports (signs v) i⟩).1.val,
    (ClosedLabelling.closedPortEquiv (C.shape next) ⟨v,F.ports (signs v) i⟩).2)=_
  rw [endpoint_exact]

theorem query_edges (next : Equiv.Perm (C.Slot n)) (signs : Fin n→Fin 2→Bool) :
    (query next signs).val.edges=List.replicate (n*2) 0 := by
  change List.ofFn (fun _ : Fin (n*2)=>(0 : Fin 1).val)=_
  simp

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneMixed
