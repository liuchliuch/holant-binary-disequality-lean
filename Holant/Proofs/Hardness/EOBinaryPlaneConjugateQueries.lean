import Holant.Proofs.Hardness.EOBinaryPlaneConjugate
import Holant.Proofs.Hardness.EOBinaryPlaneMixed
import Holant.Proofs.Hardness.GeneralCSPUnused

/-! Actual original-table/native-X queries for mixed f and conjugate-f binary
constraint products. The source field K embeds explicitly in a common star-field
L. Every positive moment duplicates the marked occurrences; every unused declared
variable is restored by its exact power of two. This leaf proves semantic queries
and polynomial counts, and does not claim a physical interpolation programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneConjugateQueries
open Holant Holant.Complexity
open scoped BigOperators
namespace C
export EOBinaryPlaneCycles (Slot incidence)
end C
namespace S
export EOBinaryPlaneCSP (value)
end S
namespace U
export GeneralCSPUnused (unusedCount scan_cycle_value)
end U
namespace R
export EOBinaryPlaneRecords (query query_denote query_counts)
end R
namespace I
export EOBinaryPlaneConjugate (polynomial conjugate_moments degree_bound)
end I
set_option backward.isDefEq.respectTransparency false

variable {n t m : ℕ}

def scope (base : C.Slot n→Fin m) (marked : C.Slot t→Fin m) (k : ℕ) :
    C.Slot (n+t*k)→Fin m := fun e=>
  let q : Fin (n+t*k)×Fin 2 := finProdFinEquiv.symm e
  match finSumFinEquiv.symm q.1 with
  | .inl v=>base (C.incidence v q.2)
  | .inr v=>marked (C.incidence (finProdFinEquiv.symm v).1 q.2)

@[simp] theorem scope_base (base : C.Slot n→Fin m) (marked : C.Slot t→Fin m)
    (k : ℕ) (v : Fin n) (j : Fin 2) :
    scope base marked k (C.incidence (finSumFinEquiv (.inl v)) j)=base (C.incidence v j) := by
  simp only [scope,C.incidence,Equiv.symm_apply_apply]

@[simp] theorem scope_marked (base : C.Slot n→Fin m) (marked : C.Slot t→Fin m)
    (k : ℕ) (v : Fin t) (copy : Fin k) (j : Fin 2) :
    scope base marked k (C.incidence (finSumFinEquiv (.inr (finProdFinEquiv (v,copy)))) j)=
      marked (C.incidence v j) := by
  simp only [scope,C.incidence,Equiv.symm_apply_apply]

def row {r : ℕ} (s : C.Slot r→Fin m) (x : Fin m→Bool) (v : Fin r) : Fin 2→Bool :=
  ![x (s (C.incidence v 0)),x (s (C.incidence v 1))]

def product {K : Type*} [CommMonoid K] {r : ℕ} (f : Signature K 2)
    (s : C.Slot r→Fin m) (x : Fin m→Bool) : K := ∏v,f (row s x v)

theorem product_scope {K : Type*} [CommMonoid K] (f : Signature K 2)
    (base : C.Slot n→Fin m) (marked : C.Slot t→Fin m) (k : ℕ) (x : Fin m→Bool) :
    product f (scope base marked k) x=product f base x*(product f marked x)^k := by
  unfold product
  rw [←finSumFinEquiv.prod_comp (fun v=>f (row (scope base marked k) x v)),
    Fintype.prod_sum_type]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    simp only [row,scope_base]
  · rw [←finProdFinEquiv.prod_comp (fun v : Fin (t*k)=>
      f (row (scope base marked k) x (finSumFinEquiv (.inr v)))),Fintype.prod_prod_type]
    simp only [row,scope_marked,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    exact Finset.prod_pow _ _ _

def coefficients {K : Type*} (f : Signature K 2) : Fin 4→K :=
  ![f ![false,false],f ![false,true],f ![true,false],f ![true,true]]

def label (x : Fin 2→Bool) : Fin 4 := if x 0 then (if x 1 then 3 else 2) else if x 1 then 1 else 0

theorem coefficient_label {K : Type*} (f : Signature K 2) (x : Fin 2→Bool) :
    coefficients f (label x)=f x := by
  have hx : x=![x 0,x 1] := by funext j; fin_cases j <;> rfl
  rw [hx]
  cases x 0 <;> cases x 1 <;> rfl

variable {K L : Type*} [Field K] [Field L] [StarRing L]

def mixed (into : K→+*L) (f : Signature K 2)
    (base : C.Slot n→Fin m) (marked : C.Slot t→Fin m) : L :=
  ∑x : Fin m→Bool,into (product f base x)*star (into (product f marked x))

def query (base : C.Slot n→Fin m) (marked : C.Slot t→Fin m) (k : ℕ) :=
  R.query (EOBinaryPlaneScan.next (scope base marked k))

theorem query_counts (base : C.Slot n→Fin m) (marked : C.Slot t→Fin m) (k : ℕ) :
    (query base marked k).val.vertices.length=n+t*k ∧
      (query base marked k).val.edges.length=(n+t*k)*2 := R.query_counts _

def answer (f : Signature K 2) (base : C.Slot n→Fin m) (marked : C.Slot t→Fin m) (k : ℕ) : K :=
  ((query base marked k).val.realize (query base marked k).property
    (fun _=>EOBinaryPlaneCore.lift f) (fun _=>Signature.disequality)).denote Fin.elim0

omit [Field L] [StarRing L] in
theorem moment_query (f : Signature K 2) (base : C.Slot n→Fin m)
    (marked : C.Slot t→Fin m) (k : ℕ) :
    (∑x : Fin m→Bool,product f base x*(product f marked x)^k)=
      (2 : K)^U.unusedCount (scope base marked k)*answer f base marked k := by
  have hv : S.value f (scope base marked k)=
      ∑x : Fin m→Bool,product f base x*(product f marked x)^k := by
    change (∑x,product f (scope base marked k) x)=_
    simp_rw [product_scope]
  rw [←hv,U.scan_cycle_value]
  simp only [answer,query,R.query_denote,EOBinaryPlaneCycles.denote_lift]

/-- At most (t+1)^4 positive-power original-field oracle moments suffice.
Each query is a concrete native-X cycle record over lift f alone. -/
theorem mixed_queries (into : K→+*L) (f : Signature K 2)
    (base : C.Slot n→Fin m) (marked : C.Slot t→Fin m) :
    mixed into f base marked=
      ∑k ∈ Finset.range (I.polynomial into (coefficients f) t).natDegree,
        (I.polynomial into (coefficients f) t).coeff (k+1)*
          into ((2 : K)^U.unusedCount (scope base marked (k+1))*answer f base marked (k+1)) := by
  have h := I.conjugate_moments into (coefficients f) t (product f base)
    (fun x v=>label (row marked x v))
  simp_rw [coefficient_label] at h
  change mixed into f base marked=
    ∑k ∈ Finset.range (I.polynomial into (coefficients f) t).natDegree,
      (I.polynomial into (coefficients f) t).coeff (k+1)*
        into (∑x : Fin m→Bool,product f base x*(product f marked x)^(k+1)) at h
  simp_rw [moment_query] at h
  exact h

theorem moment_bound (into : K→+*L) (f : Signature K 2)
    (base : C.Slot n→Fin m) (marked : C.Slot t→Fin m) (k : ℕ)
    (hk : k∈Finset.range (I.polynomial into (coefficients f) t).natDegree) :
    (query base marked (k+1)).val.vertices.length≤n+t*(t+1)^4 := by
  rw [(query_counts base marked (k+1)).1]
  have hd := I.degree_bound into (coefficients f) t
  have hk := Finset.mem_range.mp hk
  exact Nat.add_le_add_left (Nat.mul_le_mul_left t (by omega)) n

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneConjugateQueries
