import Holant.Proofs.Tetrahedral.EvenCSPReduction.Data
import Mathlib.Data.List.Count
import Mathlib.Data.List.FinRange

/-! Literal constraint duplication turns arbitrary CSP occurrences into even
occurrences. Variables and every original port address remain unchanged;
this is the combinatorial entry for the squared-row hardness branch. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentOrdinarySquare
open Holant Holant.Complexity
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Ordinary validity before requiring the computed incidence counts to be even. -/
def Valid (s : ℕ) (a : ℕ → ℕ) (r : Raw) : Prop :=
  ∀ row ∈ r.factors, row.1<s ∧ row.2.length=a row.1 ∧ ∀ i ∈ row.2, i<r.variables

def duplicate (r : Raw) : Raw := ⟨r.variables,r.factors++r.factors⟩

theorem variables_same (r : Raw) : (duplicate r).variables=r.variables := rfl
theorem factors_twice (r : Raw) : (duplicate r).factors.length=2*r.factors.length := by
  simp [duplicate,two_mul]

theorem addresses_exact (r : Raw) : r.portList.map r.address=r.factors.flatMap Prod.snd := by
  have get_rows : (List.finRange r.factors.length).map r.factors.get=r.factors := by
    rw [←List.ofFn_eq_map,List.ofFn_get]
  calc
    _ = (List.finRange r.factors.length).flatMap (fun v => (r.factors.get v).2) := by
      simp only [Raw.portList,List.map_flatMap,List.map_map]
      congr 1
      funext v
      change (List.finRange (r.factors.get v).2.length).map (r.factors.get v).2.get=_
      rw [←List.ofFn_eq_map,List.ofFn_get]
    _ = _ := by
      simpa only [List.flatMap_map] using congrArg (fun rows => rows.flatMap Prod.snd) get_rows

theorem degree_flat (r : Raw) (i : ℕ) : r.degree i=(r.factors.flatMap Prod.snd).count i := by
  rw [←addresses_exact]
  simp only [Raw.degree,Raw.occurrences,List.count,List.countP_map,Function.comp_def]
  rw [List.countP_eq_length_filter]

theorem degree_twice (r : Raw) (i : ℕ) : (duplicate r).degree i=2*r.degree i := by
  rw [degree_flat,degree_flat]
  simp [duplicate,List.flatMap_append,List.count_append,two_mul]

theorem duplicate_valid {s : ℕ} {a : ℕ → ℕ} (r : Raw) (valid : Valid s a r) :
    (duplicate r).Valid s a := by
  have retained (row : Factor) (mem : row ∈ (duplicate r).factors) :
      row.1<s ∧ row.2.length=a row.1 ∧ ∀ i ∈ row.2, i<r.variables := by
    exact valid row (by simpa [duplicate,List.mem_append] using mem)
  refine ⟨?_,?_,?_⟩
  · intro v
    have h := retained ((duplicate r).factors.get v) (List.get_mem _ _)
    exact ⟨h.1,h.2.1⟩
  · intro p
    have h := retained ((duplicate r).factors.get p.1) (List.get_mem _ _)
    exact h.2.2 _ (List.get_mem _ _)
  · intro i _
    rw [degree_twice]
    exact even_two_mul _

def input {s : ℕ} {a : ℕ → ℕ} (r : Raw) (valid : Valid s a r) : Raw.Input s a :=
  ⟨duplicate r,duplicate_valid r valid⟩

section Semantics
variable {K : Type*} [CommSemiring K] {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (a i.val))

def rowValue (row : Factor) (x : ℕ → Bool) : K :=
  if h : row.1<s then G ⟨row.1,h⟩ (fun k => x (row.2.getD k.val 0)) else 0

def weight (rows : List Factor) (x : ℕ → Bool) : K :=
  (rows.map (fun row => rowValue G row x)).prod

def extend {n : ℕ} (x : Fin n → Bool) (i : ℕ) : Bool :=
  if h : i<n then x ⟨i,h⟩ else false

def value (r : Raw) : K := ∑x : Fin r.variables → Bool,weight G r.factors (extend x)

def square (i : Fin s) : Signature K (a i.val) := fun x => (G i x)^2

theorem square_row (row : Factor) (x : ℕ → Bool) :
    rowValue (square G) row x=(rowValue G row x)^2 := by
  unfold rowValue
  split_ifs <;> simp [square]

theorem square_weight (rows : List Factor) (x : ℕ → Bool) :
    weight (square G) rows x=(weight G rows x)^2 := by
  induction rows with
  | nil => simp [weight]
  | cons row rows ih =>
      simp only [weight,List.map_cons,List.prod_cons] at ih ⊢
      rw [square_row,ih,mul_pow]

theorem duplicate_value (r : Raw) : value G (duplicate r)=value (square G) r := by
  apply Finset.sum_congr rfl
  intro x _
  rw [square_weight]
  simp [weight,duplicate,List.map_append,List.prod_append,pow_two]

theorem typed_value (r : Raw.Input s a) : Raw.value G r=value G r.val := by
  apply Finset.sum_congr rfl
  intro x _
  change (∏v : Fin r.val.factors.length,G (Raw.label r v)
    (fun j => x (Raw.route r (Raw.portCast r v j))))=_
  calc
    _ = ∏v : Fin r.val.factors.length,rowValue G (r.val.factors.get v) (extend x) := by
      apply Finset.prod_congr rfl
      intro v _
      unfold rowValue
      rw [dif_pos (r.property.1 v).1]
      congr 1
      funext j
      have hl : j.val<(r.val.factors.get v).2.length := by
        rw [(r.property.1 v).2]
        exact j.isLt
      rw [List.getD_eq_getElem _ _ hl]
      have hp := r.property.2.1 (Raw.portCast r v j)
      simp only [Raw.address,Raw.portCast,Fin.val_cast,List.get_eq_getElem] at hp
      simp only [extend,dif_pos hp,Raw.route,Raw.address,Raw.portCast,List.get_eq_getElem,Fin.val_cast]
    _ = _ := by
      rw [←List.prod_ofFn]
      apply congrArg List.prod
      simpa only [weight,List.get_eq_getElem] using
        (List.ofFn_getElem_eq_map r.val.factors (fun row => rowValue G row (extend x)))

theorem duplicate_typed_value (r : Raw) (valid : Valid s a r) :
    Raw.value G (input r valid)=value (square G) r := by
  rw [typed_value]
  exact duplicate_value G r

/-- The exact value identity preserves even unused declared variables: the
assignment domain on both sides is literally the same finite Boolean cube. -/
theorem duplicate_assignment_domain (r : Raw) :
    (Fin (duplicate r).variables → Bool)=(Fin r.variables → Bool) := rfl
end Semantics

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentOrdinarySquare
end
