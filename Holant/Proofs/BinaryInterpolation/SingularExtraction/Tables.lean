import Holant.Proofs.BinaryInterpolation.SingularExtraction.GroupedQuery
import Holant.Proofs.BinaryInterpolation.SingularExtraction.PowerGadgets


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Tables
open Holant Holant.Complexity
open Holant.Complexity.UniversalPairReduction.Surgery

variable {K : Type*} [CommSemiring K]

def typed (F : Choice.Table K) (s : ℕ) (arity : ℕ → ℕ) :
    (i : Fin s) → Signature K (arity i.val) := fun i x => F i.val (List.ofFn x)

theorem ofFn_getD {α : Type*} (bits : List α) (default : α) (n : ℕ) (hn : bits.length = n) :
    List.ofFn (fun i : Fin n => bits.getD i.val default) = bits := by
  subst n
  convert List.ofFn_get bits using 1
  congr 1
  funext i
  simp [List.getD_eq_getElem, i.isLt]

/-- The exponential sum appears only in this semantic identity, never in a
purported polynomial-time evaluator. -/
theorem denote_eq_evaluate (F : Choice.Table K) {s : ℕ} {arity : ℕ → ℕ}
    (r : RawClosedNetwork) (hr : r.WellFormed s 1 arity) :
    (r.realize hr (typed F s arity) (fun _ => Signature.disequality)).denote Fin.elim0 =
      Choice.evaluate F r.edges.length r.vertices := by
  rw [Choice.denote_eq_evaluate]
  unfold Choice.evaluate
  apply Finset.sum_congr rfl
  intro c _
  unfold Choice.weight
  congr 1
  apply List.map_congr_left
  intro row hrow
  have H := (RawGrouping.wellFormed_iff_members s 1 arity r).mp hr
  unfold Choice.rowValue Choice.table
  rw [dif_pos (H.1 row hrow).1]
  unfold typed
  rw [ofFn_getD _ false _ (by simpa using (H.1 row hrow).2)]

def adjoinedArity (s : ℕ) (arity : ℕ → ℕ) (k l : ℕ) (i : ℕ) : ℕ :=
  if i = s then k else if i = s+1 then l else arity i

def familyTable {s : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature K (arity i.val)) (u v : Bool → K) : Choice.Table K :=
  RawGrouping.withPower (RawGrouping.withPower (Choice.table G) s u) (s+1) v

theorem familyTable_old {s : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature K (arity i.val)) (u v : Bool → K)
    (i : Fin s) (bits : List Bool) :
    familyTable G u v i.val bits = G i (fun j => bits.getD j.val false) := by
  have h₁ : i.val ≠ s := Nat.ne_of_lt i.isLt
  have h₂ : i.val ≠ s+1 := by omega
  simp [familyTable, GroupedQuery.table, RawGrouping.withPower, h₁, h₂,
    Choice.table, i.isLt]

@[simp] theorem familyTable_left {s : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature K (arity i.val)) (u v : Bool → K) (bits : List Bool) :
    familyTable G u v s bits = (bits.map u).prod := by
  simp [familyTable, GroupedQuery.table, RawGrouping.withPower]

@[simp] theorem familyTable_right {s : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature K (arity i.val)) (u v : Bool → K) (bits : List Bool) :
    familyTable G u v (s+1) bits = (bits.map v).prod := by
  simp [familyTable, GroupedQuery.table, RawGrouping.withPower]

theorem typed_old {s : ℕ} {arity A : ℕ → ℕ}
    (G : (i : Fin s) → Signature K (arity i.val)) (u v : Bool → K)
    (i : Fin s) (ha : A i.val = arity i.val) (x : Fin (A i.val) → Bool) :
    typed (familyTable G u v) (s+2) A ⟨i.val, by omega⟩ x =
      G i (fun j => x (Fin.cast ha.symm j)) := by
  unfold typed
  rw [familyTable_old]
  congr 1
  funext j
  have hj : j.val < A i.val := by simpa [ha] using j.isLt
  simp only [List.getD_eq_getElem, List.length_ofFn, hj, ↓reduceDIte, List.getElem_ofFn]
  rfl

theorem typed_left {s : ℕ} {arity A : ℕ → ℕ}
    (G : (i : Fin s) → Signature K (arity i.val)) (u v : Bool → K)
    (x : Fin (A s) → Bool) :
    typed (familyTable G u v) (s+2) A ⟨s, by omega⟩ x =
      Signature.unaryPower u (A s) x := by
  simp [typed, Signature.unaryPower, List.map_ofFn, List.prod_ofFn]

theorem typed_right {s : ℕ} {arity A : ℕ → ℕ}
    (G : (i : Fin s) → Signature K (arity i.val)) (u v : Bool → K)
    (x : Fin (A (s+1)) → Bool) :
    typed (familyTable G u v) (s+2) A ⟨s+1, by omega⟩ x =
      Signature.unaryPower v (A (s+1)) x := by
  simp [typed, Signature.unaryPower, List.map_ofFn, List.prod_ofFn]

theorem changed_adjoined (s : ℕ) (arity : ℕ → ℕ) (k l : ℕ) :
    RawGrouping.changedArity (RawGrouping.changedArity (adjoinedArity s arity 1 1) s k) (s+1) l =
      adjoinedArity s arity k l := by
  funext i
  by_cases hi : i < s <;> by_cases hs : i = s <;> by_cases ht : i = s+1 <;>
    simp_all [RawGrouping.changedArity, adjoinedArity]
  all_goals omega

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Tables
