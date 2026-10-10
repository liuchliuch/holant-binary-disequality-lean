import Holant.Complexity.UniversalPairReduction.Surgery.Choices

namespace Holant.Complexity.UniversalPairReduction.Surgery.Choice
open Smoothing
variable {K : Type*} [CommSemiring K]

def mapRows (f : RawEndpoint → RawEndpoint) (rows : List RawVertex) : List RawVertex :=
  rows.map fun row => (row.1,row.2.map f)

 theorem weight_congr (F : Table K) (a b : ℕ → Bool) (rows : List RawVertex)
    (h : ∀row∈rows,∀p∈row.2,bit a p=bit b p) : weight F a rows=weight F b rows := by
  unfold weight
  congr 1
  apply List.map_congr_left
  intro row hr
  unfold rowValue
  congr 1
  exact List.map_congr_left (h row hr)

 theorem weight_splice (F : Table K) (p q : RawEndpoint) (c : ℕ → Bool) (rows : List RawVertex)
    (hpq : p.1≠q.1) (hr : ∀row∈rows,∀r∈row.2,r≠p ∧ r≠q) :
    weight F (restore q.1 (forced p q c) c) rows =
      weight F c (mapRows (spliceEndpoint p q) rows) := by
  unfold weight mapRows
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro row hrow
  unfold rowValue
  simp only [Function.comp_apply,List.map_map]
  congr 1
  apply List.map_congr_left
  intro r hrr
  exact bit_splice p q r c hpq (hr row hrow r hrr).1 (hr row hrow r hrr).2

 theorem weight_loop (F : Table K) (e : ℕ) (d : Bool) (c : ℕ → Bool) (rows : List RawVertex)
    (hr : ∀row∈rows,∀p∈row.2,p.1≠e) :
    weight F (restore e d c) rows = weight F c (mapRows (removeLoopEndpoint e) rows) := by
  unfold weight mapRows
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro row hrow
  unfold rowValue
  simp only [Function.comp_apply,List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  exact bit_restore e d c p (hr row hrow p hp)

 theorem weight_extend_split (F : Table K) (m e : ℕ) (he : e<m)
    (d : Bool) (c : Fin (m-1) → Bool) (rows : List RawVertex)
    (hr : ∀row∈rows,∀p∈row.2,p.1<m) :
    weight F (extend ((splitEdge m e he).symm (d,c))) rows =
      weight F (restore e d (extend c)) rows := by
  apply weight_congr
  intro row hrow p hp
  unfold bit
  rw [extend_split m e he d c p.1 (hr row hrow p hp)]

 theorem evaluate_perm (F : Table K) (m : ℕ) {a b : List RawVertex} (h : a.Perm b) :
    evaluate F m a=evaluate F m b := by
  unfold evaluate
  apply Finset.sum_congr rfl
  intro c _
  exact weight_perm F _ h

end Holant.Complexity.UniversalPairReduction.Surgery.Choice
