import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Disjoint

/-! Counted (not support-valued) arity rank for the actual generated occurrence
schedule. Replacing one selected resource by any finite lower-arity family is
Dershowitz--Manna progress; deleting a binary resource is its empty case. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedOccurrenceWorklist
open Multiset
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def arityRank (weight : α → ℕ) (todo : Finset α) : Multiset ℕ := todo.val.map weight

theorem arityRank_erase_split (weight : α → ℕ) (todo : Finset α) (o : α) (pending : o ∈ todo) :
    arityRank weight todo = arityRank weight (todo.erase o) + {weight o} := by
  have he : o ::ₘ (todo.erase o).val = todo.val := by
    rw [Finset.erase_val]
    exact Multiset.cons_erase pending
  have hm := congrArg (Multiset.map weight) he
  simpa [arityRank,Multiset.map_cons,← Multiset.singleton_add,add_comm] using hm.symm

theorem arityRank_map (copy : α ↪ β) (oldWeight : α → ℕ) (newWeight : β → ℕ)
    (exact : ∀ o, newWeight (copy o) = oldWeight o) (todo : Finset α) :
    arityRank newWeight (todo.map copy) = arityRank oldWeight todo := by
  change (todo.val.map copy).map newWeight = todo.val.map oldWeight
  rw [Multiset.map_map]
  congr 1
  funext o
  exact exact o

theorem arityRank_disjUnion (weight : α → ℕ) (A B : Finset α) (hd : Disjoint A B) :
    arityRank weight (A.disjUnion B hd) = arityRank weight A + arityRank weight B :=
  Multiset.map_add _ _ _

/-- This concrete replacement lemma is used with the injective exact old-tree
copy map and ALL new addressed occurrences of the returned retained batch. -/
theorem replacement_decreases (oldWeight : α → ℕ) (newWeight : β → ℕ)
    (copy : α ↪ β) (exact : ∀ o, newWeight (copy o) = oldWeight o)
    (todo : Finset α) (o : α) (pending : o ∈ todo) (fresh : Finset β)
    (disjoint : Disjoint ((todo.erase o).map copy) fresh)
    (lower : ∀ q ∈ fresh, newWeight q < oldWeight o) :
    Multiset.IsDershowitzMannaLT
      (arityRank newWeight (((todo.erase o).map copy).disjUnion fresh disjoint))
      (arityRank oldWeight todo) := by
  refine ⟨arityRank oldWeight (todo.erase o),arityRank newWeight fresh,{oldWeight o},by simp,?_,?_,?_⟩
  · rw [arityRank_disjUnion,arityRank_map copy oldWeight newWeight exact]
  · exact arityRank_erase_split oldWeight todo o pending
  · intro n hn
    obtain ⟨q,hq,rfl⟩ := Multiset.mem_map.mp hn
    exact ⟨oldWeight o,Multiset.mem_singleton_self _,lower q hq⟩

theorem erasure_decreases (weight : α → ℕ) (todo : Finset α) (o : α) (pending : o ∈ todo) :
    Multiset.IsDershowitzMannaLT (arityRank weight (todo.erase o)) (arityRank weight todo) := by
  refine ⟨arityRank weight (todo.erase o),0,{weight o},by simp,by simp,?_,?_⟩
  · exact arityRank_erase_split weight todo o pending
  · simp

end Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedOccurrenceWorklist
