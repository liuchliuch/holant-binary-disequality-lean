import Holant.Proofs.Closure.GeneratedOccurrenceWorklistRank

/-! Finite disjoint preparation ledgers used by the real copied-root/new-label
partition. Old prepared resources are copied only; fresh addressed resources
are scheduled exactly once. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedOccurrenceWorklist
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem erase_insert_disjoint (todo done : Finset α) (hd : Disjoint todo done) (o : α) :
    Disjoint (todo.erase o) (insert o done) := by
  apply Finset.disjoint_left.mpr
  intro q hq hdone
  have he := Finset.mem_erase.mp hq
  rcases Finset.mem_insert.mp hdone with hsame | old
  · exact he.1 hsame
  · exact Finset.disjoint_left.mp hd he.2 old

theorem erase_insert_partition (todo done : Finset α) (hp : todo ∪ done = Finset.univ)
    (o : α) (ho : o ∈ todo) : (todo.erase o) ∪ insert o done = Finset.univ := by
  apply Finset.ext
  intro q
  simp only [Finset.mem_univ,iff_true,Finset.mem_union,Finset.mem_erase,Finset.mem_insert]
  have hq : q ∈ todo ∨ q ∈ done := by rw [← Finset.mem_union,hp]; exact Finset.mem_univ _
  by_cases he : q = o
  · exact .inr (.inl he)
  · rcases hq with ht | hd
    · exact .inl ⟨he,ht⟩
    · exact .inr (.inr hd)

theorem map_disjoint_fresh (copy : α ↪ β) (fresh : Finset β)
    (hd : Disjoint (Finset.univ.map copy) fresh) (A : Finset α) : Disjoint (A.map copy) fresh := by
  apply hd.mono_left
  exact Finset.map_subset_map.mpr (Finset.subset_univ A)

theorem replacement_disjoint (copy : α ↪ β) (fresh : Finset β)
    (hf : Disjoint (Finset.univ.map copy) fresh) (todo done : Finset α)
    (hd : Disjoint todo done) (o : α)
    (newDisjoint : Disjoint ((todo.erase o).map copy) fresh) :
    Disjoint (((todo.erase o).map copy).disjUnion fresh newDisjoint) ((insert o done).map copy) := by
  apply Finset.disjoint_left.mpr
  intro q hq hdone
  obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hdone
  rcases Finset.mem_disjUnion.mp hq with old | new
  · obtain ⟨x,hx,hxy⟩ := Finset.mem_map.mp old
    have he := copy.injective hxy
    subst y
    exact Finset.disjoint_left.mp (erase_insert_disjoint todo done hd o) hx hy
  · exact Finset.disjoint_left.mp hf (Finset.mem_map.mpr ⟨y,Finset.mem_univ _,rfl⟩) new

theorem replacement_partition (copy : α ↪ β) (fresh : Finset β)
    (copied : Finset.univ.map copy ∪ fresh = Finset.univ) (todo done : Finset α)
    (hp : todo ∪ done = Finset.univ) (o : α) (ho : o ∈ todo)
    (newDisjoint : Disjoint ((todo.erase o).map copy) fresh) :
    (((todo.erase o).map copy).disjUnion fresh newDisjoint) ∪ ((insert o done).map copy) = Finset.univ := by
  apply Finset.ext
  intro q
  simp only [Finset.mem_univ,iff_true,Finset.mem_union,Finset.mem_disjUnion]
  have hq : q ∈ Finset.univ.map copy ∨ q ∈ fresh := by
    rw [← Finset.mem_union,copied]
    exact Finset.mem_univ _
  rcases hq with old | new
  · obtain ⟨x,_,rfl⟩ := Finset.mem_map.mp old
    have hx : x ∈ todo.erase o ∨ x ∈ insert o done := by
      rw [← Finset.mem_union,erase_insert_partition todo done hp o ho]
      exact Finset.mem_univ _
    rcases hx with ht | hd
    · exact .inl (.inl (Finset.mem_map.mpr ⟨x,ht,rfl⟩))
    · exact .inr (Finset.mem_map.mpr ⟨x,hd,rfl⟩)
  · exact .inl (.inr new)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedOccurrenceWorklist
