import Holant.Algebraic.RationalEncoding
import Mathlib.Logic.Encodable.Pi


namespace Holant.LocalDrafts.EffectiveAlgebraic

/-- One explicit code, possibly rejected by the decoder. -/
def tupleAt {α : Type} [Encodable α] (n k : ℕ) : Option (Fin n → α) :=
  Encodable.decode (α := Fin n → α) k

/-- Finite code height, inclusive. Invalid codes are discarded. -/
def tuplesThrough {α : Type} [Encodable α] (n height : ℕ) : List (Fin n → α) :=
  (List.range (height + 1)).filterMap (tupleAt n)

@[simp] theorem tupleAt_encode {α : Type} [Encodable α] {n : ℕ}
    (v : Fin n → α) : tupleAt n (Encodable.encode v) = some v :=
  Encodable.encodek v

theorem mem_tuplesThrough_iff {α : Type} [Encodable α] {n height : ℕ}
    (v : Fin n → α) :
    v ∈ tuplesThrough n height ↔ ∃ k ≤ height, tupleAt n k = some v := by
  simp only [tuplesThrough, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨k, hk, hv⟩
    exact ⟨k, by omega, hv⟩
  · rintro ⟨k, hk, hv⟩
    exact ⟨k, by omega, hv⟩

/-- Every tuple occurs by its actual natural-number code, including dimension 0. -/
theorem tuplesThrough_complete {α : Type} [Encodable α] {n : ℕ}
    (v : Fin n → α) : v ∈ tuplesThrough n (Encodable.encode v) :=
  (mem_tuplesThrough_iff v).mpr ⟨_, le_rfl, tupleAt_encode v⟩

theorem tuplesThrough_mono {α : Type} [Encodable α] {n a b : ℕ}
    (hab : a ≤ b) :
    ∀ v ∈ (tuplesThrough n a : List (Fin n → α)), v ∈ tuplesThrough n b := by
  intro v hv
  obtain ⟨k, hk, hv⟩ := (mem_tuplesThrough_iff v).mp hv
  exact (mem_tuplesThrough_iff v).mpr ⟨k, hk.trans hab, hv⟩

end Holant.LocalDrafts.EffectiveAlgebraic
