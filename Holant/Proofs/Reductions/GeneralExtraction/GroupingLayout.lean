import Holant.Proofs.Reductions.GeneralExtraction.RawFactorGrouping
import Holant.Proofs.BinaryInterpolation.SingularExtraction.GroupingMachine


namespace Holant.LocalDrafts.Hardness.GeneralExtraction.GroupingLayout
open Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open RawFactorGrouping

theorem selected_length (a : ℕ) (r : RawClosedNetwork) {s b : ℕ} {arity : ℕ → ℕ}
    (hr : r.WellFormed s b arity) :
    (RawGrouping.selected a r.vertices).length = occurrences a r * arity a := by
  apply GroupedWords.flatMap_length
  intro row hrow
  have hh := List.mem_filter.mp hrow
  have he : row.1 = a := by simpa using hh.2
  have H := (RawGrouping.wellFormed_iff_members _ _ _ _).mp hr
  simpa [he] using (H.1 row hh.1).2

theorem prefix_length (n k : ℕ) (rs : List RawVertex) (hk : k ≤ rs.length)
    (hn : ∀ row ∈ rs, row.2.length = n) :
    ((rs.take k).flatMap Prod.snd).length = k*n := by
  rw [GroupedWords.flatMap_length Prod.snd _
    (fun row hrow => hn row (List.mem_of_mem_take hrow)), List.length_take,
    Nat.min_eq_left hk]

theorem take_ports (n k : ℕ) (rs : List RawVertex) (hk : k ≤ rs.length)
    (hn : ∀ row ∈ rs, row.2.length = n) :
    (rs.flatMap Prod.snd).take (k*n) = (rs.take k).flatMap Prod.snd := by
  have he : rs.flatMap Prod.snd = (rs.take k).flatMap Prod.snd ++ (rs.drop k).flatMap Prod.snd := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [he, ← prefix_length n k rs hk hn, List.take_left]

theorem drop_ports (n k : ℕ) (rs : List RawVertex) (hk : k ≤ rs.length)
    (hn : ∀ row ∈ rs, row.2.length = n) :
    (rs.flatMap Prod.snd).drop (k*n) = (rs.drop k).flatMap Prod.snd := by
  have he : rs.flatMap Prod.snd = (rs.take k).flatMap Prod.snd ++ (rs.drop k).flatMap Prod.snd := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [he, ← prefix_length n k rs hk hn, List.drop_left]

/-- Even when leftover rows exist, the full q blocks agree byte for byte. -/
theorem packs_eq_blocks (a n k q : ℕ) (rs : List RawVertex) (hq : q*k ≤ rs.length)
    (hn : ∀ row ∈ rs, row.2.length = n) :
    packs a k q rs = RawGrouping.blocks a (k*n) q (rs.flatMap Prod.snd) := by
  induction q generalizing rs with
  | zero => rfl
  | succ q ih =>
    have hq' : q*k+k ≤ rs.length := by simpa only [Nat.succ_mul] using hq
    have hk : k ≤ rs.length := by omega
    rw [packs, RawGrouping.blocks, take_ports n k rs hk hn, drop_ports n k rs hk hn,
      ih _ (by rw [List.length_drop]; omega)
        (fun row hrow => hn row (List.mem_of_mem_drop hrow))]

theorem group_eq_indexed_blocks (a k : ℕ) (r : RawClosedNetwork)
    {s b : ℕ} {arity : ℕ → ℕ} (hr : r.WellFormed s b arity) :
    (group a k r).vertices = RawGrouping.keep a r.vertices ++
      RawGrouping.blocks a (k*arity a) (occurrences a r/k) (RawGrouping.selected a r.vertices) := by
  have H := (RawGrouping.wellFormed_iff_members _ _ _ _).mp hr
  have hn : ∀ row ∈ selectedRows a r.vertices, row.2.length = arity a := by
    intro row hrow
    have hh := List.mem_filter.mp hrow
    have he : row.1 = a := by simpa using hh.2
    simpa [he] using (H.1 row hh.1).2
  change _ ++ packs a k ((selectedRows a r.vertices).length/k) _ = _
  rw [packs_eq_blocks a (arity a) k _ _ (Nat.div_mul_le_self _ _) hn]
  rfl

end Holant.LocalDrafts.Hardness.GeneralExtraction.GroupingLayout
