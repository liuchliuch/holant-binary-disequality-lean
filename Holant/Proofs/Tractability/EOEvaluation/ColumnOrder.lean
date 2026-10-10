import Holant.Proofs.Tractability.EOEvaluation.MatrixCompiler
import Mathlib.Data.List.NodupEquivFin


namespace Holant.LocalDrafts.Tractability.EOEvaluation.ColumnOrder
open Holant.Tractable Holant.Complexity
open FixedGadgetSubstitution.Compiler RawColumns
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ}
variable (r : Source.Input (s := s) (arity := arity))

def words (v : Fin r.val.vertices.length) :=
  List.ofFn (Fintype.equivFin (Word (arity (r.val.vertices.get v).1))).symm

def entries : List (Source.Coordinate r) :=
  (List.finRange r.val.vertices.length).sigma (words r)

def encode (c : Source.Coordinate r) : Column :=
  (c.1.val, r.val.vertices.get c.1,
    (Fintype.equivFin (Word (arity (r.val.vertices.get c.1).1)) c.2).val)

theorem nodup : (entries r).Nodup :=
  (List.nodup_finRange _).sigma (fun v =>
    List.nodup_ofFn_ofInjective (Fintype.equivFin (Word (arity (r.val.vertices.get v).1))).symm.injective)

theorem mem (c : Source.Coordinate r) : c ∈ entries r := by
  rcases c with ⟨v, a⟩
  simp only [entries, List.mem_sigma, List.mem_finRange, true_and, words, List.mem_ofFn]
  exact ⟨Fintype.equivFin _ a, (Fintype.equivFin _).symm_apply_apply a⟩

theorem columns_eq : columns r = (entries r).map (encode r) := by
  unfold columns
  rw [← finRange_values]
  simp only [List.flatMap_map, entries, List.sigma, List.map_flatMap, List.map_map]
  apply List.flatMap_congr
  intro v _
  rw [List.getD_eq_getElem _ _ v.isLt, vertexColumns_valid _ (r.property.1 v).1]
  have hcard (n : ℕ) : Fintype.card (Fin n → Bool)=2^n := by
    simpa only [Fintype.card_bool,Fintype.card_fin] using
      (Fintype.card_fun (α := Fin n) (β := Bool))
  simp [words, List.ofFn_eq_map, encode, localCount, Function.comp_def,
    RawColumns.Word, Distribution.Word, hcard]
  rw [hcard]

theorem length_eq : (columns r).length = (entries r).length := by
  rw [columns_eq, List.length_map]

/-- Its forward map is the literal column at the given physical offset. -/
def order : Fin (columns r).length ≃ Source.Coordinate r :=
  (finCongr (length_eq r)).trans
    (List.Nodup.getEquivOfForallMemList (entries r) (nodup r) (mem r))

theorem get_order (j : Fin (columns r).length) :
    (columns r).get j = encode r (order r j) := by
  simp only [columns_eq, List.get_eq_getElem, List.getElem_map]
  rfl

theorem ids_iff (a b : Source.Coordinate r) :
    (encode r a).1 = (encode r b).1 ∧ (encode r a).2.2 = (encode r b).2.2 ↔ a = b := by
  constructor
  · rintro ⟨hv, hw⟩
    rcases a with ⟨v, a⟩
    rcases b with ⟨w, b⟩
    have h : v = w := Fin.ext hv
    subst w
    have hab : a = b := (Fintype.equivFin _).injective (Fin.ext hw)
    subst b
    rfl
  · rintro rfl; exact ⟨rfl, rfl⟩

theorem encode_injective : Function.Injective (encode r) := by
  intro a b h
  exact (ids_iff r a b).mp ⟨congrArg Prod.fst h, congrArg (fun c : Column => c.2.2) h⟩

end
end Holant.LocalDrafts.Tractability.EOEvaluation.ColumnOrder
