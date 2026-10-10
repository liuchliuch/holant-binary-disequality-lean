import Holant.Proofs.Reductions.RootPreprocessing.ScalarProduct


noncomputable section
namespace Holant.LocalDrafts.Hardness.RootPreprocessing
open Holant.Tractable
set_option backward.isDefEq.respectTransparency false
open Holant.Algebraic Holant.Complexity RawClosedNetwork
open UniversalPairReduction.Surgery
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

theorem target_table (j : Fin (count G)) (bits : List Bool) :
    Choice.table (targetTable G) j.val bits =
      G (includeLabel G j) (fun k => bits.getD k.val false) := by
  unfold Choice.table
  rw [dif_pos j.isLt]
  exact congrArg (fun f : AnySignature AlgebraicComplex =>
    f.2 (fun k => bits.getD k.val false))
    (FactorSaturation.OriginalCodec.rootLookup_old (signature G) j)

theorem row_factor (row : RawVertex) (hi : row.1 < s)
    (hp : row.2.length = a row.1) (hn : G ⟨row.1,hi⟩ ≠ 0) (c : ℕ → Bool) :
    Choice.rowValue (Choice.table G) c row =
      scalarNat G row.1 * Choice.weight (Choice.table (targetTable G)) c (rowChunk G row) := by
  by_cases hk : keepNat G row.1
  · have hkeep : Keep G ⟨row.1,hi⟩ := (keepNat_fin G ⟨row.1,hi⟩).mp hk
    have ha : a row.1 ≠ 0 := Nat.ne_of_gt hkeep.1
    simp only [rowChunk,if_pos hk,Choice.weight,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,mul_one,Choice.rowValue]
    rw [compactNat_fin G ⟨row.1,hi⟩ hkeep,target_table,include_compact]
    simp [scalarNat,hi,ha,Choice.table]
  · have ha : a row.1 = 0 := by
      by_contra hz
      exact hk ⟨hi,⟨Nat.pos_of_ne_zero hz,hn⟩⟩
    have hports : row.2 = [] := List.eq_nil_of_length_eq_zero (hp.trans ha)
    simp [rowChunk,hk,Choice.weight,Choice.rowValue,Choice.table,scalarNat,hi,ha,hports]

theorem weight_factor (rows : List RawVertex)
    (hv : ∀ row ∈ rows, row.1 < s ∧ row.2.length = a row.1)
    (hn : ∀ row ∈ rows, ∀ hi : row.1 < s, G ⟨row.1,hi⟩ ≠ 0) (c : ℕ → Bool) :
    Choice.weight (Choice.table G) c rows =
      (rows.map (fun row => scalarNat G row.1)).prod *
        Choice.weight (Choice.table (targetTable G)) c (keptRows G rows) := by
  induction rows with
  | nil => simp [Choice.weight,keptRows]
  | cons row rows ih =>
    have hrow := hv row (by simp)
    have ht := ih (fun q hq => hv q (List.mem_cons_of_mem _ hq))
      (fun q hq => hn q (List.mem_cons_of_mem _ hq))
    rw [Choice.weight_cons,row_factor G row hrow.1 hrow.2 (hn row (by simp) hrow.1),ht]
    simp only [keptRows,List.flatMap_cons,Choice.weight,List.map_append,List.prod_append,
      List.map_cons,List.prod_cons]
    ring

def ambientValue (r : Input (s:=s) (a:=a)) : AlgebraicComplex :=
  (r.val.realize r.property G nativeX).denote Fin.elim0
def targetAmbient (r : TargetInput G) : AlgebraicComplex :=
  (r.val.realize r.property (targetTable G) nativeX).denote Fin.elim0

theorem clean_value (r : GoodInput G) :
    ambientValue G r.val = (scalar G r.val.val : AlgebraicComplex) * targetAmbient G (cleanQuery G r) := by
  unfold ambientValue targetAmbient Holant.LocalDrafts.Hardness.RootPreprocessing.nativeX
  rw [Choice.denote_eq_evaluate,Choice.denote_eq_evaluate,scalar_coe]
  change Choice.evaluate (Choice.table G) r.val.val.edges.length r.val.val.vertices =
    _ * Choice.evaluate (Choice.table (targetTable G)) r.val.val.edges.length (keptRows G r.val.val.vertices)
  unfold Choice.evaluate
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  exact weight_factor G _
    ((RawGrouping.wellFormed_iff_members _ _ _ _).mp r.val.property).1
    ((clean_iff G r.val).mp r.property) _

theorem zero_value (r : Input (s:=s) (a:=a)) (h : ¬ Clean G r.val) : ambientValue G r = 0 := by
  have hz : ¬ ∀ row ∈ r.val.vertices, ∀ hi : row.1 < s, G ⟨row.1,hi⟩ ≠ 0 :=
    fun hn => h ((clean_iff G r).mpr hn)
  push_neg at hz
  obtain ⟨row,hm,hi,hzero⟩ := hz
  unfold ambientValue Holant.LocalDrafts.Hardness.RootPreprocessing.nativeX
  rw [Choice.denote_eq_evaluate]
  apply Finset.sum_eq_zero
  intro c _
  apply List.prod_eq_zero_iff.mpr
  apply List.mem_map.mpr
  refine ⟨row,hm,?_⟩
  simp [Choice.rowValue,Choice.table,hi,hzero]

/-- Includes all-zero/nullary inputs, empty input, and repeated scalars. -/
theorem query_value (r : Input (s:=s) (a:=a)) :
    ambientValue G r = (context G r : AlgebraicComplex) * targetAmbient G (query G r) := by
  by_cases h : Clean G r.val
  · rw [query_clean G r h]
    simpa only [context,if_pos h] using clean_value G ⟨r,h⟩
  · simp [zero_value G r h,context,h]

@[simp] theorem empty_target_value : targetAmbient G (emptyQuery G) = 1 := by
  unfold targetAmbient Holant.LocalDrafts.Hardness.RootPreprocessing.nativeX
  rw [Choice.denote_eq_evaluate]
  simp [Choice.evaluate,Choice.weight,emptyQuery]

end Holant.LocalDrafts.Hardness.RootPreprocessing
