import Holant.Proofs.Reductions.CanonicalFamily.Queries


noncomputable section
namespace Holant.LocalDrafts.Hardness.CanonicalFamily
open Holant.Tractable
set_option backward.isDefEq.respectTransparency false
open Holant.Algebraic Holant.Complexity RawClosedNetwork
open UniversalPairReduction.Surgery
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (hn : ∀ i, G i ≠ 0)

def read (f : AnySignature AlgebraicComplex) (bits : List Bool) : AlgebraicComplex :=
  f.2 (fun k => bits.getD k.val false)
theorem table_read (j : Fin (count G)) (bits : List Bool) :
    Choice.table (table G) j.val bits = read (signature G j) bits := by
  unfold Choice.table
  rw [dif_pos j.isLt]
  exact congrArg (fun f : AnySignature AlgebraicComplex => read f bits)
    (FactorSaturation.OriginalCodec.rootLookup_old (signature G) j)

theorem forward_row (i : Fin s) (bits : List Bool) :
    Choice.table G i.val bits = pivot G hn i * Choice.table (table G) (toKey G i).val bits := by
  rw [table_read,signature_toKey]
  have h := congrFun (recover G hn i) (fun k => bits.getD k.val false)
  simpa [Choice.table,i.isLt,read,key,Pi.smul_apply,smul_eq_mul] using h
theorem backward_row (j : Fin (count G)) (bits : List Bool) :
    Choice.table G (selected G j).val bits =
      pivot G hn (selected G j) * Choice.table (table G) j.val bits := by
  simpa only [toKey_selected] using forward_row G hn (selected G j) bits

namespace Relabel
variable {K : Type} [Field K] {m n : ℕ}
variable (σ : Fin m → Fin n) (F H : Choice.Table K) (p : Fin m → K)

/-- A local algebraic lemma, instantiated below with the proved literal table
equations. No graph/oracle reduction or runtime contract is an input. -/
theorem weight_scaled (rows : List RawVertex) (hb : ∀ v ∈ rows, v.1 < m)
    (ht : ∀ i : Fin m, ∀ bits, F i.val bits = p i * H (σ i).val bits)
    (z : ℕ → Bool) :
    Choice.weight F z rows =
      (rows.map (fun v => RootPreprocessing.OccurrenceProduct.total p v.1)).prod *
        Choice.weight H z (rows.map (row σ)) := by
  induction rows with
  | nil => simp [Choice.weight]
  | cons v rows ih =>
    have hi := hb v (by simp)
    have htail := ih (fun w hw => hb w (List.mem_cons_of_mem _ hw))
    have hv := ht ⟨v.1,hi⟩ (v.2.map (Choice.bit z))
    simp only [Choice.weight_cons,List.map_cons,List.prod_cons]
    rw [show Choice.rowValue F z v = p ⟨v.1,hi⟩ * Choice.rowValue H z (row σ v) by
      simpa [Choice.rowValue,row,label,hi] using hv,htail]
    simp only [RootPreprocessing.OccurrenceProduct.total,dif_pos hi]
    ring

theorem value_scaled {a c : ℕ → ℕ} (ha : ∀ i : Fin m, c (σ i).val = a i.val)
    (r : ExactSignatureTables.Input m 1 a)
    (ht : ∀ i : Fin m, ∀ bits, F i.val bits = p i * H (σ i).val bits) :
    Choice.evaluate F r.val.edges.length r.val.vertices =
      RootPreprocessing.OccurrenceProduct.value p r.val *
        Choice.evaluate H (input σ ha r).val.edges.length (input σ ha r).val.vertices := by
  unfold Choice.evaluate
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact weight_scaled σ F H p _
    (fun v hv => (((RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property).1 v hv).1) ht _

end Relabel

def sourceAmbient (r : Input (s:=s) (a:=a)) : AlgebraicComplex :=
  (r.val.realize r.property G RootPreprocessing.nativeX).denote Fin.elim0
def keyAmbient (r : KeyInput G) : AlgebraicComplex :=
  (r.val.realize r.property (table G) RootPreprocessing.nativeX).denote Fin.elim0

theorem forward_value (r : Input (s:=s) (a:=a)) :
    sourceAmbient G r = RootPreprocessing.OccurrenceProduct.value (pivot G hn) r.val *
      keyAmbient G (forwardQuery G r) := by
  unfold sourceAmbient keyAmbient RootPreprocessing.nativeX
  rw [Choice.denote_eq_evaluate,Choice.denote_eq_evaluate]
  exact Relabel.value_scaled (toKey G) (Choice.table G) (Choice.table (table G))
    (pivot G hn) (arity_toKey G) r (forward_row G hn)

theorem backward_value (r : KeyInput G) :
    sourceAmbient G (backwardQuery G r) =
      RootPreprocessing.OccurrenceProduct.value (fun j => pivot G hn (selected G j)) r.val * keyAmbient G r := by
  unfold sourceAmbient keyAmbient RootPreprocessing.nativeX
  rw [Choice.denote_eq_evaluate,Choice.denote_eq_evaluate]
  unfold Choice.evaluate
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  -- Run the same row induction in the reverse direction: the source value
  -- is evaluated on the INCLUDED rows, so no relabelled source is omitted.
  have ht : ∀ row ∈ r.val.vertices,
      Choice.rowValue (Choice.table G) (Choice.extend z) (Relabel.row (selected G) row) =
        RootPreprocessing.OccurrenceProduct.total (fun j => pivot G hn (selected G j)) row.1 *
          Choice.rowValue (Choice.table (table G)) (Choice.extend z) row := by
    intro row hm
    have hi := (((RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property).1 row hm).1
    simpa [Choice.rowValue,Relabel.row,Relabel.label,RootPreprocessing.OccurrenceProduct.total,hi] using
      backward_row G hn ⟨row.1,hi⟩ (row.2.map (Choice.bit (Choice.extend z)))
  change ((r.val.vertices.map (Relabel.row (selected G))).map _).prod = _
  rw [List.map_map]
  have he := List.map_congr_left ht
  dsimp only [Function.comp_def]
  rw [he,List.prod_map_mul] <;> rfl

end Holant.LocalDrafts.Hardness.CanonicalFamily
