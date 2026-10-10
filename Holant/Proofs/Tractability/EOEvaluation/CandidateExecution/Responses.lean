import Holant.Proofs.Tractability.EOEvaluation.CandidateExecution.Catalogue


namespace Holant.LocalDrafts.Tractability.EOEvaluation.CandidateExecution.Responses
set_option backward.isDefEq.respectTransparency false
open Computability Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing AffineMachine LocalAffineMachine.Relabel FixedGadgetSubstitution.Compiler
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ}
abbrev Input := Source.Input (s := s) (arity := arity) × List Bool
def inputEncoding := pairEncoding (Source.inputEncoding (s := s) (arity := arity)) WordLookup.wordEncoding
def source : Computes (inputEncoding (s := s) (arity := arity)) Source.inputEncoding Prod.fst := Wiring.firstComputes _ _
def bits : Computes (inputEncoding (s := s) (arity := arity)) WordLookup.wordEncoding Prod.snd := Wiring.secondComputes _ _

def valid (x : Input (s := s) (arity := arity)) : Bool :=
  decide (x.2.length = (RawColumns.columns x.1).length)
def validComputes : Computes (inputEncoding (s := s) (arity := arity)) encodingBoolBool valid :=
  (pairComputes (bits.andThen (WireLists.lengthComputes encodingBoolBool))
    (source.andThen MatrixCompiler.dimensionComputes)).andThen
      Holant.LocalDrafts.TraversalCompletion.RationalLP.Parsing.unaryEqual

def queryEncoding := pairEncoding (inputEncoding (s := s) (arity := arity)) RawColumns.columnEncoding
def hit (q : Input (s := s) (arity := arity) × RawColumns.Column) (j : ℕ) : Bool :=
  let c := (RawColumns.columns q.1.1).getD j (0, (0, []), 0)
  (decide (c.1 = q.2.1) && decide (c.2.2 = q.2.2.2)) && q.1.2.getD j false
def lookup (q : Input (s := s) (arity := arity) × RawColumns.Column) : Bool :=
  ((List.range (RawColumns.columns q.1.1).length).map (hit q)).any id

def lookupComputes : Computes (queryEncoding (s := s) (arity := arity)) encodingBoolBool lookup := by
  let input := Wiring.firstComputes (inputEncoding (s := s) (arity := arity)) RawColumns.columnEncoding
  let wanted := Wiring.secondComputes (inputEncoding (s := s) (arity := arity)) RawColumns.columnEncoding
  let ctx := Wiring.firstComputes (queryEncoding (s := s) (arity := arity)) UnaryBinary.unaryEncoding
  let j := Wiring.secondComputes (queryEncoding (s := s) (arity := arity)) UnaryBinary.unaryEncoding
  let col := AccessPrograms.get RawColumns.columnEncoding (0, (0, []), 0)
    (ctx.andThen (input.andThen (source.andThen RawColumns.computes))) j
  let vmatch := (pairComputes (col.andThen MatrixCells.vertexID)
    (ctx.andThen (wanted.andThen MatrixCells.vertexID))).andThen
      Holant.LocalDrafts.TraversalCompletion.RationalLP.Parsing.unaryEqual
  let wmatch := AccessPrograms.eqNat (col.andThen MatrixCells.wordID)
    (ctx.andThen (wanted.andThen MatrixCells.wordID))
  let bit := AccessPrograms.get encodingBoolBool false (ctx.andThen (input.andThen bits)) j
  exact (WireLists.tabulate (queryEncoding (s := s) (arity := arity)) encodingBoolBool _
    (input.andThen (source.andThen MatrixCompiler.dimensionComputes)) _
    (AccessPrograms.bool Bool.and (AccessPrograms.bool Bool.and vmatch wmatch) bit)).andThen ResidueCells.any

theorem lookup_exact (x : Input (s := s) (arity := arity)) (c : Source.Coordinate x.1) :
    lookup (x, ColumnOrder.encode x.1 c) = x.2.getD ((ColumnOrder.order x.1).symm c).val false := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    obtain ⟨b, hb, hbtrue⟩ := List.any_eq_true.mp h
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    have hj' := List.mem_range.mp hj
    have hc : (RawColumns.columns x.1).getD j (0, (0, []), 0) =
        ColumnOrder.encode x.1 (ColumnOrder.order x.1 ⟨j, hj'⟩) := by
      rw [List.getD_eq_get _ _ (⟨j, hj'⟩ : Fin (RawColumns.columns x.1).length)]
      exact ColumnOrder.get_order _ _
    have hh := hbtrue
    simp only [id_eq, hit, hc, Bool.and_eq_true, decide_eq_true_eq] at hh
    have he := (ColumnOrder.ids_iff x.1 _ c).mp hh.1
    have hi : (⟨j, hj'⟩ : Fin (RawColumns.columns x.1).length) =
        (ColumnOrder.order x.1).symm c := (ColumnOrder.order x.1).injective (by simpa using he)
    simpa only [← hi] using hh.2
  · intro h
    let j := (ColumnOrder.order x.1).symm c
    apply List.any_eq_true.mpr
    refine ⟨hit (x, ColumnOrder.encode x.1 c) j.val, List.mem_map.mpr ⟨j.val, List.mem_range.mpr j.isLt, rfl⟩, ?_⟩
    have hc : (RawColumns.columns x.1).getD j.val (0, (0, []), 0) = ColumnOrder.encode x.1 c := by
      rw [List.getD_eq_get _ _ j]
      simpa only [j, Equiv.apply_symm_apply] using ColumnOrder.get_order x.1 j
    change hit (x, ColumnOrder.encode x.1 c) j.val = true
    dsimp only [hit]
    rw [hc]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨True.intro, True.intro⟩, h⟩

abbrev LocalInput := Input (s := s) (arity := arity) × RawColumns.Vertex
def localEncoding := pairEncoding (inputEncoding (s := s) (arity := arity)) RawColumns.vertexEncoding
def mask (n : ℕ) (x : LocalInput (s := s) (arity := arity)) : PairingTemplates.Mask n :=
  fun k => lookup (x.1, x.2.1, x.2.2, k.val)

def maskComputes (n : ℕ) : Computes (localEncoding (s := s) (arity := arity))
    (PairingTemplates.inputEncoding n) (mask n) := by
  let input := Wiring.firstComputes (inputEncoding (s := s) (arity := arity)) RawColumns.vertexEncoding
  let row := Wiring.secondComputes (inputEncoding (s := s) (arity := arity)) RawColumns.vertexEncoding
  let v := row.andThen (Wiring.firstComputes UnaryBinary.unaryEncoding RawClosedNetwork.vertexEncoding)
  let record := row.andThen (Wiring.secondComputes UnaryBinary.unaryEncoding RawClosedNetwork.vertexEncoding)
  let bit (k : Fin (Fintype.card (Distribution.Word n))) :=
    (pairComputes input (pairComputes v (pairComputes record
      (constantComputes (localEncoding (s := s) (arity := arity)) encodingNatBool k.val)))).andThen lookupComputes
  refine recode (fixedListComputes (localEncoding (s := s) (arity := arity)) encodingBoolBool _ bit (List.finRange _)) id (fun _ => rfl) ?_
  intro x
  change (framedListEncoding encodingBoolBool).encode
    ((List.finRange (Fintype.card (Distribution.Word n))).map (mask n x)) =
      (framedListEncoding encodingBoolBool).encode (List.ofFn (mask n x))
  rw [List.ofFn_eq_map]

/-- Mathematical list of the required answers, not an executable LP oracle. -/
def truth (D : Source.Family s arity) (r : Source.Input (s := s) (arity := arity)) : List Bool := by
  classical
  exact List.ofFn (fun j : Fin (MatrixCompiler.raw D r).dimension =>
    decide (Relaxation.Candidate (Source.network D r) (ColumnOrder.order r j).1 (ColumnOrder.order r j).2))

theorem truth_valid (D : Source.Family s arity) (r : Source.Input (s := s) (arity := arity)) :
    valid (r, truth D r) = true := by simp [valid, truth, MatrixCompiler.raw]

theorem truth_at (D : Source.Family s arity) (r : Source.Input (s := s) (arity := arity))
    (j : Fin (MatrixCompiler.raw D r).dimension) :
    (truth D r).getD j.val false = true ↔ Holant.LocalDrafts.TraversalCompletion.RationalLP.Codec.Positive
      (MatrixCompiler.raw D r) j := by
  classical
  rw [truth, DensePrograms.getD_ofFn]
  simp only [decide_eq_true_eq]
  exact (MatrixRefinement.positive_iff D r j).symm

theorem mask_truth (D : Source.Family s arity) (r : Source.Input (s := s) (arity := arity))
    (v : Fin r.val.vertices.length) :
    mask (arity (r.val.vertices.get v).1) ((r, truth D r), v.val, r.val.vertices.get v) =
      CandidatePairing.mask D r v := by
  classical
  funext k
  let a := (Fintype.equivFin (Distribution.Word (arity (r.val.vertices.get v).1))).symm k
  have he : (v.val, r.val.vertices.get v, k.val) = ColumnOrder.encode r ⟨v, a⟩ := by
    simp [ColumnOrder.encode, a]
  change lookup ((r, truth D r), (v.val, r.val.vertices.get v, k.val)) = _
  rw [he]
  rw [lookup_exact (r, truth D r) ⟨v, a⟩]
  dsimp only [Prod.fst, Prod.snd]
  rw [truth, DensePrograms.getD_ofFn _ ((ColumnOrder.order r).symm ⟨v, a⟩) false]
  have horder := (ColumnOrder.order r).apply_symm_apply (⟨v, a⟩ : Source.Coordinate r)
  have hc := congrArg (fun c : Source.Coordinate r =>
    decide (Relaxation.Candidate (Source.network D r) c.1 c.2)) horder
  simpa only [CandidatePairing.mask, a, Source.network, RawClosedNetwork.realize,
    RawClosedNetwork.shape] using hc

end
end Holant.LocalDrafts.Tractability.EOEvaluation.CandidateExecution.Responses
