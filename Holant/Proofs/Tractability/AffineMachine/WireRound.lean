import Holant.Proofs.Tractability.AffineMachine.FreeRewrite
import Holant.Proofs.Tractability.ProductMachine.Bytecode


namespace Holant.LocalDrafts.Tractability.AffineMachine.WireRound

open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open ProductMachine
noncomputable section

variable {s b : ℕ}
abbrev Label := RawCode.Label (s := s) (b := b)
abbrev State := BlockAggregation.Output (s := s) (b := b)
abbrev encoding := BlockAggregation.outputEncoding (s := s) (b := b)

def dead (_x : State (s := s) (b := b)) : State (s := s) (b := b) := ((0, [], 0, [], []), .zero)
def step (x : State (s := s) (b := b)) : State (s := s) (b := b) :=
  if x.1.1 = 0 then x else if PivotPrograms.badRows x.1 then dead x else
    if (PivotPrograms.selected x.1).1 then
      (ConstraintRewrite.value (x.1, (PivotPrograms.selected x.1).2), x.2)
    else (FreeRewrite.value x.1, .mul x.2 (.literal (.inr (.inr (FreeRewrite.headLinear x.1)))))

noncomputable def data : Computes (encoding (s := s) (b := b)) EncodedTable.encoding Prod.fst := Wiring.firstComputes _ _
noncomputable def accumulator : Computes (encoding (s := s) (b := b)) (Expr.encoding (FamilyField.labelEncoding (s := s) (b := b))) Prod.snd := Wiring.secondComputes _ _
noncomputable def dimension := (data (s := s) (b := b)).andThen EncodedTable.count

noncomputable def computes : Computes (encoding (s := s) (b := b)) encoding step := by
  let stopped := (pairComputes (dimension (s := s) (b := b)) (constantComputes encoding UnaryBinary.unaryEncoding 0)).andThen
    (equalComputes UnaryBinary.unaryEncoding)
  let pivot := (data (s := s) (b := b)).andThen PivotPrograms.computes
  let found := pivot.andThen (Wiring.firstComputes encodingBoolBool
    (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding))
  let indices := pivot.andThen (Wiring.secondComputes encodingBoolBool
    (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding))
  let constrained := pairComputes ((pairComputes (data (s := s) (b := b)) indices).andThen ConstraintRewrite.computes) (accumulator (s := s) (b := b))
  let multiplierLabel := ((data (s := s) (b := b)).andThen FreeRewrite.headComputes).andThen
    (ResidueCells.unary4 (FamilyField.labelEncoding (s := s) (b := b)) (fun q => (Sum.inr (Sum.inr q) : Label (s := s) (b := b))))
  let factor := multiplierLabel.andThen (Bytecode.literal (FamilyField.labelEncoding (s := s) (b := b)))
  let expr := Bytecode.finish (Bytecode.binary (encoding (s := s) (b := b)) (FamilyField.labelEncoding (s := s) (b := b)) true _ _
    ((accumulator (s := s) (b := b)).andThen (Bytecode.unfinish (FamilyField.labelEncoding (s := s) (b := b)))) factor)
  let free := pairComputes ((data (s := s) (b := b)).andThen FreeRewrite.computes) expr
  exact congrComputes (ifComputes stopped (identityComputes encoding)
    (ifComputes ((data (s := s) (b := b)).andThen PivotPrograms.badRowsComputes)
      (constantComputes encoding encoding ((0, [], 0, [], []), Expr.zero))
      (ifComputes found constrained free))) (fun x => by simp [step, dead])

def finish (x : State (s := s) (b := b)) : Expr (Label (s := s) (b := b)) :=
  if PivotPrograms.badRows x.1 then .zero else .mul x.2 (.literal (.inr (.inl (EncodedTable.constant x.1))))

noncomputable def finishComputes : Computes (encoding (s := s) (b := b))
    (Expr.encoding (FamilyField.labelEncoding (s := s) (b := b))) finish := by
  let phase := (((data (s := s) (b := b)).andThen EncodedTable.phaseData).andThen EncodedTable.phaseConstant).andThen
    (ResidueCells.unary4 (FamilyField.labelEncoding (s := s) (b := b)) (fun q => (Sum.inr (Sum.inl q) : Label (s := s) (b := b))))
  let expr := Bytecode.finish (Bytecode.binary (encoding (s := s) (b := b)) (FamilyField.labelEncoding (s := s) (b := b)) true _ _
    ((accumulator (s := s) (b := b)).andThen (Bytecode.unfinish (FamilyField.labelEncoding (s := s) (b := b))))
    (phase.andThen (Bytecode.literal (FamilyField.labelEncoding (s := s) (b := b)))))
  exact ifComputes ((data (s := s) (b := b)).andThen PivotPrograms.badRowsComputes)
    (constantComputes encoding (Expr.encoding (FamilyField.labelEncoding (s := s) (b := b))) Expr.zero) expr

theorem dimension_step (x : State (s := s) (b := b)) : (step x).1.1 ≤ x.1.1 - 1 := by
  unfold step dead
  split_ifs <;> simp_all [ConstraintRewrite.value, FreeRewrite.value]

theorem rows_step (x : State (s := s) (b := b)) : (step x).1.2.1.length ≤ max x.1.2.1.length 1 := by
  unfold step
  split_ifs
  · exact le_max_left _ _
  · simp [dead]
  · simpa [ConstraintRewrite.value] using (le_max_left x.1.2.1.length 1)
  · exact (FreeRewrite.rows_value x.1).trans (le_max_right _ _)

theorem expression_step (x : State (s := s) (b := b)) : (step x).2.size ≤ x.2.size + 2 := by
  unfold step dead
  split_ifs <;> simp [Expr.size] <;> omega

theorem stable (x : State (s := s) (b := b)) (h : x.1.1 = 0) : step x = x := by simp [step, h]

theorem dimension_iterate (x : State (s := s) (b := b)) (k : ℕ) : ((step^[k]) x).1.1 ≤ x.1.1 - k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := dimension_step ((step^[k]) x)
    omega

theorem padded (x : State (s := s) (b := b)) (k : ℕ) (h : x.1.1 ≤ k) :
    (step^[k]) x = (step^[x.1.1]) x := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  have hz : ((step^[x.1.1]) x).1.1 = 0 := by have h := dimension_iterate x x.1.1; omega
  have fixed (j : ℕ) : (step^[j]) ((step^[x.1.1]) x) = (step^[x.1.1]) x := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, stable _ hz]
  rw [Nat.add_comm x.1.1 j, Function.iterate_add_apply, fixed]

end
end Holant.LocalDrafts.Tractability.AffineMachine.WireRound
