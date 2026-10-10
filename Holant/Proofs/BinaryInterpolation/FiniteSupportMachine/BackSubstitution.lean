import Holant.Proofs.BinaryInterpolation.FiniteSupportMachine.Codec


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine.BackSubstitution

open Computability Holant.Tractable AffinePhase TwoTranslate Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open EncodedTable (Row bitsEncoding rowEncoding)

abbrev FrameData := ℕ × (ℕ × Row)
def frameEncoding := pairEncoding UnaryBinary.unaryEncoding
  (pairEncoding UnaryBinary.unaryEncoding rowEncoding)
abbrev Query := FrameData × List Bool
def queryEncoding := pairEncoding frameEncoding bitsEncoding
def save {n : ℕ} (S : AffineSystem (n + 1)) (r : Fin S.rows) (j : Fin (n + 1)) : FrameData :=
  (n + 1, j.val, Codec.storedRow S r)

def beforeBit (x : Query) (k : ℕ) : Bool :=
  if k = x.1.2.1 then false else x.2.getD (if k = 0 then x.1.2.1 - 1 else k - 1) false
def before (x : Query) := (List.range x.1.1).map (beforeBit x)
def selectedBit (x : Query) := Bool.xor x.1.2.2.1 (DensePrograms.dot x.1.2.2.2 (before x))
def value (x : Query) := (List.range x.1.1).map
  (fun k => if k = x.1.2.1 then selectedBit x else beforeBit x k)

noncomputable def frame : Computes queryEncoding frameEncoding Prod.fst := Wiring.firstComputes _ _
noncomputable def word : Computes queryEncoding bitsEncoding Prod.snd := Wiring.secondComputes _ _
noncomputable def dimension := frame.andThen (Wiring.firstComputes _ _)
noncomputable def rest := frame.andThen (Wiring.secondComputes _ _)
noncomputable def column := rest.andThen (Wiring.firstComputes _ _)
noncomputable def row := rest.andThen (Wiring.secondComputes _ _)

noncomputable def beforeBitComputes : Computes (pairEncoding queryEncoding UnaryBinary.unaryEncoding)
    encodingBoolBool (fun x => beforeBit x.1 x.2) := by
  let old := Wiring.firstComputes queryEncoding UnaryBinary.unaryEncoding
  let k := Wiring.secondComputes queryEncoding UnaryBinary.unaryEncoding
  let j := old.andThen column
  let isPivot := (pairComputes k j).andThen (equalComputes UnaryBinary.unaryEncoding)
  let isZero := (pairComputes k (constantComputes _ UnaryBinary.unaryEncoding 0)).andThen
    (equalComputes UnaryBinary.unaryEncoding)
  let tailIndex := (ifComputes isZero j k).andThen Endpoints.unaryPredecessorComputes
  exact congrComputes (ifComputes isPivot (constantComputes _ encodingBoolBool false)
    (AccessPrograms.get encodingBoolBool false (old.andThen word) tailIndex))
    (fun x => by by_cases h : x.2 = 0 <;> simp [beforeBit, h])

noncomputable def beforeComputes : Computes queryEncoding bitsEncoding before :=
  WireLists.tabulate queryEncoding encodingBoolBool (fun x => x.1.1) dimension beforeBit beforeBitComputes

noncomputable def selectedComputes : Computes queryEncoding encodingBoolBool selectedBit := by
  let rhs := row.andThen (Wiring.firstComputes encodingBoolBool bitsEncoding)
  let coeffs := row.andThen (Wiring.secondComputes encodingBoolBool bitsEncoding)
  exact AccessPrograms.bool Bool.xor rhs ((pairComputes coeffs beforeComputes).andThen DensePrograms.dotComputes)

noncomputable def computes : Computes queryEncoding bitsEncoding value := by
  let old := Wiring.firstComputes queryEncoding UnaryBinary.unaryEncoding
  let k := Wiring.secondComputes queryEncoding UnaryBinary.unaryEncoding
  let isPivot := (pairComputes k (old.andThen column)).andThen (equalComputes UnaryBinary.unaryEncoding)
  exact WireLists.tabulate queryEncoding encodingBoolBool (fun x => x.1.1) dimension _
    (congrComputes (ifComputes isPivot (old.andThen selectedComputes) beforeBitComputes)
      (fun x => by simp))

@[simp] theorem value_length (x : Query) : (value x).length = x.1.1 := by simp [value]

theorem before_bit {n : ℕ} (S : AffineSystem (n + 1)) (r : Fin S.rows)
    (j k : Fin (n + 1)) (x : Word n) :
    beforeBit (save S r j, List.ofFn x) k.val = Fin.cons (α := fun _ => Bool) false x (Equiv.swap 0 j k) := by
  by_cases hkj : k = j
  · subst k; simp [beforeBit, save]
  · by_cases hk : k = 0
    · subst k
      cases j using Fin.cases with
      | zero => exact False.elim (hkj rfl)
      | succ t => simp [beforeBit, save, DensePrograms.getD_ofFn]
    · cases k using Fin.cases with
      | zero => exact False.elim (hk rfl)
      | succ t =>
        have hn : t.succ.val ≠ j.val := fun h => hkj (Fin.ext h)
        simp [beforeBit, save, hn, DensePrograms.getD_ofFn,
          Equiv.swap_apply_of_ne_of_ne hk hkj]
        simpa only [Fin.val_succ] using fun _ => hn

theorem before_word {n : ℕ} (S : AffineSystem (n + 1)) (r : Fin S.rows)
    (j : Fin (n + 1)) (x : Word n) :
    before (save S r j, List.ofFn x) = List.ofFn (permute j (Fin.cons false x)) := by
  rw [before, DensePrograms.range_map]
  congr 1; funext k; exact before_bit S r j k x

theorem selected_bit {n : ℕ} (S : AffineSystem (n + 1)) (r : Fin S.rows)
    (j : Fin (n + 1)) (hj : S.matrix r j = 1) (x : Word n) :
    selectedBit (save S r j, List.ofFn x) = Constraint.selectedBit S r j x := by
  apply bitValue_injective
  have hd : FiniteCore.bit2 (DensePrograms.dot (Codec.storedRow S r).2
      (before (save S r j, List.ofFn x))) = dot (Constraint.tailRow S r j) x := by
    rw [before_word]
    simp only [Codec.storedRow, DensePrograms.dot_exact, EncodedTable.bit2_residue, FiniteCore.dot_eq]
    simpa [rowDot, TwoTranslate.dot, bitValue] using Constraint.selected_row S r j hj false x
  change FiniteCore.bit2 (Bool.xor (Codec.storedRow S r).1
    (DensePrograms.dot (Codec.storedRow S r).2 (before (save S r j, List.ofFn x)))) = _
  rw [ConstraintRefinement.bit2_xor, hd]
  simp only [Codec.storedRow, EncodedTable.bit2_residue, Constraint.selectedBit,
    bitValue_residueBit, ConstraintRefinement.sub_two]

theorem value_exact {n : ℕ} (S : AffineSystem (n + 1)) (r : Fin S.rows)
    (j : Fin (n + 1)) (hj : S.matrix r j = 1) (x : Word n) :
    value (save S r j, List.ofFn x) = List.ofFn (FiniteCore.solve S r j x) := by
  rw [value, DensePrograms.range_map]
  congr 1; funext k
  change Fin (n + 1) at k
  simp only [FiniteCore.solve_eq, Constraint.solveMap, permute]
  by_cases hkj : k = j
  · subst k
    simp only [save, if_pos rfl, Equiv.swap_apply_right, Fin.cons_zero]
    exact selected_bit S r j hj x
  · have hv : k.val ≠ j.val := fun h => hkj (Fin.ext h)
    simp only [save, if_neg hv]
    change beforeBit (save S r j, List.ofFn x) k.val = _
    rw [before_bit]
    have hzero : Equiv.swap (0 : Fin (n + 1)) j k ≠ 0 := by
      intro h
      exact hkj ((Equiv.swap (0 : Fin (n + 1)) j).injective
        (h.trans (Equiv.swap_apply_right 0 j).symm))
    generalize Equiv.swap (0 : Fin (n + 1)) j k = t at *
    cases t using Fin.cases with
    | zero => exact False.elim (hzero rfl)
    | succ t => rfl

theorem reconstruct_holds {n : ℕ} (S : AffineSystem (n + 1)) (r : Fin S.rows)
    (j : Fin (n + 1)) (hj : S.matrix r j = 1) (x : Word n)
    (hx : (Holant.LocalDrafts.MainChain.LocalAffineSupportSolver.descend S r j).Holds x) :
    S.Holds (fun k => (value (save S r j, List.ofFn x)).getD k.val false) := by
  rw [value_exact S r j hj]
  simp only [DensePrograms.getD_ofFn]
  rw [Holant.LocalDrafts.MainChain.LocalAffineSupportSolver.descend_eq,
    AffineSystem.pullback_holds _ _ (Constraint.solveMap_affine S r j)] at hx
  simpa only [FiniteCore.solve_eq] using hx

theorem primitive_bound (x : Query) :
    primitiveCost computes.machine (computes.outputs x).steps
      (some (Turing.initList computes.machine.computer (queryEncoding.encode x))) ≤
        (primitivePolynomial computes).eval (queryEncoding.encode x).length :=
  computes_primitive_cost computes x

end Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine.BackSubstitution
