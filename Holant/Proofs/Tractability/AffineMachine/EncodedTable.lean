import Holant.Proofs.Tractability.AffineMachine.SamplePrograms


namespace Holant.LocalDrafts.Tractability.AffineMachine.EncodedTable

set_option backward.isDefEq.respectTransparency false
open Computability Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open ProductMachine

abbrev Row := Bool × List Bool
abbrev Phase := ZMod 4 × (List (ZMod 4) × List (List (ZMod 4)))
abbrev Data := ℕ × (List Row × Phase)

def bitsEncoding := framedListEncoding encodingBoolBool
def rowEncoding := pairEncoding encodingBoolBool bitsEncoding
def rowsEncoding := framedListEncoding rowEncoding
def vectorEncoding := framedListEncoding ResidueCells.encoding4
def matrixEncoding := framedListEncoding vectorEncoding
def phaseEncoding := pairEncoding ResidueCells.encoding4 (pairEncoding vectorEncoding matrixEncoding)
def encoding := pairEncoding UnaryBinary.unaryEncoding (pairEncoding rowsEncoding phaseEncoding)

def store {n : ℕ} (T : Dense.Table n) : Data :=
  (n, List.ofFn (fun r => (decide (T.support.rhs r = 1),
    List.ofFn (fun j => decide (T.support.matrix r j = 1)))),
    T.constant, T.linear.toList, T.mixed.toList.map List.Vector.toList)

def support (d : Data) : AffineSystem d.1 where
  rows := d.2.1.length
  matrix r j := FiniteCore.bit2 ((d.2.1.get r).2.getD j.val false)
  rhs r := FiniteCore.bit2 (d.2.1.get r).1

def constant (d : Data) := d.2.2.1
def linear (d : Data) (j : ℕ) := d.2.2.2.1.getD j 0
def mixed (d : Data) (j k : ℕ) := (d.2.2.2.2.getD j []).getD k 0

def Regular (d : Data) : Prop :=
  (∀ r ∈ d.2.1, r.2.length = d.1) ∧ d.2.2.2.1.length = d.1 ∧
    d.2.2.2.2.length = d.1 ∧ (∀ row ∈ d.2.2.2.2, row.length = d.1) ∧
      ∀ j k : Fin d.1, j < k → mixed d j.val k.val = 0 ∨ mixed d j.val k.val = 2

def phase (d : Data) (h : Regular d) : QuadraticPhase d.1 :=
  ⟨constant d, fun j => linear d j.val, fun j k => mixed d j.val k.val, h.2.2.2.2⟩

def restore (d : Data) (h : Regular d) : Dense.Table d.1 := Dense.snapshot (support d) (phase d h)

theorem bit2_residue (a : ZMod 2) : FiniteCore.bit2 (decide (a = 1)) = a := by fin_cases a <;> rfl

theorem vector_getD {A : Type} {n : ℕ} (v : List.Vector A n) (i : Fin n) (d : A) :
    v.toList.getD i.val d = v.get i := by
  rw [List.getD_eq_getElem (l := v.toList) (d := d) (n := i.val) (by simpa using i.isLt)]
  rfl

theorem mapped_vector_getD {A B : Type} {n : ℕ} (v : List.Vector A n)
    (f : A → B) (i : Fin n) (d : B) :
    (v.toList.map f).getD i.val d = f (v.get i) := by
  rw [List.getD_eq_getElem (l := v.toList.map f) (d := d) (n := i.val) (by simpa using i.isLt),List.getElem_map]
  rfl

theorem vector_getElem {A : Type} {n : ℕ} (v : List.Vector A n)
    (i : ℕ) (h : i < v.toList.length) :
    v.toList[i] = v.get ⟨i, by simpa using h⟩ := rfl

theorem store_regular {n : ℕ} (T : Dense.Table n) : Regular (store T) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [store]
  · simp [store]
  · simp [store]
  · simp [store, List.mem_map]
  · intro j k hjk
    change ((T.mixed.toList.map List.Vector.toList).getD j.val []).getD k.val 0 = 0 ∨
      ((T.mixed.toList.map List.Vector.toList).getD j.val []).getD k.val 0 = 2
    rw [mapped_vector_getD, vector_getD]
    exact T.even_mixed j k hjk

theorem vector_reindex_ofFn {A : Type} {m n : ℕ} (h : m = n) (v : List.Vector A n) :
    HEq (List.Vector.ofFn (fun i : Fin m => v.get (Fin.cast h i))) v := by
  subst n
  simpa using heq_of_eq (List.Vector.ofFn_get v)

theorem restore_store {n : ℕ} (T : Dense.Table n) : restore (store T) (store_regular T) = T := by
  cases T with
  | mk m a b c l q h =>
    simp [restore, Dense.snapshot, support, phase, constant, linear, mixed, store,
      Dense.Table.support, bit2_residue, vector_getD, mapped_vector_getD,
      List.getD_eq_getElem, vector_getElem, List.Vector.ofFn_get]
    exact ⟨vector_reindex_ofFn (by simp) a, vector_reindex_ofFn (by simp) b⟩

noncomputable def count : Computes encoding UnaryBinary.unaryEncoding Prod.fst := Wiring.firstComputes _ _
noncomputable def rest := Wiring.secondComputes UnaryBinary.unaryEncoding (pairEncoding rowsEncoding phaseEncoding)
noncomputable def rows : Computes encoding rowsEncoding (fun d => d.2.1) := rest.andThen (Wiring.firstComputes _ _)
noncomputable def phaseData : Computes encoding phaseEncoding (fun d => d.2.2) := rest.andThen (Wiring.secondComputes _ _)
noncomputable def phaseConstant : Computes phaseEncoding ResidueCells.encoding4 Prod.fst := Wiring.firstComputes _ _
noncomputable def phaseRest := Wiring.secondComputes ResidueCells.encoding4 (pairEncoding vectorEncoding matrixEncoding)
noncomputable def phaseLinear := phaseRest.andThen (Wiring.firstComputes vectorEncoding matrixEncoding)
noncomputable def phaseMixed := phaseRest.andThen (Wiring.secondComputes vectorEncoding matrixEncoding)

end Holant.LocalDrafts.Tractability.AffineMachine.EncodedTable
