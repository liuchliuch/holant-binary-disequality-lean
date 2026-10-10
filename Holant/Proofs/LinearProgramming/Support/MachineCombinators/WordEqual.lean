import Holant.Complexity.GraphPreprocessing.Primitive
import Holant.Complexity.BinaryArithmetic.Addition
import Holant.Complexity.BinaryCompose.Interface

/-! Literal bit-word equality on finite Boolean stacks. It consumes both words,
counts every bit/EOF test, preserves caller memory and unrelated tapes, and
returns to distinct equal/different labels. This compares actual serialized IDs
without any numeric-magnitude loop or host-language whole-word equality opcode. -/
open Holant.Complexity Holant.Complexity.GraphPreprocessing
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.WordEqual
open Turing BinaryArithmetic
open Turing.TM2.Stmt
variable {K Λ τ : Type} [DecidableEq K]
abbrev Memory (τ : Type) := Option Bool × (Bool × Option Bool × τ)
abbrev Config (K Λ τ : Type) := TM2.Cfg (fun _ : K => Bool) Λ (Memory τ)
abbrev Statement (K Λ τ : Type) := TM2.Stmt (fun _ : K => Bool) Λ (Memory τ)

def clean (same : Bool) (memory : τ) : Memory τ := (none, (same, none, memory))
def cfg (label : Λ) (same : Bool) (memory : τ) (tapes : K → List Bool) : Config K Λ τ :=
  ⟨some label, clean same memory, tapes⟩
def tapes2 (frame : K → List Bool) (left right : K) (a b : List Bool) : K → List Bool :=
  Function.update (Function.update frame left a) right b

def statement (left right : K) (loop good bad : Λ) : Statement K Λ τ :=
  pop left (fun v bit => (bit, v.2))
    (pop right (fun v bit => (v.1, (v.2.1, bit, v.2.2.2)))
      (branch (fun v => v.1.isSome || v.2.2.1.isSome)
        (load (fun v => clean (v.2.1 && (v.1 == v.2.2.1)) v.2.2.2) (goto (fun _ => loop)))
        (load (fun v => clean v.2.1 v.2.2.2) (goto (fun v => if v.2.1 then good else bad)))))

def ExecutesAt (step : Config K Λ τ → Option (Config K Λ τ)) (label : Λ)
    (stmt : Statement K Λ τ) : Prop :=
  ∀ state tapes, step ⟨some label, state, tapes⟩ = some (TM2.stepAux stmt state tapes)

def Runs (step : Config K Λ τ → Option (Config K Λ τ)) (a b : Config K Λ τ) (n : ℕ) : Prop :=
  (fun c => c.bind step)^[n] (some a) = some b

omit [DecidableEq K] in
theorem Runs.one {step : Config K Λ τ → Option (Config K Λ τ)} {a b : Config K Λ τ}
    (h : step a = some b) : Runs step a b 1 := h
omit [DecidableEq K] in
theorem Runs.trans {step : Config K Λ τ → Option (Config K Λ τ)}
    {a b c : Config K Λ τ} {n m : ℕ} (h : Runs step a b n) (h' : Runs step b c m) :
    Runs step a c (m + n) := by
  unfold Runs at *
  rw [Function.iterate_add_apply, h, h']

variable (left right : K) (hne : left ≠ right)
include hne in
@[simp] theorem tapes_left (frame : K → List Bool) (a b : List Bool) : tapes2 frame left right a b left = a := by
  simp [tapes2, hne]
@[simp] theorem tapes_right (frame : K → List Bool) (a b : List Bool) : tapes2 frame left right a b right = b := by
  simp [tapes2]
include hne in
@[simp] theorem update_left (frame : K → List Bool) (a b word : List Bool) :
    Function.update (tapes2 frame left right a b) left word = tapes2 frame left right word b := by
  funext k
  by_cases hk : k = left
  · subst k; simp [tapes2, hne]
  · simp [tapes2, Function.update_apply, hk]
@[simp] theorem update_right (frame : K → List Bool) (a b word : List Bool) :
    Function.update (tapes2 frame left right a b) right word = tapes2 frame left right a word := by
  simp [tapes2, Function.update_idem]

variable (step : Config K Λ τ → Option (Config K Λ τ)) (loop good bad : Λ)
variable (hs : ExecutesAt step loop (statement left right loop good bad))
include hne hs

theorem step_pair (same x y : Bool) (memory : τ) (frame : K → List Bool) (a b : List Bool) :
    step (cfg loop same memory (tapes2 frame left right (x :: a) (y :: b))) =
      some (cfg loop (same && (x == y)) memory (tapes2 frame left right a b)) := by
  rw [cfg, hs]
  simp [statement, TM2.stepAux, cfg, clean, tapes_left left right hne, update_left left right hne]

theorem step_left (same x : Bool) (memory : τ) (frame : K → List Bool) (a : List Bool) :
    step (cfg loop same memory (tapes2 frame left right (x :: a) [])) =
      some (cfg loop false memory (tapes2 frame left right a [])) := by
  rw [cfg, hs]
  simp [statement, TM2.stepAux, cfg, clean, tapes_left left right hne, update_left left right hne]

theorem step_right (same y : Bool) (memory : τ) (frame : K → List Bool) (b : List Bool) :
    step (cfg loop same memory (tapes2 frame left right [] (y :: b))) =
      some (cfg loop false memory (tapes2 frame left right [] b)) := by
  rw [cfg, hs]
  simp [statement, TM2.stepAux, cfg, clean, tapes_left left right hne, update_left left right hne]

theorem step_done (same : Bool) (memory : τ) (frame : K → List Bool) :
    step (cfg loop same memory (tapes2 frame left right [] [])) =
      some (cfg (if same then good else bad) same memory (tapes2 frame left right [] [])) := by
  rw [cfg, hs]
  simp [statement, TM2.stepAux, cfg, clean, tapes_left left right hne, update_left left right hne]

/-- Equality is accumulated by finite bit comparisons, with exact actual runtime. -/
theorem compare_exact (same : Bool) (memory : τ) (frame : K → List Bool) (a b : List Bool) :
    Runs step (cfg loop same memory (tapes2 frame left right a b))
      (cfg (if same && decide (a = b) then good else bad) (same && decide (a = b)) memory
        (tapes2 frame left right [] [])) (max a.length b.length + 1) := by
  induction a generalizing b same with
  | nil =>
    induction b generalizing same with
    | nil => simpa using Runs.one (step_done left right hne step loop good bad hs same memory frame)
    | cons y b ih =>
      have h := (Runs.one (step_right left right hne step loop good bad hs same y memory frame b)).trans (ih false)
      simpa using h
  | cons x a ih =>
    cases b with
    | nil =>
      have h := (Runs.one (step_left left right hne step loop good bad hs same x memory frame a)).trans (ih false [])
      simpa using h
    | cons y b =>
      have h := (Runs.one (step_pair left right hne step loop good bad hs same x y memory frame a b)).trans
        (ih (same && (x == y)) b)
      have he : (x == y) = decide (x = y) := by cases x <;> cases y <;> rfl
      simpa [List.cons.injEq, Bool.and_assoc, Nat.succ_max_succ, he] using h

omit [DecidableEq K] hne hs in
@[simp] theorem statement_budget : TM2Cost.budget (statement (τ := τ) left right loop good bad) = 5 := rfl

end Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.WordEqual
