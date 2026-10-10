import Holant.Proofs.Recognition.UniformTensorDecisionSyntax
import Holant.Proofs.Recognition.UniformKPolynomial

/-!
# Physical original-RootCode tensor-recognition branch machines

The only runtime input is the old original-family RootCode word. The original
packer appends the prescribed literal I and positive square-root-of-two codes.
Every branch then executes one two-sided polynomial-system decision, with one
existential pivot inverse. The source values below index the correctness proof;
they are not inputs to the machine and do not choose its programme.
-/

namespace Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTensorDecisionBranch

open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open PolynomialDecision UniformTensorDecisionSyntax
noncomputable section
set_option backward.isDefEq.respectTransparency false

structure Data (s : ℕ) (arity : Fin s → ℕ) where
  input : OriginalFamilyInput.Input arity
  G : (i : Fin s) → Signature AlgebraicComplex (arity i)
  represented : ∀ i x, (input i x).Represents (G i x : ℂ)

variable {s : ℕ} (arity : Fin s → ℕ)

abbrev Count := UniformKPolynomial.Count arity

def original (d : Data s arity) : OriginalFamilyPackingMachine.Input :=
  OriginalFamilyPackingSource.fromSource arity d.input false

/-- `none` means original coordinates; `some o` means the prescribed inverse K/KX action. -/
def table (mode : Option Bool) (i : Fin s) (x : Fin (arity i) → Bool) : Expr (Count arity) :=
  match mode with
  | none => UniformKPolynomial.original arity i x
  | some false => UniformKPolynomial.native arity i x
  | some true => UniformKPolynomial.native arity i (fun j => !(x j))

def signature (mode : Option Bool) (d : Data s arity) (i : Fin s) : Signature AlgebraicComplex (arity i) :=
  match mode with
  | none => d.G i
  | some o => (TensorDecisionMatching.basis o).symm.action (d.G i)

theorem table_eval (mode : Option Bool) (d : Data s arity) (i : Fin s)
    (x : Fin (arity i) → Bool) :
    (table arity mode i x).eval (UniformKPolynomial.values arity d.G) = signature arity mode d i x := by
  cases mode with
  | none => exact UniformKPolynomial.original_eval arity d.G i x
  | some o =>
    cases o with
    | false => exact UniformKPolynomial.native_eval arity d.G i x
    | true =>
      change (UniformKPolynomial.native arity i (fun j => !(x j))).eval _ = _
      rw [UniformKPolynomial.native_eval]
      exact (TensorDecisionMatching.inverse_true_apply (d.G i) x).symm

/-- The semantic answer is defined by the actual two-sided root-system run. -/
def ground (e : Expr (Count arity)) (d : Data s arity) : Bool :=
  PolynomialDecision.answer (q:=0) (UniformKPolynomial.descriptors arity d.input)
    (UniformKPolynomial.valid arity d.G d.input d.represented) [e]

def groundMachine (e : Expr (Count arity)) : BinaryCompose.Machine :=
  OriginalFamilyPackingMachine.rootsComputes.machine.compose
    (PolynomialDecision.machine (q:=0) [e])

theorem ground_outputs (e : Expr (Count arity)) (d : Data s arity) :
    ∃ ticks, Nonempty (TM2OutputsInTime (groundMachine arity e).computer
      (OriginalFamilyPackingMachine.encoding.encode (original arity d))
      (some (encodingBoolBool.encode (ground arity e d))) ticks) := by
  obtain ⟨ticks,⟨right⟩⟩ := PolynomialDecision.source_outputs (q:=0)
    (UniformKPolynomial.descriptors arity d.input)
    (UniformKPolynomial.valid arity d.G d.input d.represented) [e]
  have left := OriginalFamilyPackingMachine.rootsComputes.outputs (original arity d)
  rw [original,OriginalFamilyPackingSource.roots_exact] at left
  exact ⟨_,⟨Machine.compose_correct _ _ _ _ _ _ _ left right⟩⟩

theorem ground_correct (e : Expr (Count arity)) (d : Data s arity) :
    ground arity e d = true ↔ e.eval (UniformKPolynomial.values arity d.G) = 0 := by
  rw [ground,PolynomialDecision.ground_correct _ _ (UniformKPolynomial.values arity d.G)
    (UniformKPolynomial.descriptors_represents arity d.G d.input d.represented)]
  have he := Expr.map_eval (algebraicClosure ℚ ℂ).val (UniformKPolynomial.values arity d.G) e
  change ((e.eval (UniformKPolynomial.values arity d.G) : AlgebraicComplex) : ℂ) =
    e.eval (fun i => (UniformKPolynomial.values arity d.G i : ℂ)) at he
  rw [←he]
  constructor
  · intro h; exact Subtype.ext h
  · intro h; exact congrArg (fun z : AlgebraicComplex => (z : ℂ)) h

variable {n : ℕ}

def branchAnswer (oneHot : Bool) (entries : (Fin n → Bool) → Expr (Count arity))
    (count : ℕ) (sizes : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (sizes i)) ≃ Fin n) (pivot : Fin n → Bool)
    (d : Data s arity) : Bool :=
  PolynomialDecision.answer (q:=1) (UniformKPolynomial.descriptors arity d.input)
    (UniformKPolynomial.valid arity d.G d.input d.represented)
    (branch oneHot entries count sizes ports pivot)

def branchMachine (oneHot : Bool) (entries : (Fin n → Bool) → Expr (Count arity))
    (count : ℕ) (sizes : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (sizes i)) ≃ Fin n) (pivot : Fin n → Bool) : BinaryCompose.Machine :=
  OriginalFamilyPackingMachine.rootsComputes.machine.compose
    (PolynomialDecision.machine (q:=1) (branch oneHot entries count sizes ports pivot))

theorem branch_outputs (oneHot : Bool) (entries : (Fin n → Bool) → Expr (Count arity))
    (count : ℕ) (sizes : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (sizes i)) ≃ Fin n) (pivot : Fin n → Bool)
    (d : Data s arity) : ∃ ticks,
      Nonempty (TM2OutputsInTime (branchMachine arity oneHot entries count sizes ports pivot).computer
        (OriginalFamilyPackingMachine.encoding.encode (original arity d))
        (some (encodingBoolBool.encode (branchAnswer arity oneHot entries count sizes ports pivot d))) ticks) := by
  obtain ⟨ticks,⟨right⟩⟩ := PolynomialDecision.source_outputs (q:=1)
    (UniformKPolynomial.descriptors arity d.input)
    (UniformKPolynomial.valid arity d.G d.input d.represented)
    (branch oneHot entries count sizes ports pivot)
  have left := OriginalFamilyPackingMachine.rootsComputes.outputs (original arity d)
  rw [original,OriginalFamilyPackingSource.roots_exact] at left
  exact ⟨_,⟨Machine.compose_correct _ _ _ _ _ _ _ left right⟩⟩

theorem branch_correct (oneHot : Bool) (entries : (Fin n → Bool) → Expr (Count arity))
    (count : ℕ) (sizes : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (sizes i)) ≃ Fin n) (pivot : Fin n → Bool)
    (d : Data s arity) :
    branchAnswer arity oneHot entries count sizes ports pivot d = true ↔
      BranchTest oneHot (fun x => (entries x).eval (UniformKPolynomial.values arity d.G))
        count sizes ports pivot := by
  rw [branchAnswer,PolynomialDecision.answer_correct _ _ (UniformKPolynomial.values arity d.G)
    (UniformKPolynomial.descriptors_represents arity d.G d.input d.represented)]
  rw [branch_solutions_iff]
  have he : (fun x => (entries x).eval (fun i => (UniformKPolynomial.values arity d.G i : ℂ))) =
      (fun x => (((entries x).eval (UniformKPolynomial.values arity d.G) : AlgebraicComplex) : ℂ)) := by
    funext x
    exact (Expr.map_eval (algebraicClosure ℚ ℂ).val (UniformKPolynomial.values arity d.G) (entries x)).symm
  rw [he]
  exact branchTest_map_iff (algebraicClosure ℚ ℂ).val.toRingHom Subtype.val_injective _ _ _ _ _ _


end
end Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTensorDecisionBranch
