import Holant.Proofs.Recognition.PolynomialDecision
import Holant.Proofs.Algorithms.TransformRecognition.OriginalFamilyPackingSource
import Holant.Proofs.Algorithms.KSourceTransport

/-!
# Uniform original-RootCode tests of prescribed K-inverse entries

A single rational expression is emitted for each prescribed output entry.
The original input root descriptors are copied; the established numerical I and
POSITIVE sqrt(2) descriptors are physically appended by the old packer. No root
orientation, field, transformed coefficients, common basis or desired answer is
supplied or selected from the input values. The same two-sided search programme
runs for every legal family of these fixed arities. Its answer distinguishes
zero from nonzero at the exact normalized source K-inverse entry.
-/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.UniformKPolynomial
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.MainChain
open TransformRecognition
open PolynomialDecision
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} (arity : Fin s → ℕ)

abbrev Count := OriginalAffineSystem.Entries arity+2

def imaginary : Expr (Count arity) := .variable (Fin.natAdd (OriginalAffineSystem.Entries arity) 0)
def sqrt : Expr (Count arity) := .variable (Fin.natAdd (OriginalAffineSystem.Entries arity) 1)

def inverseMatrix (a b : Bool) : Expr (Count arity) :=
  .mul (.mul (.constant (1/2)) (sqrt arity))
    (if b then (if a then imaginary arity else .neg (imaginary arity)) else .constant 1)

def original (i : Fin s) (x : Fin (arity i) → Bool) : Expr (Count arity) :=
  .variable (Fin.castAdd 2 (OriginalAffineSystem.entryIndex arity (.inl i) x))

def native (i : Fin s) (x : Fin (arity i) → Bool) : Expr (Count arity) :=
  Expr.sum ((SparseTransform.allWords (arity i)).map (fun y =>
    .mul (Expr.product (List.ofFn (fun j => inverseMatrix arity (x j) (y j))))
      (original arity i y)))

variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i))
def values : Fin (Count arity) → AlgebraicComplex :=
  Fin.addCases (OriginalFamilyInput.values arity G false) ![imaginaryUnit,sqrtTwo]

theorem imaginary_eval : (imaginary arity).eval (values arity G)=imaginaryUnit := by
  simp [imaginary,Expr.eval,values]
theorem sqrt_eval : (sqrt arity).eval (values arity G)=sqrtTwo := by
  simp [sqrt,Expr.eval,values]

theorem inverse_eval (a b : Bool) :
    (inverseMatrix arity a b).eval (values arity G)=KInverse a b := by
  have hhalf : sqrtTwo*(2 : AlgebraicComplex)⁻¹=sqrtTwo⁻¹ := by
    apply (mul_left_cancel₀ sqrtTwo_ne_zero)
    calc
      sqrtTwo*(sqrtTwo*(2 : AlgebraicComplex)⁻¹)=1 := by
        rw [←mul_assoc,←pow_two,sqrtTwo_sq]
        norm_num
      _ = sqrtTwo*sqrtTwo⁻¹ := (mul_inv_cancel₀ sqrtTwo_ne_zero).symm
  cases a <;> cases b <;>
    simp [inverseMatrix,Expr.eval,imaginary_eval,sqrt_eval,KInverse,hhalf,div_eq_mul_inv,mul_comm]

theorem original_eval (i : Fin s) (x : Fin (arity i) → Bool) :
    (original arity i x).eval (values arity G)=G i x := by
  simp only [original,Expr.eval,values,Fin.addCases_left]
  exact congrFun (congrFun (OriginalFamilyInput.sourceVertex_values arity G false) i) x

theorem native_eval (i : Fin s) (x : Fin (arity i) → Bool) :
    (native arity i x).eval (values arity G)=sourceKBasis.symm.action (G i) x := by
  simp only [native,Expr.eval_sum,List.map_map,Function.comp_def,Expr.eval,
    Expr.eval_product,List.map_ofFn,List.prod_ofFn,inverse_eval,original_eval]
  rw [SparseTransform.sum_allWords]
  rfl

variable (input : OriginalFamilyInput.Input arity)
variable (hG : ∀ i x, (input i x).Represents (G i x : ℂ))

def descriptors : Fin (Count arity) → RootCode :=
  OriginalVariableLayout.descriptors (OriginalFamilyInput.pack arity input false)

include hG in
theorem descriptors_represents : ∀ i,
    (descriptors arity input i).Represents (values arity G i : ℂ) := by
  have hw := OriginalFamilyInput.pack_represents arity input G hG false
  have h := OriginalVariableLayout.descriptors_represents
    (OriginalFamilyInput.pack arity input false)
    (fun i => (OriginalFamilyInput.values arity G false i : ℂ)) hw
  have hv : (fun i => (values arity G i : ℂ)) =
      OriginalVariableLayout.boundValues (fun i => (OriginalFamilyInput.values arity G false i : ℂ)) := by
    funext i
    induction i using Fin.addCases with
    | left i => simp [values,OriginalVariableLayout.boundValues]
    | right i => fin_cases i <;> simp [values,OriginalVariableLayout.boundValues,StandardRootCodes.values]
  simpa only [←hv,descriptors] using h

def valid : OriginalSystemDecision.Valid (descriptors arity input) :=
  ⟨values arity G,descriptors_represents arity G input hG⟩

abbrev inputBytes := OriginalFamilyPackingMachine.encoding.encode
  (OriginalFamilyPackingSource.fromSource arity input false)

def answer (i : Fin s) (x : Fin (arity i) → Bool) : Bool :=
  PolynomialDecision.answer (q:=0) (descriptors arity input) (valid arity G input hG)
    [native arity i x]

/-- No family values occur in this programme definition. Arity, original label
and word select only a finite rational-expression programme. -/
def machine (i : Fin s) (x : Fin (arity i) → Bool) : BinaryCompose.Machine :=
  OriginalFamilyPackingMachine.rootsComputes.machine.compose
    (PolynomialDecision.machine (q:=0) [native arity i x])

theorem source_outputs (i : Fin s) (x : Fin (arity i) → Bool) :
    ∃ ticks, Nonempty (TM2OutputsInTime (machine arity i x).computer (inputBytes arity input)
      (some (encodingBoolBool.encode (answer arity G input hG i x))) ticks) := by
  obtain ⟨ticks,⟨right⟩⟩ := PolynomialDecision.source_outputs (q:=0)
    (descriptors arity input) (valid arity G input hG) [native arity i x]
  have left := OriginalFamilyPackingMachine.rootsComputes.outputs
    (OriginalFamilyPackingSource.fromSource arity input false)
  rw [OriginalFamilyPackingSource.roots_exact] at left
  exact ⟨_,⟨Machine.compose_correct _ _ _ _ _ _ _ left right⟩⟩

theorem answer_correct (i : Fin s) (x : Fin (arity i) → Bool) :
    answer arity G input hG i x=true ↔ sourceKBasis.symm.action (G i) x=0 := by
  rw [answer,PolynomialDecision.ground_correct _ _ (values arity G)
    (descriptors_represents arity G input hG)]
  have he := Expr.map_eval (algebraicClosure ℚ ℂ).val (values arity G) (native arity i x)
  change (((native arity i x).eval (values arity G) : AlgebraicComplex) : ℂ)=
    (native arity i x).eval (fun i => (values arity G i : ℂ)) at he
  rw [←he,native_eval]
  constructor
  · intro h; exact Subtype.ext h
  · intro h; exact congrArg (fun z : AlgebraicComplex => (z : ℂ)) h

theorem answer_false_iff (i : Fin s) (x : Fin (arity i) → Bool) :
    answer arity G input hG i x=false ↔ sourceKBasis.symm.action (G i) x≠0 := by
  have hb : ∀ b : Bool, b=false ↔ ¬b=true := by intro b; cases b <;> simp
  rw [hb,answer_correct]

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.UniformKPolynomial
