import Holant.Proofs.Tractability.EOEvaluation.EOConditionCertificate.LiteralTemplates
import Holant.Proofs.Algorithms.TransformRecognition.OriginalVariableLayout
import Holant.Proofs.Algorithms.TransformRecognition.SymbolicPhaseCoefficients
import Holant.Proofs.Algorithms.TransformRecognition.OriginalSystemMachine


namespace Holant.LocalDrafts.Tractability.EOEvaluation.EOConditionCertificate.LiteralAffine
open Turing Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Sparse Descriptors FixedFieldMachines
variable {n : ℕ}

abbrev Entries (n : ℕ) := (words n).length
abbrev Extra (n : ℕ) := OriginalVariableLayout.Extra (Entries n) 1
abbrev Width (n : ℕ) := OriginalVariableLayout.Width (Entries n) 1

def address (x : Word n) : Fin (Entries n) :=
  ⟨(words n).idxOf x,List.idxOf_lt_length_iff.mpr (SparseTransform.mem_allWords x)⟩

@[simp] theorem get_address (x : Word n) : (words n).get (address x)=x := List.idxOf_get _

def indexedInput (input : Word n → RootCode) : Fin (Entries n) → RootCode :=
  fun i => input ((words n).get i)
def original (x : Word n) : Fin (Width n) :=
  OriginalVariableLayout.original (Entries n) 1 (address x)
def scale : Fin (Width n) := OriginalVariableLayout.parameter (Entries n) 1 0
def imaginary : Fin (Width n) := OriginalVariableLayout.special (Entries n) 1 0
def identityValues : Fin 5 → ℚ := ![1,0,0,1,1]
def identityRow (j : Fin 5) : Poly (Width n) 1 :=
  sub (SparseTransform.variableCode RationalCompiler.data
    (OriginalVariableLayout.matrix (Entries n) 1 j))
    (RationalCompiler.constant (identityValues j))
def row (C : AffineNormalForm.Code n) (x : Word n) : Poly (Width n) 1 :=
  sub (SparseTransform.variableCode RationalCompiler.data (original x))
    (mul RationalCompiler.data (SparseTransform.variableCode RationalCompiler.data scale)
      (SymbolicPhaseCoefficients.affineCoefficient imaginary C x))
def body (C : AffineNormalForm.Code n) : List (Poly (Width n) 1) :=
  SparseTransform.guard RationalCompiler.data (Extra n) ::
    ((List.finRange 5).map identityRow ++ (words n).map (row C))

theorem guard_mem (C : AffineNormalForm.Code n) :
    SparseTransform.guard RationalCompiler.data (Extra n) ∈ body C := List.mem_cons_self ..

theorem body_length (C : AffineNormalForm.Code n) : (body C).length=6+2^n := by
  simp [body,SparseTransform.allWords_length]
  omega

noncomputable section

def values (f : Signature AlgebraicComplex n) : Fin (Entries n) → AlgebraicComplex :=
  fun i => f ((words n).get i)
def descriptorValues (f : Signature AlgebraicComplex n) :
    Fin (Entries n+2) → AlgebraicComplex :=
  Fin.addCases (values f) ![imaginaryUnit,sqrtTwo]

theorem descriptorValues_coe (f : Signature AlgebraicComplex n) :
    (fun i => (descriptorValues f i : ℂ)) =
      OriginalVariableLayout.boundValues (fun i => (values f i : ℂ)) := by
  funext i
  induction i using Fin.addCases with
  | left i => simp [descriptorValues,OriginalVariableLayout.boundValues]
  | right i =>
      fin_cases i <;> simp [descriptorValues,OriginalVariableLayout.boundValues,StandardRootCodes.values]

theorem descriptors_represents (input : Word n → RootCode) (f : Signature AlgebraicComplex n)
    (hf : ∀ x, (input x).Represents (f x : ℂ)) :
    ∀ i, (OriginalVariableLayout.descriptors (indexedInput input) i).Represents
      (descriptorValues f i : ℂ) := by
  have h := OriginalVariableLayout.descriptors_represents (indexedInput input)
    (fun i => (values f i : ℂ)) (fun i => hf ((words n).get i))
  simpa only [←descriptorValues_coe] using h

def valid (input : Word n → RootCode) (f : Signature AlgebraicComplex n)
    (hf : ∀ x, (input x).Represents (f x : ℂ)) :
    OriginalSystemDecision.Valid (OriginalVariableLayout.descriptors (indexedInput input)) :=
  ⟨descriptorValues f,descriptors_represents input f hf⟩

def Bound (f : Signature AlgebraicComplex n) (z : Fin (Width n) → ℂ) : Prop :=
  ∀ i, z (OriginalVariableLayout.binding (Entries n) 1 i)=
    OriginalVariableLayout.boundValues (fun j => (values f j : ℂ)) i

theorem row_eval (C : AffineNormalForm.Code n) (f : Signature AlgebraicComplex n)
    (z : Fin (Width n) → ℂ) (hz : Bound f z) (x : Word n) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z (row C x)=
      (f x : ℂ)-z scale*(AffineNormalForm.formula C 1 x : ℂ) := by
  have he : z (original x)=(f x : ℂ) := by
    simpa only [original,values,get_address] using
      OriginalVariableLayout.binding_original z (fun i => (values f i : ℂ)) hz (address x)
  have hi : z imaginary=Complex.I :=
    OriginalVariableLayout.binding_imaginary z (fun i => (values f i : ℂ)) hz
  unfold row
  change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
    (sub (SparseTransform.variableCode RationalCompiler.field.toArithmeticData (original x))
      (mul RationalCompiler.field.toArithmeticData
        (SparseTransform.variableCode RationalCompiler.field.toArithmeticData scale)
        (SymbolicPhaseCoefficients.affineCoefficient imaginary C x))) = _
  rw [SparseEvaluation.sub_eval,SparseEvaluation.variable_eval,SparseEvaluation.mul_eval,
    SparseEvaluation.variable_eval,he,SymbolicPhaseCoefficients.affineCoefficient_eval imaginary C x z hi]

def fill (f : Signature AlgebraicComplex n) (c : ℂ) : Fin (Width n) → ℂ :=
  OriginalVariableLayout.fill (fun j => (identityValues j : ℂ)) (fun _ => c)
    (fun i => (values f i : ℂ)) OriginalVariableLayout.constants

theorem fill_bound (f : Signature AlgebraicComplex n) (c : ℂ) : Bound f (fill f c) :=
  OriginalVariableLayout.fill_binding _ _ _

@[simp] theorem fill_scale (f : Signature AlgebraicComplex n) (c : ℂ) : fill f c scale=c := by
  simp [fill,scale]

theorem fill_identity (f : Signature AlgebraicComplex n) (c : ℂ) (j : Fin 5) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) (fill f c)
      (identityRow j)=0 := by
  unfold identityRow
  change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) (fill f c)
    (sub (SparseTransform.variableCode RationalCompiler.field.toArithmeticData
      (OriginalVariableLayout.matrix (Entries n) 1 j))
      (RationalCompiler.constant (identityValues j)))=0
  rw [SparseEvaluation.sub_eval,SparseEvaluation.variable_eval,RationalCompiler.constant_eval]
  simp [fill]

theorem fill_guard (f : Signature AlgebraicComplex n) (c : ℂ) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) (fill f c)
      (SparseTransform.guard RationalCompiler.data (Extra n))=0 := by
  change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) (fill f c)
    (SparseTransform.guard RationalCompiler.field.toArithmeticData (Extra n))=0
  rw [SparseEvaluation.guard_eval]
  simp [fill,identityValues,SymbolicTransform.determinant,SymbolicTransform.matrix,
    SparseTransform.point,SymbolicTransform.index,OriginalVariableLayout.fill,
    OriginalVariableLayout.matrix]

theorem body_zero_iff (C : AffineNormalForm.Code n) (z : Fin (Width n) → ℂ) :
    (∀ p ∈ body C, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0) ↔
      SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
        (SparseTransform.guard RationalCompiler.data (Extra n))=0 ∧
      (∀ j, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
        (identityRow j)=0) ∧
      ∀ x, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z (row C x)=0 := by
  simp only [body,List.forall_mem_cons,List.forall_mem_append,List.forall_mem_map]
  constructor
  · rintro ⟨hg,hi,hr⟩
    exact ⟨hg,fun j => hi j (List.mem_finRange j),fun x => hr x (SparseTransform.mem_allWords x)⟩
  · rintro ⟨hg,hi,hr⟩
    exact ⟨hg,fun j _ => hi j,fun x _ => hr x⟩

theorem formula_scale (C : AffineNormalForm.Code n) (c : AlgebraicComplex) (x : Word n) :
    AffineNormalForm.formula C c x=c*AffineNormalForm.formula C 1 x := by
  rw [AffineNormalForm.entry_formula,AffineNormalForm.entry_formula]
  simp only [one_mul]

/-- A complex scale does not strengthen literal A for an algebraic table:
an original nonzero coefficient determines the same algebraic scale. -/
theorem scalar_descent (C : AffineNormalForm.Code n) (f : Signature AlgebraicComplex n) :
    (∃ c : ℂ, ∀ x, (f x : ℂ)=c*(AffineNormalForm.formula C 1 x : ℂ)) ↔
      ∃ c : AlgebraicComplex, f=AffineNormalForm.formula C c := by
  classical
  constructor
  · rintro ⟨c,hc⟩
    by_cases hz : ∀ x, AffineNormalForm.formula C 1 x=0
    · refine ⟨0,?_⟩
      funext x
      apply Subtype.ext
      have hx := hc x
      rw [hz x] at hx
      rw [formula_scale]
      simpa only [zero_mul,mul_zero,IntermediateField.coe_zero] using hx
    · push_neg at hz
      obtain ⟨x,hx⟩ := hz
      let d : AlgebraicComplex := f x / AffineNormalForm.formula C 1 x
      have hp : (AffineNormalForm.formula C 1 x : ℂ)≠0 := by
        intro h
        exact hx (Subtype.ext h)
      have hd : (d : ℂ)=c := by
        change (algebraMap AlgebraicComplex ℂ) (f x / AffineNormalForm.formula C 1 x)=c
        rw [map_div₀]
        change (f x : ℂ)/(AffineNormalForm.formula C 1 x : ℂ)=c
        rw [hc x,mul_div_cancel_right₀ _ hp]
      refine ⟨d,?_⟩
      funext y
      apply Subtype.ext
      rw [formula_scale]
      change (f y : ℂ)=(algebraMap AlgebraicComplex ℂ) (d*AffineNormalForm.formula C 1 y)
      rw [map_mul]
      change (f y : ℂ)=(d : ℂ)*(AffineNormalForm.formula C 1 y : ℂ)
      rw [hd]
      exact hc y
  · rintro ⟨c,hc⟩
    refine ⟨(c : ℂ),?_⟩
    intro x
    rw [congrFun hc x,formula_scale]
    exact map_mul (algebraMap AlgebraicComplex ℂ) c (AffineNormalForm.formula C 1 x)

theorem system_solution_iff (C : AffineNormalForm.Code n) (f : Signature AlgebraicComplex n) :
    (∃ z : Fin (Width n) → ℂ, ∀ e ∈ RationalInputSystem.system (body C)
        (OriginalVariableLayout.binding (Entries n) 1),
      MvPolynomial.aeval z (EncodedSystem.polynomial
        (RationalInputSystem.values (fun i => (descriptorValues f i : ℂ)) (body C)) e)=0) ↔
      ∃ c : AlgebraicComplex, f=AffineNormalForm.formula C c := by
  rw [←scalar_descent C f]
  constructor
  · rintro ⟨z,hz⟩
    rw [descriptorValues_coe] at hz
    obtain ⟨hb,he⟩ := (RationalInputSystem.system_zero_iff _ _ _ z).mp hz
    have hr := ((body_zero_iff C z).mp he).2.2
    refine ⟨z scale,?_⟩
    intro x
    have hx := hr x
    rw [row_eval C f z hb x] at hx
    exact sub_eq_zero.mp hx
  · rintro ⟨c,hc⟩
    refine ⟨fill f c,?_⟩
    rw [descriptorValues_coe]
    apply (RationalInputSystem.system_zero_iff _ _ _ _).mpr
    refine ⟨fill_bound f c,(body_zero_iff C _).mpr ⟨fill_guard f c,fill_identity f c,?_⟩⟩
    intro x
    rw [row_eval C f _ (fill_bound f c) x,fill_scale,hc x,sub_self]

def branchAnswer (input : Word n → RootCode) (f : Signature AlgebraicComplex n)
    (hf : ∀ x, (input x).Represents (f x : ℂ)) (C : AffineNormalForm.Code n) : Bool :=
  OriginalSystemDecision.answer (OriginalVariableLayout.descriptors (indexedInput input))
    (valid input f hf) (body C) (OriginalVariableLayout.binding (Entries n) 1)

theorem branch_root_only (input : Word n → RootCode) (f g : Signature AlgebraicComplex n)
    (hf : ∀ x, (input x).Represents (f x : ℂ))
    (hg : ∀ x, (input x).Represents (g x : ℂ)) (C : AffineNormalForm.Code n) :
    branchAnswer input f hf C=branchAnswer input g hg C := rfl

theorem branchAnswer_iff (input : Word n → RootCode) (f : Signature AlgebraicComplex n)
    (hf : ∀ x, (input x).Represents (f x : ℂ)) (C : AffineNormalForm.Code n) :
    branchAnswer input f hf C=true ↔ ∃ c : AlgebraicComplex, f=AffineNormalForm.formula C c := by
  rw [branchAnswer,OriginalSystemDecision.answer_correct _ _ _
    (descriptors_represents input f hf) _ _ (guard_mem C)]
  exact system_solution_iff C f

def answer (input : Word n → RootCode) (f : Signature AlgebraicComplex n)
    (hf : ∀ x, (input x).Represents (f x : ℂ)) : Bool :=
  (FiniteBranchEnumeration.affineCodes n).any (branchAnswer input f hf)

theorem answer_iff (input : Word n → RootCode) (f : Signature AlgebraicComplex n)
    (hf : ∀ x, (input x).Represents (f x : ℂ)) : answer input f hf=true ↔ Affine f := by
  rw [answer,List.any_eq_true,AffineNormalForm.affine_iff]
  constructor
  · rintro ⟨C,_,hc⟩
    exact ⟨C,(branchAnswer_iff input f hf C).mp hc⟩
  · rintro ⟨C,hc⟩
    exact ⟨C,FiniteBranchEnumeration.mem_affineCodes C,(branchAnswer_iff input f hf C).mpr hc⟩

theorem answer_false_iff (input : Word n → RootCode) (f : Signature AlgebraicComplex n)
    (hf : ∀ x, (input x).Represents (f x : ℂ)) : answer input f hf=false ↔ ¬ Affine f := by
  have h := answer_iff input f hf
  cases hb : answer input f hf <;> simpa [hb] using not_congr h

/-- Same internally emitted literal body, bindings and input root descriptors.
This is a physical branch run on its generated request, not an outer fold or
an original-bytes-to-request compilation theorem. -/
theorem branch_outputs (input : Word n → RootCode) (f : Signature AlgebraicComplex n)
    (hf : ∀ x, (input x).Represents (f x : ℂ)) (C : AffineNormalForm.Code n) :
    ∃ bound, Nonempty (TM2OutputsInTime OriginalSystemMachine.machine.computer
      (RationalInputMachine.encoding.encode (RationalInputMachine.fromSource
        (OriginalVariableLayout.descriptors (indexedInput input)) (body C)
        (OriginalVariableLayout.binding (Entries n) 1)))
      (some (encodingBoolBool.encode (branchAnswer input f hf C))) bound) :=
  OriginalSystemMachine.source_outputs _ (valid input f hf) _ _

theorem branch_run (input : Word n → RootCode) (f : Signature AlgebraicComplex n)
    (hf : ∀ x, (input x).Represents (f x : ℂ)) (C : AffineNormalForm.Code n) :
    ∃ ticks bound,
      (fun p => p.bind OriginalSystemMachine.machine.computer.step)^[ticks]
        (some (initList OriginalSystemMachine.machine.computer
          (RationalInputMachine.encoding.encode (RationalInputMachine.fromSource
            (OriginalVariableLayout.descriptors (indexedInput input)) (body C)
            (OriginalVariableLayout.binding (Entries n) 1))))) =
        some (haltList OriginalSystemMachine.machine.computer
          (encodingBoolBool.encode (branchAnswer input f hf C))) ∧
      ticks ≤ bound ∧
      primitiveCost OriginalSystemMachine.machine ticks
        (some (initList OriginalSystemMachine.machine.computer
          (RationalInputMachine.encoding.encode (RationalInputMachine.fromSource
            (OriginalVariableLayout.descriptors (indexedInput input)) (body C)
            (OriginalVariableLayout.binding (Entries n) 1))))) ≤
        bound*OriginalSystemMachine.machine.primitiveBudget :=
  OriginalSystemMachine.complete_run _ (valid input f hf) _ _

end
end Holant.LocalDrafts.Tractability.EOEvaluation.EOConditionCertificate.LiteralAffine
