import Holant.Proofs.Tractability.EOEvaluation.EOConditionCertificate.LiteralAffine
import Holant.Proofs.Algorithms.TransformRecognition.OriginalProductSystem
import Holant.Proofs.Algorithms.TransformRecognition.ConstructibleDescent


namespace Holant.LocalDrafts.Tractability.EOEvaluation.EOConditionCertificate.LiteralProduct
open Turing Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm
open Sparse Descriptors FixedFieldMachines
variable {n : ℕ}

def parameters (n : ℕ) : List (Parameter n) :=
  none :: (List.finRange n).flatMap (fun i => [some (i,false),some (i,true)])

theorem mem_parameters (p : Parameter n) : p ∈ parameters n := by
  cases p with
  | none => exact List.mem_cons_self ..
  | some p =>
      rcases p with ⟨i,b⟩
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      refine ⟨i,List.mem_finRange i,?_⟩
      cases b <;> simp

abbrev Count (n : ℕ) := (parameters n).length
abbrev Extra (n : ℕ) := OriginalVariableLayout.Extra (LiteralAffine.Entries n) (Count n)
abbrev Width (n : ℕ) := OriginalVariableLayout.Width (LiteralAffine.Entries n) (Count n)

def parameterAddress (p : Parameter n) : Fin (Count n) :=
  ⟨(parameters n).idxOf p,List.idxOf_lt_length_iff.mpr (mem_parameters p)⟩

@[simp] theorem get_parameterAddress (p : Parameter n) :
    (parameters n).get (parameterAddress p)=p := List.idxOf_get _

def parameter (p : Parameter n) : Fin (Width n) :=
  OriginalVariableLayout.parameter (LiteralAffine.Entries n) (Count n) (parameterAddress p)
def original (x : Word n) : Fin (Width n) :=
  OriginalVariableLayout.original (LiteralAffine.Entries n) (Count n) (LiteralAffine.address x)
def identityRow (j : Fin 5) : Poly (Width n) 1 :=
  sub (SparseTransform.variableCode RationalCompiler.data
    (OriginalVariableLayout.matrix (LiteralAffine.Entries n) (Count n) j))
    (RationalCompiler.constant (LiteralAffine.identityValues j))
def row (S : Skeleton n) (x : Word n) : Poly (Width n) 1 :=
  sub (SparseTransform.variableCode RationalCompiler.data (original x))
    (SparseProductTemplate.entry RationalCompiler.data (OriginalProductSystem.edgeList S) parameter x)
def body (S : Skeleton n) : List (Poly (Width n) 1) :=
  SparseTransform.guard RationalCompiler.data (Extra n) ::
    ((List.finRange 5).map identityRow ++ (words n).map (row S))

theorem guard_mem (S : Skeleton n) :
    SparseTransform.guard RationalCompiler.data (Extra n) ∈ body S := List.mem_cons_self ..

theorem body_length (S : Skeleton n) : (body S).length=6+2^n := by
  simp [body,SparseTransform.allWords_length]
  omega

noncomputable section
local instance : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ

def Bound (f : Signature AlgebraicComplex n) (z : Fin (Width n) → ℂ) : Prop :=
  ∀ i, z (OriginalVariableLayout.binding (LiteralAffine.Entries n) (Count n) i)=
    OriginalVariableLayout.boundValues (fun j => (LiteralAffine.values f j : ℂ)) i
def point (z : Fin (Width n) → ℂ) : Parameter n → ℂ := fun p => z (parameter p)

theorem row_eval (S : Skeleton n) (f : Signature AlgebraicComplex n)
    (z : Fin (Width n) → ℂ) (hz : Bound f z) (x : Word n) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z (row S x)=
      (f x : ℂ)-evaluate S (point z) x := by
  have he : z (original x)=(f x : ℂ) := by
    simpa only [original,LiteralAffine.values,LiteralAffine.get_address] using
      OriginalVariableLayout.binding_original z
        (fun i => (LiteralAffine.values f i : ℂ)) hz (LiteralAffine.address x)
  unfold row
  change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
    (sub (SparseTransform.variableCode RationalCompiler.field.toArithmeticData (original x))
      (SparseProductTemplate.entry RationalCompiler.field.toArithmeticData
        (OriginalProductSystem.edgeList S) parameter x)) = _
  rw [SparseEvaluation.sub_eval,SparseEvaluation.variable_eval,he,
    SparseProductTemplate.entry_eval,OriginalProductSystem.edgeList_exact]
  rfl

def fill (f : Signature AlgebraicComplex n) (theta : Parameter n → ℂ) : Fin (Width n) → ℂ :=
  OriginalVariableLayout.fill (fun j => (LiteralAffine.identityValues j : ℂ))
    (fun i => theta ((parameters n).get i)) (fun i => (LiteralAffine.values f i : ℂ))
    OriginalVariableLayout.constants

theorem fill_bound (f : Signature AlgebraicComplex n) (theta : Parameter n → ℂ) :
    Bound f (fill f theta) := OriginalVariableLayout.fill_binding _ _ _

@[simp] theorem point_fill (f : Signature AlgebraicComplex n) (theta : Parameter n → ℂ) :
    point (fill f theta)=theta := by
  funext p
  simp only [point,parameter,fill,OriginalVariableLayout.fill_parameter,get_parameterAddress]

theorem fill_identity (f : Signature AlgebraicComplex n) (theta : Parameter n → ℂ)
    (j : Fin 5) : SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ)
      (fill f theta) (identityRow j)=0 := by
  unfold identityRow
  change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) (fill f theta)
    (sub (SparseTransform.variableCode RationalCompiler.field.toArithmeticData
      (OriginalVariableLayout.matrix (LiteralAffine.Entries n) (Count n) j))
      (RationalCompiler.constant (LiteralAffine.identityValues j)))=0
  rw [SparseEvaluation.sub_eval,SparseEvaluation.variable_eval,RationalCompiler.constant_eval]
  simp [fill]

theorem fill_guard (f : Signature AlgebraicComplex n) (theta : Parameter n → ℂ) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) (fill f theta)
      (SparseTransform.guard RationalCompiler.data (Extra n))=0 := by
  change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) (fill f theta)
    (SparseTransform.guard RationalCompiler.field.toArithmeticData (Extra n))=0
  rw [SparseEvaluation.guard_eval]
  simp [fill,LiteralAffine.identityValues,SymbolicTransform.determinant,SymbolicTransform.matrix,
    SparseTransform.point,SymbolicTransform.index,OriginalVariableLayout.fill,
    OriginalVariableLayout.matrix]

theorem body_zero_iff (S : Skeleton n) (z : Fin (Width n) → ℂ) :
    (∀ p ∈ body S, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0) ↔
      SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
        (SparseTransform.guard RationalCompiler.data (Extra n))=0 ∧
      (∀ j, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
        (identityRow j)=0) ∧
      ∀ x, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z (row S x)=0 := by
  simp only [body,List.forall_mem_cons,List.forall_mem_append,List.forall_mem_map]
  constructor
  · rintro ⟨hg,hi,hr⟩
    exact ⟨hg,fun j => hi j (List.mem_finRange j),fun x => hr x (SparseTransform.mem_allWords x)⟩
  · rintro ⟨hg,hi,hr⟩
    exact ⟨hg,fun j _ => hi j,fun x _ => hr x⟩

/-- All literal Product parameter tuples, including zero unary entries and
zero scalar, descend for an algebraic original table. -/
theorem parameter_descent (S : Skeleton n) (f : Signature AlgebraicComplex n) :
    (∃ theta : Parameter n → ℂ, ∀ x, (f x : ℂ)=evaluate S theta x) ↔
      ∃ theta : Parameter n → AlgebraicComplex, f=evaluate S theta := by
  constructor
  · rintro ⟨theta,ht⟩
    have ha : ∀ x, MvPolynomial.aeval theta (entryEquation f S x)=0 := by
      intro x
      change MvPolynomial.eval₂ (algebraMap AlgebraicComplex ℂ) theta
        (MvPolynomial.C (f x)-entryPolynomial AlgebraicComplex S x)=0
      rw [MvPolynomial.eval₂_sub,MvPolynomial.eval₂_C,eval₂_entry]
      exact sub_eq_zero.mpr (ht x)
    obtain ⟨y,hy⟩ := ConstructibleDescent.equations_descend (entryEquation f S) theta ha
    refine ⟨y,?_⟩
    funext x
    apply (entryEquation_zero_iff f S y x).mp
    exact hy x
  · rintro ⟨theta,ht⟩
    refine ⟨fun p => (theta p : ℂ),?_⟩
    intro x
    rw [congrFun ht x]
    exact (evaluate_map (algebraMap AlgebraicComplex ℂ) S theta x).symm

theorem system_solution_iff (S : Skeleton n) (f : Signature AlgebraicComplex n) :
    (∃ z : Fin (Width n) → ℂ, ∀ e ∈ RationalInputSystem.system (body S)
        (OriginalVariableLayout.binding (LiteralAffine.Entries n) (Count n)),
      MvPolynomial.aeval z (EncodedSystem.polynomial
        (RationalInputSystem.values (fun i => (LiteralAffine.descriptorValues f i : ℂ)) (body S)) e)=0) ↔
      ∃ theta : Parameter n → AlgebraicComplex, f=evaluate S theta := by
  rw [←parameter_descent S f]
  constructor
  · rintro ⟨z,hz⟩
    rw [LiteralAffine.descriptorValues_coe] at hz
    obtain ⟨hb,he⟩ := (RationalInputSystem.system_zero_iff _ _ _ z).mp hz
    have hr := ((body_zero_iff S z).mp he).2.2
    refine ⟨point z,?_⟩
    intro x
    have hx := hr x
    rw [row_eval S f z hb x] at hx
    exact sub_eq_zero.mp hx
  · rintro ⟨theta,ht⟩
    refine ⟨fill f theta,?_⟩
    rw [LiteralAffine.descriptorValues_coe]
    apply (RationalInputSystem.system_zero_iff _ _ _ _).mpr
    refine ⟨fill_bound f theta,(body_zero_iff S _).mpr
      ⟨fill_guard f theta,fill_identity f theta,?_⟩⟩
    intro x
    rw [row_eval S f _ (fill_bound f theta) x,point_fill,ht x,sub_self]

def branchAnswer (input : Word n → RootCode) (f : Signature AlgebraicComplex n)
    (hf : ∀ x, (input x).Represents (f x : ℂ)) (S : Skeleton n) : Bool :=
  OriginalSystemDecision.answer (OriginalVariableLayout.descriptors (LiteralAffine.indexedInput input))
    (LiteralAffine.valid input f hf) (body S)
    (OriginalVariableLayout.binding (LiteralAffine.Entries n) (Count n))

theorem branch_root_only (input : Word n → RootCode) (f g : Signature AlgebraicComplex n)
    (hf : ∀ x, (input x).Represents (f x : ℂ))
    (hg : ∀ x, (input x).Represents (g x : ℂ)) (S : Skeleton n) :
    branchAnswer input f hf S=branchAnswer input g hg S := rfl

theorem branchAnswer_iff (input : Word n → RootCode) (f : Signature AlgebraicComplex n)
    (hf : ∀ x, (input x).Represents (f x : ℂ)) (S : Skeleton n) :
    branchAnswer input f hf S=true ↔ ∃ theta, f=evaluate S theta := by
  rw [branchAnswer,OriginalSystemDecision.answer_correct _ _ _
    (LiteralAffine.descriptors_represents input f hf) _ _ (guard_mem S)]
  exact system_solution_iff S f

def answer (input : Word n → RootCode) (f : Signature AlgebraicComplex n)
    (hf : ∀ x, (input x).Represents (f x : ℂ)) : Bool :=
  (FiniteBranchEnumeration.productCodes n).any (branchAnswer input f hf)

theorem answer_iff (input : Word n → RootCode) (f : Signature AlgebraicComplex n)
    (hf : ∀ x, (input x).Represents (f x : ℂ)) : answer input f hf=true ↔ Product f := by
  rw [answer,List.any_eq_true,product_iff]
  constructor
  · rintro ⟨S,_,hs⟩
    exact ⟨S,(branchAnswer_iff input f hf S).mp hs⟩
  · rintro ⟨S,hs⟩
    exact ⟨S,FiniteBranchEnumeration.mem_productCodes S,(branchAnswer_iff input f hf S).mpr hs⟩

theorem answer_false_iff (input : Word n → RootCode) (f : Signature AlgebraicComplex n)
    (hf : ∀ x, (input x).Represents (f x : ℂ)) : answer input f hf=false ↔ ¬ Product f := by
  have h := answer_iff input f hf
  cases hb : answer input f hf <;> simpa [hb] using not_congr h

/-- The generated request contains the same original descriptors, fixed
identity rows and literal Product template. No supplied system or solution. -/
theorem branch_outputs (input : Word n → RootCode) (f : Signature AlgebraicComplex n)
    (hf : ∀ x, (input x).Represents (f x : ℂ)) (S : Skeleton n) :
    ∃ bound, Nonempty (TM2OutputsInTime OriginalSystemMachine.machine.computer
      (RationalInputMachine.encoding.encode (RationalInputMachine.fromSource
        (OriginalVariableLayout.descriptors (LiteralAffine.indexedInput input)) (body S)
        (OriginalVariableLayout.binding (LiteralAffine.Entries n) (Count n))))
      (some (encodingBoolBool.encode (branchAnswer input f hf S))) bound) :=
  OriginalSystemMachine.source_outputs _ (LiteralAffine.valid input f hf) _ _

theorem branch_run (input : Word n → RootCode) (f : Signature AlgebraicComplex n)
    (hf : ∀ x, (input x).Represents (f x : ℂ)) (S : Skeleton n) :
    ∃ ticks bound,
      (fun p => p.bind OriginalSystemMachine.machine.computer.step)^[ticks]
        (some (initList OriginalSystemMachine.machine.computer
          (RationalInputMachine.encoding.encode (RationalInputMachine.fromSource
            (OriginalVariableLayout.descriptors (LiteralAffine.indexedInput input)) (body S)
            (OriginalVariableLayout.binding (LiteralAffine.Entries n) (Count n)))))) =
        some (haltList OriginalSystemMachine.machine.computer
          (encodingBoolBool.encode (branchAnswer input f hf S))) ∧
      ticks ≤ bound ∧
      primitiveCost OriginalSystemMachine.machine ticks
        (some (initList OriginalSystemMachine.machine.computer
          (RationalInputMachine.encoding.encode (RationalInputMachine.fromSource
            (OriginalVariableLayout.descriptors (LiteralAffine.indexedInput input)) (body S)
            (OriginalVariableLayout.binding (LiteralAffine.Entries n) (Count n)))))) ≤
        bound*OriginalSystemMachine.machine.primitiveBudget :=
  OriginalSystemMachine.complete_run _ (LiteralAffine.valid input f hf) _ _

end
end Holant.LocalDrafts.Tractability.EOEvaluation.EOConditionCertificate.LiteralProduct
