import Holant.Proofs.Algorithms.TransformRecognition.OriginalVariableLayout
import Holant.Proofs.Algorithms.TransformRecognition.RationalInputSystem
import Holant.Proofs.Algorithms.TransformRecognition.SymbolicPhaseCoefficients
import Holant.Proofs.Algorithms.TransformRecognition.LocalAffineVariableLayout
import Holant.Proofs.Algorithms.TransformRecognition.AffineBranch


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalAffineSystem
open Holant Holant.Tractable Holant.Algebraic MvPolynomial
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.Sparse
open ProductVariableLayout (Slot slotArity slots mem_slots)
variable {s : ℕ} (arity : Fin s → ℕ)

abbrev Entries := (LocalAffineVariableLayout.catalogue arity).length
abbrev Width := OriginalVariableLayout.Width (Entries arity) (s+1)
abbrev Extra := OriginalVariableLayout.Extra (Entries arity) (s+1)
abbrev Input := Fin (Entries arity) → RootCode

def entryIndex (j : Slot s) (x : Fin (slotArity arity j) → Bool) : Fin (Entries arity) :=
  LocalAffineVariableLayout.address arity ⟨j,x⟩
def entryVariable (j : Slot s) (x : Fin (slotArity arity j) → Bool) : Fin (Width arity) :=
  OriginalVariableLayout.original (Entries arity) (s+1) (entryIndex arity j x)

def scaleIndex : Slot s → Fin (s+1)
  | .inl i => i.castSucc
  | .inr _ => Fin.last s
def scaleVariable (j : Slot s) : Fin (Width arity) :=
  OriginalVariableLayout.parameter (Entries arity) (s+1) (scaleIndex j)
def imaginaryVariable : Fin (Width arity) := OriginalVariableLayout.special (Entries arity) (s+1) 0
def sqrtVariable : Fin (Width arity) := OriginalVariableLayout.special (Entries arity) (s+1) 1
def eighthVariable : Fin (Width arity) := OriginalVariableLayout.special (Entries arity) (s+1) 2

def compiled : (j : Slot s) → (Fin (slotArity arity j) → Bool) → Poly (Width arity) 1
  | .inl i => SymbolicInputTable.vertex RationalCompiler.data
      (SparseTransform.inverse RationalCompiler.data (Extra arity))
      (fun x => SparseTransform.variableCode RationalCompiler.data (entryVariable arity (.inl i) x))
  | .inr _ => fun (x : Fin 2 → Bool) => SymbolicInputTable.edge RationalCompiler.data
      (SparseTransform.matrix RationalCompiler.data (Extra arity))
      (fun a b => SparseTransform.variableCode RationalCompiler.data
        (entryVariable arity (.inr ()) ![a,b])) (x 0) (x 1)

def codeAt (B : AffineBranch.Branch arity) : (j : Slot s) → AffineNormalForm.Code (slotArity arity j)
  | .inl i => B.1 i
  | .inr _ => B.2

def row (B : AffineBranch.Branch arity) (j : Slot s)
    (x : Fin (slotArity arity j) → Bool) : Poly (Width arity) 1 :=
  sub (compiled arity j x)
    (mul RationalCompiler.data (SparseTransform.variableCode RationalCompiler.data (scaleVariable arity j))
      (SymbolicPhaseCoefficients.affineCoefficient (imaginaryVariable arity) (codeAt arity B j) x))

def eighthRow : Poly (Width arity) 1 :=
  SymbolicPhaseCoefficients.eighthRootRow
    (imaginaryVariable arity) (sqrtVariable arity) (eighthVariable arity)

def body (B : AffineBranch.Branch arity) : List (Poly (Width arity) 1) :=
  SparseTransform.guard RationalCompiler.data (Extra arity) :: eighthRow arity ::
    (slots s).flatMap (fun j => (SparseTransform.allWords (slotArity arity j)).map (row arity B j))

def system (B : AffineBranch.Branch arity) :=
  RationalInputSystem.system (body arity B) (OriginalVariableLayout.binding (Entries arity) (s+1))
def target (input : Input arity) (B : AffineBranch.Branch arity) :=
  RationalInputSystem.target (OriginalVariableLayout.descriptors input) (body arity B)

noncomputable section

def sourceVertex (w : Fin (Entries arity) → AlgebraicComplex) (i : Fin s) :
    Signature AlgebraicComplex (arity i) := fun x => w (entryIndex arity (.inl i) x)
def sourceEdge (w : Fin (Entries arity) → AlgebraicComplex) : Kernel AlgebraicComplex :=
  fun a b => w (entryIndex arity (.inr ()) ![a,b])

def point (z : Fin (Width arity) → ℂ) : SymbolicTransform.Variables (AffineBranch.Parameters (s:=s)) → ℂ :=
  Sum.elim (fun i => z (OriginalVariableLayout.matrix (Entries arity) (s+1) i))
    (fun j => z (scaleVariable arity j))

def Bound (w : Fin (Entries arity) → AlgebraicComplex) (z : Fin (Width arity) → ℂ) : Prop :=
  ∀ i, z (OriginalVariableLayout.binding (Entries arity) (s+1) i) =
    OriginalVariableLayout.boundValues (fun j => (w j : ℂ)) i

theorem bound_entry (w : Fin (Entries arity) → AlgebraicComplex) (z : Fin (Width arity) → ℂ)
    (hb : Bound arity w z) (j : Slot s) (x : Fin (slotArity arity j) → Bool) :
    z (entryVariable arity j x)=(w (entryIndex arity j x) : ℂ) :=
  OriginalVariableLayout.binding_original z _ hb _

theorem inverse_point (z : Fin (Width arity) → ℂ) :
    SymbolicTransform.inverse (SparseTransform.point z) = SymbolicTransform.inverse (point arity z) := rfl
theorem matrix_point (z : Fin (Width arity) → ℂ) :
    SymbolicTransform.matrix (SparseTransform.point z) = SymbolicTransform.matrix (point arity z) := rfl

theorem compiled_vertex_eval (w : Fin (Entries arity) → AlgebraicComplex)
    (z : Fin (Width arity) → ℂ) (hb : Bound arity w z) (i : Fin s) (x : Fin (arity i) → Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
      (compiled arity (.inl i) x) =
      Signature.coordinateAction (fun _ => SymbolicTransform.inverse (point arity z))
        (fun y => (sourceVertex arity w i y : ℂ)) x := by
  rw [compiled]
  change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
    (SymbolicInputTable.vertex RationalCompiler.field.toArithmeticData
      (SparseTransform.inverse RationalCompiler.field.toArithmeticData (Extra arity))
      (fun y => SparseTransform.variableCode RationalCompiler.field.toArithmeticData
        (entryVariable arity (.inl i) y)) x) = _
  rw [SymbolicInputTable.vertex_eval]
  simp only [SparseEvaluation.inverse_eval,SparseEvaluation.variable_eval,
    bound_entry arity w z hb,inverse_point,sourceVertex]
  rfl

theorem compiled_edge_eval (w : Fin (Entries arity) → AlgebraicComplex)
    (z : Fin (Width arity) → ℂ) (hb : Bound arity w z) (x : Fin 2 → Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
      (compiled arity (.inr ()) x) =
      Kernel.pullback (fun a b => (sourceEdge arity w a b : ℂ))
        (SymbolicTransform.matrix (point arity z)) (x 0) (x 1) := by
  rw [compiled]
  change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
    (SymbolicInputTable.edge RationalCompiler.field.toArithmeticData
      (SparseTransform.matrix RationalCompiler.field.toArithmeticData (Extra arity))
      (fun a b => SparseTransform.variableCode RationalCompiler.field.toArithmeticData
        (entryVariable arity (.inr ()) ![a,b])) (x 0) (x 1)) = _
  rw [SymbolicInputTable.edge_eval]
  simp only [SparseEvaluation.matrix_eval,SparseEvaluation.variable_eval,
    bound_entry arity w z hb,matrix_point,sourceEdge]

theorem row_eval (w : Fin (Entries arity) → AlgebraicComplex)
    (z : Fin (Width arity) → ℂ) (hb : Bound arity w z) (B : AffineBranch.Branch arity)
    (j : Slot s) (x : Fin (slotArity arity j) → Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z (row arity B j x) =
      SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z (compiled arity j x) -
      z (scaleVariable arity j) * (AffineNormalForm.formula (codeAt arity B j) 1 x : ℂ) := by
  have hi : z (imaginaryVariable arity)=Complex.I :=
    OriginalVariableLayout.binding_imaginary z (fun k => (w k : ℂ)) hb
  unfold row
  change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
    (sub (compiled arity j x) (mul RationalCompiler.field.toArithmeticData
      (SparseTransform.variableCode RationalCompiler.field.toArithmeticData (scaleVariable arity j))
      (SymbolicPhaseCoefficients.affineCoefficient (imaginaryVariable arity) (codeAt arity B j) x))) = _
  rw [SparseEvaluation.sub_eval,SparseEvaluation.mul_eval,SparseEvaluation.variable_eval,
    SymbolicPhaseCoefficients.affineCoefficient_eval (imaginaryVariable arity) (codeAt arity B j) x z hi]

theorem body_zero_iff (B : AffineBranch.Branch arity) (z : Fin (Width arity) → ℂ) :
    (∀ p ∈ body arity B, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0) ↔
      SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
        (SparseTransform.guard RationalCompiler.data (Extra arity))=0 ∧
      SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z (eighthRow arity)=0 ∧
      ∀ j x, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z (row arity B j x)=0 := by
  simp only [body,List.forall_mem_cons,List.forall_mem_flatMap,List.forall_mem_map]
  constructor
  · rintro ⟨hg,he,hr⟩
    exact ⟨hg,he,fun j x => hr j (mem_slots j) x (SparseTransform.mem_allWords x)⟩
  · rintro ⟨hg,he,hr⟩
    exact ⟨hg,he,fun j _ x _ => hr j x⟩

theorem coefficient_one {n : ℕ} (C : AffineNormalForm.Code n) (x : Fin n → Bool) :
    AffineNormalForm.formula C 1 x=ExtensionAffine.coefficient C x := by
  simp only [AffineNormalForm.formula,affineFormula,one_mul,ExtensionAffine.coefficient]
  by_cases h : AffineNormalForm.supportHolds C.1 x
  · have hs := (AffineNormalForm.system_holds C.1 x).mpr h
    simp only [h,hs,ite_true]
  · have hs : ¬(AffineNormalForm.system C.1).Holds x :=
      fun hs => h ((AffineNormalForm.system_holds C.1 x).mp hs)
    simp only [h,hs,ite_false]

def equationIndex (j : Slot s) (x : Fin (slotArity arity j) → Bool) :
    AffineBranch.EquationIndex arity :=
  match j with
  | .inl i => .inr (.inl ⟨i,x⟩)
  | .inr _ => .inr (.inr x)

theorem row_source (w : Fin (Entries arity) → AlgebraicComplex)
    (z : Fin (Width arity) → ℂ) (hb : Bound arity w z) (B : AffineBranch.Branch arity)
    (j : Slot s) (x : Fin (slotArity arity j) → Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z (row arity B j x) =
      eval₂ (algebraMap AlgebraicComplex ℂ) (point arity z)
        (AffineBranch.equations (sourceVertex arity w) (sourceEdge arity w) B (equationIndex arity j x)) := by
  rw [row_eval arity w z hb,coefficient_one]
  cases j with
  | inl i =>
    rw [compiled_vertex_eval arity w z hb]
    simp [equationIndex,AffineBranch.equations,SymbolicTransform.eval_vertex,
      point,codeAt]
  | inr u =>
    cases u
    rw [compiled_edge_eval arity w z hb]
    simp [equationIndex,AffineBranch.equations,SymbolicTransform.eval_edge,
      point,codeAt]

theorem guard_source (w : Fin (Entries arity) → AlgebraicComplex)
    (z : Fin (Width arity) → ℂ) (B : AffineBranch.Branch arity) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
      (SparseTransform.guard RationalCompiler.data (Extra arity)) =
      eval₂ (algebraMap AlgebraicComplex ℂ) (point arity z)
        (AffineBranch.equations (sourceVertex arity w) (sourceEdge arity w) B (.inl ())) := by
  change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
    (SparseTransform.guard RationalCompiler.field.toArithmeticData (Extra arity)) = _
  rw [SparseEvaluation.guard_eval]
  simp only [AffineBranch.equations,SymbolicTransform.eval_guard,matrix_point]
  rfl

theorem body_source_iff (w : Fin (Entries arity) → AlgebraicComplex)
    (z : Fin (Width arity) → ℂ) (hb : Bound arity w z) (B : AffineBranch.Branch arity) :
    (∀ p ∈ body arity B, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0) ↔
      SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z (eighthRow arity)=0 ∧
      ∀ r, eval₂ (algebraMap AlgebraicComplex ℂ) (point arity z)
        (AffineBranch.equations (sourceVertex arity w) (sourceEdge arity w) B r)=0 := by
  rw [body_zero_iff]
  constructor
  · rintro ⟨hg,he,hr⟩
    refine ⟨he,?_⟩
    intro r
    rcases r with u | (⟨i,x⟩ | x)
    · cases u
      rwa [←guard_source arity w z B]
    · simpa only [row_source arity w z hb,equationIndex] using hr (.inl i) x
    · simpa only [row_source arity w z hb,equationIndex] using hr (.inr ()) x
  · rintro ⟨he,hr⟩
    refine ⟨?_,he,?_⟩
    · rw [guard_source]
      exact hr (.inl ())
    · intro j x
      rw [row_source arity w z hb]
      exact hr _

def fill (w : Fin (Entries arity) → AlgebraicComplex)
    (y : SymbolicTransform.Variables (AffineBranch.Parameters (s:=s)) → ℂ) : Fin (Width arity) → ℂ :=
  OriginalVariableLayout.fill (fun i => y (.inl i))
    (Fin.lastCases (y (.inr (.inr ()))) (fun i => y (.inr (.inl i))))
    (fun i => (w i : ℂ)) OriginalVariableLayout.constants

theorem point_fill (w : Fin (Entries arity) → AlgebraicComplex)
    (y : SymbolicTransform.Variables (AffineBranch.Parameters (s:=s)) → ℂ) :
    point arity (fill arity w y)=y := by
  funext j
  rcases j with j | (i | u)
  · simp [point,fill]
  · simp [point,fill,scaleVariable,scaleIndex]
  · cases u
    simp [point,fill,scaleVariable,scaleIndex]

theorem fill_bound (w : Fin (Entries arity) → AlgebraicComplex)
    (y : SymbolicTransform.Variables (AffineBranch.Parameters (s:=s)) → ℂ) :
    Bound arity w (fill arity w y) :=
  OriginalVariableLayout.fill_binding _ _ _

theorem fill_eighth (w : Fin (Entries arity) → AlgebraicComplex)
    (y : SymbolicTransform.Variables (AffineBranch.Parameters (s:=s)) → ℂ) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ)
      (fill arity w y) (eighthRow arity)=0 := by
  rw [eighthRow,SymbolicPhaseCoefficients.eighthRootRow_eval]
  simp only [imaginaryVariable,sqrtVariable,eighthVariable,fill,
    OriginalVariableLayout.fill_special,OriginalVariableLayout.constants,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  rw [coe_zetaEight]
  change ((1+Complex.I)/(Real.sqrt 2 : ℂ))*(Real.sqrt 2 : ℂ)-(1+Complex.I)=0
  rw [div_mul_cancel₀,sub_self]
  exact_mod_cast (ne_of_gt (lt_trans (by norm_num : (0:ℝ)<1) StandardRootCodes.sqrtTwo_bounds.1))

/-- The literal output system, including input bindings, has a solution
exactly when the source common-A branch equations do. No encoded solution or
transformability certificate is an input to the compiler. -/
theorem source_solution_iff (w : Fin (Entries arity) → AlgebraicComplex)
    (B : AffineBranch.Branch arity) :
    (∃ z : Fin (Width arity) → ℂ, ∀ e ∈ system arity B,
      aeval z (EncodedSystem.polynomial
        (RationalInputSystem.values
          (OriginalVariableLayout.boundValues (fun i => (w i : ℂ))) (body arity B)) e)=0) ↔
    ∃ y : SymbolicTransform.Variables (AffineBranch.Parameters (s:=s)) → ℂ,
      ∀ r, eval₂ (algebraMap AlgebraicComplex ℂ) y
        (AffineBranch.equations (sourceVertex arity w) (sourceEdge arity w) B r)=0 := by
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨hb,he⟩ := (RationalInputSystem.system_zero_iff _ _ _ z).mp hz
    exact ⟨point arity z,((body_source_iff arity w z hb B).mp he).2⟩
  · rintro ⟨y,hy⟩
    refine ⟨fill arity w y,?_⟩
    apply (RationalInputSystem.system_zero_iff _ _ _ _).mpr
    refine ⟨fill_bound arity w y,?_⟩
    apply (body_source_iff arity w _ (fill_bound arity w y) B).mpr
    exact ⟨fill_eighth arity w y,by simpa only [point_fill] using hy⟩

theorem source_shared_iff (w : Fin (Entries arity) → AlgebraicComplex) :
    AffineBranch.Shared (sourceVertex arity w) (sourceEdge arity w) (algebraMap AlgebraicComplex ℂ) ↔
      ∃ B : AffineBranch.Branch arity, ∃ z : Fin (Width arity) → ℂ,
        ∀ e ∈ system arity B, aeval z (EncodedSystem.polynomial
          (RationalInputSystem.values
            (OriginalVariableLayout.boundValues (fun i => (w i : ℂ))) (body arity B)) e)=0 := by
  rw [AffineBranch.shared_iff_solution]
  exact exists_congr (fun B => (source_solution_iff arity w B).symm)

end
end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalAffineSystem
