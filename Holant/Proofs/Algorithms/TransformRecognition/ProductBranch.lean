import Holant.Proofs.Algorithms.TransformRecognition.ProductVariableLayout
import Holant.Proofs.Algorithms.TransformRecognition.AffineBranch
import Holant.Proofs.Tetrahedral.TransformRecognition.ProductNormalForm.Polynomials
import Holant.Proofs.Tetrahedral.TransformRecognition.ProductNormalForm.ExtensionSource


namespace Holant.LocalDrafts.MainChain.TransformRecognition.ProductBranch
set_option backward.isDefEq.respectTransparency false
open Holant.Tractable MvPolynomial
open Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm
noncomputable section
attribute [local instance] Classical.propDecidable
local instance : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
variable {s : ℕ} (arity : Fin s → ℕ)

abbrev Slot := Fin s ⊕ Unit
abbrev slotArity : Slot (s:=s) → ℕ := ProductVariableLayout.slotArity arity
abbrev Parameters := Σ j : Slot (s:=s), Parameter (slotArity arity j)
abbrev Branch := (j : Slot (s:=s)) → Skeleton (slotArity arity j)
abbrev EquationIndex := Unit ⊕ (Σ j : Slot (s:=s), Fin (slotArity arity j) → Bool)

variable {arity} (G : (i : Fin s) → Signature AlgebraicComplex (arity i))
    (E₀ : Kernel AlgebraicComplex)

def compiled : (j : Slot (s:=s)) → Signature (SymbolicTransform.Poly (Parameters arity))
    (slotArity arity j)
  | .inl i => SymbolicTransform.vertex (G i)
  | .inr _ => fun x => SymbolicTransform.edge E₀ (x (0 : Fin 2)) (x (1 : Fin 2))

def templatePolynomial (B : Branch arity) (j : Slot (s:=s))
    (x : Fin (slotArity arity j) → Bool) : SymbolicTransform.Poly (Parameters arity) :=
  rename (fun p => Sum.inr (⟨j,p⟩ : Parameters arity))
    (entryPolynomial AlgebraicComplex (B j) x)

def equations (B : Branch arity) : EquationIndex arity → SymbolicTransform.Poly (Parameters arity)
  | .inl _ => SymbolicTransform.guard _
  | .inr ⟨j,x⟩ => compiled G E₀ j x-templatePolynomial B j x

variable {E : Type*} [Field E] (φ : AlgebraicComplex →+* E)

theorem eval_template (B : Branch arity) (z : SymbolicTransform.Variables (Parameters arity) → E)
    (j : Slot (s:=s)) (x : Fin (slotArity arity j) → Bool) :
    eval₂ φ z (templatePolynomial B j x)=evaluate (B j) (fun p => z (.inr ⟨j,p⟩)) x := by
  rw [templatePolynomial,eval₂_rename]
  exact eval₂_entry φ (B j) _ x

def transformed (U V : Kernel E) : (j : Slot (s:=s)) → Signature E (slotArity arity j)
  | .inl i => Signature.coordinateAction (fun _ => V) (fun x => φ (G i x))
  | .inr _ => fun x => Kernel.pullback (fun a b => φ (E₀ a b)) U (x (0 : Fin 2)) (x (1 : Fin 2))

def evaluated (z : SymbolicTransform.Variables (Parameters arity) → E)
    (j : Slot (s:=s)) : Signature E (slotArity arity j) :=
  fun x => eval₂ φ z (compiled G E₀ j x)

def SharedTemplates : Prop := ∃ U V : Kernel E,
  Kernel.mul U V=Signature.equality ∧ Kernel.mul V U=Signature.equality ∧
  ∀ j, ∃ S : Skeleton (slotArity arity j), ∃ c : Parameter (slotArity arity j) → E,
    transformed G E₀ φ U V j=evaluate S c

/-- This uses the original arbitrary finite factor-list class over E, not a
definition by the desired bounded-template conclusion. -/
def SharedSource : Prop := ∃ U V : Kernel E,
  Kernel.mul U V=Signature.equality ∧ Kernel.mul V U=Signature.equality ∧
  ∀ j, ExtensionSource.ProductOver (transformed G E₀ φ U V j)

theorem source_iff_templates : SharedSource G E₀ φ ↔ SharedTemplates G E₀ φ := by
  simp only [SharedSource,SharedTemplates,ExtensionSource.productOver_iff]

theorem evaluated_point (U V : Kernel E) (c : Parameters arity → E)
    (hUV : Kernel.mul U V=Signature.equality)
    (hVU : Kernel.mul V U=Signature.equality) (j : Slot (s:=s)) :
    evaluated G E₀ φ (SymbolicTransform.point U c) j=transformed G E₀ φ U V j := by
  cases j with
  | inl i =>
    funext x
    exact SymbolicTransform.point_vertex φ U V c hUV hVU (G i) x
  | inr u =>
    funext x
    exact SymbolicTransform.point_edge φ U c E₀ (x (0 : Fin 2)) (x (1 : Fin 2))

theorem evaluated_at (z : SymbolicTransform.Variables (Parameters arity) → E)
    (j : Slot (s:=s)) : evaluated G E₀ φ z j=
      transformed G E₀ φ (SymbolicTransform.matrix z) (SymbolicTransform.inverse z) j := by
  cases j with
  | inl i =>
    funext x
    exact SymbolicTransform.eval_vertex φ z (G i) x
  | inr u =>
    funext x
    exact SymbolicTransform.eval_edge φ z E₀ (x (0 : Fin 2)) (x (1 : Fin 2))

theorem solution_of_templates (h : SharedTemplates G E₀ φ) :
    ∃ B : Branch arity, ∃ z : SymbolicTransform.Variables (Parameters arity) → E,
      ∀ r, eval₂ φ z (equations G E₀ B r)=0 := by
  obtain ⟨U,V,hUV,hVU,hT⟩ := h
  choose B c hc using hT
  let parameters : Parameters arity → E := fun p => c p.1 p.2
  refine ⟨B,SymbolicTransform.point U parameters,?_⟩
  intro r
  rcases r with u | ⟨j,x⟩
  · exact SymbolicTransform.point_guard φ U V parameters hUV
  · have he := congrFun (evaluated_point G E₀ φ U V parameters hUV hVU j) x
    rw [hc j] at he
    change eval₂ φ (SymbolicTransform.point U parameters) (compiled G E₀ j x)=_ at he
    simpa [equations,eval_template,SymbolicTransform.point,parameters,sub_eq_zero] using he

theorem templates_of_solution (B : Branch arity)
    (z : SymbolicTransform.Variables (Parameters arity) → E)
    (hz : ∀ r, eval₂ φ z (equations G E₀ B r)=0) : SharedTemplates G E₀ φ := by
  have hg : eval₂ φ z (SymbolicTransform.guard (Parameters arity))=0 := hz (.inl ())
  have hi := SymbolicTransform.inverse_identities φ z hg
  refine ⟨SymbolicTransform.matrix z,SymbolicTransform.inverse z,hi.1,hi.2,?_⟩
  intro j
  refine ⟨B j,fun p => z (.inr ⟨j,p⟩),?_⟩
  rw [← evaluated_at G E₀ φ z j]
  funext x
  have he := hz (.inr ⟨j,x⟩)
  simpa [equations,eval_template,evaluated,sub_eq_zero] using he

theorem templates_iff_solution : SharedTemplates G E₀ φ ↔
    ∃ B : Branch arity, ∃ z : SymbolicTransform.Variables (Parameters arity) → E,
      ∀ r, eval₂ φ z (equations G E₀ B r)=0 :=
  ⟨solution_of_templates G E₀ φ,fun ⟨B,z,hz⟩ => templates_of_solution G E₀ φ B z hz⟩

theorem descend_templates [Algebra AlgebraicComplex E]
    (h : SharedTemplates G E₀ (algebraMap AlgebraicComplex E)) :
    SharedTemplates G E₀ (RingHom.id AlgebraicComplex) := by
  obtain ⟨B,z,hz⟩ := solution_of_templates G E₀ (algebraMap AlgebraicComplex E) h
  have ha : ∀ r, aeval z (equations G E₀ B r)=0 := hz
  obtain ⟨y,hy⟩ := ConstructibleDescent.equations_descend (equations G E₀ B) z ha
  exact templates_of_solution G E₀ (RingHom.id AlgebraicComplex) B y hy

def branchIdeal (B : Branch arity) : Ideal (SymbolicTransform.Poly (Parameters arity)) :=
  Ideal.span (Set.range (equations G E₀ B))

theorem templates_iff_proper : SharedTemplates G E₀ (RingHom.id AlgebraicComplex) ↔
    ∃ B : Branch arity, branchIdeal G E₀ B ≠ ⊤ := by
  rw [templates_iff_solution]
  constructor
  · rintro ⟨B,z,hz⟩
    refine ⟨B,?_⟩
    have hker : branchIdeal G E₀ B ≤ RingHom.ker (aeval z).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨r,rfl⟩
      exact hz r
    intro ht
    have hone : (1 : SymbolicTransform.Poly (Parameters arity)) ∈ branchIdeal G E₀ B := by
      rw [ht]
      trivial
    have he := hker hone
    change aeval z 1=0 at he
    simpa using he
  · rintro ⟨B,hB⟩
    obtain ⟨z,hz⟩ := ConstructibleDescent.point_of_proper (branchIdeal G E₀ B) hB
    exact ⟨B,z,fun r => hz _ (Ideal.subset_span ⟨r,rfl⟩)⟩

theorem actual_basis (h : SharedTemplates G E₀ (RingHom.id AlgebraicComplex)) :
    ∃ U : InvertibleKernel, (∀ i, Product (U.symm.action (G i))) ∧
      Product (kernelSignature (Kernel.pullback E₀ U.matrix)) := by
  obtain ⟨U,V,hUV,hVU,hT⟩ := h
  refine ⟨⟨U,V,hUV,hVU⟩,?_,?_⟩
  · intro i
    exact (product_iff _).mpr (hT (.inl i))
  · exact (product_iff _).mpr (hT (.inr ()))

/-- Mathematical descent for an actual source Product common transform.
The original scales and unary entries may be arbitrary complex numbers.
This theorem asserts existence, not effective discovery of the new basis. -/
theorem source_algebraic_basis [Algebra AlgebraicComplex E]
    (h : SharedSource G E₀ (algebraMap AlgebraicComplex E)) :
    ∃ U : InvertibleKernel, (∀ i, Product (U.symm.action (G i))) ∧
      Product (kernelSignature (Kernel.pullback E₀ U.matrix)) :=
  actual_basis G E₀ (descend_templates G E₀
    ((source_iff_templates G E₀ (algebraMap AlgebraicComplex E)).mp h))

theorem templates_of_actual_basis (U : InvertibleKernel)
    (hG : ∀ i, Product (U.symm.action (G i)))
    (hE : Product (kernelSignature (Kernel.pullback E₀ U.matrix))) :
    SharedTemplates G E₀ (RingHom.id AlgebraicComplex) := by
  refine ⟨U.matrix,U.inverse,U.matrix_inverse,U.inverse_matrix,?_⟩
  intro j
  cases j with
  | inl i => exact (product_iff _).mp (hG i)
  | inr u => exact (product_iff _).mp hE

theorem common_iff_templates : CommonTransformable productClass (AffineBranch.indexedFamily G) ↔
    SharedTemplates G Signature.equality (RingHom.id AlgebraicComplex) := by
  constructor
  · rintro ⟨_,U,hE,hG⟩
    exact templates_of_actual_basis G Signature.equality U (fun i => hG _ ⟨i,rfl⟩) hE
  · intro h
    obtain ⟨U,hG,hE⟩ := actual_basis G Signature.equality h
    refine ⟨Set.finite_range _,U,hE,?_⟩
    rintro _ ⟨i,rfl⟩
    exact hG i

theorem commonK_iff_templates :
    CommonKPresentationInKCoordinates productClass (AffineBranch.indexedFamily G) ↔
      SharedTemplates G Signature.disequality (RingHom.id AlgebraicComplex) := by
  constructor
  · rintro ⟨_,U,hE,hG⟩
    exact templates_of_actual_basis G Signature.disequality U (fun i => hG _ ⟨i,rfl⟩) hE
  · intro h
    obtain ⟨U,hG,hE⟩ := actual_basis G Signature.disequality h
    refine ⟨Set.finite_range _,U,hE,?_⟩
    rintro _ ⟨i,rfl⟩
    exact hG i

theorem common_iff_proper : CommonTransformable productClass (AffineBranch.indexedFamily G) ↔
    ∃ B : Branch arity, branchIdeal G Signature.equality B ≠ ⊤ := by
  rw [common_iff_templates,templates_iff_proper]

theorem commonK_iff_proper :
    CommonKPresentationInKCoordinates productClass (AffineBranch.indexedFamily G) ↔
      ∃ B : Branch arity, branchIdeal G Signature.disequality B ≠ ⊤ := by
  rw [commonK_iff_templates,templates_iff_proper]

/-- All bounded Product-template coefficients are included in the actual
finite generated field. Unary/scalar witness parameters remain variables. -/
abbrev coefficientField (B : Branch arity) :=
  FiniteCoefficientSystem.field (equations G E₀ B)

def coefficientIdeal (B : Branch arity) :
    Ideal (MvPolynomial (SymbolicTransform.Variables (Parameters arity))
      (coefficientField G E₀ B)) :=
  Ideal.span (Set.range (FiniteCoefficientSystem.lower (equations G E₀ B)))

theorem templates_iff_coefficient_proper :
    SharedTemplates G E₀ (RingHom.id AlgebraicComplex) ↔
      ∃ B : Branch arity, coefficientIdeal G E₀ B ≠ ⊤ := by
  rw [templates_iff_proper]
  exact exists_congr (fun B => (FiniteCoefficientSystem.proper_iff (equations G E₀ B)).symm)

theorem commonK_iff_coefficient_proper :
    CommonKPresentationInKCoordinates productClass (AffineBranch.indexedFamily G) ↔
      ∃ B : Branch arity, coefficientIdeal G Signature.disequality B ≠ ⊤ := by
  rw [commonK_iff_templates,templates_iff_coefficient_proper]

end
end Holant.LocalDrafts.MainChain.TransformRecognition.ProductBranch
