import Holant.Proofs.Algorithms.TransformRecognition.ExtensionAffine
import Holant.Proofs.Algorithms.TransformRecognition.SymbolicTransform
import Holant.Proofs.Algorithms.TransformRecognition.ConstructibleDescent
import Holant.Proofs.Algorithms.TransformRecognition.FiniteCoefficientSystem
import Mathlib.Analysis.Complex.Polynomial.Basic


namespace Holant.LocalDrafts.MainChain.TransformRecognition.AffineBranch
open Holant.Tractable MvPolynomial
noncomputable section
attribute [local instance] Classical.propDecidable
local instance : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ

variable {s : ℕ} (arity : Fin s → ℕ)

abbrev Parameters := Fin s ⊕ Unit
abbrev Branch := ((i : Fin s) → AffineNormalForm.Code (arity i)) × AffineNormalForm.Code 2
abbrev EquationIndex := Unit ⊕ ((Σ i : Fin s, Fin (arity i) → Bool) ⊕ (Fin 2 → Bool))

variable {arity} (G : (i : Fin s) → Signature AlgebraicComplex (arity i))
    (E₀ : Kernel AlgebraicComplex)

def equations (B : Branch arity) : EquationIndex arity → SymbolicTransform.Poly (Parameters (s:=s))
  | .inl _ => SymbolicTransform.guard _
  | .inr (.inl ⟨i,x⟩) => SymbolicTransform.vertex (G i) x -
      X (.inr (.inl i)) * C (ExtensionAffine.coefficient (B.1 i) x)
  | .inr (.inr x) => SymbolicTransform.edge E₀ (x 0) (x 1) -
      X (.inr (.inr ())) * C (ExtensionAffine.coefficient B.2 x)

variable {E : Type*} [Field E] (φ : AlgebraicComplex →+* E)

/-- Literal source condition over E, with extension-valued scales allowed. -/
def Shared : Prop := ∃ U V : Kernel E,
  Kernel.mul U V=Signature.equality ∧ Kernel.mul V U=Signature.equality ∧
  (∀ i, ExtensionAffine.AffineOver φ
    (Signature.coordinateAction (fun _ => V) (fun x => φ (G i x)))) ∧
  ExtensionAffine.AffineOver φ
    (fun x : Fin 2 → Bool => Kernel.pullback (fun a b => φ (E₀ a b)) U (x 0) (x 1))

theorem solution_of_shared (h : Shared G E₀ φ) :
    ∃ B : Branch arity, ∃ z : SymbolicTransform.Variables (Parameters (s:=s)) → E,
      ∀ r, eval₂ φ z (equations G E₀ B r)=0 := by
  obtain ⟨U,V,hUV,hVU,hG,hE⟩ := h
  have hv := fun i => (ExtensionAffine.affine_iff φ _).mp (hG i)
  choose codes scalars hcodes using hv
  obtain ⟨ecode,escale,hecode⟩ := (ExtensionAffine.affine_iff φ _).mp hE
  let B : Branch arity := (codes,ecode)
  let parameters : Parameters (s:=s) → E := Sum.elim scalars (fun _ => escale)
  refine ⟨B,SymbolicTransform.point U parameters,?_⟩
  intro r
  rcases r with u | (⟨i,x⟩ | x)
  · exact SymbolicTransform.point_guard φ U V parameters hUV
  · have hx := congrFun (hcodes i) x
    simp only [equations,eval₂_sub,eval₂_mul,eval₂_X,eval₂_C]
    rw [SymbolicTransform.point_vertex φ U V parameters hUV hVU]
    exact sub_eq_zero.mpr hx
  · have hx := congrFun hecode x
    simp only [equations,eval₂_sub,eval₂_mul,eval₂_X,eval₂_C]
    rw [SymbolicTransform.point_edge]
    exact sub_eq_zero.mpr hx

theorem shared_of_solution (B : Branch arity)
    (z : SymbolicTransform.Variables (Parameters (s:=s)) → E)
    (hz : ∀ r, eval₂ φ z (equations G E₀ B r)=0) : Shared G E₀ φ := by
  have hg : eval₂ φ z (SymbolicTransform.guard (Parameters (s:=s)))=0 := hz (.inl ())
  have hi := SymbolicTransform.inverse_identities φ z hg
  refine ⟨SymbolicTransform.matrix z,SymbolicTransform.inverse z,hi.1,hi.2,?_,?_⟩
  · intro i
    apply (ExtensionAffine.affine_iff φ _).mpr
    refine ⟨B.1 i,z (.inr (.inl i)),?_⟩
    funext x
    have hx := hz (.inr (.inl ⟨i,x⟩))
    simpa [equations,SymbolicTransform.eval_vertex,ExtensionAffine.formula,
      sub_eq_zero] using hx
  · apply (ExtensionAffine.affine_iff φ _).mpr
    refine ⟨B.2,z (.inr (.inr ())),?_⟩
    funext x
    have hx := hz (.inr (.inr x))
    simpa [equations,SymbolicTransform.eval_edge,ExtensionAffine.formula,
      sub_eq_zero] using hx

theorem shared_iff_solution : Shared G E₀ φ ↔
    ∃ B : Branch arity, ∃ z : SymbolicTransform.Variables (Parameters (s:=s)) → E,
      ∀ r, eval₂ φ z (equations G E₀ B r)=0 :=
  ⟨solution_of_shared G E₀ φ,fun ⟨B,z,hz⟩ => shared_of_solution G E₀ φ B z hz⟩

/-- All matrix entries, inverse determinant and ALL scales descend together.
No algebraicity of the original E-valued witness is a premise. -/
theorem descend [Algebra AlgebraicComplex E]
    (h : Shared G E₀ (algebraMap AlgebraicComplex E)) :
    Shared G E₀ (RingHom.id AlgebraicComplex) := by
  obtain ⟨B,z,hz⟩ := solution_of_shared G E₀ (algebraMap AlgebraicComplex E) h
  have ha : ∀ r, aeval z (equations G E₀ B r)=0 := hz
  obtain ⟨y,hy⟩ := ConstructibleDescent.equations_descend (equations G E₀ B) z ha
  exact shared_of_solution G E₀ (RingHom.id AlgebraicComplex) B y hy

def branchIdeal (B : Branch arity) :
    Ideal (SymbolicTransform.Poly (Parameters (s:=s))) :=
  Ideal.span (Set.range (equations G E₀ B))

/-- Finite union of explicit proper-ideal tests. This is an equivalence of
propositions; it does not use classical decidability to claim an algorithm. -/
theorem shared_iff_proper : Shared G E₀ (RingHom.id AlgebraicComplex) ↔
    ∃ B : Branch arity, branchIdeal G E₀ B ≠ ⊤ := by
  rw [shared_iff_solution]
  constructor
  · rintro ⟨B,z,hz⟩
    refine ⟨B,?_⟩
    have hker : branchIdeal G E₀ B ≤ RingHom.ker (aeval z).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨r,rfl⟩
      exact hz r
    intro ht
    have hone : (1 : SymbolicTransform.Poly (Parameters (s:=s))) ∈ branchIdeal G E₀ B := by
      rw [ht]
      trivial
    have he := hker hone
    change aeval z 1=0 at he
    simpa using he
  · rintro ⟨B,hB⟩
    obtain ⟨z,hz⟩ := ConstructibleDescent.point_of_proper (branchIdeal G E₀ B) hB
    exact ⟨B,z,fun r => hz _ (Ideal.subset_span ⟨r,rfl⟩)⟩

/-- Recover the existing source's actual common inverse object, including
the required transformed edge; no per-signature choice of matrix occurs. -/
theorem actual_basis (h : Shared G E₀ (RingHom.id AlgebraicComplex)) :
    ∃ U : InvertibleKernel,
      (∀ i, Affine (U.symm.action (G i))) ∧
      Affine (kernelSignature (Kernel.pullback E₀ U.matrix)) := by
  obtain ⟨U,V,hUV,hVU,hG,hE⟩ := h
  refine ⟨⟨U,V,hUV,hVU⟩,?_,?_⟩
  · intro i
    exact (ExtensionAffine.affine_id_iff _).mp (hG i)
  · exact (ExtensionAffine.affine_id_iff _).mp hE

theorem shared_of_actual_basis (U : InvertibleKernel)
    (hG : ∀ i, Affine (U.symm.action (G i)))
    (hE : Affine (kernelSignature (Kernel.pullback E₀ U.matrix))) :
    Shared G E₀ (RingHom.id AlgebraicComplex) := by
  refine ⟨U.matrix,U.inverse,U.matrix_inverse,U.inverse_matrix,?_,?_⟩
  · intro i
    exact (ExtensionAffine.affine_id_iff _).mpr (hG i)
  · exact (ExtensionAffine.affine_id_iff _).mpr hE

def indexedFamily : SignatureFamily AlgebraicComplex :=
  Set.range (fun i : Fin s => (⟨arity i,G i⟩ : AnySignature AlgebraicComplex))

theorem common_iff_shared : CommonTransformable affineClass (indexedFamily G) ↔
    Shared G Signature.equality (RingHom.id AlgebraicComplex) := by
  constructor
  · rintro ⟨_,U,hE,hG⟩
    exact shared_of_actual_basis G Signature.equality U
      (fun i => hG _ ⟨i,rfl⟩) hE
  · intro h
    obtain ⟨U,hG,hE⟩ := actual_basis G Signature.equality h
    refine ⟨Set.finite_range _,U,hE,?_⟩
    rintro _ ⟨i,rfl⟩
    exact hG i

theorem commonK_iff_shared :
    CommonKPresentationInKCoordinates affineClass (indexedFamily G) ↔
      Shared G Signature.disequality (RingHom.id AlgebraicComplex) := by
  constructor
  · rintro ⟨_,U,hE,hG⟩
    exact shared_of_actual_basis G Signature.disequality U
      (fun i => hG _ ⟨i,rfl⟩) hE
  · intro h
    obtain ⟨U,hG,hE⟩ := actual_basis G Signature.disequality h
    refine ⟨Set.finite_range _,U,hE,?_⟩
    rintro _ ⟨i,rfl⟩
    exact hG i

theorem common_iff_proper : CommonTransformable affineClass (indexedFamily G) ↔
    ∃ B : Branch arity, branchIdeal G Signature.equality B ≠ ⊤ := by
  rw [common_iff_shared,shared_iff_proper]

theorem commonK_iff_proper :
    CommonKPresentationInKCoordinates affineClass (indexedFamily G) ↔
      ∃ B : Branch arity, branchIdeal G Signature.disequality B ≠ ⊤ := by
  rw [commonK_iff_shared,shared_iff_proper]

/-- Literal finite coefficient systems for each branch. The field contains
all coefficients of the guard, every vertex equation and the transformed
edge equation, including the chosen finite phase code. Witness coordinates
are not required to belong to this field. -/
abbrev coefficientField (B : Branch arity) :=
  FiniteCoefficientSystem.field (equations G E₀ B)

def coefficientIdeal (B : Branch arity) :
    Ideal (MvPolynomial (SymbolicTransform.Variables (Parameters (s:=s)))
      (coefficientField G E₀ B)) :=
  Ideal.span (Set.range (FiniteCoefficientSystem.lower (equations G E₀ B)))

theorem shared_iff_coefficient_proper :
    Shared G E₀ (RingHom.id AlgebraicComplex) ↔
      ∃ B : Branch arity, coefficientIdeal G E₀ B ≠ ⊤ := by
  rw [shared_iff_proper]
  exact exists_congr (fun B => (FiniteCoefficientSystem.proper_iff (equations G E₀ B)).symm)

theorem commonK_iff_coefficient_proper :
    CommonKPresentationInKCoordinates affineClass (indexedFamily G) ↔
      ∃ B : Branch arity, coefficientIdeal G Signature.disequality B ≠ ⊤ := by
  rw [commonK_iff_shared,shared_iff_coefficient_proper]

end
end Holant.LocalDrafts.MainChain.TransformRecognition.AffineBranch
