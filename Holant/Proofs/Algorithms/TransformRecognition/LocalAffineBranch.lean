import Holant.Proofs.Algorithms.TransformRecognition.ProductVariableLayout
import Holant.Proofs.Algorithms.TransformRecognition.AffineBranch
import Holant.Proofs.Algorithms.TransformRecognition.ExtensionLocalAffine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.LocalAffineBranch
set_option backward.isDefEq.respectTransparency false
open Holant.Tractable MvPolynomial
noncomputable section
attribute [local instance] Classical.propDecidable
local instance : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
variable {s : ℕ} (arity : Fin s → ℕ)

abbrev Slot := Fin s ⊕ Unit
abbrev slotArity : Slot (s:=s) → ℕ := ProductVariableLayout.slotArity arity
abbrev WordAt (j : Slot (s:=s)) := Fin (slotArity arity j) → Bool
abbrev Parameters := Σ j : Slot (s:=s), WordAt arity j
abbrev Branch := (j : Slot (s:=s)) → LocalAffineNormalForm.Code (slotArity arity j)
abbrev EquationIndex := Unit ⊕ (Parameters arity ⊕
  (Σ j : Slot (s:=s), WordAt arity j × WordAt arity j))

variable {arity} (G : (i : Fin s) → Signature AlgebraicComplex (arity i))
    (E₀ : Kernel AlgebraicComplex)

def compiled : (j : Slot (s:=s)) → Signature (SymbolicTransform.Poly (Parameters arity))
    (slotArity arity j)
  | .inl i => SymbolicTransform.vertex (G i)
  | .inr _ => fun x => SymbolicTransform.edge E₀ (x (0 : Fin 2)) (x (1 : Fin 2))

def equations (B : Branch arity) : EquationIndex arity → SymbolicTransform.Poly (Parameters arity)
  | .inl _ => SymbolicTransform.guard _
  | .inr (.inl ⟨j,x⟩) => if x ∈ (B j).1 then 0 else compiled G E₀ j x
  | .inr (.inr ⟨j,alpha,x⟩) => if alpha ∈ (B j).1 then
      C (LocalAffineTwists.phaseWeight alpha x)*compiled G E₀ j x -
        X (.inr ⟨j,alpha⟩)*C (ExtensionAffine.coefficient ((B j).2 alpha) x)
      else 0

abbrev NonzeroIndex (B : Branch arity) := {p : Parameters arity // p.2 ∈ (B p.1).1}

def nonzeros (B : Branch arity) (p : NonzeroIndex B) :
    SymbolicTransform.Poly (Parameters arity) := compiled G E₀ p.val.1 p.val.2

variable {E : Type*} [Field E] (φ : AlgebraicComplex →+* E)

def evaluated (z : SymbolicTransform.Variables (Parameters arity) → E)
    (j : Slot (s:=s)) : Signature E (slotArity arity j) :=
  fun x => eval₂ φ z (compiled G E₀ j x)

/-- Pointwise constraints have exactly the original support/twist meaning. -/
theorem constraints_iff (B : Branch arity)
    (z : SymbolicTransform.Variables (Parameters arity) → E) :
    ((∀ r, eval₂ φ z (equations G E₀ B r)=0) ∧
      ∀ p, eval₂ φ z (nonzeros G E₀ B p) ≠ 0) ↔
    eval₂ φ z (SymbolicTransform.guard (Parameters arity))=0 ∧
      ∀ j, ExtensionLocalAffine.Matches φ (B j) (fun alpha => z (.inr ⟨j,alpha⟩))
        (evaluated G E₀ φ z j) := by
  constructor
  · rintro ⟨he,hn⟩
    refine ⟨he (.inl ()),?_⟩
    intro j
    apply (ExtensionLocalAffine.entry_constraints φ _ _ _).mpr
    refine ⟨?_,?_,?_⟩
    · intro x hx
      exact hn ⟨⟨j,x⟩,hx⟩
    · intro x hx
      simpa [equations,hx,evaluated] using he (.inr (.inl ⟨j,x⟩))
    · intro alpha ha x
      simpa [equations,ha,evaluated,sub_eq_zero] using he (.inr (.inr ⟨j,alpha,x⟩))
  · rintro ⟨hg,hm⟩
    have hc := fun j => (ExtensionLocalAffine.entry_constraints φ _ _ _).mp (hm j)
    constructor
    · intro r
      rcases r with u | (⟨j,x⟩ | ⟨j,alpha,x⟩)
      · exact hg
      · by_cases hx : x ∈ (B j).1
        · simp [equations,hx]
        · simpa [equations,hx,evaluated] using (hc j).2.1 x hx
      · by_cases ha : alpha ∈ (B j).1
        · simpa [equations,ha,evaluated,sub_eq_zero] using (hc j).2.2 alpha ha x
        · simp [equations,ha]
    · intro p
      exact (hc p.val.1).1 p.val.2 p.property

def transformed (U V : Kernel E) : (j : Slot (s:=s)) → Signature E (slotArity arity j)
  | .inl i => Signature.coordinateAction (fun _ => V) (fun x => φ (G i x))
  | .inr _ => fun x => Kernel.pullback (fun a b => φ (E₀ a b)) U (x (0 : Fin 2)) (x (1 : Fin 2))

def Shared : Prop := ∃ U V : Kernel E,
  Kernel.mul U V=Signature.equality ∧ Kernel.mul V U=Signature.equality ∧
  ∀ j, ExtensionLocalAffine.LocalAffineOver φ (transformed G E₀ φ U V j)

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

theorem solution_of_shared (h : Shared G E₀ φ) :
    ∃ B : Branch arity, ∃ z : SymbolicTransform.Variables (Parameters arity) → E,
      (∀ r, eval₂ φ z (equations G E₀ B r)=0) ∧
      ∀ p, eval₂ φ z (nonzeros G E₀ B p) ≠ 0 := by
  obtain ⟨U,V,hUV,hVU,hL⟩ := h
  have hex := fun j => (ExtensionLocalAffine.localAffine_iff φ _).mp (hL j)
  choose B c hc using hex
  let parameters : Parameters arity → E := fun p => c p.1 p.2
  refine ⟨B,SymbolicTransform.point U parameters,?_⟩
  apply (constraints_iff G E₀ φ B _).mpr
  refine ⟨SymbolicTransform.point_guard φ U V parameters hUV,?_⟩
  intro j
  rw [evaluated_point G E₀ φ U V parameters hUV hVU]
  exact hc j

theorem shared_of_solution (B : Branch arity)
    (z : SymbolicTransform.Variables (Parameters arity) → E)
    (he : ∀ r, eval₂ φ z (equations G E₀ B r)=0)
    (hn : ∀ p, eval₂ φ z (nonzeros G E₀ B p) ≠ 0) : Shared G E₀ φ := by
  obtain ⟨hg,hm⟩ := (constraints_iff G E₀ φ B z).mp ⟨he,hn⟩
  have hi := SymbolicTransform.inverse_identities φ z hg
  refine ⟨SymbolicTransform.matrix z,SymbolicTransform.inverse z,hi.1,hi.2,?_⟩
  intro j
  rw [← evaluated_at G E₀ φ z j]
  exact (ExtensionLocalAffine.localAffine_iff φ _).mpr ⟨B j,_,hm j⟩

/-- The support inequations survive descent; preserving only equations would
not justify the supported-twist implications of the original definition. -/
theorem descend [Algebra AlgebraicComplex E]
    (h : Shared G E₀ (algebraMap AlgebraicComplex E)) :
    Shared G E₀ (RingHom.id AlgebraicComplex) := by
  obtain ⟨B,z,he,hn⟩ := solution_of_shared G E₀ (algebraMap AlgebraicComplex E) h
  have hae : ∀ r, aeval z (equations G E₀ B r)=0 := he
  have han : ∀ p, aeval z (nonzeros G E₀ B p) ≠ 0 := hn
  obtain ⟨y,hye,hyn⟩ := ConstructibleDescent.constraints_descend_indexed
    (equations G E₀ B) (nonzeros G E₀ B) z hae han
  exact shared_of_solution G E₀ (RingHom.id AlgebraicComplex) B y hye hyn

theorem actual_basis (h : Shared G E₀ (RingHom.id AlgebraicComplex)) :
    ∃ U : InvertibleKernel, (∀ i, LocalAffine (U.symm.action (G i))) ∧
      LocalAffine (kernelSignature (Kernel.pullback E₀ U.matrix)) := by
  obtain ⟨U,V,hUV,hVU,hL⟩ := h
  refine ⟨⟨U,V,hUV,hVU⟩,?_,?_⟩
  · intro i
    exact (ExtensionLocalAffine.localAffine_id_iff _).mp (hL (.inl i))
  · exact (ExtensionLocalAffine.localAffine_id_iff _).mp (hL (.inr ()))

def branchIdeal (B : Branch arity) :
    Ideal (MvPolynomial (Option (SymbolicTransform.Variables (Parameters arity))) AlgebraicComplex) :=
  Ideal.span (Set.range (ConstructibleDescent.indexedAugmented
    (equations G E₀ B) (nonzeros G E₀ B)))

theorem shared_iff_proper : Shared G E₀ (RingHom.id AlgebraicComplex) ↔
    ∃ B : Branch arity, branchIdeal G E₀ B ≠ ⊤ := by
  constructor
  · intro h
    obtain ⟨B,z,he,hn⟩ := solution_of_shared G E₀ (RingHom.id AlgebraicComplex) h
    exact ⟨B,(ConstructibleDescent.constraints_iff_proper_indexed
      (equations G E₀ B) (nonzeros G E₀ B)).mp ⟨z,he,hn⟩⟩
  · rintro ⟨B,hB⟩
    obtain ⟨z,he,hn⟩ := (ConstructibleDescent.constraints_iff_proper_indexed
      (equations G E₀ B) (nonzeros G E₀ B)).mpr hB
    exact shared_of_solution G E₀ (RingHom.id AlgebraicComplex) B z he hn

theorem shared_of_actual_basis (U : InvertibleKernel)
    (hG : ∀ i, LocalAffine (U.symm.action (G i)))
    (hE : LocalAffine (kernelSignature (Kernel.pullback E₀ U.matrix))) :
    Shared G E₀ (RingHom.id AlgebraicComplex) := by
  refine ⟨U.matrix,U.inverse,U.matrix_inverse,U.inverse_matrix,?_⟩
  intro j
  cases j with
  | inl i => exact (ExtensionLocalAffine.localAffine_id_iff _).mpr (hG i)
  | inr u => exact (ExtensionLocalAffine.localAffine_id_iff _).mpr hE

theorem common_iff_shared :
    CommonTransformable localAffineClass (AffineBranch.indexedFamily G) ↔
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
    CommonKPresentationInKCoordinates localAffineClass (AffineBranch.indexedFamily G) ↔
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

theorem common_iff_proper :
    CommonTransformable localAffineClass (AffineBranch.indexedFamily G) ↔
      ∃ B : Branch arity, branchIdeal G Signature.equality B ≠ ⊤ := by
  rw [common_iff_shared,shared_iff_proper]

theorem commonK_iff_proper :
    CommonKPresentationInKCoordinates localAffineClass (AffineBranch.indexedFamily G) ↔
      ∃ B : Branch arity, branchIdeal G Signature.disequality B ≠ ⊤ := by
  rw [commonK_iff_shared,shared_iff_proper]

/-- Lower the AUGMENTED system: retaining only equations would erase the
nonzero support constraints and change the source local-affine condition. -/
def coefficientSystem (B : Branch arity) :=
  ConstructibleDescent.indexedAugmented (equations G E₀ B) (nonzeros G E₀ B)

abbrev coefficientField (B : Branch arity) :=
  FiniteCoefficientSystem.field (coefficientSystem G E₀ B)

def coefficientIdeal (B : Branch arity) :
    Ideal (MvPolynomial (Option (SymbolicTransform.Variables (Parameters arity)))
      (coefficientField G E₀ B)) :=
  Ideal.span (Set.range (FiniteCoefficientSystem.lower (coefficientSystem G E₀ B)))

theorem shared_iff_coefficient_proper :
    Shared G E₀ (RingHom.id AlgebraicComplex) ↔
      ∃ B : Branch arity, coefficientIdeal G E₀ B ≠ ⊤ := by
  rw [shared_iff_proper]
  exact exists_congr (fun B =>
    (FiniteCoefficientSystem.proper_iff (coefficientSystem G E₀ B)).symm)

theorem commonK_iff_coefficient_proper :
    CommonKPresentationInKCoordinates localAffineClass (AffineBranch.indexedFamily G) ↔
      ∃ B : Branch arity, coefficientIdeal G Signature.disequality B ≠ ⊤ := by
  rw [commonK_iff_shared,shared_iff_coefficient_proper]

end
end Holant.LocalDrafts.MainChain.TransformRecognition.LocalAffineBranch
