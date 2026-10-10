import Holant.Proofs.Algorithms.TransformRecognition.SymbolicLocalAffineRows
import Holant.Proofs.Algorithms.TransformRecognition.LocalAffineVariableLayout
import Holant.Proofs.Algorithms.TransformRecognition.LocalAffineBranch
import Holant.Proofs.Algorithms.TransformRecognition.FiniteBranchEnumeration


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalLocalAffineSystem
set_option backward.isDefEq.respectTransparency false
open Holant Holant.Tractable Holant.Algebraic MvPolynomial
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.Sparse
open ProductVariableLayout (Slot slotArity slots mem_slots)
variable {s : ℕ} (arity : Fin s → ℕ)

abbrev Entries := OriginalAffineSystem.Entries arity
abbrev Count := Entries arity + Entries arity
abbrev Extra := OriginalTensorRows.Extra arity (Count arity)
abbrev Width := OriginalTensorRows.Width arity (Count arity)

def scaleIndex (p : LocalAffineBranch.Parameters arity) : Fin (Count arity) :=
  Fin.castAdd (Entries arity) (LocalAffineVariableLayout.address arity p)
def scaleVariable (p : LocalAffineBranch.Parameters arity) : Fin (Width arity) :=
  OriginalVariableLayout.parameter (Entries arity) (Count arity) (scaleIndex arity p)
def inverseVariable (p : LocalAffineBranch.Parameters arity) : Fin (Width arity) :=
  OriginalVariableLayout.parameter (Entries arity) (Count arity)
    (Fin.natAdd (Entries arity) (LocalAffineVariableLayout.address arity p))
def imaginaryVariable : Fin (Width arity) := OriginalVariableLayout.special (Entries arity) (Count arity) 0
def sqrtVariable : Fin (Width arity) := OriginalVariableLayout.special (Entries arity) (Count arity) 1
def eighthVariable : Fin (Width arity) := OriginalVariableLayout.special (Entries arity) (Count arity) 2
def eighthRow : Poly (Width arity) 1 :=
  SymbolicPhaseCoefficients.eighthRootRow (imaginaryVariable arity) (sqrtVariable arity) (eighthVariable arity)
def slotRows (B : LocalAffineBranch.Branch arity) (j : Slot s) : List (Poly (Width arity) 1) :=
  SymbolicLocalAffineRows.rows (OriginalTensorRows.compiled arity (Count arity) j) (B j)
    (imaginaryVariable arity) (eighthVariable arity)
    (fun a => scaleVariable arity ⟨j,a⟩) (fun a => inverseVariable arity ⟨j,a⟩)
def body (B : LocalAffineBranch.Branch arity) : List (Poly (Width arity) 1) :=
  SparseTransform.guard RationalCompiler.data (Extra arity) :: eighthRow arity ::
    (slots s).flatMap (slotRows arity B)
def system (B : LocalAffineBranch.Branch arity) :=
  RationalInputSystem.system (body arity B) (OriginalVariableLayout.binding (Entries arity) (Count arity))
def target (input : OriginalAffineSystem.Input arity) (B : LocalAffineBranch.Branch arity) :=
  RationalInputSystem.target (OriginalVariableLayout.descriptors input) (body arity B)

noncomputable section
abbrev Bound := OriginalTensorRows.Bound arity (Count arity)
def point (z : Fin (Width arity) → ℂ) : SymbolicTransform.Variables (LocalAffineBranch.Parameters arity) → ℂ :=
  OriginalTensorRows.point arity (Count arity) (scaleIndex arity) z
abbrev ev (z : Fin (Width arity) → ℂ) (p : Poly (Width arity) 1) :=
  SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p

theorem compiled_eval (w : Fin (Entries arity) → AlgebraicComplex)
    (z : Fin (Width arity) → ℂ) (hb : Bound arity w z) (j : Slot s)
    (x : Fin (slotArity arity j) → Bool) :
    ev arity z (OriginalTensorRows.compiled arity (Count arity) j x) =
      LocalAffineBranch.evaluated (OriginalAffineSystem.sourceVertex arity w)
        (OriginalAffineSystem.sourceEdge arity w) (algebraMap AlgebraicComplex ℂ) (point arity z) j x := by
  unfold ev
  cases j with
  | inl i =>
    erw [OriginalTensorRows.compiled_vertex_eval arity (Count arity) (scaleIndex arity) w z hb]
    simp [LocalAffineBranch.evaluated,LocalAffineBranch.compiled,SymbolicTransform.eval_vertex,point]
    rfl
  | inr u =>
    cases u
    erw [OriginalTensorRows.compiled_edge_eval arity (Count arity) (scaleIndex arity) w z hb]
    simp [LocalAffineBranch.evaluated,LocalAffineBranch.compiled,SymbolicTransform.eval_edge,point]

theorem body_zero_iff (B : LocalAffineBranch.Branch arity) (z : Fin (Width arity) → ℂ) :
    (∀ p ∈ body arity B, ev arity z p=0) ↔
      ev arity z (SparseTransform.guard RationalCompiler.data (Extra arity))=0 ∧
      ev arity z (eighthRow arity)=0 ∧ ∀ j, ∀ p ∈ slotRows arity B j, ev arity z p=0 := by
  simp only [body,List.mem_cons,forall_eq_or_imp,List.mem_flatMap]
  constructor
  · rintro ⟨hg,hu,hr⟩
    exact ⟨hg,hu,fun j p hp => hr p ⟨j,mem_slots j,hp⟩⟩
  · rintro ⟨hg,hu,hr⟩
    exact ⟨hg,hu,fun p ⟨j,_,hp⟩ => hr j p hp⟩

theorem bound_eighth (w : Fin (Entries arity) → AlgebraicComplex)
    (z : Fin (Width arity) → ℂ) (hb : Bound arity w z)
    (he : ev arity z (eighthRow arity)=0) : z (eighthVariable arity)=(zetaEight : ℂ) := by
  apply SymbolicPhaseCoefficients.eighthRoot_of_row (imaginaryVariable arity)
    (sqrtVariable arity) (eighthVariable arity) z _ _ he
  · rw [show z (imaginaryVariable arity)=Complex.I from OriginalVariableLayout.binding_imaginary z _ hb]
    exact StandardRootCodes.represents 0
  · rw [show z (sqrtVariable arity)=(Real.sqrt 2 : ℂ) from OriginalVariableLayout.binding_sqrt z _ hb]
    exact StandardRootCodes.represents 1

theorem constraints_of_zero (w : Fin (Entries arity) → AlgebraicComplex)
    (z : Fin (Width arity) → ℂ) (hb : Bound arity w z) (B : LocalAffineBranch.Branch arity)
    (h : ∀ p ∈ body arity B, ev arity z p=0) :
    (∀ r, eval₂ (algebraMap AlgebraicComplex ℂ) (point arity z)
      (LocalAffineBranch.equations (OriginalAffineSystem.sourceVertex arity w)
        (OriginalAffineSystem.sourceEdge arity w) B r)=0) ∧
    ∀ p, eval₂ (algebraMap AlgebraicComplex ℂ) (point arity z)
      (LocalAffineBranch.nonzeros (OriginalAffineSystem.sourceVertex arity w)
        (OriginalAffineSystem.sourceEdge arity w) B p) ≠ 0 := by
  obtain ⟨hg,he,hr⟩ := (body_zero_iff arity B z).mp h
  apply (LocalAffineBranch.constraints_iff _ _ _ B _).mpr
  refine ⟨?_,?_⟩
  · exact (OriginalTensorRows.guard_eval arity (Count arity) (scaleIndex arity) z) ▸ hg
  · intro j
    have hm := SymbolicLocalAffineRows.matches_of_zero
      (OriginalTensorRows.compiled arity (Count arity) j) (B j)
      (imaginaryVariable arity) (eighthVariable arity)
      (fun a => scaleVariable arity ⟨j,a⟩) (fun a => inverseVariable arity ⟨j,a⟩) z
      (OriginalVariableLayout.binding_imaginary z _ hb) (bound_eighth arity w z hb he) (hr j)
    change ExtensionLocalAffine.Matches _ _ (fun a => z (scaleVariable arity ⟨j,a⟩)) _
    simpa only [SymbolicLocalAffineRows.ev,compiled_eval arity w z hb] using hm

def fill (w : Fin (Entries arity) → AlgebraicComplex)
    (y : SymbolicTransform.Variables (LocalAffineBranch.Parameters arity) → ℂ) : Fin (Width arity) → ℂ :=
  OriginalVariableLayout.fill (fun i => y (.inl i))
    (Fin.addCases (fun i => y (.inr ((LocalAffineVariableLayout.catalogue arity).get i)))
      (fun i => (LocalAffineBranch.evaluated (OriginalAffineSystem.sourceVertex arity w)
        (OriginalAffineSystem.sourceEdge arity w) (algebraMap AlgebraicComplex ℂ) y
        ((LocalAffineVariableLayout.catalogue arity).get i).1
        ((LocalAffineVariableLayout.catalogue arity).get i).2)⁻¹))
    (fun i => (w i : ℂ)) OriginalVariableLayout.constants

theorem point_fill (w : Fin (Entries arity) → AlgebraicComplex)
    (y : SymbolicTransform.Variables (LocalAffineBranch.Parameters arity) → ℂ) :
    point arity (fill arity w y)=y := by
  funext p
  cases p with
  | inl i => simp [point,OriginalTensorRows.point,fill]
  | inr p =>
    simp only [point,OriginalTensorRows.point,fill,scaleIndex,Sum.elim_inr,
      OriginalVariableLayout.fill_parameter,Fin.addCases_left,LocalAffineVariableLayout.get_address]

theorem fill_scale (w : Fin (Entries arity) → AlgebraicComplex)
    (y : SymbolicTransform.Variables (LocalAffineBranch.Parameters arity) → ℂ)
    (p : LocalAffineBranch.Parameters arity) :
    fill arity w y (scaleVariable arity p)=y (.inr p) := by
  simp only [fill,scaleVariable,scaleIndex,OriginalVariableLayout.fill_parameter,
    Fin.addCases_left,LocalAffineVariableLayout.get_address]

theorem fill_bound (w : Fin (Entries arity) → AlgebraicComplex)
    (y : SymbolicTransform.Variables (LocalAffineBranch.Parameters arity) → ℂ) :
    Bound arity w (fill arity w y) := OriginalVariableLayout.fill_binding _ _ _

theorem fill_inverse (w : Fin (Entries arity) → AlgebraicComplex)
    (y : SymbolicTransform.Variables (LocalAffineBranch.Parameters arity) → ℂ)
    (p : LocalAffineBranch.Parameters arity) :
    fill arity w y (inverseVariable arity p) =
      (LocalAffineBranch.evaluated (OriginalAffineSystem.sourceVertex arity w)
        (OriginalAffineSystem.sourceEdge arity w) (algebraMap AlgebraicComplex ℂ) y p.1 p.2)⁻¹ := by
  simp only [fill,inverseVariable,OriginalVariableLayout.fill_parameter,
    Fin.addCases_right]
  erw [LocalAffineVariableLayout.get_address arity p]

theorem fill_eighth (w : Fin (Entries arity) → AlgebraicComplex)
    (y : SymbolicTransform.Variables (LocalAffineBranch.Parameters arity) → ℂ) :
    ev arity (fill arity w y) (eighthRow arity)=0 := by
  unfold ev
  rw [eighthRow,SymbolicPhaseCoefficients.eighthRootRow_eval]
  simp only [imaginaryVariable,sqrtVariable,eighthVariable,fill,
    OriginalVariableLayout.fill_special,OriginalVariableLayout.constants,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  change (zetaEight : ℂ)*(Real.sqrt 2 : ℂ)-(1+Complex.I)=0
  rw [coe_zetaEight,div_mul_cancel₀,sub_self]
  exact_mod_cast (ne_of_gt (lt_trans (by norm_num : (0:ℝ)<1) StandardRootCodes.sqrtTwo_bounds.1))

theorem zero_of_constraints (w : Fin (Entries arity) → AlgebraicComplex)
    (y : SymbolicTransform.Variables (LocalAffineBranch.Parameters arity) → ℂ)
    (B : LocalAffineBranch.Branch arity)
    (he : ∀ r, eval₂ (algebraMap AlgebraicComplex ℂ) y
      (LocalAffineBranch.equations (OriginalAffineSystem.sourceVertex arity w)
        (OriginalAffineSystem.sourceEdge arity w) B r)=0)
    (hn : ∀ p, eval₂ (algebraMap AlgebraicComplex ℂ) y
      (LocalAffineBranch.nonzeros (OriginalAffineSystem.sourceVertex arity w)
        (OriginalAffineSystem.sourceEdge arity w) B p) ≠ 0) :
    ∀ p ∈ body arity B, ev arity (fill arity w y) p=0 := by
  obtain ⟨hg,hm⟩ := (LocalAffineBranch.constraints_iff _ _ _ B y).mp ⟨he,hn⟩
  apply (body_zero_iff arity B _).mpr
  refine ⟨?_,fill_eighth arity w y,?_⟩
  · unfold ev
    erw [OriginalTensorRows.guard_eval arity (Count arity) (scaleIndex arity)]
    change eval₂ (algebraMap AlgebraicComplex ℂ) (point arity (fill arity w y)) _ = 0
    rw [point_fill]
    exact hg
  · intro j
    apply SymbolicLocalAffineRows.zero_of_matches
    · exact OriginalVariableLayout.binding_imaginary _ _ (fill_bound arity w y)
    · simp [eighthVariable,fill,OriginalVariableLayout.constants]
    · have h := hm j
      simpa only [SymbolicLocalAffineRows.ev,compiled_eval arity w _ (fill_bound arity w y),
        point_fill,fill_scale] using h
    · intro x _
      rw [fill_inverse]
      change _ = (ev arity (fill arity w y) (OriginalTensorRows.compiled arity (Count arity) j x))⁻¹
      rw [compiled_eval arity w _ (fill_bound arity w y),point_fill]

theorem source_solution_iff (w : Fin (Entries arity) → AlgebraicComplex)
    (B : LocalAffineBranch.Branch arity) :
    (∃ z : Fin (Width arity) → ℂ, ∀ e ∈ system arity B,
      aeval z (EncodedSystem.polynomial
        (RationalInputSystem.values (OriginalVariableLayout.boundValues (fun i => (w i : ℂ)))
          (body arity B)) e)=0) ↔
    ∃ y : SymbolicTransform.Variables (LocalAffineBranch.Parameters arity) → ℂ,
      (∀ r, eval₂ (algebraMap AlgebraicComplex ℂ) y
        (LocalAffineBranch.equations (OriginalAffineSystem.sourceVertex arity w)
          (OriginalAffineSystem.sourceEdge arity w) B r)=0) ∧
      ∀ p, eval₂ (algebraMap AlgebraicComplex ℂ) y
        (LocalAffineBranch.nonzeros (OriginalAffineSystem.sourceVertex arity w)
          (OriginalAffineSystem.sourceEdge arity w) B p) ≠ 0 := by
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨hb,hr⟩ := (RationalInputSystem.system_zero_iff _ _ _ z).mp hz
    exact ⟨point arity z,constraints_of_zero arity w z hb B hr⟩
  · rintro ⟨y,he,hn⟩
    refine ⟨fill arity w y,(RationalInputSystem.system_zero_iff _ _ _ _).mpr ?_⟩
    exact ⟨fill_bound arity w y,zero_of_constraints arity w y B he hn⟩

end
end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalLocalAffineSystem
