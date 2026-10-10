import Holant.Proofs.Algorithms.TransformRecognition.OriginalTensorRows
import Holant.Proofs.Algorithms.TransformRecognition.SparseProductTemplate
import Holant.Proofs.Algorithms.TransformRecognition.ProductBranch
import Holant.Proofs.Algorithms.TransformRecognition.FiniteBranchEnumeration


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalProductSystem
set_option backward.isDefEq.respectTransparency false
open Holant Holant.Tractable Holant.Algebraic MvPolynomial
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.Sparse
open Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm
open ProductVariableLayout (Slot slotArity slots mem_slots)
variable {s : ℕ} (arity : Fin s → ℕ)

abbrev Entries := OriginalAffineSystem.Entries arity
abbrev Count := (ProductVariableLayout.catalogue arity).length
abbrev Width := OriginalTensorRows.Width arity (Count arity)
abbrev Extra := OriginalTensorRows.Extra arity (Count arity)

def edgeList {n : ℕ} (B : Skeleton n) : List (Edge n) :=
  (FiniteBranchEnumeration.productEdges n).filter (fun e => decide (e ∈ B))

theorem edgeList_exact {n : ℕ} (B : Skeleton n) : (edgeList B).toFinset=B := by
  ext e
  simp [edgeList,FiniteBranchEnumeration.mem_productEdges]

def parameterVariable (p : ProductBranch.Parameters arity) : Fin (Width arity) :=
  OriginalVariableLayout.parameter (Entries arity) (Count arity) (ProductVariableLayout.address arity p)
def row (B : ProductBranch.Branch arity) (j : Slot s)
    (x : Fin (slotArity arity j) → Bool) : Poly (Width arity) 1 :=
  sub (OriginalTensorRows.compiled arity (Count arity) j x)
    (SparseProductTemplate.entry RationalCompiler.data (edgeList (B j))
      (fun p => parameterVariable arity ⟨j,p⟩) x)

def body (B : ProductBranch.Branch arity) : List (Poly (Width arity) 1) :=
  SparseTransform.guard RationalCompiler.data (Extra arity) ::
    (slots s).flatMap (fun j => (SparseTransform.allWords (slotArity arity j)).map (row arity B j))
def system (B : ProductBranch.Branch arity) :=
  RationalInputSystem.system (body arity B) (OriginalVariableLayout.binding (Entries arity) (Count arity))
def target (input : OriginalAffineSystem.Input arity) (B : ProductBranch.Branch arity) :=
  RationalInputSystem.target (OriginalVariableLayout.descriptors input) (body arity B)

noncomputable section

def point (z : Fin (Width arity) → ℂ) : SymbolicTransform.Variables (ProductBranch.Parameters arity) → ℂ :=
  OriginalTensorRows.point arity (Count arity) (ProductVariableLayout.address arity) z
abbrev Bound := OriginalTensorRows.Bound arity (Count arity)

theorem template_eval (B : ProductBranch.Branch arity) (j : Slot s)
    (x : Fin (slotArity arity j) → Bool) (z : Fin (Width arity) → ℂ) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
      (SparseProductTemplate.entry RationalCompiler.data (edgeList (B j))
        (fun p => parameterVariable arity ⟨j,p⟩) x) =
      evaluate (B j) (fun p => point arity z (.inr ⟨j,p⟩)) x := by
  change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
    (SparseProductTemplate.entry RationalCompiler.field.toArithmeticData (edgeList (B j))
      (fun p => parameterVariable arity ⟨j,p⟩) x) = _
  erw [SparseProductTemplate.entry_eval,edgeList_exact]
  rfl

theorem compiled_eval (w : Fin (Entries arity) → AlgebraicComplex)
    (z : Fin (Width arity) → ℂ) (hb : Bound arity w z)
    (j : Slot s) (x : Fin (slotArity arity j) → Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
      (OriginalTensorRows.compiled arity (Count arity) j x) =
      eval₂ (algebraMap AlgebraicComplex ℂ) (point arity z)
        (ProductBranch.compiled (OriginalAffineSystem.sourceVertex arity w)
          (OriginalAffineSystem.sourceEdge arity w) j x) := by
  cases j with
  | inl i =>
    erw [OriginalTensorRows.compiled_vertex_eval arity (Count arity)
      (ProductVariableLayout.address arity) w z hb]
    simp [ProductBranch.compiled,SymbolicTransform.eval_vertex,point]
    rfl
  | inr u =>
    cases u
    erw [OriginalTensorRows.compiled_edge_eval arity (Count arity)
      (ProductVariableLayout.address arity) w z hb]
    simp [ProductBranch.compiled,SymbolicTransform.eval_edge,point]

theorem row_source (w : Fin (Entries arity) → AlgebraicComplex)
    (z : Fin (Width arity) → ℂ) (hb : Bound arity w z) (B : ProductBranch.Branch arity)
    (j : Slot s) (x : Fin (slotArity arity j) → Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z (row arity B j x) =
      eval₂ (algebraMap AlgebraicComplex ℂ) (point arity z)
        (ProductBranch.equations (OriginalAffineSystem.sourceVertex arity w)
          (OriginalAffineSystem.sourceEdge arity w) B (.inr ⟨j,x⟩)) := by
  rw [row,SparseEvaluation.sub_eval,compiled_eval arity w z hb,template_eval]
  simp [ProductBranch.equations,ProductBranch.eval_template]

theorem body_source_iff (w : Fin (Entries arity) → AlgebraicComplex)
    (z : Fin (Width arity) → ℂ) (hb : Bound arity w z) (B : ProductBranch.Branch arity) :
    (∀ p ∈ body arity B, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0) ↔
      ∀ r, eval₂ (algebraMap AlgebraicComplex ℂ) (point arity z)
        (ProductBranch.equations (OriginalAffineSystem.sourceVertex arity w)
          (OriginalAffineSystem.sourceEdge arity w) B r)=0 := by
  constructor
  · intro h r
    rcases r with u | ⟨j,x⟩
    · cases u
      have hg := h _ (List.mem_cons_self ..)
      rw [OriginalTensorRows.guard_eval arity (Count arity) (ProductVariableLayout.address arity)] at hg
      exact hg
    · rw [←row_source arity w z hb]
      exact h _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr
        ⟨j,mem_slots j,List.mem_map.mpr ⟨x,SparseTransform.mem_allWords x,rfl⟩⟩))
  · intro h p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [OriginalTensorRows.guard_eval arity (Count arity) (ProductVariableLayout.address arity)]
      exact h (.inl ())
    · obtain ⟨j,_,hx⟩ := List.mem_flatMap.mp hp
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hx
      rw [row_source arity w z hb]
      exact h (.inr ⟨j,x⟩)

def fill (w : Fin (Entries arity) → AlgebraicComplex)
    (y : SymbolicTransform.Variables (ProductBranch.Parameters arity) → ℂ) : Fin (Width arity) → ℂ :=
  OriginalVariableLayout.fill (fun i => y (.inl i))
    (fun i => y (.inr ((ProductVariableLayout.catalogue arity).get i)))
    (fun i => (w i : ℂ)) OriginalVariableLayout.constants

theorem point_fill (w : Fin (Entries arity) → AlgebraicComplex)
    (y : SymbolicTransform.Variables (ProductBranch.Parameters arity) → ℂ) :
    point arity (fill arity w y)=y := by
  funext p
  cases p with
  | inl i => simp [point,OriginalTensorRows.point,fill]
  | inr p =>
    simp only [point,OriginalTensorRows.point,fill,Sum.elim_inr,
      OriginalVariableLayout.fill_parameter,ProductVariableLayout.get_address]

theorem fill_bound (w : Fin (Entries arity) → AlgebraicComplex)
    (y : SymbolicTransform.Variables (ProductBranch.Parameters arity) → ℂ) : Bound arity w (fill arity w y) :=
  OriginalVariableLayout.fill_binding _ _ _

theorem source_solution_iff (w : Fin (Entries arity) → AlgebraicComplex) (B : ProductBranch.Branch arity) :
    (∃ z : Fin (Width arity) → ℂ, ∀ e ∈ system arity B,
      aeval z (EncodedSystem.polynomial
        (RationalInputSystem.values (OriginalVariableLayout.boundValues (fun i => (w i : ℂ)))
          (body arity B)) e)=0) ↔
    ∃ y : SymbolicTransform.Variables (ProductBranch.Parameters arity) → ℂ,
      ∀ r, eval₂ (algebraMap AlgebraicComplex ℂ) y
        (ProductBranch.equations (OriginalAffineSystem.sourceVertex arity w)
          (OriginalAffineSystem.sourceEdge arity w) B r)=0 := by
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨hb,he⟩ := (RationalInputSystem.system_zero_iff _ _ _ z).mp hz
    exact ⟨point arity z,(body_source_iff arity w z hb B).mp he⟩
  · rintro ⟨y,hy⟩
    refine ⟨fill arity w y,?_⟩
    apply (RationalInputSystem.system_zero_iff _ _ _ _).mpr
    refine ⟨fill_bound arity w y,?_⟩
    apply (body_source_iff arity w _ (fill_bound arity w y) B).mpr
    simpa only [point_fill] using hy

theorem source_shared_iff (w : Fin (Entries arity) → AlgebraicComplex) :
    ProductBranch.SharedSource (OriginalAffineSystem.sourceVertex arity w)
      (OriginalAffineSystem.sourceEdge arity w) (algebraMap AlgebraicComplex ℂ) ↔
      ∃ B : ProductBranch.Branch arity, ∃ z : Fin (Width arity) → ℂ,
        ∀ e ∈ system arity B, aeval z (EncodedSystem.polynomial
          (RationalInputSystem.values (OriginalVariableLayout.boundValues (fun i => (w i : ℂ)))
            (body arity B)) e)=0 := by
  rw [ProductBranch.source_iff_templates,ProductBranch.templates_iff_solution]
  exact exists_congr (fun B => (source_solution_iff arity w B).symm)

end
end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalProductSystem
