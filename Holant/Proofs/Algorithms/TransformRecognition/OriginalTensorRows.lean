import Holant.Proofs.Algorithms.TransformRecognition.OriginalAffineSystem


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalTensorRows
set_option backward.isDefEq.respectTransparency false
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.Sparse
open ProductVariableLayout (Slot slotArity)
variable {s : ℕ} (arity : Fin s → ℕ) (q : ℕ)

abbrev Entries := OriginalAffineSystem.Entries arity
abbrev Extra := OriginalVariableLayout.Extra (Entries arity) q
abbrev Width := OriginalVariableLayout.Width (Entries arity) q

def entryVariable (j : Slot s) (x : Fin (slotArity arity j) → Bool) : Fin (Width arity q) :=
  OriginalVariableLayout.original (Entries arity) q (OriginalAffineSystem.entryIndex arity j x)

def compiled : (j : Slot s) → (Fin (slotArity arity j) → Bool) → Poly (Width arity q) 1
  | .inl i => SymbolicInputTable.vertex RationalCompiler.data
      (SparseTransform.inverse RationalCompiler.data (Extra arity q))
      (fun x => SparseTransform.variableCode RationalCompiler.data (entryVariable arity q (.inl i) x))
  | .inr _ => fun x => SymbolicInputTable.edge RationalCompiler.data
      (SparseTransform.matrix RationalCompiler.data (Extra arity q))
      (fun a b => SparseTransform.variableCode RationalCompiler.data
        (entryVariable arity q (.inr ()) ![a,b])) (x (0 : Fin 2)) (x (1 : Fin 2))

def point {E τ : Type*} (index : τ → Fin q) (z : Fin (Width arity q) → E) :
    SymbolicTransform.Variables τ → E :=
  Sum.elim (fun i => z (OriginalVariableLayout.matrix (Entries arity) q i))
    (fun p => z (OriginalVariableLayout.parameter (Entries arity) q (index p)))

noncomputable section

def Bound (w : Fin (Entries arity) → AlgebraicComplex) (z : Fin (Width arity q) → ℂ) : Prop :=
  ∀ i, z (OriginalVariableLayout.binding (Entries arity) q i) =
    OriginalVariableLayout.boundValues (fun j => (w j : ℂ)) i

theorem bound_entry (w : Fin (Entries arity) → AlgebraicComplex) (z : Fin (Width arity q) → ℂ)
    (hb : Bound arity q w z) (j : Slot s) (x : Fin (slotArity arity j) → Bool) :
    z (entryVariable arity q j x) = (w (OriginalAffineSystem.entryIndex arity j x) : ℂ) :=
  OriginalVariableLayout.binding_original z _ hb _

theorem compiled_vertex_eval {τ : Type*} (index : τ → Fin q)
    (w : Fin (Entries arity) → AlgebraicComplex) (z : Fin (Width arity q) → ℂ)
    (hb : Bound arity q w z) (i : Fin s) (x : Fin (arity i) → Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z (compiled arity q (.inl i) x) =
      Signature.coordinateAction (fun _ => SymbolicTransform.inverse (point arity q index z))
        (fun y => (OriginalAffineSystem.sourceVertex arity w i y : ℂ)) x := by
  rw [compiled]
  change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
    (SymbolicInputTable.vertex RationalCompiler.field.toArithmeticData
      (SparseTransform.inverse RationalCompiler.field.toArithmeticData (Extra arity q))
      (fun y => SparseTransform.variableCode RationalCompiler.field.toArithmeticData
        (entryVariable arity q (.inl i) y)) x) = _
  erw [SymbolicInputTable.vertex_eval]
  simp only [SparseEvaluation.inverse_eval,SparseEvaluation.variable_eval,bound_entry arity q w z hb]
  rfl

theorem compiled_edge_eval {τ : Type*} (index : τ → Fin q)
    (w : Fin (Entries arity) → AlgebraicComplex) (z : Fin (Width arity q) → ℂ)
    (hb : Bound arity q w z) (x : Fin 2 → Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z (compiled arity q (.inr ()) x) =
      Kernel.pullback (fun a b => (OriginalAffineSystem.sourceEdge arity w a b : ℂ))
        (SymbolicTransform.matrix (point arity q index z)) (x (0 : Fin 2)) (x (1 : Fin 2)) := by
  rw [compiled]
  change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
    (SymbolicInputTable.edge RationalCompiler.field.toArithmeticData
      (SparseTransform.matrix RationalCompiler.field.toArithmeticData (Extra arity q))
      (fun a b => SparseTransform.variableCode RationalCompiler.field.toArithmeticData
        (entryVariable arity q (.inr ()) ![a,b])) (x (0 : Fin 2)) (x (1 : Fin 2))) = _
  rw [SymbolicInputTable.edge_eval]
  simp only [SparseEvaluation.matrix_eval,SparseEvaluation.variable_eval,bound_entry arity q w z hb]
  rfl

theorem guard_eval {τ : Type*} (index : τ → Fin q) (z : Fin (Width arity q) → ℂ) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
      (SparseTransform.guard RationalCompiler.data (Extra arity q)) =
    MvPolynomial.eval₂ (algebraMap AlgebraicComplex ℂ) (point arity q index z)
      (SymbolicTransform.guard τ) := by
  change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
    (SparseTransform.guard RationalCompiler.field.toArithmeticData (Extra arity q)) = _
  rw [SparseEvaluation.guard_eval,SymbolicTransform.eval_guard]
  rfl

end
end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalTensorRows
