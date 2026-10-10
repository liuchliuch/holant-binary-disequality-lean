import Holant.Proofs.Algorithms.LocalAffine.SupportSystem
import Holant.Proofs.Algorithms.LocalAffine.FiniteLabels


namespace Holant.LocalDrafts.TraversalCompletion.LocalAffineSupport.LocalData
open Holant Holant.Tractable AffinePhase TwoTranslate
open Holant.LocalDrafts.MainChain
noncomputable section

def system {n : ℕ} (f : Signature AlgebraicComplex n) (hf : LocalAffine f) :
    AffineSystem n := by
  classical
  exact if f = 0 then LocalAffineSupport.impossible n else LocalAffineSupport.localSystem f hf

theorem system_holds {n : ℕ} (f : Signature AlgebraicComplex n) (hf : LocalAffine f)
    (x : Word n) : (system f hf).Holds x ↔ f x ≠ 0 := by
  classical
  by_cases hz : f = 0
  · simp [system, hz, LocalAffineSupport.impossible_holds]
  · simpa [system, hz] using LocalAffineSupport.localSystem_holds f hf x

theorem system_zero {n : ℕ} (f : Signature AlgebraicComplex n) (hf : LocalAffine f)
    (hz : f = 0) : system f hf = LocalAffineSupport.impossible n := by
  classical
  simp [system, hz]

/-- Even a noncanonical chosen support witness for zero must have a row. -/
theorem zero_rows_pos {n : ℕ} (f : Signature AlgebraicComplex n) (hf : LocalAffine f)
    (hz : f = 0) : 0 < (LocalAffineSupport.localSystem f hf).rows := by
  by_contra hn
  have hh : (LocalAffineSupport.localSystem f hf).Holds (fun _ => false) := by
    intro j
    have hj := j.isLt
    omega
  have he := (LocalAffineSupport.localSystem_holds f hf (fun _ => false)).mp hh
  simp [hz] at he

theorem rows_le {n : ℕ} (f : Signature AlgebraicComplex n) (hf : LocalAffine f) :
    (system f hf).rows ≤ (LocalAffineSupport.localSystem f hf).rows := by
  classical
  by_cases hz : f = 0
  · simpa [system, hz, LocalAffineSupport.impossible] using Nat.succ_le_of_lt (zero_rows_pos f hf hz)
  · simp [system, hz]

variable {s b : ℕ} {arity : ℕ → ℕ} (D : LocalAffineLabels.Family s b arity)
def vertex (i : Fin s) := system (D.signatures i) (D.vertexLocal i)
def edge (i : Fin b) := system (kernelSignature (D.kernels i)) (D.edgeLocal i)

theorem vertex_holds (i : Fin s) (x : Word (arity i.val)) :
    (vertex D i).Holds x ↔ D.signatures i x ≠ 0 := system_holds _ _ _
theorem edge_holds (i : Fin b) (x : Word 2) :
    (edge D i).Holds x ↔ kernelSignature (D.kernels i) x ≠ 0 := system_holds _ _ _
theorem vertex_rows_le (i : Fin s) : (vertex D i).rows ≤ LocalAffineLabels.rowBudget D :=
  (rows_le _ _).trans (LocalAffineLabels.vertex_rows_le D i)
theorem edge_rows_le (i : Fin b) : (edge D i).rows ≤ LocalAffineLabels.rowBudget D :=
  (rows_le _ _).trans (LocalAffineLabels.edge_rows_le D i)

end
end Holant.LocalDrafts.TraversalCompletion.LocalAffineSupport.LocalData
