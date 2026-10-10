import Holant.Tractable.Anchor
import Holant.Holographic
import Holant.Complexity.ClosedNetworkSemantics


namespace Holant.LocalDrafts.TraversalCompletion.MatchingExpansion.Orientation
open Holant Holant.Tractable Holant.Complexity
noncomputable section
set_option backward.isDefEq.respectTransparency false

def basis (opposite : Bool) : InvertibleKernel :=
  if opposite then sourceKBasis.comp bitFlipBasis else sourceKBasis

theorem matrix (opposite : Bool) : (basis opposite).matrix =
    if opposite then Kernel.mul KMatrix Signature.disequality else KMatrix := by
  cases opposite <;> rfl

theorem native_edge (opposite : Bool) :
    Kernel.pullback Signature.equality (basis opposite).matrix = Signature.disequality := by
  cases opposite with
  | false => exact sourceKBasis_pullback
  | true =>
    change Kernel.pullback Signature.equality (Kernel.mul sourceKBasis.matrix bitFlipBasis.matrix) = _
    rw [pullback_mul, sourceKBasis_pullback]
    funext a b
    cases a <;> cases b <;>
      simp [Kernel.pullback, Kernel.mul_apply, Kernel.transpose, bitFlipBasis,
        Signature.disequality, Signature.equality]

theorem inverse_factor (opposite : Bool) (n : ℕ) (f : Signature AlgebraicComplex n)
    (hf : matchingImage opposite n f) : Signature.OneHot ((basis opposite).symm.action f) := by
  cases opposite with
  | false => exact matchingImage_inverse_false n f hf
  | true => exact matchingImage_inverse_true n f hf

theorem inverse_closure (opposite : Bool) {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : SourceTensorClosure (matchingImage opposite) f) :
    SourceTensorClosure (fun _ g => Signature.OneHot g) ((basis opposite).symm.action f) := by
  rcases hf with hz | ht
  · left
    subst f
    funext x
    simp [InvertibleKernel.action, Signature.coordinateAction]
  · right
    exact ht.map_action (basis opposite).inverse (inverse_factor opposite)

variable {s : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val)) (opposite : Bool)

def transformed (i : Fin s) := (basis opposite).symm.action (G i)

/-- This identity applies to the actual original parsed graph, including loops,
parallel edges, nullary factors and empty graphs. There is no scalar quotient. -/
theorem denote (r : {r : RawClosedNetwork // r.WellFormed s 1 arity}) :
    (r.val.realize r.property (transformed G opposite) (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 =
      (r.val.realize r.property G (fun _ : Fin 1 => Signature.equality)).denote Fin.elim0 := by
  have h := congrFun (Network.denote_holographicTransform
    (r.val.realize r.property G (fun _ : Fin 1 => Signature.equality))
    (basis opposite).matrix (basis opposite).inverse (basis opposite).matrix_inverse) Fin.elim0
  refine Eq.trans ?_ h
  apply congrFun
  apply Network.denote_congr
  · intro v x
    rfl
  · intro e a b
    exact (congrFun (congrFun (native_edge opposite) a) b).symm

end
end Holant.LocalDrafts.TraversalCompletion.MatchingExpansion.Orientation
