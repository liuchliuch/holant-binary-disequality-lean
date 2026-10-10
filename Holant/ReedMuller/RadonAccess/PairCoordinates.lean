import Holant.ReedMuller.RadonAccess.PairNetwork
import Holant.ReedMuller.RadonAccess.Coordinates
import Holant.ReedMuller.RadonAccess.AffineQuotient
import Holant.ReedMuller.RadonAccess.Plane
import Holant.Dihedral.TwoCardLocalization.ResidualOrder

/-! The actual pair-closure network uses the same original ports and the
same quotient coordinates as the affine Radon construction. -/
namespace Holant.ReedMuller.RadonAccess
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.Dihedral.CompatibleClosure
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}
namespace RadonFrame

/-- The original-port incidence order used by the literal pair closure. -/
def pairRemainingOrder (F : RadonFrame (n+2)) : Fin n ≃ F.Remaining :=
  Dihedral.TwoCardLocalization.remainingOrder F.i F.j F.distinct

/-- Reinterpret the physical residual word on its exact original port names. -/
def pairRemainingWord (F : RadonFrame (n+2)) (w : BinaryVector n) : F.Remaining → ZMod 2 :=
  fun k => w (F.pairRemainingOrder.symm k)

@[simp] theorem pairRemainingWord_apply (F : RadonFrame (n+2)) (w : BinaryVector n)
    (k : Fin n) : F.pairRemainingWord w (F.pairRemainingOrder k) = w k := by
  simp [pairRemainingWord]

/-- The physical pair lift has the claimed two singled-out coordinates and
zero-extended surviving coordinates, in their actual original incidences. -/
theorem orderedVector_decomposition (F : RadonFrame (n+2)) (a b : ZMod 2)
    (w : BinaryVector n) :
    orderedVector (pairOrder F.i F.j) a b w =
      a • unitWord F.i + b • unitWord F.j + F.extendRemaining (F.pairRemainingWord w) := by
  funext k
  obtain ⟨l,rfl⟩ := (pairOrder F.i F.j).surjective k
  refine Fin.cases ?_ (fun l => Fin.cases ?_ (fun k => ?_) l) l
  · change (Fin.cons a (Fin.cons b w) : BinaryVector (n+2))
      ((pairOrder F.i F.j).symm (pairOrder F.i F.j 0)) = _
    rw [Equiv.symm_apply_apply]
    simp [pairOrder_first _ _ F.distinct,unitWord_apply,F.distinct]
  · change (Fin.cons a (Fin.cons b w) : BinaryVector (n+2))
      ((pairOrder F.i F.j).symm (pairOrder F.i F.j 1)) = _
    rw [Equiv.symm_apply_apply]
    simp [pairOrder_second,unitWord_apply,Ne.symm F.distinct]
  · have he : pairOrder F.i F.j k.succ.succ = (F.pairRemainingOrder k).val := rfl
    rw [he]
    have hi := (F.pairRemainingOrder k).property.1
    have hj := (F.pairRemainingOrder k).property.2
    have ho : (pairOrder F.i F.j).symm (F.pairRemainingOrder k).val = k.succ.succ :=
      (pairOrder F.i F.j).symm_apply_apply _
    simp [orderedVector,ho,unitWord_apply,hi,hj]

/-- The exact surviving-port coordinate map used by the pair network. -/
def pairBoundaryLinearEquiv (F : RadonFrame (n+2)) : F.complement ≃ₗ[ZMod 2] BinaryVector n :=
  F.boundaryLinearEquiv.trans
    (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) F.pairRemainingOrder)

@[simp] theorem pairBoundaryLinearEquiv_apply (F : RadonFrame (n+2))
    (w : F.complement) (k : Fin n) :
    F.pairBoundaryLinearEquiv w k = F.A w (F.pairRemainingOrder k).1 := rfl

theorem pairBoundaryLinearEquiv_isometry (F : RadonFrame (n+2)) (w z : F.complement) :
    dot (F.pairBoundaryLinearEquiv w) (F.pairBoundaryLinearEquiv z) =
      dot (w : BinaryVector (n+2)) z := by
  change (∑ k : Fin n, F.boundaryCoordinate w (F.pairRemainingOrder k) *
    F.boundaryCoordinate z (F.pairRemainingOrder k)) = _
  exact (Equiv.sum_comp F.pairRemainingOrder
    (fun k => F.boundaryCoordinate w k * F.boundaryCoordinate z k)).trans
      (F.boundaryCoordinate_isometry w z)

@[simp] theorem pairBoundaryLinearEquiv_symm (F : RadonFrame (n+2)) (w : BinaryVector n) :
    F.pairBoundaryLinearEquiv.symm w = F.fromBoundary (F.pairRemainingWord w) := rfl

end RadonFrame

/-- The pair network's translation direction is the frame's original-input
vector, not an abstract direction with an assumed realization. -/
theorem pairDirection_eq_frame (p : GenerationProgram (n+2)) (F : RadonFrame (n+2))
    (hA : F.A = p.orthogonalMap) :
    pairDirection p (pairOrder F.i F.j) = F.v := by
  rw [pairDirection,←GenerationProgram.orthogonalMap_symm_apply,←hA,
    F.orderedVector_decomposition]
  have hzero : F.extendRemaining (F.pairRemainingWord 0) = 0 := by
    funext k
    simp [RadonFrame.extendRemaining,RadonFrame.pairRemainingWord]
  rw [hzero,one_smul,one_smul,add_zero]
  rfl

/-- The network's first lift is exactly `ε r + w` for the inverse of the
actual residual boundary-coordinate isometry. -/
theorem pairBase_eq_frame (p : GenerationProgram (n+2)) (F : RadonFrame (n+2))
    (hA : F.A = p.orthogonalMap) (ε : ZMod 2) (x : Fin n → Bool) :
    pairBase p (pairOrder F.i F.j) ε x =
      ε • F.r + F.pairBoundaryLinearEquiv.symm (vectorWord x) := by
  rw [pairBase,←GenerationProgram.orthogonalMap_symm_apply,←hA,
    F.orderedVector_decomposition,zero_smul,add_zero,F.A.symm.map_add,F.A.symm.map_smul]
  rfl

/-- Exact identification of the literal two-lift contraction with the Radon
signature on the genuine affine quotient. -/
theorem pairSum_eq_radon (p : GenerationProgram (n+2)) (F : RadonFrame (n+2))
    (hA : F.A = p.orthogonalMap) (ε : ZMod 2) (g : Signature ℂ (n+2)) :
    pairSum p (pairOrder F.i F.j) ε g = fun x =>
      F.radon ε (fun z => g (wordVector z))
        (F.iota ε (F.pairBoundaryLinearEquiv.symm (vectorWord x))) := by
  funext x
  unfold pairSum
  rw [pairBase_eq_frame p F hA,pairDirection_eq_frame p F hA,F.radon_iota]

/-- Source boundary semantics with original ports, genuine quotient, and the
actual single-copy pair network all identified in one theorem. -/
theorem pairNetwork_denote_radon (p : GenerationProgram (n+2)) (F : RadonFrame (n+2))
    (hA : F.A = p.orthogonalMap) (ε : ZMod 2) (g : Signature ℂ (n+2)) :
    (pairNetwork p g (pairOrder F.i F.j) ε).denote = fun x =>
      F.radon ε (fun z => g (wordVector z))
        (F.iota ε (F.pairBoundaryLinearEquiv.symm (vectorWord x))) := by
  rw [pairNetwork_denote,pairSum_eq_radon p F hA]

end
end Holant.ReedMuller.RadonAccess
