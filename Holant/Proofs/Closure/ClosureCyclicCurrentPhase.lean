import Holant.Proofs.Closure.ClosureCyclicCurrentRepresentatives
import Holant.Proofs.Closure.ClosurePhysicalBridge

/-! Original-field pivot data and actual native-X cyclic phase resources.
Walsh normalization is analytic; each actual matrix remains the literal mapped
original representative, and its scalar is the original pivot divided by two. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
namespace CP
export Holant.Projective.CyclicPhasePencil (phase Z diagonal IsPhase)
end CP
namespace Physical
export Holant.Projective.CyclicQuaternary.Physical
  (Root Representatives walshBinary PhysicalCards physicalTransfer P Pinv)
end Physical
variable {L : Type*} [Field L] [NumberField L]
variable (φ : L →+* AlgebraicComplex) (F : SignatureFamily L) (τ : ResidualTorsion F)
variable (N : C.NativeCyclic (D.group φ F τ))

def normalizedTransfer (B : Binary (K:=L)) : Binary (K:=L) :=
  ((C.sourceCoordinates (L:=L))⁻¹ : Matrix.GeneralLinearGroup Bool L).val *
    transfer B * (C.sourceCoordinates (L:=L)).val

/-- Literal inverse-Hadamard binary action, with its exact 1/2 correction.
The native physical edge itself is the separate exact edge 2Z. -/
theorem walsh_normalized_transfer (B : Binary (K:=L)) :
    Physical.walshBinary (B.map φ) = (1/2 : AlgebraicComplex) •
      Kernel.mul ((normalizedTransfer B).map φ) CP.Z := by
  have hinv : (((C.sourceCoordinates (L:=L))⁻¹ : Matrix.GeneralLinearGroup Bool L) : Matrix Bool Bool L) =
      Matrix.of ClosureMarkedCyclic.Source.sourceInverse := rfl
  funext a b
  cases a <;> cases b <;>
    simp [Physical.walshBinary,Physical.P,Physical.Pinv,Kernel.mul,Kernel.transpose,
      normalizedTransfer,hinv,C.sourceCoordinates,ClosureMarkedCyclic.Source.sourceCoordinates,
      ClosureMarkedCyclic.Source.sourceMatrix,ClosureMarkedCyclic.Source.sourceInverse,
      Matrix.map_apply,Matrix.mul_apply,Fintype.sum_bool,transfer,X,Signature.disequality,
      CP.Z,CP.diagonal,map_mul,map_add,map_sub,map_inv₀,map_ofNat,div_eq_mul_inv] <;> ring

structure PhaseIndex (t : Physical.Root N.m) where
  key : completeGroup F τ
  coefficient : L
  nonzero : coefficient ≠ 0
  pivot : coefficient = normalizedTransfer (actualRepresentative F τ key) false false
  normalized : (normalizedTransfer (actualRepresentative F τ key)).map φ =
    Holant.Marked.scale (φ coefficient) (diagonalKernel 1 t.val)

def phaseIndex (t : Physical.Root N.m) : PhaseIndex φ F τ N t := by
  let spec := source_phase_representative φ F τ N t
  let j := Classical.choose spec
  let coefficientSpec := Classical.choose_spec spec
  let c := Classical.choose coefficientSpec
  have hc := (Classical.choose_spec coefficientSpec).1
  have he : (normalizedTransfer (actualRepresentative F τ j)).map φ =
      Holant.Marked.scale (φ c) (diagonalKernel 1 t.val) :=
    (Classical.choose_spec coefficientSpec).2
  have pivot : c = normalizedTransfer (actualRepresentative F τ j) false false := by
    apply φ.injective
    have h := congrFun (congrFun he false) false
    simpa [Matrix.map_apply,Holant.Marked.scale,diagonalKernel] using h.symm
  exact ⟨j,c,hc,pivot,he⟩

theorem phaseIndex_walsh (t : Physical.Root N.m) :
    Physical.walshBinary ((actualRepresentative F τ (phaseIndex φ F τ N t).key).map φ) =
      (φ ((phaseIndex φ F τ N t).coefficient / 2)) • Kernel.mul (CP.phase t.val) CP.Z := by
  rw [walsh_normalized_transfer φ, (phaseIndex φ F τ N t).normalized]
  funext a b
  cases a <;> cases b <;>
    simp [Holant.Marked.scale,CP.phase,CP.diagonal,diagonalKernel,CP.Z,Kernel.mul,
      map_div₀,map_ofNat,div_eq_mul_inv] <;> ring

/-- Internally derived source resources for EVERY literal algebraic root. -/
def representatives : Physical.Representatives (RingHomRealization.mapFamily φ F) N.m where
  matrix t := (actualRepresentative F τ (phaseIndex φ F τ N t).key).map φ
  scalar t := φ ((phaseIndex φ F τ N t).coefficient / 2)
  scalar_ne_zero t := (map_ne_zero φ).mpr (div_ne_zero (phaseIndex φ F τ N t).nonzero (by norm_num))
  actual t := RingHomRealization.realizes_map φ
    (actualRepresentative_actual F τ (phaseIndex φ F τ N t).key).1
  walsh_form := phaseIndex_walsh φ F τ N

/-- Every actual ordered binary has a phase transfer in the SAME cyclic model,
with its source scalar and ratio retained in the original field. -/
theorem actual_physical_phase (B : Binary (K:=L)) (actual : ActualNonsingular F B) :
    CP.IsPhase N.m (Kernel.mul (Physical.walshBinary (B.map φ)) CP.Z) := by
  obtain ⟨c,t,hc,ht,he⟩ := ClosureMarkedCyclic.Source.actual_source_ratios φ F τ N B actual
  have he' : (normalizedTransfer B).map φ = Holant.Marked.scale (φ c) (diagonalKernel 1 (φ t)) := by
    rw [show normalizedTransfer B = c • C.rotation t from he]
    funext a b
    cases a <;> cases b <;>
      simp [C.rotation,ClosureMarkedCyclic.Source.rotation,Matrix.map_apply,Holant.Marked.scale,
        diagonalKernel,map_mul]
  refine ⟨φ t,φ (c/2),?_,(map_ne_zero φ).mpr (div_ne_zero hc (by norm_num)),?_⟩
  · rw [← map_pow,ht,map_one]
  · rw [walsh_normalized_transfer φ,he']
    funext a b
    cases a <;> cases b <;>
      simp [Holant.Marked.scale,diagonalKernel,CP.phase,CP.Z,CP.diagonal,Kernel.mul,
        map_div₀,map_ofNat,div_eq_mul_inv] <;> ring

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
