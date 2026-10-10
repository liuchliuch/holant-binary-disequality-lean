import Holant.Proofs.Closure.ClosureMarkedCyclic
import Holant.Projective.CyclicQuaternary.PhysicalSource

/-! Actual cyclic phase representatives selected from the SAME current complete
source group. Hadamard coordinates and the pivot scalar remain in the original
field. The native edge is exactly 2Z; normalized phase matrices are not source
labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
open Holant Holant.Tractable Holant.Marked
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open Holant.Projective.FiniteSubgroupClassification
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
namespace C
export ClosureMarkedCyclic (NativeCyclic normalize normalized basis)
export ClosureMarkedCyclic.Source (sourceCoordinates sourceNormalize rotation sourceNormalize_class)
end C
namespace D
export ClosureMarkedDihedral.Source (group complexEmbedding)
end D
variable {L : Type*} [Field L] [NumberField L]
variable (φ : L →+* AlgebraicComplex) (F : SignatureFamily L) (τ : ResidualTorsion F)
variable (N : C.NativeCyclic (D.group φ F τ))

/-- Every literal algebraic m-th root belongs to the internally chosen full
cyclic model, including roots not explicitly named by its generator. -/
theorem phase_class_mem (t : Holant.Projective.CyclicQuaternary.Physical.Root N.m) :
    pglMk ℂ (ClosureMarkedDihedral.phaseGL (by have := N.range; omega) false t.val t.property) ∈
      cyclicModel N.omega := by
  have hm : 0 < N.m := by have := N.range; omega
  letI : NeZero N.m := ⟨Nat.ne_zero_of_lt hm⟩
  let u := Units.mk0 (ClosureMarkedDihedral.inclusion t.val)
    ((map_ne_zero ClosureMarkedDihedral.inclusion).mpr (Holant.Projective.CyclicPhasePencil.root_ne_zero hm t.property))
  have hu : u ^ N.m = 1 := by
    apply Units.ext
    change (ClosureMarkedDihedral.inclusion t.val)^N.m = 1
    rw [← map_pow,t.property,map_one]
  obtain ⟨k,hk,he⟩ := N.primitive.eq_pow_of_mem_rootsOfUnity
    ((mem_rootsOfUnity' N.m u).mpr (by
      simpa only [Units.val_pow_eq_pow_val,Units.val_one] using congrArg Units.val hu))
  apply (mem_cyclicModel_iff hm N.primitive _).mpr
  refine ⟨k,hk,?_⟩
  change pglMk ℂ (diagonalGL 1 u) = _
  rw [he]

/-- Inverse full-model coverage selects a real ORIGINAL-field frozen key.
The source scalar is the (0,0) entry after the ORIGINAL Hadamard conjugation. -/
theorem source_phase_representative (t : Holant.Projective.CyclicQuaternary.Physical.Root N.m) :
    ∃ j : completeGroup F τ, ∃ c : L, c ≠ 0 ∧
      Matrix.map
        (((C.sourceCoordinates (L:=L))⁻¹ : Matrix.GeneralLinearGroup Bool L).val *
          transfer (actualRepresentative F τ j) * (C.sourceCoordinates (L:=L)).val) φ =
        Holant.Marked.scale (φ c) (Holant.Tractable.diagonalKernel 1 t.val) := by
  let V := ClosureMarkedDihedral.phaseGL (by have := N.range; omega) false t.val t.property
  let q := C.normalize.symm (pglMk ℂ V)
  have hq : q ∈ D.group φ F τ := by
    have hv : pglMk ℂ V ∈ C.normalized (D.group φ F τ) := by
      rw [N.model]
      exact phase_class_mem φ F τ N t
    obtain ⟨r,hr,he⟩ := hv
    have h : r = q := by
      apply C.normalize.injective
      change C.normalize r = pglMk ℂ V at he
      simpa only [q,MulEquiv.apply_symm_apply] using he
    exact h ▸ hr
  change q ∈ completeGroup (RingHomRealization.mapFamily (D.complexEmbedding φ) F)
    (ClosureFieldBridgeGroups.mappedTorsion (D.complexEmbedding φ) F τ) at hq
  rw [ClosureFieldBridgeGroups.completeGroup_image (D.complexEmbedding φ) F τ] at hq
  obtain ⟨j,hj,he⟩ := hq
  let key : completeGroup F τ := ⟨j,hj⟩
  let B := actualRepresentative F τ key
  have hb := actualRepresentative_actual F τ key
  have hd : Matrix.det (transfer B) ≠ 0 := by
    rw [transfer,Matrix.det_mul]
    exact mul_ne_zero hb.2 det_X_ne_zero
  let U := Matrix.GeneralLinearGroup.mkOfDetNeZero (transfer B) hd
  have hj' : pglMk L U = j := by
    apply pglToProjectiveClass_injective
    rw [pglToProjectiveClass_mk]
    exact actualRepresentative_class F τ key
  have hmap : pglMk ℂ (Matrix.GeneralLinearGroup.map (D.complexEmbedding φ) U) = q := by
    rw [← pglExtend_mk,hj']
    exact he
  have hn : pglMk ℂ (Matrix.GeneralLinearGroup.map (D.complexEmbedding φ) (C.sourceNormalize U)) =
      pglMk ℂ V := by
    rw [C.sourceNormalize_class φ U,hmap]
    exact C.normalize.apply_symm_apply _
  obtain ⟨d,hd0,heq⟩ := projectiveClass_eq_iff.mp (pglMk_eq_iff_projectiveClass_eq.mp hn)
  have hv : (V : Binary (K:=ℂ)) = Matrix.map (diagonalKernel 1 t.val) ClosureMarkedDihedral.inclusion := by
    simpa only [V,ClosureMarkedDihedral.standard,Bool.false_eq_true,ite_false,R] using
      ClosureMarkedDihedral.phaseGL_matrix (by have := N.range; omega) false t.val t.property
  rw [hv] at heq
  let W : Binary (K:=L) := (C.sourceNormalize U).val
  let c := W false false
  have hp : D.complexEmbedding φ c = d := by
    have h := congrFun (congrFun heq false) false
    simpa [c,W,Matrix.map_apply,diagonalKernel] using h
  have hc : c ≠ 0 := by
    apply (map_ne_zero (D.complexEmbedding φ)).mp
    rw [hp]
    exact hd0
  refine ⟨key,c,hc,?_⟩
  have hval : Matrix.map W (D.complexEmbedding φ) =
      d • Matrix.map (Holant.Tractable.diagonalKernel 1 t.val) ClosureMarkedDihedral.inclusion := by
    exact heq
  rw [← hp] at hval
  funext a b
  apply ClosureMarkedDihedral.inclusion.injective
  have h := congrFun (congrFun hval a) b
  simpa [C.sourceNormalize,W,U,B,c,Holant.Marked.scale,
    D.complexEmbedding,Matrix.map_apply] using h

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
