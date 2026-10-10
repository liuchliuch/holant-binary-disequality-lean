import Holant.Proofs.Closure.ClosureCyclicCurrentInstalled

/-! A real retained installed factor has a genuinely new ORIGINAL transfer
class relative to the selected actual cyclic group. Strict growth is asserted
only when the new palette's actual residual-torsion premise holds; otherwise
ordinary source dispatch must continue to its real unsafe/unary alternatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
open Holant Holant.Tractable Holant.Marked Holant.Algebraic
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

/-- Exact complex Walsh-transfer convention for an original-field binary.
Hadamard is a coordinate calculation; it is not installed as a source gadget. -/
theorem complex_walsh_normalized_generic {L : Type*} [Field L] [NumberField L]
    (φ : L →+* ℂ) (B : Binary (K:=L)) :
    CyclicBoundary.ActualCards.walshTransfer
      (RingHomRealization.mapSignature φ (Holant.Projective.BoundedTorsion.binarySignature B)) =
      (1/2 : ℂ) • (normalizedTransfer B).map φ := by
  have hinv : (((C.sourceCoordinates (L:=L))⁻¹ : Matrix.GeneralLinearGroup Bool L) :
      Binary (K:=L)) = Matrix.of ClosureMarkedCyclic.Source.sourceInverse := rfl
  funext u v
  cases u <;> cases v <;>
    simp [CyclicBoundary.ActualCards.walshTransfer,Signature.coordinateAction,sum_wordsTwo,
      RingHomRealization.mapSignature,Holant.Projective.BoundedTorsion.binarySignature,
      CyclicBoundary.CoordinateFactors.inverseHadamard,CyclicBoundary.ZeroEndpointDressing.hadamard,
      Kernel.mul,CP.Z,CP.diagonal,Fin.prod_univ_succ,normalizedTransfer,hinv,
      C.sourceCoordinates,ClosureMarkedCyclic.Source.sourceCoordinates,
      ClosureMarkedCyclic.Source.sourceMatrix,ClosureMarkedCyclic.Source.sourceInverse,
      Matrix.map_apply,Matrix.mul_apply,Fintype.sum_bool,transfer,X,Signature.disequality,
      map_mul,map_add,map_sub,map_inv₀,map_ofNat,div_eq_mul_inv] <;> ring

theorem complex_walsh_normalized (B : Binary (K:=OI.K G)) :
    CyclicBoundary.ActualCards.walshTransfer
      (RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G)
        (Holant.Projective.BoundedTorsion.binarySignature B)) =
      (1/2 : ℂ) • (normalizedTransfer B).map (ClosurePhysicalBridge.complexEmbedding G) :=
  complex_walsh_normalized_generic (ClosurePhysicalBridge.complexEmbedding G) B

variable (τ : ResidualTorsion P.family)
variable (N : C.NativeCyclic (D.group (ClosureSourceRows.embedding G) P.family τ))

/-- Membership in the old actual group alone forces the cyclic phase test,
by its original-field Hadamard conjugate and the internally selected model. -/
theorem old_class_phase (B : Binary (K:=OI.K G)) (det : Matrix.det (transfer B) ≠ 0)
    (member : pglMk (OI.K G) (Matrix.GeneralLinearGroup.mkOfDetNeZero (transfer B) det) ∈ completeGroup P.family τ) :
    CP.IsPhase N.m (CyclicBoundary.ActualCards.walshTransfer
      (RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G)
        (Holant.Projective.BoundedTorsion.binarySignature B))) := by
  let U := Matrix.GeneralLinearGroup.mkOfDetNeZero (transfer B) det
  have embedded : pglMk ℂ (Matrix.GeneralLinearGroup.map (ClosurePhysicalBridge.complexEmbedding G) U) ∈
      D.group (ClosureSourceRows.embedding G) P.family τ := by
    change _ ∈ completeGroup
      (RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) P.family)
      (ClosureFieldBridgeGroups.mappedTorsion (ClosurePhysicalBridge.complexEmbedding G) P.family τ)
    rw [ClosureFieldBridgeGroups.completeGroup_image (ClosurePhysicalBridge.complexEmbedding G) P.family τ]
    exact ⟨pglMk (OI.K G) U,member,(pglExtend_mk _ U).symm⟩
  have normalized : pglMk ℂ (Matrix.GeneralLinearGroup.map (ClosurePhysicalBridge.complexEmbedding G)
      (C.sourceNormalize U)) ∈ Holant.Projective.FiniteSubgroupClassification.cyclicModel N.omega := by
    rw [← N.model,C.sourceNormalize_class]
    exact ⟨_,embedded,rfl⟩
  obtain ⟨c,t,hc,ht,eqn⟩ := ClosureMarkedCyclic.Source.cyclic_source_ratio
    (ClosurePhysicalBridge.complexEmbedding G) (by have := N.range; omega) N.omega N.primitive
    (C.sourceNormalize U) normalized
  have source : normalizedTransfer B = (fun u v => c * C.rotation (L:=OI.K G) t u v) := eqn
  refine ⟨ClosurePhysicalBridge.complexEmbedding G t,ClosurePhysicalBridge.complexEmbedding G (c/2),?_,
    (map_ne_zero _).mpr (div_ne_zero hc (by norm_num)),?_⟩
  · rw [← map_pow,ht,map_one]
  · rw [complex_walsh_normalized,source]
    funext u v
    cases u <;> cases v <;>
      simp [C.rotation,ClosureMarkedCyclic.Source.rotation,CP.phase,CP.diagonal,Matrix.map_apply,
        map_mul,map_div₀,map_ofNat,div_eq_mul_inv] <;> ring

variable (d : CyclicBoundary.NonsquareExit.DoubledOutside
  (RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) P.family) N.m)

def installedTransfer : Matrix.GeneralLinearGroup Bool (OI.K G) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (transfer (binaryMatrix (doubleFactors G P d).left)) (by
    rw [transfer,Matrix.det_mul]
    exact mul_ne_zero (doubleFactor_nonsingular G P d) det_X_ne_zero)

theorem installed_class_new : pglMk (OI.K G) (installedTransfer G P τ N d) ∉ completeGroup P.family τ := by
  intro member
  have phase := old_class_phase G P τ N (binaryMatrix (doubleFactors G P d).left) _ member
  rw [binarySignature_binaryMatrix] at phase
  exact doubleFactor_outside G P d phase

theorem installed_group_growth (currentTorsion : ResidualTorsion (installedPalette G P d).family) :
    completeGroup P.family τ < completeGroup (installedPalette G P d).family currentTorsion := by
  have old : P.family ⊆ (installedPalette G P d).family := by
    rintro f ⟨i,rfl⟩
    exact ⟨installedOldLabel G P d i,congrArg Sigma.fst (installed_old_saved G P d i)⟩
  apply completeGroup_lt_of_new_class old τ currentTorsion (installedTransfer G P τ N d)
  · refine ⟨binaryMatrix (doubleFactors G P d).left,installed_factor_actual G P d,1,one_ne_zero,?_⟩
    ext u v
    exact (one_mul _).symm
  · exact installed_class_new G P τ N d
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
