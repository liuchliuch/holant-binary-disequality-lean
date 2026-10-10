import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralLowerNormalization

/-! Two actual even resources with supported lower words and closed support
supply an actual unsigned binary outside both Affine and Product. All fixed
one-pins, tensor copies and private summations are flattened into old labels. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLowerBinary
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
end B
namespace N
export NoXGeneralLowerNormalization (block value normalized fill_origin nonaffine nonproduct closed)
end N
namespace L
export NoXGeneralLatticeSupport (Below)
end L
namespace O
export NoXGeneralEvenOperations (tensor tensor_value gadget gadget_value)
end O
namespace T
export GeneralEOPairedFamilyExtractionTensor (tensor tensor_failures)
end T
namespace C
export GeneralEONegativeClosedSupport (Closed)
export GeneralEOPairedFamilyExtractionChoice (tensor_closed)
export GeneralEOPairedFamilyExtractionSupport (xorClosed_of_closed)
end C
namespace U
export GeneralEOPairedFamilyExtractionUniversal (exists_gadget)
end U
namespace Q
export GeneralEOPairedFamilyExtractionGadget (Gadget denote)
end Q
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable {s m n : ℕ} {b : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (b i.val))
variable (first : B.Block (s:=s) (b:=b) m) (second : B.Block (s:=s) (b:=b) n)
variable (lo : Word m) (hi : Word n)
variable (leftBound : ∀x,(first.signature H x : AlgebraicComplex)≠0→L.Below lo x)
variable (rightBound : ∀x,(second.signature H x : AlgebraicComplex)≠0→L.Below hi x)
variable (leftLive : (first.signature H lo : AlgebraicComplex)≠0)
variable (rightLive : (second.signature H hi : AlgebraicComplex)≠0)
variable (leftClosed : C.Closed (fun x=>(first.signature H x : AlgebraicComplex)))
variable (rightClosed : C.Closed (fun x=>(second.signature H x : AlgebraicComplex)))
variable (nonaffine : ¬Affine (fun x=>(first.signature H x : AlgebraicComplex)))
variable (nonproduct : ¬Product (fun x=>(second.signature H x : AlgebraicComplex)))

def left : Signature AlgebraicComplex m := N.normalized (fun x=>(first.signature H x : AlgebraicComplex)) lo
def right : Signature AlgebraicComplex n := N.normalized (fun x=>(second.signature H x : AlgebraicComplex)) hi

def combined : B.Block (s:=s) (b:=b) (m+n) := O.tensor (N.block first lo) (N.block second hi)

theorem combined_value : (fun x=>((combined first second lo hi).signature H x : AlgebraicComplex))=
    T.tensor (left K H first lo) (right K H second hi) := by
  funext x
  rw [combined,O.tensor_value,N.value,N.value,IntermediateField.coe_mul]
  rfl

theorem gadget_value (row : B.Block (s:=s) (b:=b) m) (q : Q.Gadget m n) :
    (fun x=>((O.gadget row q).signature H x : AlgebraicComplex))=
      Q.denote (fun x=>(row.signature H x : AlgebraicComplex)) q := by
  funext x
  rw [O.gadget_value]
  simp only [Q.denote,IntermediateField.coe_sum,OrdinaryNegativePhaseBundleChoice.coe_evaluate]

include leftBound rightBound leftLive rightLive leftClosed rightClosed nonaffine nonproduct in
theorem exists_binary : ∃row : B.Block (s:=s) (b:=b) 2,
    (¬Affine (fun x=>(row.signature H x : AlgebraicComplex))) ∧
    ¬Product (fun x=>(row.signature H x : AlgebraicComplex)) := by
  have l0 : left K H first lo (origin m)≠0 := by
    simpa only [left,N.normalized,N.fill_origin] using leftLive
  have r0 : right K H second hi (origin n)≠0 := by
    simpa only [right,N.normalized,N.fill_origin] using rightLive
  have ln : left K H first lo≠0 := fun h=>l0 (congrFun h _)
  have rn : right K H second hi≠0 := fun h=>r0 (congrFun h _)
  have bad:=T.tensor_failures ln rn (N.nonaffine _ lo leftBound nonaffine)
    (N.nonproduct _ hi rightBound nonproduct)
  have closed:=C.tensor_closed _ _ (N.closed _ lo leftClosed) (N.closed _ hi rightClosed)
  have live : T.tensor (left K H first lo) (right K H second hi) (origin (m+n))≠0 :=
    mul_ne_zero l0 r0
  obtain ⟨q,ha,hp⟩ := U.exists_gadget _ live (C.xorClosed_of_closed _ live closed) bad.1 bad.2
  refine ⟨O.gadget (combined first second lo hi) q,?_,?_⟩
  · rw [gadget_value,combined_value]
    exact ha
  · rw [gadget_value,combined_value]
    exact hp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLowerBinary
end
