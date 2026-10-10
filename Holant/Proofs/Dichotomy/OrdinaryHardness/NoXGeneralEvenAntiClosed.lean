import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenOperations
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXScaleAux

/-! Affine-support extraction from two actual even resources and an actual
even anti resource. Both support shifts, the tensor and the selected binary
gadget are real flattened blocks over the unchanged original table. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenAntiClosed
open Holant Holant.Tractable
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
end B
namespace E
export OrdinaryNegativeAffineSupportExtraction (Choice choose combined)
end E
namespace O
export NoXGeneralEvenOperations (shiftedTensor shiftedTensor_value gadget gadget_value)
end O
namespace C
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport (Closed)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable {s m n : ℕ} {b : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (b i.val))
variable (first : B.Block (s:=s) (b:=b) m) (second : B.Block (s:=s) (b:=b) n)
variable (hf : C.Closed (fun x=>(first.signature H x : AlgebraicComplex)))
variable (hg : C.Closed (fun x=>(second.signature H x : AlgebraicComplex)))
variable (ha : ¬Affine (fun x=>(first.signature H x : AlgebraicComplex)))
variable (hp : ¬Product (fun x=>(second.signature H x : AlgebraicComplex)))

def choice : E.Choice K (first.signature H) (second.signature H) :=
  E.choose K _ _ hf hg ha hp

variable (antiRow : B.Block (s:=s) (b:=b) 2)

def shifted := O.shiftedTensor first second antiRow
  (choice K H first second hf hg ha hp).left (choice K H first second hf hg ha hp).right

def binary := O.gadget (shifted K H first second hf hg ha hp antiRow)
  (choice K H first second hf hg ha hp).gadget

variable (v w : K) (hv : v≠0) (hw : w≠0)
variable (anti : antiRow.signature H=NoXWeightedAntiSigned.anti v w)

include anti in
theorem binary_exact : (binary K H first second hf hg ha hp antiRow).signature H=
    fun z=>((v*w)^(m+n))^(choice K H first second hf hg ha hp).gadget.ports.length*
      (choice K H first second hf hg ha hp).coefficient z := by
  funext z
  rw [binary,O.gadget_value]
  have hrow : (shifted K H first second hf hg ha hp antiRow).signature H=
      fun x=>(v*w)^(m+n)*E.combined (first.signature H) (second.signature H)
        (choice K H first second hf hg ha hp).left (choice K H first second hf hg ha hp).right x := by
    funext x
    exact O.shiftedTensor_value first second H antiRow _ _ v w anti x
  rw [hrow,NoXScaleAux.gadget_scale]
  rfl

include hv hw anti in
theorem binary_nonaffine : ¬Affine (fun x=>
    ((binary K H first second hf hg ha hp antiRow).signature H x : AlgebraicComplex)) := by
  rw [binary_exact K H first second hf hg ha hp antiRow v w anti]
  exact NoXScaleAux.nonaffine_scale _ (choice K H first second hf hg ha hp).nonaffine _
    (fun hz=>(pow_ne_zero _ (pow_ne_zero _ (mul_ne_zero hv hw))) (Subtype.ext hz))

include hv hw anti in
theorem binary_nonproduct : ¬Product (fun x=>
    ((binary K H first second hf hg ha hp antiRow).signature H x : AlgebraicComplex)) := by
  rw [binary_exact K H first second hf hg ha hp antiRow v w anti]
  exact NoXScaleAux.nonproduct_scale _ (choice K H first second hf hg ha hp).nonproduct _
    (fun hz=>(pow_ne_zero _ (pow_ne_zero _ (mul_ne_zero hv hw))) (Subtype.ext hz))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenAntiClosed
end
