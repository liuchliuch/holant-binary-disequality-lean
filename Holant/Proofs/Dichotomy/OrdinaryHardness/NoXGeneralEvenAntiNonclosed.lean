import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenOperations
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonclosedSupportWitness
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXScaleAux

/-! A nonclosed support of an actual even resource is shifted using an
actual even anti block, then its selected three-support gadget is flattened
into the original table. All scalar factors survive the extraction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenAntiNonclosed
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
end B
namespace W
export OrdinaryNegativeNonclosedSupportWitness (Choice choose nonaffine nonproduct)
end W
namespace O
export NoXGeneralEvenOperations (gadget gadget_value)
export NoXGeneralEvenAntiSigned (block block_value)
end O
namespace E
export OrdinaryNegativeAffineSupportExtraction (shift)
end E
namespace C
export GeneralEONegativeClosedSupport (Closed)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable {s n : ℕ} {b : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (b i.val))
variable (row : B.Block (s:=s) (b:=b) n)
variable (nonclosed : ¬C.Closed (fun x=>(row.signature H x : AlgebraicComplex)))

include nonclosed in
theorem resource_nonclosed : ¬∀a c e,row.signature H a≠0→ row.signature H c≠0→
    row.signature H e≠0→ row.signature H (tripleXor a c e)≠0 := by
  intro hh
  apply nonclosed
  intro a c e ha hc he
  have hne (x : Fin n→Bool) (hx : (row.signature H x : AlgebraicComplex)≠0) : row.signature H x≠0 :=
    fun hz=>hx (congrArg (fun v : K=>(v : AlgebraicComplex)) hz)
  intro hz
  exact hh a c e (hne a ha) (hne c hc) (hne e he) (Subtype.ext hz)

def choice : W.Choice (row.signature H) := W.choose _ (resource_nonclosed K H row nonclosed)

variable (antiRow : B.Block (s:=s) (b:=b) 2)

def shifted := O.block row antiRow (choice K H row nonclosed).base

def binary := O.gadget (shifted K H row nonclosed antiRow) (choice K H row nonclosed).gadget

variable (v w : K) (hv : v≠0) (hw : w≠0)
variable (anti : antiRow.signature H=NoXWeightedAntiSigned.anti v w)

include anti in
theorem binary_exact : (binary K H row nonclosed antiRow).signature H=
    fun z=>((v*w)^n)^(choice K H row nonclosed).gadget.ports.length*(choice K H row nonclosed).coefficient z := by
  funext z
  rw [binary,O.gadget_value]
  have hrow : (shifted K H row nonclosed antiRow).signature H=
      fun x=>(v*w)^n*E.shift (row.signature H) (choice K H row nonclosed).base x := by
    funext x
    exact O.block_value row antiRow _ H v w anti x
  rw [hrow,NoXScaleAux.gadget_scale]
  rfl

include hv hw anti in
theorem binary_nonaffine : ¬Affine (fun x=>((binary K H row nonclosed antiRow).signature H x : AlgebraicComplex)) := by
  rw [binary_exact K H row nonclosed antiRow v w anti]
  exact NoXScaleAux.nonaffine_scale _ (W.nonaffine K _ (choice K H row nonclosed).three) _
    (fun hz=>(pow_ne_zero _ (pow_ne_zero _ (mul_ne_zero hv hw))) (Subtype.ext hz))

include hv hw anti in
theorem binary_nonproduct : ¬Product (fun x=>((binary K H row nonclosed antiRow).signature H x : AlgebraicComplex)) := by
  rw [binary_exact K H row nonclosed antiRow v w anti]
  exact NoXScaleAux.nonproduct_scale _ (W.nonproduct K _ (choice K H row nonclosed).three) _
    (fun hz=>(pow_ne_zero _ (pow_ne_zero _ (mul_ne_zero hv hw))) (Subtype.ext hz))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenAntiNonclosed
end
