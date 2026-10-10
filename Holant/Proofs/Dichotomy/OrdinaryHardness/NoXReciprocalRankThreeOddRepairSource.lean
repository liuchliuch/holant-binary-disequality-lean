import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeOddRepairRecipe
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeOddRepairClass
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralOddCompose
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralOddLabel
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralOddRelabel

/-! The two-copy repair is flattened into the unchanged original table.
The old seven-port resource and retained zero pin are the only inner rows;
all scalars, private variables and source-label multiplicities are preserved. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeOddRepairSource
open Holant Holant.Tractable
namespace C
export NoXReciprocalRankThreeOddRepairCore (Exotic exotic correction full)
export NoXReciprocalMixedProjectionCore (logical)
export OrdinaryNegativeSparseMixingAlpha (codeSeven)
end C
namespace R
export NoXReciprocalRankThreeOddRepairRecipe (arity table resource value)
end R
namespace D
export OrdinaryNegativeXUniversalResource (OddResource AlphaResource AffineResource)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (p0 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (row : D.OddResource (s:=s) b 7)

def pinResource : D.OddResource (s:=s) b 1 :=
  NoXGeneralOddRelabel.resource (a:=fun _=>1)
    (fun _ : Fin 1=>OrdinaryNegativeSignedPortsCore.pin false) H (fun _=>p0) (fun _=>h0)
    (NoXGeneralOddLabel.resource (b:=fun _=>1) (0 : Fin 1))

theorem pin_value (x : Fin 1→Bool) : (pinResource H p0 h0).signature H x=
    OrdinaryNegativeSignedPortsCore.pin false x := by
  rw [pinResource,NoXGeneralOddRelabel.signature,NoXGeneralOddLabel.value]

def inner : (i : Fin 2)→D.OddResource (s:=s) b (R.arity i.val)
  | ⟨0,_⟩=>row
  | ⟨1,_⟩=>pinResource H p0 h0
  | ⟨j+2,h⟩=>False.elim (by omega)

def resource : D.OddResource (s:=s) b 7 :=
  NoXGeneralOddCompose.resource R.resource (inner H p0 h0 row)

theorem inner_value : (fun i=>(inner H p0 h0 row i).signature H)=R.table (row.signature H) := by
  funext i
  fin_cases i
  · rfl
  · exact funext (pin_value H p0 h0)

variable (support : ∀z,row.ambient H z≠0 ↔ C.Exotic z)
include support in
theorem value (z : Fin 7→Bool) : (resource H p0 h0 row).signature H z=
    row.signature H (C.logical C.exotic z)*row.signature H (C.correction z) := by
  rw [resource,NoXGeneralOddCompose.value,inner_value]
  apply R.value
  intro x
  have he:row.signature H x≠0 ↔ row.ambient H x≠0:=Subtype.coe_ne_coe.symm
  exact he.trans (support x)

include support in
theorem ambient_value (z : Fin 7→Bool) : (resource H p0 h0 row).ambient H z=
    row.ambient H (C.logical C.exotic z)*row.ambient H (C.correction z) := by
  change ((resource H p0 h0 row).signature H z : AlgebraicComplex)=_
  rw [value H p0 h0 row support]
  exact map_mul K.subtype _ _

def alphaResource
    (alpha : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action (row.ambient H))) :
    D.AlphaResource H .seven where
  toOddResource := resource H p0 h0 row
  alpha := by
    change Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action
      (fun z : Fin 7→Bool=>(resource H p0 h0 row).ambient H z))
    rw [funext (ambient_value H p0 h0 row support)]
    exact NoXReciprocalRankThreeOddRepairClass.alpha (row.ambient H) alpha
  full := by
    intro x
    change (resource H p0 h0 row).ambient H (C.codeSeven x)≠0
    rw [ambient_value H p0 h0 row support]
    exact C.full (row.ambient H) support x

def affineResource (affine : Affine (row.ambient H)) : D.AffineResource H .seven where
  toOddResource := resource H p0 h0 row
  affine := by
    change Affine (fun z : Fin 7→Bool=>(resource H p0 h0 row).ambient H z)
    rw [funext (ambient_value H p0 h0 row support)]
    exact NoXReciprocalRankThreeOddRepairClass.affine (row.ambient H) affine
  full := by
    intro x
    change (resource H p0 h0 row).ambient H (C.codeSeven x)≠0
    rw [ambient_value H p0 h0 row support]
    exact C.full (row.ambient H) support x


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeOddRepairSource
end
