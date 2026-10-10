import Holant.Proofs.Hardness.GeneralEOBinaryPinInterpolation
import Holant.Proofs.Reductions.GeneralExtraction.GeneralOriginalTarget

/-! A concrete global pinning branch in the unchanged original coefficient
field. An actual original binary EO row with nonzero unequal opposite norms
supplies every sample chain; all other original arities and values are retained.
The runtime input can contain the new directed paired pin arbitrarily often. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOBinaryPinSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace I
export GeneralEOBinaryPinInterpolation
  (p q Input inputEncoding sourceSignatures sourceValue targetTables unequalNormSource)
end I
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (coefficients originalField originalPresentation originalTables originalValue)
end O
namespace OT
export Holant.LocalDrafts.BinaryInterpolation.OriginalTables (castSignature castSignature_any binarySlot_old binarySlot_new)
end OT
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance fieldAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'

def original (i : Fin s) (x : Fin (a i.val)→Bool) : O.originalField G :=
  fieldCoefficient (O.coefficients G) ⟨i,x⟩

variable (M : Signature AlgebraicComplex 2) (j : Fin s)
variable (hj : (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex)=⟨2,M⟩)

def binary : Signature (O.originalField G) 2 := OT.castSignature (congrArg Sigma.fst hj) (original G j)

theorem original_binary : (⟨a j.val,original G j⟩ : AnySignature (O.originalField G))=
    ⟨2,binary G M j hj⟩ := (OT.castSignature_any (congrArg Sigma.fst hj) (original G j)).symm

private theorem cast_apply {K : Type} [Field K] {m n : ℕ} (h : m=n)
    (f : Signature K m) (x : Fin n→Bool) :
    OT.castSignature h f x=f (fun k=>x (Fin.cast h k)) := by
  subst n
  rfl

theorem binary_value (x : Fin 2→Bool) : (binary G M j hj x : AlgebraicComplex)=M x := by
  rw [binary,cast_apply]
  exact BinaryInterpolation.Chains.signature_cast_apply (G j) M hj (congrArg Sigma.fst hj) x

theorem binary_norm (x : Fin 2→Bool) : ‖binary G M j hj x‖=‖M x‖ := by
  change ‖(binary G M j hj x : AlgebraicComplex)‖=‖M x‖
  rw [binary_value]

variable (he : Signature.CentralSupport M)

include he in
theorem binary_eo : Signature.CentralSupport (binary G M j hj) := by
  intro x hx
  apply Subtype.ext
  change (binary G M j hj x : AlgebraicComplex)=0
  rw [binary_value,he x hx]

abbrev presentation := O.originalPresentation G
abbrev Input := I.Input (original G) (binary G M j hj) j (original_binary G M j hj) (presentation G)
abbrev inputEncoding := I.inputEncoding (original G) (binary G M j hj) j (original_binary G M j hj) (presentation G)
abbrev pinValue := I.sourceValue (original G) (binary G M j hj) j (original_binary G M j hj) (presentation G)
abbrev targetEncoding := RawClosedNetwork.validatedEncoding s 1 a

theorem original_tables : I.targetTables (original G) (presentation G)=O.originalTables G := rfl

variable (hp : I.p M≠0) (hq : I.q M≠0) (hn : ‖I.p M‖≠‖I.q M‖)

include hp in
theorem first_nonzero : I.p (binary G M j hj)≠0 := by
  intro hz
  have hv := binary_value G M j hj ![false,true]
  rw [show binary G M j hj ![false,true]=0 from hz] at hv
  exact hp hv.symm

include hq in
theorem second_nonzero : I.q (binary G M j hj)≠0 := by
  intro hz
  have hv := binary_value G M j hj ![true,false]
  rw [show binary G M j hj ![true,false]=0 from hz] at hv
  exact hq hv.symm

include hn in
theorem unequal : ‖I.p (binary G M j hj)‖≠‖I.q (binary G M j hj)‖ := by
  change ‖binary G M j hj ![false,true]‖≠‖binary G M j hj ![true,false]‖
  rw [binary_norm,binary_norm]
  exact hn

/-- Unbounded use of the new directed paired pin reduces to the original
family, with its original generated field, basis and answer bytes. -/
def source : LengthControlledOracleReduction (inputEncoding G M j hj) (presentation G).encoding
    (targetEncoding (s:=s) (a:=a)) (presentation G).encoding (pinValue G M j hj) (O.originalValue G) := by
  have r := I.unequalNormSource (original G) (binary G M j hj) j (original_binary G M j hj)
    (binary_eo G M j hj he) (presentation G)
    (first_nonzero G M j hj hp) (second_nonzero G M j hj hq) (unequal G M j hj hn)
  exact r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOBinaryPinSource
