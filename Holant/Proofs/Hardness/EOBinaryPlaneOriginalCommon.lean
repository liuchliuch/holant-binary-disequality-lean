import Holant.Proofs.Hardness.EOBinaryPlaneCommonField
import Holant.Proofs.Reductions.EightVertexNonexception.Source
import Holant.Proofs.Algorithms.FieldTransport
import Holant.NetworkAlgebra

/-! The common conjugate field and every answer conversion are derived from
one original M and its algebraicity proof. The final oracle still uses exactly
Source.field M and Source.presentation M halg; graph bytes and the original
M/native-X palette are unchanged by these answer-only conversions. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneOriginalCommon
open Holant Holant.Algebraic Holant.Complexity
open Holant.Complexity.BinaryCompose
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (coefficient coefficient_algebraic field fieldSignature presentation tables TargetInput targetEncoding targetValue target_value_exact)
end O
namespace C
export EOBinaryPlaneCommonField
  (common commonPresentation into into_value star_value conjugationComputes)
end C
namespace T
export Holant.LocalDrafts.MainChain.FieldTransport (toOriginal fromOriginal)
end T
set_option backward.isDefEq.respectTransparency false

variable (M : Signature ℂ 4) (halg : ∀x,IsAlgebraic ℚ (M x))

abbrev field := C.common (O.coefficient M)
abbrev presentation := C.commonPresentation (O.coefficient M) (O.coefficient_algebraic M halg)
def into : O.field M→ₐ[ℚ]field M := C.into (O.coefficient M)

def original : Signature (field M) 4 := fun x=>into M (O.fieldSignature M x)
def conjugate : Signature (field M) 4 := fun x=>star (original M x)

theorem original_value (x : Fin 4→Bool) : ((original M x : field M) : ℂ)=M x :=
  C.into_value (O.coefficient M) (O.fieldSignature M x)

theorem conjugate_value (x : Fin 4→Bool) : ((conjugate M x : field M) : ℂ)=star (M x) := by
  rw [conjugate,C.star_value,original_value]

abbrev embedComputes := Holant.LocalDrafts.MainChain.FieldCodec.computes
  (O.presentation M halg) (presentation M halg) (into M).toLinearMap
abbrev retractComputes := Holant.LocalDrafts.MainChain.FieldCodec.retractComputes
  (O.presentation M halg) (presentation M halg) (into M)
abbrev conjugationComputes := C.conjugationComputes (O.coefficient M) (O.coefficient_algebraic M halg)

def value (r : O.TargetInput) : field M :=
  (r.val.realize r.property (fun _=>original M) (fun _=>Signature.disequality)).denote Fin.elim0

theorem network_map (r : O.TargetInput) :
    (r.val.realize r.property (fun _=>original M) (fun _=>Signature.disequality)).map (field M).subtype=
      r.val.realize r.property (fun _=>M) (fun _=>Signature.disequality) := by
  unfold Network.map RawClosedNetwork.realize
  congr 1
  funext e x y
  cases x <;> cases y <;> rfl

theorem value_exact (r : O.TargetInput) : value M r=into M (O.targetValue M halg r) := by
  apply Subtype.ext
  change ((value M r : field M) : ℂ)=((C.into (O.coefficient M) (O.targetValue M halg r) : field M) : ℂ)
  rw [C.into_value,O.target_value_exact]
  exact (Network.denote_map (field M).subtype _ Fin.elim0).symm.trans
    (congrArg (fun N : Network ℂ 0=>N.denote Fin.elim0) (network_map M r))

/-- Actual codec conversion to the original-M oracle. No field equality and
no inverse complex conjugation algorithm is a supplied hypothesis. -/
def toOriginal : LengthControlledOracleReduction O.targetEncoding (presentation M halg).encoding
    O.targetEncoding (O.presentation M halg).encoding (value M) (O.targetValue M halg) := by
  have h : value M=(fun r=>into M (O.targetValue M halg r)) := funext (value_exact M halg)
  rw [h]
  exact T.toOriginal (O.presentation M halg) (presentation M halg) (into M) O.targetEncoding
    (O.targetValue M halg) ((O.tables M halg).outputBound (O.presentation M halg))

def fromOriginal : LengthControlledOracleReduction O.targetEncoding (O.presentation M halg).encoding
    O.targetEncoding (presentation M halg).encoding (O.targetValue M halg) (value M) := by
  have h : value M=(fun r=>into M (O.targetValue M halg r)) := funext (value_exact M halg)
  rw [h]
  exact T.fromOriginal (O.presentation M halg) (presentation M halg) (into M) O.targetEncoding
    (O.targetValue M halg) ((O.tables M halg).outputBound (O.presentation M halg))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneOriginalCommon
