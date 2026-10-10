import Holant.Proofs.Hardness.EOQuaternaryCompleteSource
import Holant.Proofs.Hardness.SignatureFieldMap
import Holant.Proofs.Hardness.SelectedOriginalFamily

/-! The accepted complex quaternary producer is returned to the ORIGINAL
algebraic-complex generated field by a real rational-matrix answer programme.
The family endpoint is exactly GeneralOriginalTarget.originalValue G. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternaryOriginalSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field presentation targetEncoding targetValue)
end O
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
namespace Standard
export Holant.LocalDrafts.MainChain.CBStandardNativeHardness.Standard
  (Model injectedEncoding standard_to_witness)
end Standard
set_option backward.isDefEq.respectTransparency false
variable (M : Signature AlgebraicComplex 4)

theorem algebraic : ∀x,IsAlgebraic ℚ (M x) := fun _=>Algebra.IsAlgebraic.isAlgebraic _
abbrev complexMap : AlgebraicComplex→ₐ[ℚ]ℂ := (algebraicClosure ℚ ℂ).val
local instance originalAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'
local instance complexAlgebra : Algebra ℚ (O.field (EOQuaternarySparseDispatch.complex M)) :=
  (O.field (EOQuaternarySparseDispatch.complex M)).algebra'
variable (he : DenseEOUnitLocal.EOSupport M) (hn : ¬EOTract {⟨4,M⟩})
variable {α : Type} {ea : Encoding α Bool} {f : α→ℕ}

def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding (O.presentation M (algebraic M)).encoding f (O.targetValue M (algebraic M)) :=
  C.composeControlled (EOQuaternaryCompleteSource.source M he hn w)
    (SignatureFieldMap.controlled M (algebraic M) complexMap)

include he hn in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    O.targetEncoding (O.presentation M (algebraic M)).encoding (O.targetValue M (algebraic M)) := by
  intro α ea f w
  exact ⟨(source M he hn w).reduction⟩

variable {Δ Q : Type} [Fintype Δ] [Fintype Q]
variable (m : Standard.Model Δ Q) (input : Bool→Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

def standardSource : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding (O.presentation M (algebraic M)).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (O.targetValue M (algebraic M)) :=
  source M he hn (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

namespace Family
namespace A
export SelectedOriginalFamily (controlled targetEncoding)
end A
namespace T
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalValue)
end T
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val)) (j : Fin s)
variable (hj : (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex)=⟨4,M⟩)
local instance targetAlgebra : Algebra ℚ (T.originalField G) := (T.originalField G).algebra'

def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (A.targetEncoding (s:=s) (a:=a)) (T.originalPresentation G).encoding f (T.originalValue G) :=
  C.composeControlled (EOQuaternaryOriginalSource.source M he hn w) (A.controlled G M j hj)

include M he hn j hj in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (A.targetEncoding (s:=s) (a:=a)) (T.originalPresentation G).encoding (T.originalValue G) := by
  intro α ea f w
  exact ⟨(source M he hn G j hj w).reduction⟩

def standardSource : LengthControlledOracleReduction ea encodingNatBool
    (A.targetEncoding (s:=s) (a:=a)) (T.originalPresentation G).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (T.originalValue G) :=
  source M he hn G j hj (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)
end Family

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternaryOriginalSource
