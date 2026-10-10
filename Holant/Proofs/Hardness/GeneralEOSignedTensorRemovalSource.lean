import Holant.Proofs.Hardness.GeneralEOSignedTensorRemovalMacro
import Holant.Proofs.Hardness.GeneralEOTensorPowerRemovalOriginalSource
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionSelfdualQuaternary

/-! An actual scaled signed tensor square supplies a controlled removal of a
literal signed binary label. The conclusion is an oracle programme, not a
claim that the signed binary is a physical gadget. Both generated source and
original target answer codecs are retained by the composition. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedTensorRemovalSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalValue)
end O
namespace A
export GeneralEOTensorPowerRemovalOriginalField (sourceFamily targetFamily)
end A
namespace T
export GeneralEOTensorPowerRemovalOriginalSource (source)
end T
namespace M
export GeneralEOSignedTensorRemovalMacro (source)
end M
namespace R
export GeneralEOPinnedDescentNetwork (reboundary reboundaryLabels reboundary_denote)
end R
namespace C
export Holant.LocalDrafts.Hardness.GeneralExtraction.Carrier (blockPower)
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def signed {K : Type} [Field K] : Signature K 2 :=
  fun x => if x 0 then (if x 1 then 0 else -1) else (if x 1 then 1 else 0)

abbrev square : Signature AlgebraicComplex 4 := C.blockPower (signed (K:=AlgebraicComplex)) 2

theorem square_unit : square ![false,true,false,true]=1 := by
  norm_num [square,C.blockPower,signed,Fin.prod_univ_two,finProdFinEquiv]

theorem lifted_product (c : AlgebraicComplex) :
    EOBinaryPlaneCore.lift (GeneralEOPhaseExtractionSelfdualQuaternary.product c true)=c • square := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [EOBinaryPlaneCore.lift,GeneralEOPhaseExtractionSelfdualQuaternary.product,
      square,C.blockPower,signed,Fin.prod_univ_two,finProdFinEquiv,h0,h1,h2,h3]

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))

theorem signed_mem (x : Fin 2→Bool) : signed (K:=AlgebraicComplex) x∈O.originalField G := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [signed,h0,h1]

theorem square_mem (x : Fin 4→Bool) : square x∈O.originalField G := by
  unfold square C.blockPower
  exact (O.originalField G).prod_mem (fun _ _ => signed_mem G _)

variable (N : Network AlgebraicComplex 4) (NL : Labelling N.shape s 1 a)
variable (hN : LabelledNetwork.Exact G N NL) (hn : ∀e,N.edge e=Signature.disequality)
variable (e : Equiv.Perm (Fin 4)) (c : AlgebraicComplex) (hc : c≠0)
variable (hv : Tensor.reindex e N.denote=
  EOBinaryPlaneCore.lift (GeneralEOPhaseExtractionSelfdualQuaternary.product c true))

abbrev permuted := R.reboundary N e
abbrev labels := R.reboundaryLabels N NL e

include hv in
theorem actual_square : (permuted N e).denote=c • square := by
  rw [permuted,R.reboundary_denote,hv,lifted_product]

include hN hn hc hv in
def squareRemoval : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (s+1) 1
      (GeneralEOTensorPowerRemovalRaw.targetArity s 2 2 a))
    (O.originalPresentation (A.targetFamily G (signed (K:=AlgebraicComplex)) 2)).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    (O.originalValue (A.targetFamily G (signed (K:=AlgebraicComplex)) 2)) (O.originalValue G) :=
  M.source G square (square_mem G) (permuted N e) (labels N NL e) hN hn c hc
    (actual_square N e c hv) ![false,true,false,true] square_unit

include hN hn hc hv in
/-- Genuine literal signed-label elimination at original generated fields.
The finite residue choices inside tensor-power removal depend only on G. -/
def source : LengthControlledOracleReduction
    (GeneralEOTensorPowerRemovalPadding.inputEncoding s 2 a)
    (O.originalPresentation (A.sourceFamily G (signed (K:=AlgebraicComplex)))).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    (O.originalValue (A.sourceFamily G (signed (K:=AlgebraicComplex)))) (O.originalValue G) :=
  C.composeControlled (T.source G (signed (K:=AlgebraicComplex)) 2 (by decide))
    (squareRemoval G N NL hN hn e c hc hv)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedTensorRemovalSource
