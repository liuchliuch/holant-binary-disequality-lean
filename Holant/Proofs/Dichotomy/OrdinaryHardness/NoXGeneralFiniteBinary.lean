import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralZBinarySplit
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralSupportSplit

/-! A finite first-row ratio is normalized by a fixed positive bundle of
literal pinned copies. The resulting actual binary has equal first-row
entries and retains its nonzero determinant, so the strict Z filter applies. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralFiniteBinary
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseBundle (evaluate)
end B
namespace O
export NoXGeneralEvenOperations (gadget gadget_value)
end O
namespace Q
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionGadget (direct direct_value)
end Q
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] {s : ℕ} {b : ℕ→ℕ}

def identityPorts : Fin 2→Bool ⊕ Fin 2 := Sum.inr

def pinPorts : Fin 2→Bool ⊕ Fin 2 := ![.inl false,.inr 1]

def ports (k : ℕ) : List (Fin 2→Bool ⊕ Fin 2) := identityPorts::List.replicate k pinPorts

def columnPower (row : B.Block (s:=s) (b:=b) 2) (k : ℕ) : B.Block (s:=s) (b:=b) 2 :=
  O.gadget row (Q.direct (ports k))

theorem value (H : (i : Fin s)→Signature K (b i.val)) (row : B.Block (s:=s) (b:=b) 2)
    (k : ℕ) (x : Fin 2→Bool) :
    (columnPower row k).signature H x=row.signature H x*row.signature H ![false,x 1]^k := by
  have hi : T.substitute identityPorts x=x := rfl
  have hp : T.substitute pinPorts x=![false,x 1] := by funext i;fin_cases i <;> rfl
  rw [columnPower,O.gadget_value,Q.direct_value]
  simp only [B.evaluate,ports,List.map_cons,List.map_replicate,List.prod_cons,List.prod_replicate,hi,hp]

section Original
variable {s0 : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s0)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (zLabel : Fin src.size)
variable (zLiteral : (⟨src.b zLabel.val,src.H zLabel⟩ : AnySignature src.K)=⟨2,NoXGeneralZSign.signature⟩)
variable (row : B.Block (s:=src.size) (b:=src.b) 2)
variable (ha : row.signature src.H ![false,false]≠0) (hb : row.signature src.H ![false,true]≠0)
variable (det : row.signature src.H ![false,false]*row.signature src.H ![true,true]≠
  row.signature src.H ![false,true]*row.signature src.H ![true,false])
variable (k : ℕ) (finite : row.signature src.H ![false,false]^(k+1)=row.signature src.H ![false,true]^(k+1))

include ha hb det finite in
theorem normalized_properties :
    (columnPower row k).signature src.H ![false,false]≠0 ∧
    (columnPower row k).signature src.H ![false,false]^4=(columnPower row k).signature src.H ![false,true]^4 ∧
    (columnPower row k).signature src.H ![false,false]*(columnPower row k).signature src.H ![true,true]≠
      (columnPower row k).signature src.H ![false,true]*(columnPower row k).signature src.H ![true,false] := by
  simp only [value,Matrix.cons_val_one,Matrix.cons_val_zero]
  constructor
  · exact mul_ne_zero ha (pow_ne_zero _ ha)
  constructor
  · have eqn : row.signature src.H ![false,false]*row.signature src.H ![false,false]^k=
      row.signature src.H ![false,true]*row.signature src.H ![false,true]^k := by
      simpa only [pow_succ',Nat.add_comm] using finite
    rw [eqn]
  · intro eqn
    apply det
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero k ha) (pow_ne_zero k hb))
    linear_combination eqn

include zLiteral ha hb det finite in
theorem anti_or_hard : NoXWeightedAntiResourcesOriginal.Hard G ∨ NoXGeneralSupportSplit.EvenAnti G src := by
  have props:=normalized_properties G src row ha hb det k finite
  exact NoXGeneralZBinarySplit.anti_or_hard G src zLabel zLiteral (columnPower row k) props.1 props.2.1 props.2.2

end Original
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralFiniteBinary
end
