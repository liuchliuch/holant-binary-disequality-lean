import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNANDMinorSemantics

/-! Internally bounded ordinary queries for weighted NAND binary minors.
The concrete emitter, validated output and exact answer are all derived. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNANDMinorSource
open Holant Holant.Algebraic Holant.Complexity Computability
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeNANDMinorRaw OrdinaryNegativeNANDMinorSemantics
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K d) (H : (i : Fin s)→Signature K (a i.val))
variable (j p₀ p₁ : Fin s) (q : Fin (a j.val)→Bool ⊕ Fin 2)
variable (h₀ : (⟨a p₀.val,H p₀⟩ : AnySignature K)=⟨1,Gates.pin false⟩)
variable (h₁ : (⟨a p₁.val,H p₁⟩ : AnySignature K)=⟨1,Gates.pin true⟩)

def controlled : LengthControlledOracleReduction P.inputEncoding F.encoding
    (O.inputEncoding s a) F.encoding
    (fun r=>V.value (fun b c=>minor H j q ![b,c]) r.val) (fun r=>W.value H r.val) :=
  controlledOneQueryOfEq (queryComputes j p₀ p₁ q (congrArg Sigma.fst h₀) (congrArg Sigma.fst h₁))
    (identityComputes F.encoding) (OrdinaryNegativeNANDTable.targetOutput F H)
    (fun r=>V.value (fun b c=>minor H j q ![b,c]) r.val)
    (fun r=>(query_value H j p₀ p₁ q h₀ h₁ r).symm)

variable (h00 : minor H j q ![false,false]≠0) (h01 : minor H j q ![false,true]≠0)
variable (h10 : minor H j q ![true,false]≠0) (h11 : minor H j q ![true,true]=0)
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (O.inputEncoding s a) F.encoding count (fun r=>W.value H r.val) :=
  Programme.compose (OrdinaryNegativeNANDSource.source F (fun b c=>minor H j q ![b,c])
    h00 h01 h10 h11 w) (controlled F H j p₀ p₁ q h₀ h₁)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNANDMinorSource
end
