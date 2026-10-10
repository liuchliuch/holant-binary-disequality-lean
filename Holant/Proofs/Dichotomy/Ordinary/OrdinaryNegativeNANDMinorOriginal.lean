import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNANDMinorSource
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentEvenCSPSource
import Holant.Proofs.Counting.Hardness

/-! An actual NAND-support binary pinning/identification minor of any retained
ordinary row gives a physical counted-verifier source to the original G.
The two pins and the final whole-family square compiler are internal. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNANDMinorOriginal
open Holant Holant.Algebraic Holant.Tractable Holant.Complexity Computability
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeNANDMinorSemantics (minor)
namespace E
export StableHigherCurrentEvenCSPSource (current ordinary ordinaryArity field squareToOriginal)
end E
namespace Pins
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Source
  (palette_first_pin palette_second_pin)
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Single (K)
end Pins
namespace Gates
export Holant.LocalDrafts.RemoteWork.CountingBridge.Gates (pin)
end Gates
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace O
export StableHigherCurrentOrdinarySquare (square)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem square_pin {K : Type} [CommSemiring K] {s : ℕ} {a : ℕ→ℕ}
    (H : (i : Fin s)→Signature K (a i.val)) (p : Fin s) (b : Bool)
    (h : (⟨a p.val,H p⟩ : AnySignature K)=⟨1,Gates.pin b⟩) :
    (⟨a p.val,O.square H p⟩ : AnySignature K)=⟨1,Gates.pin b⟩ := by
  have hp : (fun x=>(Gates.pin (K:=K) b x)^2)=Gates.pin b := by
    funext x
    simp only [Gates.pin]
    split_ifs <;> simp
  have hh := congrArg (fun f : AnySignature K=>(⟨f.1,fun x=>(f.2 x)^2⟩ : AnySignature K)) h
  change (⟨a p.val,fun x=>(H p x)^2⟩ : AnySignature K)=⟨1,Gates.pin b⟩
  simpa only [hp] using hh

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (A : QuaternaryEqualityTerminal.AnchorStep
  (UniversalPairReduction.FiniteFamily.family (E.current G P)))
local instance : Algebra ℚ (Pins.K (E.current G P) A) := (Pins.K (E.current G P) A).algebra'

def falseLabel : Fin (P.count+3) := ⟨P.count+1,by omega⟩
def trueLabel : Fin (P.count+3) := ⟨P.count+2,by omega⟩

theorem false_literal :
    (⟨E.ordinaryArity G P A (falseLabel G P).val,E.ordinary G P A (falseLabel G P)⟩ :
      AnySignature (Pins.K (E.current G P) A))=⟨1,Gates.pin false⟩ :=
  Pins.palette_first_pin (E.current G P) A

theorem true_literal :
    (⟨E.ordinaryArity G P A (trueLabel G P).val,E.ordinary G P A (trueLabel G P)⟩ :
      AnySignature (Pins.K (E.current G P) A))=⟨1,Gates.pin true⟩ :=
  Pins.palette_second_pin (E.current G P) A

variable (j : Fin (P.count+3)) (q : Fin (E.ordinaryArity G P A j.val)→Bool ⊕ Fin 2)
variable (h00 : E.ordinary G P A j (T.substitute q ![false,false])≠0)
variable (h01 : E.ordinary G P A j (T.substitute q ![false,true])≠0)
variable (h10 : E.ordinary G P A j (T.substitute q ![true,false])≠0)
variable (h11 : E.ordinary G P A j (T.substitute q ![true,true])=0)
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

/-- The actual selected row and actual substitution are the only minor data.
Every pin, byte programme, output bound and original-family query is built here. -/
def source (w : SharpPWitness ea count) : PhysicalProgramme ea encodingNatBool
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding count (OriginalForestSource.value G) :=
  PhysicalProgramme.ofControlled (Programme.compose
    (OrdinaryNegativeNANDMinorSource.source (E.field G P A) (O.square (E.ordinary G P A))
      j (falseLabel G P) (trueLabel G P) q
      (square_pin (E.ordinary G P A) (falseLabel G P) false (false_literal G P A))
      (square_pin (E.ordinary G P A) (trueLabel G P) true (true_literal G P A))
      (pow_ne_zero 2 h00) (pow_ne_zero 2 h01) (pow_ne_zero 2 h10)
      (by change (E.ordinary G P A j (T.substitute q ![true,true]))^2=0; rw [h11]; simp) w)
    (E.squareToOriginal G P A).controlled)

include j q h00 h01 h10 h11 in
theorem countingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) := by
  intro α ea count w
  exact ⟨(source G P A j q h00 h01 h10 h11 w).controlled.reduction⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNANDMinorOriginal
end
