import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicCriterion
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentOrdinarySourceTerminal
import Holant.Proofs.CountingMachines.StandardMachine.Source

/-! Original-G negative phase endpoint for the exact retained ordinary table.
The cubic member is resolved in that table's existing coefficient field and
the actual internally supplied Eq4 and pin labels are reused. No new family,
basis, ordinary oracle or final counting-hardness premise is introduced. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeCubicOriginal
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace S
export StableHigherCurrentEvenCSPSource (current ordinary ordinaryArity field eq4Label eq4_literal)
end S
namespace O
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Source
  (palette_first_pin palette_second_pin)
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Single (K)
end O
namespace T
export StableHigherCurrentOrdinarySourceTerminal (physicalFamily physical_family_exact)
end T
namespace C
export OrdinaryNegativeCubicCore (cubic)
end C
namespace Standard
export Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine (Model)
export Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Source (standard_to_witness)
export Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.InputRecoding (injectedEncoding)
end Standard
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (A : QuaternaryEqualityTerminal.AnchorStep
  (UniversalPairReduction.FiniteFamily.family (S.current G P)))
local instance : Algebra ℚ (O.K (S.current G P) A) := (O.K (S.current G P) A).algebra'

def falseLabel : Fin (P.count+3) := ⟨P.count+1,by omega⟩
def trueLabel : Fin (P.count+3) := ⟨P.count+2,by omega⟩

theorem false_literal :
    (⟨S.ordinaryArity G P A (falseLabel G P).val,S.ordinary G P A (falseLabel G P)⟩ :
      AnySignature (O.K (S.current G P) A))=
        ⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩ :=
  O.palette_first_pin (S.current G P) A

theorem true_literal :
    (⟨S.ordinaryArity G P A (trueLabel G P).val,S.ordinary G P A (trueLabel G P)⟩ :
      AnySignature (O.K (S.current G P) A))=
        ⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩ :=
  O.palette_second_pin (S.current G P) A

private theorem mapAny_injective {K : Type} [Field K] (φ : K →+* AlgebraicComplex)
    (hi : Function.Injective φ) : Function.Injective (RingHomRealization.mapAny φ) := by
  rintro ⟨n,f⟩ ⟨m,g⟩ h
  have hn : n=m := congrArg Sigma.fst h
  subst m
  have hf : RingHomRealization.mapSignature φ f=RingHomRealization.mapSignature φ g :=
    eq_of_heq (Sigma.mk.inj h).2
  apply congrArg (fun t : Signature K n=>(⟨n,t⟩ : AnySignature K))
  funext x
  exact hi (congrFun hf x)

theorem cubic_field_map :
    RingHomRealization.mapAny (O.K (S.current G P) A).subtype
      (⟨3,C.cubic⟩ : AnySignature (O.K (S.current G P) A))=
        (⟨3,C.cubic⟩ : AnySignature AlgebraicComplex) := by
  apply congrArg (fun f : Signature AlgebraicComplex 3=>(⟨3,f⟩ : AnySignature AlgebraicComplex))
  funext x
  unfold RingHomRealization.mapSignature C.cubic
  by_cases h : (x 0 && x 1 && x 2)=true
  · simp only [ite_eq_left h]
    rfl
  · simp only [ite_eq_right h]
    rfl

/-- Membership resolves an original physical label, reflecting coefficients
through the actual field inclusion rather than identifying answer encodings. -/
theorem cubic_label (h : (⟨3,C.cubic⟩ : AnySignature AlgebraicComplex)∈T.physicalFamily G P A) :
    ∃j : Fin (P.count+3),
      (⟨S.ordinaryArity G P A j.val,S.ordinary G P A j⟩ :
        AnySignature (O.K (S.current G P) A))=⟨3,C.cubic⟩ := by
  obtain ⟨j,hj⟩ := h
  refine ⟨j,?_⟩
  apply mapAny_injective (O.K (S.current G P) A).subtype Subtype.val_injective
  exact hj.trans (cubic_field_map G P A).symm

variable (j : Fin (P.count+3))
variable (hj : (⟨S.ordinaryArity G P A j.val,S.ordinary G P A j⟩ :
  AnySignature (O.K (S.current G P) A))=⟨3,C.cubic⟩)
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

/-- The terminal external oracle is the unchanged original-G problem.
Both scalar-two NAND corrections and all anchor/pin corrections are physical. -/
def source (w : SharpPWitness ea count) : PhysicalProgramme ea encodingNatBool
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding count (OriginalForestSource.value G) :=
  PhysicalProgramme.ofControlled (Programme.compose
    (OrdinaryNegativeCubicSource.source (S.field G P A) (S.ordinary G P A)
      j (S.eq4Label G P) (falseLabel G P) (trueLabel G P) hj (S.eq4_literal G P A)
      (false_literal G P A) (true_literal G P A) w)
    (StableHigherCurrentAnchorPins.toOriginal G P A).controlled)

def source_of_member
    (h : (⟨3,C.cubic⟩ : AnySignature AlgebraicComplex)∈T.physicalFamily G P A)
    (w : SharpPWitness ea count) :=
  source G P A (cubic_label G P A h).choose (cubic_label G P A h).choose_spec w

theorem countingHard
    (h : (⟨3,C.cubic⟩ : AnySignature AlgebraicComplex)∈T.physicalFamily G P A) :
    Holant.LocalDrafts.CountingHardness.WitnessCountingHard
      (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) := by
  intro α ea count w
  exact ⟨(source_of_member G P A h w).controlled.reduction⟩

variable {Δ Q : Type} [Fintype Δ] [Fintype Q]
variable (m : Standard.Model Δ Q) (input : Bool→Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

def standardSource
    (h : (⟨3,C.cubic⟩ : AnySignature AlgebraicComplex)∈T.physicalFamily G P A) :=
  source_of_member G P A h (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeCubicOriginal
end
