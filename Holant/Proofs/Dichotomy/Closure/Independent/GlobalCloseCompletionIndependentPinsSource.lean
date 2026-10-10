import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsAdjoin
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryDescentSource

/-! Actual ordinary Holant-c source data. Only the two literal pins and a
controlled reduction are recorded; no equality-four or classification result
is a field. Scalar-pin graphs are normalized by physical substitution and
the full old dictionary remains literally included. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps
namespace A
export GlobalCloseCompletionIndependentPinsAdjoin
  (Output signatures arity old newLabel old_literal normalized_literal source lift)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

structure Data : Type 1 where
  K : IntermediateField ℚ AlgebraicComplex
  degree : ℕ
  F : letI : Algebra ℚ K := K.algebra'; FixedField K degree
  size : ℕ
  b : ℕ→ℕ
  H : (i : Fin size)→Signature K (b i.val)
  p : Bool→Fin size
  hp : ∀v : Bool,(⟨b (p v).val,H (p v)⟩ : AnySignature K)=⟨1,QuaternaryUnaryAccess.pin v⟩
  toOriginal : letI : Algebra ℚ K := K.algebra'; LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding size 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G)

def family (src : Data G) : SignatureFamily AlgebraicComplex := Set.range fun i : Fin src.size=>
  RingHomRealization.mapAny src.K.subtype (⟨src.b i.val,src.H i⟩ : AnySignature src.K)

theorem purePin_eq {K : Type} [Field K] (c : K) (v : Bool) :
    purePin c v 1=fun x=>c*QuaternaryUnaryAccess.pin v x := by
  funext x
  have word : (x=(fun _=>v))↔x 0=v := by
    constructor
    · intro h
      exact congrFun h 0
    · intro h
      funext i
      simpa only [Subsingleton.elim i 0] using h
  simp [purePin,QuaternaryUnaryAccess.pin,word]

section Install
variable {r degree : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L := L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (b i.val))
variable (back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))
variable (pins : Bool→A.Output H 1) (scale : Bool→L)
variable (nonzero : ∀v,scale v≠0)
variable (form : ∀v,(pins v).network.denote=purePin (scale v) v 1)

abbrev first := A.signatures F H (pins false) (scale false)
abbrev firstArity := A.arity H (pins false)
def secondGraph := A.lift F H (pins false) (scale false) (pins true)
abbrev table := A.signatures F (first L F H pins scale) (secondGraph L F H pins scale) (scale true)
abbrev arity := A.arity (first L F H pins scale) (secondGraph L F H pins scale)
def oldLabel (i : Fin r) : Fin ((r+1)+1) := A.old (first L F H pins scale) (A.old H i)
def pinLabel : Bool→Fin ((r+1)+1)
  | false=>A.old (first L F H pins scale) (A.newLabel H)
  | true=>A.newLabel (first L F H pins scale)

theorem old_literal (i : Fin r) :
    (⟨arity L F H pins scale (oldLabel L F H pins scale i).val,
      table L F H pins scale (oldLabel L F H pins scale i)⟩ : AnySignature L)=⟨b i.val,H i⟩ :=
  (A.old_literal F (first L F H pins scale) (secondGraph L F H pins scale) (scale true) (A.old H i)).trans
    (A.old_literal F H (pins false) (scale false) i)

include nonzero form in
theorem pin_literal (v : Bool) :
    (⟨arity L F H pins scale (pinLabel L F H pins scale v).val,
      table L F H pins scale (pinLabel L F H pins scale v)⟩ : AnySignature L)=
      ⟨1,QuaternaryUnaryAccess.pin v⟩ := by
  cases v
  · refine (A.old_literal F (first L F H pins scale) (secondGraph L F H pins scale)
      (scale true) (A.newLabel H)).trans ?_
    exact A.normalized_literal F H (pins false) (scale false) (QuaternaryUnaryAccess.pin false)
      (nonzero false) ((form false).trans (purePin_eq (scale false) false))
  · exact A.normalized_literal F (first L F H pins scale) (secondGraph L F H pins scale)
      (scale true) (QuaternaryUnaryAccess.pin true) (nonzero true)
      ((form true).trans (purePin_eq (scale true) true))

def data : Data G where
  K := L
  degree := degree
  F := F
  size := (r+1)+1
  b := arity L F H pins scale
  H := table L F H pins scale
  p := pinLabel L F H pins scale
  hp := pin_literal L F H pins scale nonzero form
  toOriginal := Programme.compose
    (A.source F (first L F H pins scale) (secondGraph L F H pins scale) (scale true) (nonzero true))
    (Programme.compose (A.source F H (pins false) (scale false) (nonzero false)) back)

theorem old_included : GlobalCloseCompletionUnaryDescentSource.ambient L H⊆
    family G (data G L F H back pins scale nonzero form) := by
  rintro f ⟨i,rfl⟩
  refine ⟨oldLabel L F H pins scale i,?_⟩
  exact congrArg (RingHomRealization.mapAny L.subtype) (old_literal L F H pins scale i)

theorem obstruction (negative : ¬Tract (GlobalCloseCompletionUnaryDescentSource.ambient L H)) :
    ¬Tract (family G (data G L F H back pins scale nonzero form)) :=
  fun h=>negative (h.mono_family (old_included G L F H back pins scale nonzero form))


end Install
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsSource
end
