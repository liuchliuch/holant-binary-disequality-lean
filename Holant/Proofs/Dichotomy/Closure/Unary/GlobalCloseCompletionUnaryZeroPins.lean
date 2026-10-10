import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryZeroOriginSource
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsSource
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryUniversalSelector

/-! The zero-origin exit has a genuine ordinary two-pin source. Normalize
the actual zero pin, extract the pure opposite power by actual caps, and use
the implemented unary-power source. Both literal pins and every old row are
then present in one fixed field with an exact original-G reduction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryZeroPins
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace A
export GlobalCloseCompletionIndependentPinsAdjoin
  (signatures arity newLabel old old_literal normalized_literal source lift)
end A
namespace Z
export GlobalCloseCompletionUnaryZeroOrigin (power)
export GlobalCloseCompletionUnaryZeroPower (opposite)
end Z
namespace P
export GlobalCloseCompletionUnaryPowerOrdinary (field presentation table family arity old_included unary_member)
export GlobalCloseCompletionUnaryPowerSource (toOriginal)
end P
namespace C
export GlobalCloseCompletionUnaryOrdinaryFieldCodec (ambient)
end C
namespace U
export GeneralOddNonisotropicFrame (norm chart frame inverse)
end U
namespace D
export GlobalCloseCompletionUnaryDescentSource (ambient)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s r degree n : ℕ} {a b : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L := L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (b i.val))
variable (back : LengthControlledOracleReduction
  (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
  ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))
variable (first : NoXOrdinaryGraphAdjoin.Output H 1) (scalar : L) (scalarNonzero : scalar≠0)
variable (pin0 : first.network.denote (fun _=>false)=scalar)
variable (pin1 : first.network.denote (fun _=>true)=0)
variable (N : NoXOrdinaryGraphAdjoin.Output H n)
variable (nonzero : N.network.denote≠0) (zero : N.network.denote (fun _=>false)=0)

abbrev firstTable := A.signatures F H first scalar
abbrev firstArity := A.arity H first

include pin0 pin1 in
theorem first_form : first.network.denote=fun x=>scalar*QuaternaryUnaryAccess.pin false x := by
  funext x
  have hx : x=(fun _=>x 0) := by funext i;rw [Fin.eq_zero i]
  rw [hx]
  cases h : x 0 <;>simp [pin0,pin1,QuaternaryUnaryAccess.pin]

include scalarNonzero pin0 pin1 in
theorem first_literal :
    (⟨firstArity L H first (A.newLabel H).val,firstTable L F H first scalar (A.newLabel H)⟩ : AnySignature L)=
      ⟨1,QuaternaryUnaryAccess.pin false⟩ :=
  A.normalized_literal F H first scalar (QuaternaryUnaryAccess.pin false) scalarNonzero
    (first_form L H first scalar pin0 pin1)

def firstGraph : NoXOrdinaryGraphAdjoin.Output (firstTable L F H first scalar) 1 where
  network:=Network.corolla (QuaternaryUnaryAccess.pin false)
  labels := {
    vertex := fun _=>A.newLabel H
    vertex_arity := fun _=>congrArg Sigma.fst (first_literal L F H first scalar scalarNonzero pin0 pin1)
    edge := fun e=>Fin.elim0 e }
  exact _:=first_literal L F H first scalar scalarNonzero pin0 pin1
  ordinary e:=Fin.elim0 e

theorem first_value : (firstGraph L F H first scalar scalarNonzero pin0 pin1).network.denote=
    QuaternaryUnaryAccess.pin false := Network.denote_corolla _

theorem first_norm : U.norm (firstGraph L F H first scalar scalarNonzero pin0 pin1).network.denote=1 := by
  rw [first_value]
  simp [U.norm,QuaternaryUnaryAccess.pin]

theorem first_chart (f : Signature L n) :
    U.chart (firstGraph L F H first scalar scalarNonzero pin0 pin1).network.denote f=f := by
  rw [first_value]
  have frame : U.frame (QuaternaryUnaryAccess.pin (K:=L) false)=Signature.equality := by
    funext p q
    cases p <;>cases q <;>simp [U.frame,QuaternaryUnaryAccess.pin,Signature.equality]
  rw [U.chart,frame,Signature.coordinateAction_equality]

def vector : Bool→L := fun v=>if v then 1 else 0

theorem first_opposite : Z.opposite (firstGraph L F H first scalar scalarNonzero pin0 pin1).network.denote=
    vector L := by
  rw [first_value]
  funext v
  cases v <;>simp [Z.opposite,U.inverse,U.norm,U.frame,QuaternaryUnaryAccess.pin,vector]

abbrev lifted := A.lift F H first scalar N

def power := Z.power (firstTable L F H first scalar)
  (firstGraph L F H first scalar scalarNonzero pin0 pin1).network
  (firstGraph L F H first scalar scalarNonzero pin0 pin1).labels
  (firstGraph L F H first scalar scalarNonzero pin0 pin1).exact
  (firstGraph L F H first scalar scalarNonzero pin0 pin1).ordinary
  (lifted L F H first scalar N).network (lifted L F H first scalar N).labels
  (lifted L F H first scalar N).exact (lifted L F H first scalar N).ordinary
  (by rw [first_norm];exact one_ne_zero) nonzero
  (by rw [first_chart];exact zero)

theorem power_form :
    (power L F H first scalar scalarNonzero pin0 pin1 N nonzero zero).graph.denote=
      fun x=>(power L F H first scalar scalarNonzero pin0 pin1 N nonzero zero).scalar*
        Signature.unaryPower (vector L) (power L F H first scalar scalarNonzero pin0 pin1 N nonzero zero).arity x := by
  have h:=(power L F H first scalar scalarNonzero pin0 pin1 N nonzero zero).equation
  rwa [first_opposite] at h

abbrev ambientVector : Bool→AlgebraicComplex := fun v=>(vector L v : AlgebraicComplex)
abbrev field := P.field (C.ambient L (firstTable L F H first scalar)) (ambientVector L)
local instance : Algebra ℚ (field L F H first scalar) := (field L F H first scalar).algebra'
abbrev presentation := P.presentation (C.ambient L (firstTable L F H first scalar)) (ambientVector L)
abbrev table := P.table (C.ambient L (firstTable L F H first scalar)) (ambientVector L)
abbrev arity := P.arity (r:=r+1) (b:=firstArity L H first)
abbrev family := P.family (C.ambient L (firstTable L F H first scalar)) (ambientVector L)

def source :=
  let E:=power L F H first scalar scalarNonzero pin0 pin1 N nonzero zero
  P.toOriginal G L F (firstTable L F H first scalar)
    (Programme.compose (A.source F H first scalar scalarNonzero) back)
    E.graph E.labels E.exact E.edges E.positive (vector L) E.scalar E.nonzero
    (power_form L F H first scalar scalarNonzero pin0 pin1 N nonzero zero)

theorem old_included : D.ambient L H⊆family L F H first scalar := by
  rintro f ⟨i,rfl⟩
  apply P.old_included
  refine ⟨A.old H i,?_⟩
  exact congrArg (RingHomRealization.mapAny L.subtype) (A.old_literal F H first scalar i)

theorem map_pin (J : IntermediateField ℚ AlgebraicComplex) (v : Bool) :
    RingHomRealization.mapAny J.subtype (⟨1,QuaternaryUnaryAccess.pin v⟩ : AnySignature J)=
      (⟨1,QuaternaryUnaryAccess.pin v⟩ : AnySignature AlgebraicComplex) := by
  apply congrArg (fun f : Signature AlgebraicComplex 1=>(⟨1,f⟩ : AnySignature AlgebraicComplex))
  funext x
  change (((if x 0=v then 1 else 0) : J) : AlgebraicComplex)=(if x 0=v then 1 else 0)
  split_ifs <;>rfl

include scalarNonzero pin0 pin1 in
theorem pin_member (v : Bool) :
    (⟨1,QuaternaryUnaryAccess.pin v⟩ : AnySignature AlgebraicComplex)∈family L F H first scalar := by
  cases v
  · apply P.old_included
    refine ⟨A.newLabel H,?_⟩
    have h:=congrArg (RingHomRealization.mapAny L.subtype)
      (first_literal L F H first scalar scalarNonzero pin0 pin1)
    exact h.trans (map_pin L false)
  · have h:=P.unary_member (C.ambient L (firstTable L F H first scalar)) (ambientVector L)
    have hv : (fun x : Fin 1→Bool=>ambientVector L (x 0))=QuaternaryUnaryAccess.pin true := by
      funext x
      cases hx : x 0 <;>simp [ambientVector,vector,QuaternaryUnaryAccess.pin,hx]
    rwa [hv] at h

def pinLabel (v : Bool) : Fin ((r+1)+2) :=
  Classical.choose (pin_member L F H first scalar scalarNonzero pin0 pin1 v)

theorem pin_literal (v : Bool) :
    (⟨arity L H first (pinLabel L F H first scalar scalarNonzero pin0 pin1 v).val,
      table L F H first scalar (pinLabel L F H first scalar scalarNonzero pin0 pin1 v)⟩ :
      AnySignature (field L F H first scalar))=⟨1,QuaternaryUnaryAccess.pin v⟩ := by
  apply Holant.LocalDrafts.Hardness.FrozenFactorNormalization.mapAny_injective (field L F H first scalar).subtype
  have h:=Classical.choose_spec (pin_member L F H first scalar scalarNonzero pin0 pin1 v)
  exact h.trans (map_pin (field L F H first scalar) v).symm

def data : GlobalCloseCompletionIndependentPinsSource.Data G where
  K:=field L F H first scalar
  degree:=_
  F:=presentation L F H first scalar
  size:=(r+1)+2
  b:=arity L H first
  H:=table L F H first scalar
  p:=pinLabel L F H first scalar scalarNonzero pin0 pin1
  hp:=pin_literal L F H first scalar scalarNonzero pin0 pin1
  toOriginal:=source G L F H back first scalar scalarNonzero pin0 pin1 N nonzero zero

theorem obstruction (negative : ¬Tract (D.ambient L H)) :
    ¬Tract (GlobalCloseCompletionIndependentPinsSource.family G
      (data G L F H back first scalar scalarNonzero pin0 pin1 N nonzero zero)) :=
  fun h=>negative (h.mono_family (old_included L F H first scalar))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryZeroPins
end
