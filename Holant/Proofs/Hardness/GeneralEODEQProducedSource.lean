import Holant.Proofs.Hardness.GeneralEODEQActualAdjoin
import Holant.Proofs.Hardness.GeneralEODEQProducer
import Holant.Proofs.Hardness.GeneralEOPinnedDescentLift
import Holant.Proofs.Hardness.GeneralEOPinEliminationCases

/-! The internally produced algebraic-complex DEQ4 graph descends to the
existing original coefficient field on the same incidence shape. Its scalar
is recovered as an actual boundary value. Finite scaled substitution then
removes the new DEQ row, retaining exactly the original answer codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducedSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace P
export GeneralEOPinnedDescentPalette (arity palette pinned presentation pinnedTables pinnedValue)
end P
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget (originalField originalValue)
end O
namespace L
export GeneralEOPinnedDescentLift (lift labels exact native denote_lift)
end L
namespace R
export GeneralEODEQProducerNormalize (Produced)
end R
namespace A
export GeneralEODEQActualAdjoin (arity tables signatures inputEncoding value new_signature remove pairingSource)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance fieldAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'

def first : Fin 4 → Bool := ![false,true,false,true]
variable (Q : R.Produced (P.palette G))

abbrev scalar : O.originalField G := (L.lift G Q.network Q.labels).denote first

theorem scalar_value : (scalar G Q : AlgebraicComplex)=Q.scalar := by
  rw [scalar,L.denote_lift G Q.network Q.labels Q.exact Q.native]
  have h := congrFun Q.denote first
  simpa [Pi.smul_apply,smul_eq_mul,ExactTwoSignatures.E_reference,first] using h

theorem scalar_nonzero : scalar G Q≠0 := by
  intro h
  apply Q.nonzero
  rw [←scalar_value G Q,h]
  rfl

private theorem cast_E (x : Fin 4 → Bool) :
    (ExactTwoSignatures.E (K:=O.originalField G) x : AlgebraicComplex)=ExactTwoSignatures.E x := by
  rw [ExactTwoSignatures.E_reference,ExactTwoSignatures.E_reference]
  split_ifs <;> rfl

theorem scaled_lift : (L.lift G Q.network Q.labels).denote=scalar G Q • ExactTwoSignatures.E := by
  funext x
  apply Subtype.val_injective
  change ((L.lift G Q.network Q.labels).denote x : AlgebraicComplex)=
    (scalar G Q : AlgebraicComplex)*(ExactTwoSignatures.E (K:=O.originalField G) x : AlgebraicComplex)
  rw [L.denote_lift G Q.network Q.labels Q.exact Q.native,scalar_value,cast_E]
  exact congrFun Q.denote x

/-- Shape, labels, native edges and scalar denotation all descend together. -/
def liftProduced : R.Produced (P.pinned G) where
  network := L.lift G Q.network Q.labels
  labels := L.labels G Q.network Q.labels
  exact := L.exact G Q.network Q.labels
  native := L.native G Q.network Q.labels
  scalar := scalar G Q
  nonzero := scalar_nonzero G Q
  denote := scaled_lift G Q

variable (j : Fin s) (sign : EOSign)
variable (he : Signature.CentralSupport (G j))
variable (hs : EONegativeWitness.Supports sign ⟨a j.val,G j⟩)
variable (hp : ¬GeneralEODEQProducer.Pure sign (G j))

def selected : R.Produced (P.palette G) :=
  Classical.choice (GeneralEODEQProducer.producer G j sign he hs hp)
abbrev selectedField := liftProduced G (selected G j sign he hs hp)
abbrev network := (selectedField G j sign he hs hp).network
abbrev labels := (selectedField G j sign he hs hp).labels
abbrev selectedScalar := (selectedField G j sign he hs hp).scalar

theorem selected_exact : LabelledNetwork.Exact
    (GeneralEODEQPairingTemplates.family (P.presentation G) (P.pinnedTables G))
    (network G j sign he hs hp) (labels G j sign he hs hp) := by
  have h : GeneralEODEQPairingTemplates.family (P.presentation G) (P.pinnedTables G)=P.pinned G := by
    funext i x
    exact (P.presentation G).decode.apply_symm_apply _
  rw [h]
  exact (selectedField G j sign he hs hp).exact

theorem pinned_native : ∀ i x y,
    (P.presentation G).decode ((P.pinnedTables G).edge i x y)=Signature.disequality x y :=
  fun _ _ _ => (P.presentation G).decode.apply_symm_apply _

abbrev arity := A.arity (network G j sign he hs hp) (labels G j sign he hs hp)
abbrev tables := A.tables (P.presentation G) (P.pinnedTables G)
  (network G j sign he hs hp) (labels G j sign he hs hp) (selectedScalar G j sign he hs hp)
abbrev signatures := GeneralEODEQPairingTemplates.family (P.presentation G) (tables G j sign he hs hp)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (s+1+1) 1 (arity G j sign he hs hp)
abbrev value := (tables G j sign he hs hp).evaluate (P.presentation G)

theorem new_signature :
    (⟨arity G j sign he hs hp (s+1),
      signatures G j sign he hs hp ⟨s+1,Nat.lt_succ_self (s+1)⟩⟩ : AnySignature (O.originalField G))=
        ⟨4,ExactTwoSignatures.E⟩ :=
  A.new_signature (P.presentation G) (P.pinnedTables G)
    (network G j sign he hs hp) (labels G j sign he hs hp) (selectedScalar G j sign he hs hp)
    (selected_exact G j sign he hs hp) (pinned_native G)
    (selectedField G j sign he hs hp).native (selectedField G j sign he hs hp).denote
    (selectedField G j sign he hs hp).nonzero

/-- The only target rows are the old original labels and the one explicit
directed pin. This is the pinned conclusion of the non-pure producer. -/
def pinnedSource : LengthControlledOracleReduction (inputEncoding G j sign he hs hp)
    (P.presentation G).encoding
    (RawClosedNetwork.validatedEncoding (s+1) 1 (P.arity (s:=s) (a:=a))) (P.presentation G).encoding
    (value G j sign he hs hp) (P.pinnedValue G) :=
  A.remove (P.presentation G) (P.pinnedTables G)
    (network G j sign he hs hp) (labels G j sign he hs hp) (selectedScalar G j sign he hs hp)
    (selectedField G j sign he hs hp).nonzero

/-- An available actual pin eliminator is composed without changing either
the old target family or its existing fixed-field answer encoding. -/
def originalSource (eliminate : GeneralEOPinEliminationCases.Elimination G) :
    LengthControlledOracleReduction (inputEncoding G j sign he hs hp) (P.presentation G).encoding
      (RawClosedNetwork.validatedEncoding s 1 a) (P.presentation G).encoding
      (value G j sign he hs hp) (O.originalValue G) :=
  Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.composeControlled
    (pinnedSource G j sign he hs hp) eliminate

theorem native_tables : ∀ i x y,
    (P.presentation G).decode ((tables G j sign he hs hp).edge i x y)=Signature.disequality x y :=
  pinned_native G

variable (pairings : (i : Fin (s+1+1)) → OrientedPerfectPairing (arity G j sign he hs hp i.val))

/-- The non-pure original row supplies E internally, then every chosen
restriction is compiled before querying the original family with pins. -/
def pairedPinnedSource : LengthControlledOracleReduction
    (GeneralEOPairedCSPFamilyRaw.encoding (s+1+1)) (P.presentation G).encoding
    (RawClosedNetwork.validatedEncoding (s+1) 1 (P.arity (s:=s) (a:=a))) (P.presentation G).encoding
    (GeneralEOPairedCSPFamilyNative.totalValue (signatures G j sign he hs hp) pairings)
    (P.pinnedValue G) :=
  Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.composeControlled
    (GeneralEODEQPairingSource.controlled (P.presentation G) (tables G j sign he hs hp)
      pairings ⟨s+1,Nat.lt_succ_self (s+1)⟩ (new_signature G j sign he hs hp)
      (native_tables G j sign he hs hp))
    (pinnedSource G j sign he hs hp)

def pairedOriginalSource (eliminate : GeneralEOPinEliminationCases.Elimination G) :
    LengthControlledOracleReduction (GeneralEOPairedCSPFamilyRaw.encoding (s+1+1))
      (P.presentation G).encoding (RawClosedNetwork.validatedEncoding s 1 a) (P.presentation G).encoding
      (GeneralEOPairedCSPFamilyNative.totalValue (signatures G j sign he hs hp) pairings)
      (O.originalValue G) :=
  Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.composeControlled
    (pairedPinnedSource G j sign he hs hp pairings) eliminate

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducedSource
