import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentUnaryQueryControl
import Holant.Proofs.Closure.PhysicalCosts
import Holant.Proofs.Closure.ProgrammeCompose

/-! Controlled whole-current-family pin access from an actual retained pure
quaternary event. The existing one-Delta compiler, replication correction and
two factor steps are used unchanged. A real field-codec map restores the
original G field before composing the actual current-to-original programme. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentPurePinsCore
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open Holant.Complexity.BinaryCompose Holant.Complexity.FixedFieldMachines
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
namespace Pins
export QuaternaryUnaryAccess (pin pin_nonzero)
end Pins
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

abbrev embedding := OriginalFrozenForest.OriginalInput.embedding G
abbrev mapped := OriginalLCodec.mapped (embedding G) P.table
abbrev Work := QuaternaryUnaryAccess.K (mapped G P)
abbrev workPresentation := QuaternaryUnaryAccess.F (mapped G P)
abbrev intoOriginal := QuaternaryUnaryAccess.intoL (embedding G) P.table
abbrev count := P.count + 2
abbrev arity := QuaternaryUnaryAccess.paletteArity P.count P.arity

def table (i : Fin (count G P)) : Signature (OI.K G) (arity G P i.val) :=
  fun x => intoOriginal G P (QuaternaryUnaryAccess.palette (mapped G P) i x)

def mapAny (f : AnySignature (Work G P)) : AnySignature (OI.K G) :=
  ⟨f.1,fun x => intoOriginal G P (f.2 x)⟩

def oldLabel (i : Fin P.count) : Fin (count G P) :=
  ⟨i.val,Nat.lt.step (Nat.lt.step i.isLt)⟩
def pinLabel (b : Bool) : Fin (count G P) :=
  ⟨P.count+b.toNat,by cases b <;> simp [count] <;> omega⟩

theorem oldLabel_injective : Function.Injective (oldLabel G P) := by
  intro i j he
  exact Fin.ext (congrArg (fun k : Fin (count G P) => k.val) he)

theorem table_old (i : Fin P.count) :
    (⟨arity G P (oldLabel G P i).val,table G P (oldLabel G P i)⟩ : AnySignature (OI.K G)) =
      ⟨P.arity i.val,P.table i⟩ := by
  have h := congrArg (mapAny G P) (QuaternaryUnaryAccess.palette_old (mapped G P) i)
  change (⟨arity G P (oldLabel G P i).val,table G P (oldLabel G P i)⟩ : AnySignature (OI.K G)) =
    ⟨P.arity i.val,fun x => intoOriginal G P (QuaternaryUnaryAccess.decoded (mapped G P) i x)⟩ at h
  exact h.trans (congrArg (fun f => (⟨P.arity i.val,f⟩ : AnySignature (OI.K G)))
    (funext (fun x => QuaternaryUnaryAccess.intoL_original (embedding G) P.table i x)))

theorem table_pin (b : Bool) :
    (⟨arity G P (pinLabel G P b).val,table G P (pinLabel G P b)⟩ : AnySignature (OI.K G)) =
      ⟨1,Pins.pin b⟩ := by
  have h := congrArg (mapAny G P) (QuaternaryUnaryAccess.palette_pin (mapped G P) b)
  change (⟨arity G P (pinLabel G P b).val,table G P (pinLabel G P b)⟩ : AnySignature (OI.K G)) =
    ⟨1,fun x => intoOriginal G P (Pins.pin (K:=Work G P) b x)⟩ at h
  exact h.trans (congrArg (fun f => (⟨1,f⟩ : AnySignature (OI.K G)))
    (funext (fun x => QuaternaryUnaryAccess.pin_map (intoOriginal G P).toRingHom b x)))

theorem arity_agrees (i : Fin P.count) : arity G P i.val = P.arity i.val :=
  congrArg Sigma.fst (table_old G P i)

/-- The coefficient conversion is a proved table identity. The work-field
codec is not silently identified with the original-field codec. -/
theorem mapped_tables :
    TableFieldTransport.mapTables (workPresentation G P) (OI.presentation G)
      (intoOriginal G P) (QuaternaryUnaryAccess.paletteTables (mapped G P)) =
      OriginalLCodec.tables (table G P) := by
  unfold TableFieldTransport.mapTables QuaternaryUnaryAccess.paletteTables OriginalLCodec.tables
    GeneralFieldReduction.targetTables FieldReduction.targetTables
  congr 1
  · funext i x
    rw [LinearEquiv.apply_symm_apply]
    rfl
  · funext i x y
    rw [LinearEquiv.apply_symm_apply]
    congr 1
    cases x <;> cases y <;> simp [Signature.disequality]

def answerIntoOriginal : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (count G P) 1 (arity G P)) (OI.presentation G).encoding
    (QuaternaryUnaryAccess.paletteEncoding P.count P.arity) (workPresentation G P).encoding
    (OriginalLCodec.value (table G P)) (QuaternaryUnaryAccess.paletteValue (mapped G P)) := by
  have result := TableFieldTransport.toOriginal (workPresentation G P) (OI.presentation G)
    (intoOriginal G P) (QuaternaryUnaryAccess.paletteTables (mapped G P))
  rw [mapped_tables] at result
  exact result

/-- The reverse direction keeps the exact old graph bytes and ordered ports. -/
def includeOld (r : ExactSignatureTables.Input P.count 1 P.arity) :
    ExactSignatureTables.Input (count G P) 1 (arity G P) := by
  refine ⟨r.val,?_,r.property.2⟩
  intro v
  have hv := r.property.1 v
  exact ⟨Nat.lt.step (Nat.lt.step hv.1),hv.2.trans (arity_agrees G P ⟨_,hv.1⟩).symm⟩

def includeOldComputes : Computes
    (RawClosedNetwork.validatedEncoding P.count 1 P.arity)
    (RawClosedNetwork.validatedEncoding (count G P) 1 (arity G P)) (includeOld G P) :=
  recode (identityComputes (RawClosedNetwork.validatedEncoding P.count 1 P.arity)) id
    (fun _ => rfl) (fun _ => rfl)

theorem includeOld_value (r : ExactSignatureTables.Input P.count 1 P.arity) :
    OriginalLCodec.value P.table r = OriginalLCodec.value (table G P) (includeOld G P r) := by
  change ((FieldReduction.targetTables (OI.presentation G) P.table).evaluate (OI.presentation G) r) =
    ((FieldReduction.targetTables (OI.presentation G) (table G P)).evaluate (OI.presentation G) _)
  rw [FieldReduction.target_evaluate,FieldReduction.target_evaluate]
  simp only [Network.denote,RawClosedNetwork.realize,NetworkShape.assignment,
    RawClosedNetwork.shape_ports,Sum.elim_inr]
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro v _
    have hi := (r.property.1 v).1
    change P.table ⟨(r.val.vertices.get v).1,hi⟩
      (fun j => z (r.val.route r.property ⟨v,j⟩)) =
      table G P ⟨(r.val.vertices.get v).1,Nat.lt.step (Nat.lt.step hi)⟩
        (fun j => z (r.val.route (includeOld G P r).property ⟨v,j⟩))
    have hs := Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
      (table G P (oldLabel G P ⟨_,hi⟩)) (P.table ⟨_,hi⟩)
      (table_old G P ⟨_,hi⟩) (arity_agrees G P ⟨_,hi⟩)
      (fun j => z (r.val.route r.property ⟨v,j⟩))
    simpa only [includeOld,oldLabel,RawClosedNetwork.route,RawClosedNetwork.portEndpoint,Fin.cast_cast] using hs.symm
  · rfl

def fromCurrent : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding P.count 1 P.arity) (OI.presentation G).encoding
    (RawClosedNetwork.validatedEncoding (count G P) 1 (arity G P)) (OI.presentation G).encoding
    (OriginalLCodec.value P.table) (OriginalLCodec.value (table G P)) :=
  controlledOneQueryOfEq (includeOldComputes G P) (identityComputes (OI.presentation G).encoding)
    ((OriginalLCodec.tables (table G P)).outputBound (OI.presentation G)) _ (includeOld_value G P)

variable (j : Fin P.count) {q : Signature AlgebraicComplex 4}
variable (literal : (⟨P.arity j.val,mapped G P j⟩ : AnySignature AlgebraicComplex) = ⟨4,q⟩)
variable (pure : QuaternaryEqualityTerminal.PureStep q)

/-- The actual controlled two-pin producer is installed, not the old
existential PolyTime reduction and not a supplied pin-access assumption. -/
def toCurrent : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (count G P) 1 (arity G P)) (OI.presentation G).encoding
    (RawClosedNetwork.validatedEncoding P.count 1 P.arity) (OI.presentation G).encoding
    (OriginalLCodec.value (table G P)) (OriginalLCodec.value P.table) :=
  Programme.compose (answerIntoOriginal G P)
    (StableHigherCurrentUnaryQueryControl.SourceV2.source (embedding G) P.table j literal pure)

def toOriginal : PhysicalProgramme
    (RawClosedNetwork.validatedEncoding (count G P) 1 (arity G P)) (OI.presentation G).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (OriginalLCodec.value (table G P)) (OriginalForestSource.value G) :=
  PhysicalProgramme.ofControlled (Programme.compose (toCurrent G P j literal pure) P.toOriginal.controlled)

def fromOriginal : PhysicalProgramme
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (RawClosedNetwork.validatedEncoding (count G P) 1 (arity G P)) (OI.presentation G).encoding
    (OriginalForestSource.value G) (OriginalLCodec.value (table G P)) :=
  PhysicalProgramme.ofControlled (Programme.compose P.fromOriginal.controlled (fromCurrent G P))

theorem toOriginal_same_machine : (toOriginal G P j literal pure).controlled.reduction.machine =
    (Programme.compose (toCurrent G P j literal pure) P.toOriginal.controlled).reduction.machine := rfl

theorem fromOriginal_same_machine : (fromOriginal G P).controlled.reduction.machine =
    (Programme.compose P.fromOriginal.controlled (fromCurrent G P)).reduction.machine := rfl

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentPurePinsCore
end
