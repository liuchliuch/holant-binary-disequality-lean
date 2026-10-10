import Holant.Proofs.Closure.RetainedAdapters

/-! Reconstructed one-label charged branch boundary. Source labels are the
literal old palette followed by the actual branch q. UNVERIFIED recovery. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.RetainedBranch
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open Holant.Complexity.BinaryCompose Holant.Complexity.FixedFieldMachines
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (q : AnySignature (OI.K G))

def lookup (n : ℕ) : AnySignature (OI.K G) := if h : n < P.count then ⟨P.arity n,P.table ⟨n,h⟩⟩ else q
def arity (n : ℕ) := (lookup G P q n).1
def original (i : Fin P.count) : Signature (OI.K G) (arity G P q i.val) := (lookup G P q i.val).2
@[simp] theorem lookup_old (i : Fin P.count) : lookup G P q i.val =
    (⟨P.arity i.val,P.table i⟩ : AnySignature (OI.K G)) := by simp only [lookup,dif_pos i.isLt]
@[simp] theorem lookup_new : lookup G P q P.count = q := by simp [lookup]
theorem arity_agrees (i : Fin P.count) : arity G P q i.val = P.arity i.val := congrArg Sigma.fst (lookup_old G P q i)

def newTable : Signature (OI.K G) (arity G P q P.count) := (lookup G P q P.count).2
def extended := RetainedPairReduction.extended (original G P q) (newTable G P q)

@[simp] theorem extended_old (i : Fin P.count) :
    (⟨arity G P q i.val,extended G P q ⟨i.val,by omega⟩⟩ : AnySignature (OI.K G)) =
      ⟨P.arity i.val,P.table i⟩ := by
  unfold extended RetainedPairReduction.extended
  rw [GeneralOriginalQuery.source_old]
  exact lookup_old G P q i
@[simp] theorem extended_new :
    (⟨arity G P q P.count,extended G P q ⟨P.count,by omega⟩⟩ : AnySignature (OI.K G)) = q := by
  unfold extended RetainedPairReduction.extended
  rw [GeneralOriginalQuery.source_new]
  exact lookup_new G P q

def oldQuery := RawArityTransport.input (b:=1) (arity_agrees G P q)
def oldQueryComputes := RawArityTransport.computes (b:=1) (arity_agrees G P q)

theorem oldQuery_value (r : ExactSignatureTables.Input P.count 1 (arity G P q)) :
    OriginalLCodec.value (original G P q) r = OriginalLCodec.value P.table (oldQuery G P q r) := by
  have ht : RawArityTransport.signatures (arity_agrees G P q) (original G P q) = P.table := by
    funext i x
    exact Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply _ _
      (lookup_old G P q i) (arity_agrees G P q i) x
  change ((FieldReduction.targetTables (OI.presentation G) (original G P q)).evaluate (OI.presentation G) r) =
    ((FieldReduction.targetTables (OI.presentation G) P.table).evaluate (OI.presentation G) (oldQuery G P q r))
  rw [FieldReduction.target_evaluate,FieldReduction.target_evaluate,←ht]
  exact (RawArityTransport.denote (arity_agrees G P q) (original G P q)
    (fun _ => Signature.disequality) r).symm

def oldToP : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding P.count 1 (arity G P q)) (OI.presentation G).encoding
    (RawClosedNetwork.validatedEncoding P.count 1 P.arity) (OI.presentation G).encoding
    (OriginalLCodec.value (original G P q)) (OriginalLCodec.value P.table) :=
  controlledOneQueryOfEq (oldQueryComputes G P q) (identityComputes (OI.presentation G).encoding)
    ((OriginalLCodec.tables P.table).outputBound (OI.presentation G)) _ (oldQuery_value G P q)

def includeOld (r : ExactSignatureTables.Input P.count 1 P.arity) :
    ExactSignatureTables.Input (P.count+1) 1 (arity G P q) := by
  refine ⟨r.val,?_,r.property.2⟩
  intro v
  have hv := r.property.1 v
  exact ⟨by omega,hv.2.trans (arity_agrees G P q ⟨_,hv.1⟩).symm⟩

def includeOldComputes : Computes
    (RawClosedNetwork.validatedEncoding P.count 1 P.arity)
    (RawClosedNetwork.validatedEncoding (P.count+1) 1 (arity G P q)) (includeOld G P q) :=
  recode (identityComputes (RawClosedNetwork.validatedEncoding P.count 1 P.arity)) id
    (fun _ => rfl) (fun _ => rfl)

theorem includeOld_value (r : ExactSignatureTables.Input P.count 1 P.arity) :
    OriginalLCodec.value P.table r = OriginalLCodec.value (extended G P q) (includeOld G P q r) := by
  change ((FieldReduction.targetTables (OI.presentation G) P.table).evaluate (OI.presentation G) r) =
    ((FieldReduction.targetTables (OI.presentation G) (extended G P q)).evaluate (OI.presentation G) _)
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
      extended G P q ⟨(r.val.vertices.get v).1,by omega⟩
        (fun j => z (r.val.route (includeOld G P q r).property ⟨v,j⟩))
    have hs := Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
      (extended G P q ⟨(r.val.vertices.get v).1,by omega⟩)
      (P.table ⟨(r.val.vertices.get v).1,hi⟩) (extended_old G P q ⟨_,hi⟩)
      (arity_agrees G P q ⟨_,hi⟩) (fun j => z (r.val.route r.property ⟨v,j⟩))
    simpa only [includeOld,RawClosedNetwork.route,RawClosedNetwork.portEndpoint,Fin.cast_cast] using hs.symm
  · rfl

def fromP : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding P.count 1 P.arity) (OI.presentation G).encoding
    (RawClosedNetwork.validatedEncoding (P.count+1) 1 (arity G P q)) (OI.presentation G).encoding
    (OriginalLCodec.value P.table) (OriginalLCodec.value (extended G P q)) :=
  controlledOneQueryOfEq (includeOldComputes G P q) (identityComputes (OI.presentation G).encoding)
    ((OriginalLCodec.tables (extended G P q)).outputBound (OI.presentation G)) _ (includeOld_value G P q)

def relabelPower (M : GeneralPowerExposure.PowerMacro P.table q.2) :
    GeneralPowerExposure.PowerMacro (original G P q) (newTable G P q) := by
  have R := ProgrammePowerTransport.relabel P.table (original G P q) (fun i => i) (lookup_old G P q) M
  change GeneralPowerExposure.PowerMacro (original G P q) (lookup G P q P.count).2
  rw [lookup_new]
  exact R

def controlledStep (M : GeneralPowerExposure.PowerMacro P.table q.2) :
    LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding (P.count+1) 1 (arity G P q)) (OI.presentation G).encoding
      (RawClosedNetwork.validatedEncoding P.count 1 (arity G P q)) (OI.presentation G).encoding
      (OriginalLCodec.value (extended G P q)) (OriginalLCodec.value (original G P q)) :=
  RecursiveMachine.step (OI.presentation G) (newTable G P q) (relabelPower G P q M)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.RetainedBranch
