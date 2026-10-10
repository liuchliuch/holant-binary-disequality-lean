import Holant.Proofs.Closure.RetainedFactorCatalogue
import Holant.Proofs.Closure.ProgrammePowerTransport
import Holant.Proofs.Algorithms.RawArityTransport
import Holant.Proofs.Algorithms.ControlledReduction

/-! NEW UNVERIFIED source-backed adapters for old-tree-preserving saturation.
The actual q tree's macros build the finite dense prefix chain, in the same
original coefficient presentation. No extraction backend is caller input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.RetainedFactorCatalogue
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
variable (P : Palette G) (q : AnySignature (OI.K G)) (nonzero : q.2 ≠ 0)

def T (n : ℕ) : Signature (OI.K G) (arity G P q nonzero n) := (lookup G P q nonzero n).2
abbrev «prefix» (n : ℕ) := FactorSaturation.PrefixMachine.family (s:=P.count) (T G P q nonzero) n
abbrev original := «prefix» G P q nonzero 0

theorem arity_agrees (i : Fin P.count) : arity G P q nonzero i.val = P.arity i.val :=
  congrArg Sigma.fst (lookup_old G P q nonzero i)

def oldQuery := RawArityTransport.input (b:=1) (arity_agrees G P q nonzero)
def oldQueryComputes := RawArityTransport.computes (b:=1) (arity_agrees G P q nonzero)

@[simp] theorem oldQuery_raw (r : ExactSignatureTables.Input P.count 1 (arity G P q nonzero)) :
    (oldQuery G P q nonzero r).val = r.val := rfl

theorem oldQuery_value (r : ExactSignatureTables.Input P.count 1 (arity G P q nonzero)) :
    OriginalLCodec.value (original G P q nonzero) r = OriginalLCodec.value P.table (oldQuery G P q nonzero r) := by
  have ht : RawArityTransport.signatures (arity_agrees G P q nonzero) (original G P q nonzero) = P.table := by
    funext i x
    exact Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply _ _
      (lookup_old G P q nonzero i) (arity_agrees G P q nonzero i) x
  change ((FieldReduction.targetTables (OI.presentation G) (original G P q nonzero)).evaluate (OI.presentation G) r) =
    ((FieldReduction.targetTables (OI.presentation G) P.table).evaluate (OI.presentation G) (oldQuery G P q nonzero r))
  rw [FieldReduction.target_evaluate,FieldReduction.target_evaluate,←ht]
  exact (RawArityTransport.denote (arity_agrees G P q nonzero) (original G P q nonzero)
    (fun _ => Signature.disequality) r).symm

def toOld : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding P.count 1 (arity G P q nonzero)) (OI.presentation G).encoding
    (RawClosedNetwork.validatedEncoding P.count 1 P.arity) (OI.presentation G).encoding
    (OriginalLCodec.value (original G P q nonzero)) (OriginalLCodec.value P.table) :=
  controlledOneQueryOfEq (oldQueryComputes G P q nonzero)
    (identityComputes (OI.presentation G).encoding)
    ((OriginalLCodec.tables P.table).outputBound (OI.presentation G)) _ (oldQuery_value G P q nonzero)

/-- The raw record is unchanged when its finite label range is enlarged. -/
def includeOld (r : ExactSignatureTables.Input P.count 1 P.arity) :
    ExactSignatureTables.Input (count G P q nonzero) 1 (arity G P q nonzero) := by
  refine ⟨r.val,?_,r.property.2⟩
  intro v
  have hv := r.property.1 v
  refine ⟨by unfold count; omega,?_⟩
  exact hv.2.trans (arity_agrees G P q nonzero ⟨_,hv.1⟩).symm

@[simp] theorem includeOld_raw (r : ExactSignatureTables.Input P.count 1 P.arity) :
    (includeOld G P q nonzero r).val = r.val := rfl

def includeOldComputes : Computes
    (RawClosedNetwork.validatedEncoding P.count 1 P.arity)
    (RawClosedNetwork.validatedEncoding (count G P q nonzero) 1 (arity G P q nonzero))
    (includeOld G P q nonzero) :=
  recode (identityComputes (RawClosedNetwork.validatedEncoding P.count 1 P.arity)) id
    (fun _ => rfl) (fun _ => rfl)

theorem includeOld_value (r : ExactSignatureTables.Input P.count 1 P.arity) :
    OriginalLCodec.value P.table r = OriginalLCodec.value (table G P q nonzero) (includeOld G P q nonzero r) := by
  change ((FieldReduction.targetTables (OI.presentation G) P.table).evaluate (OI.presentation G) r) =
    ((FieldReduction.targetTables (OI.presentation G) (table G P q nonzero)).evaluate (OI.presentation G) _)
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
      table G P q nonzero ⟨(r.val.vertices.get v).1,by unfold count; omega⟩
        (fun j => z (r.val.route (includeOld G P q nonzero r).property ⟨v,j⟩))
    have hs := Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
      (table G P q nonzero ⟨(r.val.vertices.get v).1,by unfold count; omega⟩)
      (P.table ⟨(r.val.vertices.get v).1,hi⟩)
      (lookup_old G P q nonzero ⟨_,hi⟩) (arity_agrees G P q nonzero ⟨_,hi⟩)
      (fun j => z (r.val.route r.property ⟨v,j⟩))
    simpa only [includeOld,RawClosedNetwork.route,RawClosedNetwork.portEndpoint,Fin.cast_cast] using hs.symm
  · rfl

def fromOld : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding P.count 1 P.arity) (OI.presentation G).encoding
    (RawClosedNetwork.validatedEncoding (count G P q nonzero) 1 (arity G P q nonzero)) (OI.presentation G).encoding
    (OriginalLCodec.value P.table) (OriginalLCodec.value (table G P q nonzero)) :=
  controlledOneQueryOfEq (includeOldComputes G P q nonzero)
    (identityComputes (OI.presentation G).encoding)
    ((OriginalLCodec.tables (table G P q nonzero)).outputBound (OI.presentation G)) _ (includeOld_value G P q nonzero)

/-- Source labels of the same saved macro are transported using literal table
identity. No extra vertex, scalar normalization or oracle is introduced. -/
def relabelPower {n : ℕ} {f : Signature (OI.K G) n}
    (M : GeneralPowerExposure.PowerMacro P.table f) :
    GeneralPowerExposure.PowerMacro (original G P q nonzero) f :=
  ProgrammePowerTransport.relabel P.table (original G P q nonzero) (fun i => i)
    (lookup_old G P q nonzero) M

def densePower (actual : Gadget.Realizes P.family .disequality q.2)
    (j : Fin (addedCount G q nonzero)) :
    GeneralPowerExposure.PowerMacro (original G P q nonzero) (T G P q nonzero (P.count+j.val)) := by
  change GeneralPowerExposure.PowerMacro (original G P q nonzero) (lookup G P q nonzero (P.count+j.val)).2
  rw [lookup_new]
  exact relabelPower G P q nonzero (newPower G P q nonzero actual j)

def macroChain (actual : Gadget.Realizes P.family .disequality q.2) :
    RecursiveMachine.Chain (original G P q nonzero) (table G P q nonzero) :=
  FactorSaturation.PrefixMachine.chain (T G P q nonzero) (densePower G P q nonzero actual)
    (addedCount G q nonzero) le_rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.RetainedFactorCatalogue
