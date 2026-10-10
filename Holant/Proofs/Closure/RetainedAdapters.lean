import Holant.Proofs.Closure.RetainedCatalogue
import Holant.Proofs.Closure.ProgrammePowerTransport
import Holant.Proofs.Algorithms.RawArityTransport
import Holant.Proofs.Algorithms.ControlledReduction

/-! Reconstructed actual byte-preserving prefix adapters and macro chain.
The coefficient presentation remains the original one. UNVERIFIED recovery. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.RetainedCatalogue
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
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))

def T (n : ℕ) : Signature (OI.K G) (arity G P torsion f n) := (lookup G P torsion f n).2
abbrev «prefix» (n : ℕ) := FactorSaturation.PrefixMachine.family (s:=P.count) (T G P torsion f) n
abbrev original := «prefix» G P torsion f 0

theorem arity_agrees (i : Fin P.count) : arity G P torsion f i.val = P.arity i.val :=
  congrArg Sigma.fst (lookup_old G P torsion f i)

def oldQuery := RawArityTransport.input (b:=1) (arity_agrees G P torsion f)
def oldQueryComputes := RawArityTransport.computes (b:=1) (arity_agrees G P torsion f)

theorem oldQuery_value (r : ExactSignatureTables.Input P.count 1 (arity G P torsion f)) :
    OriginalLCodec.value (original G P torsion f) r = OriginalLCodec.value P.table (oldQuery G P torsion f r) := by
  have ht : RawArityTransport.signatures (arity_agrees G P torsion f) (original G P torsion f) = P.table := by
    funext i x
    exact Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply _ _
      (lookup_old G P torsion f i) (arity_agrees G P torsion f i) x
  change ((FieldReduction.targetTables (OI.presentation G) (original G P torsion f)).evaluate (OI.presentation G) r) =
    ((FieldReduction.targetTables (OI.presentation G) P.table).evaluate (OI.presentation G) (oldQuery G P torsion f r))
  rw [FieldReduction.target_evaluate,FieldReduction.target_evaluate,←ht]
  exact (RawArityTransport.denote (arity_agrees G P torsion f) (original G P torsion f)
    (fun _ => Signature.disequality) r).symm

def toOld : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding P.count 1 (arity G P torsion f)) (OI.presentation G).encoding
    (RawClosedNetwork.validatedEncoding P.count 1 P.arity) (OI.presentation G).encoding
    (OriginalLCodec.value (original G P torsion f)) (OriginalLCodec.value P.table) :=
  controlledOneQueryOfEq (oldQueryComputes G P torsion f)
    (identityComputes (OI.presentation G).encoding)
    ((OriginalLCodec.tables P.table).outputBound (OI.presentation G)) _ (oldQuery_value G P torsion f)

/-- The raw record is unchanged when its finite label range is enlarged. -/
def includeOld (r : ExactSignatureTables.Input P.count 1 P.arity) :
    ExactSignatureTables.Input (count G P torsion f) 1 (arity G P torsion f) := by
  refine ⟨r.val,?_,r.property.2⟩
  intro v
  have hv := r.property.1 v
  refine ⟨by unfold count; omega,?_⟩
  exact hv.2.trans (arity_agrees G P torsion f ⟨_,hv.1⟩).symm

def includeOldComputes : Computes
    (RawClosedNetwork.validatedEncoding P.count 1 P.arity)
    (RawClosedNetwork.validatedEncoding (count G P torsion f) 1 (arity G P torsion f))
    (includeOld G P torsion f) :=
  recode (identityComputes (RawClosedNetwork.validatedEncoding P.count 1 P.arity)) id
    (fun _ => rfl) (fun _ => rfl)

theorem includeOld_value (r : ExactSignatureTables.Input P.count 1 P.arity) :
    OriginalLCodec.value P.table r = OriginalLCodec.value (table G P torsion f) (includeOld G P torsion f r) := by
  change ((FieldReduction.targetTables (OI.presentation G) P.table).evaluate (OI.presentation G) r) =
    ((FieldReduction.targetTables (OI.presentation G) (table G P torsion f)).evaluate (OI.presentation G) _)
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
      table G P torsion f ⟨(r.val.vertices.get v).1,by unfold count; omega⟩
        (fun j => z (r.val.route (includeOld G P torsion f r).property ⟨v,j⟩))
    have hs := Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
      (table G P torsion f ⟨(r.val.vertices.get v).1,by unfold count; omega⟩)
      (P.table ⟨(r.val.vertices.get v).1,hi⟩)
      (lookup_old G P torsion f ⟨_,hi⟩) (arity_agrees G P torsion f ⟨_,hi⟩)
      (fun j => z (r.val.route r.property ⟨v,j⟩))
    simpa only [includeOld,RawClosedNetwork.route,RawClosedNetwork.portEndpoint,Fin.cast_cast] using hs.symm
  · rfl

def fromOld : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding P.count 1 P.arity) (OI.presentation G).encoding
    (RawClosedNetwork.validatedEncoding (count G P torsion f) 1 (arity G P torsion f)) (OI.presentation G).encoding
    (OriginalLCodec.value P.table) (OriginalLCodec.value (table G P torsion f)) :=
  controlledOneQueryOfEq (includeOldComputes G P torsion f)
    (identityComputes (OI.presentation G).encoding)
    ((OriginalLCodec.tables (table G P torsion f)).outputBound (OI.presentation G)) _ (includeOld_value G P torsion f)

/-- Source labels of the same saved macro are transported using literal table
identity. No extra vertex, scalar normalization or oracle is introduced. -/
def relabelPower {n : ℕ} {q : Signature (OI.K G) n}
    (M : GeneralPowerExposure.PowerMacro P.table q) :
    GeneralPowerExposure.PowerMacro (original G P torsion f) q :=
  ProgrammePowerTransport.relabel P.table (original G P torsion f) (fun i => i)
    (lookup_old G P torsion f) M

def densePower (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)
    (j : Fin (addedCount G P torsion f)) :
    GeneralPowerExposure.PowerMacro (original G P torsion f) (T G P torsion f (P.count+j.val)) := by
  change GeneralPowerExposure.PowerMacro (original G P torsion f) (lookup G P torsion f (P.count+j.val)).2
  rw [lookup_new]
  exact relabelPower G P torsion f (newPower G P torsion f core hcore j)

def macroChain (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩) :
    RecursiveMachine.Chain (original G P torsion f) (table G P torsion f) :=
  FactorSaturation.PrefixMachine.chain (T G P torsion f) (densePower G P torsion f core hcore)
    (addedCount G P torsion f) le_rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.RetainedCatalogue
