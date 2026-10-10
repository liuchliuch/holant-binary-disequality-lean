import Holant.Proofs.Dichotomy.Closure.Mixed.GlobalCloseCompletionMixedRoot
import Holant.Proofs.Dichotomy.Retained.StableDenseGaugeAnchorContinuation
import Holant.Proofs.Dichotomy.Retained.StableDenseGaugeUnary

/-! Actual native-M continuation after simultaneous low-arity closure.
Any dense current q4 runs into a whole-current ordinary anchor source or the
actual saturated unary source. Otherwise one joint EO test either supplies
the original-G counting programme or fixes one A/P basis for all binary and
q4 leaves. The latter solves the whole saved forest unless a genuine higher
ancestor remains. No generic ancestor reconstruction is silently assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionNativeMContinuation
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open GlobalCloseCompletionMixedCurrent
namespace M
export GlobalCloseCompletionMixedEOSource (family common_basis source)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable {A : GeneratedGroupWorklist.Active G base}
variable (R : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion))

def classFamily : EOClass → SignatureFamily AlgebraicComplex
  | .affine => affineClass
  | .product => productClass

abbrev eoFamily := M.family G (palette G base R) (row G base R) (models G base R noPrior N)
abbrev CurrentTract := TractX (familyAction sourceKBasis
  (CurrentFrontierClosure.currentFamily G (palette G base R)))

def denseContinuation (hd : Dense G base R) :
    StableDenseGaugeAnchorContinuation.Outcome G (palette G base R) := by
  let o := hd.choose
  let four := hd.choose_spec.choose
  let p := hd.choose_spec.choose_spec.choose
  let full := hd.choose_spec.choose_spec.choose_spec
  exact StableDenseGaugeAnchorContinuation.fromCurrent G (palette G base R) R.final.ready.torsion N
    (GeneratedGroupQ4Consumers.table G base four) (GeneratedGroupQ4Consumers.minimum G base four)
    (GeneratedGroupQ4Consumers.minimum_literal G base four)
    (GeneratedGroupQ4Consumers.matching G base (R.preparationReceipt G base noPrior o) four) p full

inductive Completion : Type 1 where
  | hard (negative : ¬EOTract (preprocess (eoFamily G base R noPrior N)))
  | tract (criterion : CurrentTract G base R)
  | anchor (receipt : StableDenseGaugeAnchorContinuation.AnchorReceipt G (palette G base R))
  | unary (singular : StableDenseGaugeCurrent.SingularReceipt G (palette G base R))
      (receipt : StableDenseGaugeUnary.UnaryReceipt G (palette G base R) singular)
  | higher (C : EOClass)
      (basis : IsCommonKBasis (classFamily C) (GlobalCloseCompletionMixedCurrent.family G base R)
        InvertibleKernel.identity)
      (noDense : ¬Dense G base R)
      (occurrence : CurrentOccurrences.Id G (palette G base R))
      (higher : 4<(CurrentOccurrences.savedLeaf G (palette G base R) occurrence).1.1)

/-- Dense q4 is processed before any higher-arity residual is returned: its
anchor source already contains the entire current family in one basis. -/
def complete : Completion G base R noPrior N := Classical.choice (by
  classical
  by_cases dense : Dense G base R
  · cases denseContinuation G base R noPrior N dense with
    | anchor receipt => exact ⟨.anchor receipt⟩
    | singular r => exact ⟨.unary r (StableDenseGaugeUnary.unaryReceipt G (palette G base R) r)⟩
  by_cases tract : EOTract (preprocess (eoFamily G base R noPrior N))
  · have basis := M.common_basis G (palette G base R) (row G base R) (models G base R noPrior N) tract
    by_cases covered : ∀o : CurrentOccurrences.Id G (palette G base R),Covered G base R o
    · rcases basis with affine|product
      · exact ⟨.tract (whole_family_of_covered G base R .affine affine covered)⟩
      · exact ⟨.tract (whole_family_of_covered G base R .product product covered)⟩
    · obtain ⟨o,ho⟩ := not_forall.mp covered
      obtain ⟨higher,hh⟩ := (uncovered G base R o ho).resolve_right dense
      rcases basis with affine|product
      · exact ⟨.higher .affine affine dense higher hh⟩
      · exact ⟨.higher .product product dense higher hh⟩
  · exact ⟨.hard tract⟩)

variable {α : Type} {ea : Encoding α Bool} {count : α → ℕ}

/-- The rejected joint class test has the actual full controlled source,
including its original-field codec and every current-palette substitution. -/
def hardSource (negative : ¬EOTract (preprocess (eoFamily G base R noPrior N)))
    (w : SharpPWitness ea count) : LengthControlledOracleReduction
      ea encodingNatBool (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding count (OriginalForestSource.value G) :=
  M.source G (palette G base R) (row G base R) (models G base R noPrior N) negative w

def tractEvaluator (criterion : CurrentTract G base R) :=
  StablePaletteTractability.originalComputes G (palette G base R) criterion

def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : Type 1 :=
  match M with
  | .monomial selected => Completion G base R noPrior selected
  | _ => PUnit.{2}

def forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : ForMarking G base R noPrior M := by
  cases M with
  | monomial N => exact complete G base R noPrior N
  | smallTwo => exact PUnit.unit
  | smallFour => exact PUnit.unit
  | cyclic => exact PUnit.unit
  | bilinear => exact PUnit.unit
  | unshifted => exact PUnit.unit
  | shifted => exact PUnit.unit
  | platonic => exact PUnit.unit

def ForResult (result : GeneratedGroupWorklist.Result G base) : Type 1 :=
  match result with
  | .initialStop .. => PUnit.{2}
  | .prepared _ _ (.inl _) => PUnit.{2}
  | .prepared _ _ (.inr exhausted) =>
      ForMarking G base exhausted rfl (ClosureMarkedActualReceipts.produce G
        exhausted.final.source.palette exhausted.final.ready.torsion).physical.marking

def forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result :=
  match result with
  | .initialStop .. => PUnit.unit
  | .prepared _ _ (.inl _) => PUnit.unit
  | .prepared _ _ (.inr exhausted) => forMarking G base exhausted rfl _

def original_current_nativeM_continuation : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionNativeMContinuation
end
