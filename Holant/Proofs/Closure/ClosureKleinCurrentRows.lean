import Holant.Proofs.Closure.ClosureSourceRowsKleinNative
import Holant.Proofs.Closure.ProgrammePowerTransport
import Holant.Proofs.Closure.OccurrenceBatch

/-! All-arity native Klein source rows. Kind and actual original-field keys
come from the SAME internally selected noncyclic order-four current group.
Canonical matrices are represented by charged source macros; their source
units are explicit and they are not declared uncharged retained resources. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureKleinCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
namespace K
export Holant.Certificates.EqualityQuaternary.Klein
  (Kind E dual theta closingSign closingSign_ne_zero closing)
end K
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))

abbrev kind := ClosureSourceRows.nativeKleinKind G P torsion cardinal noncyclic
abbrev coverage := ClosureSourceRows.nativeKleinResources G P torsion cardinal noncyclic
abbrev index (k : Fin 4) := ClosureSourceRows.kleinIndex G P torsion
  (kind G P torsion cardinal noncyclic) (coverage G P torsion cardinal noncyclic) k

/-- Every safe ORIGINAL factor has a literal canonical row with an ORIGINAL
nonzero coefficient, recovered from actual source tables. -/
theorem safe_factor_row (B : Binary (K:=OI.K G)) (safe : SafeBinary (actualTransfers P.family) B) :
    ∃ k : Fin 4,∃ c : OI.K G,c≠0 ∧
      B.map (ClosureSourceRows.embedding G)=scale (ClosureSourceRows.embedding G c)
        (K.E (kind G P torsion cardinal noncyclic) k) := by
  obtain ⟨C,actual,c,hc,equation⟩ := safe
  have table : B=c • C := by
    have h := congrArg (fun T : Binary (K:=OI.K G) => T*X) equation
    simpa only [transfer,Matrix.smul_mul,Matrix.mul_assoc,X_mul_X,Matrix.mul_one] using h
  let R := ClosureSourceRows.kleinLineSource G P torsion
    (kind G P torsion cardinal noncyclic) (coverage G P torsion cardinal noncyclic) C actual
  let J := index G P torsion cardinal noncyclic R.index
  refine ⟨R.index,c*R.coefficient*J.coefficient,
    mul_ne_zero (mul_ne_zero hc R.nonzero) J.nonzero,?_⟩
  have original : B=(c*R.coefficient) • actualRepresentative P.family torsion J.key := by
    calc
      B=c • C := table
      _=c • (R.coefficient • actualRepresentative P.family torsion J.key) :=
        congrArg (c • ·) R.literal
      _=_ := smul_smul c R.coefficient _
  have mapped := congrArg (fun B : Binary (K:=OI.K G) => B.map (ClosureSourceRows.embedding G)) original
  rw [Matrix.map_smul' _ _ _ (ClosureSourceRows.embedding G).map_mul] at mapped
  change B.map (ClosureSourceRows.embedding G)=
    (ClosureSourceRows.embedding G (c*R.coefficient)) • ClosureSourceRows.representative G P torsion J.key at mapped
  rw [J.normal] at mapped
  calc
    B.map (ClosureSourceRows.embedding G)=
      (ClosureSourceRows.embedding G (c*R.coefficient)) •
        scale (ClosureSourceRows.embedding G J.coefficient)
          (K.E (kind G P torsion cardinal noncyclic) R.index) := mapped
    _=_ := by
      funext x y
      simp only [Pi.smul_apply,smul_eq_mul,scale,map_mul,mul_assoc]

def rowTable (k : Fin 4) : Signature (OI.K G) 2 :=
  (index G P torsion cardinal noncyclic k).coefficient⁻¹ •
    binarySignature (actualRepresentative P.family torsion (index G P torsion cardinal noncyclic k).key)

theorem rowTable_mapped (k : Fin 4) :
    RingHomRealization.mapSignature (ClosureSourceRows.embedding G)
      (rowTable G P torsion cardinal noncyclic k)=
        kernelSignature (K.E (kind G P torsion cardinal noncyclic) k) := by
  let J := index G P torsion cardinal noncyclic k
  funext x
  change ClosureSourceRows.embedding G (J.coefficient⁻¹ * actualRepresentative P.family torsion J.key (x 0) (x 1))=_
  rw [map_mul,map_inv₀]
  have normal := congrFun (congrFun J.normal (x 0)) (x 1)
  change ClosureSourceRows.embedding G (actualRepresentative P.family torsion J.key (x 0) (x 1))=
    ClosureSourceRows.embedding G J.coefficient * K.E (kind G P torsion cardinal noncyclic) k (x 0) (x 1) at normal
  rw [normal,←mul_assoc,inv_mul_cancel₀ ((map_ne_zero _).mpr J.nonzero),one_mul]
  rfl

def rowPower (k : Fin 4) :
    Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralPowerExposure.PowerMacro P.table
      (rowTable G P torsion cardinal noncyclic k) :=
  ProgrammePowerTransport.scaleTarget P.table
    (ClosureSourceRows.representativeAccess G P torsion (index G P torsion cardinal noncyclic k).key).power
    (index G P torsion cardinal noncyclic k).coefficient⁻¹
    (inv_ne_zero (index G P torsion cardinal noncyclic k).nonzero) rfl

/-- This normalized source row has its actual original-G access. Its same
representative graph is reused by scaleTarget; the unit is recorded explicitly. -/
def rowAccess (k : Fin 4) : CurrentSignatureAccess G P ⟨2,rowTable G P torsion cardinal noncyclic k⟩ :=
  let M := rowPower G P torsion cardinal noncyclic k
  ⟨M,RetainedBranch.toOriginal G P _ M,RetainedBranch.fromOriginal G P _,rfl,rfl⟩

@[simp] theorem rowAccess_same_controlled (k : Fin 4) :
    (rowAccess G P torsion cardinal noncyclic k).toOriginal.controlled=
      RetainedBranch.controlledToOriginal G P ⟨2,rowTable G P torsion cardinal noncyclic k⟩
        (rowPower G P torsion cardinal noncyclic k) := rfl

variable {m : ℕ} (f : Signature (OI.K G) (m+2))
variable (retained : (⟨m+2,f⟩ : AnySignature (OI.K G))∈P.family) (large : 2≤m)

def preparedPalette := OccurrenceBatch.palette G P torsion f retained large
def representativeLabel (k : Fin 4) : Fin (preparedPalette G P torsion f retained large).count :=
  RetainedCatalogue.deckLabel G P torsion f (.inl (index G P torsion cardinal noncyclic k).key)

/-- Exact unnormalized source representative occurrence in the actual
prepared palette. Canonical row normalization does not replace its saved tree. -/
theorem representative_saved (k : Fin 4) :
    ClosureSourceRows.savedOccurrence G (preparedPalette G P torsion f retained large)
      (representativeLabel G P torsion cardinal noncyclic f retained large k)=
        fullDeckRoot P.family torsion f (.inl (index G P torsion cardinal noncyclic k).key) :=
  RetainedCatalogue.deck_saved G P torsion f _

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureKleinCurrent
