import Holant.Proofs.Hardness.GeneralEOSignedParityProgram
import Holant.Proofs.Hardness.GeneralEOPairedCSPFamilyUnused
import Holant.Proofs.Hardness.GeneralEOSignedParityAssignments
import Holant.Complexity.FixedFieldMachines.ScalarPower.Correction

/-! The parity compiler counts every unused declaration by a physical range
scan. Its same-field answer adapter removes precisely their power of two. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedParityUnused
open Computability Holant Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
open scoped BigOperators
namespace P
export GeneralEOSignedParityProgram (Input inputEncoding unary scopes scopesComputes sizeComputes goodComputes)
end P
namespace S
export GeneralEOSignedParityComponents (scope Good Consistent reconstruct assignment_sum inconsistent_sum_zero)
end S
namespace R
export GeneralEOPairedCSPFamilyRaw (Raw encoding fieldsEncoding labelsEncoding addressesEncoding)
end R
namespace U
export GeneralEOPairedCSPFamilyUnused (unused unusedComputes)
end U
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

def record (x : P.Input) : R.Raw 0 := ⟨x.1*2,[],P.scopes x⟩

def recordComputes : Computes P.inputEncoding (R.encoding 0) record := by
  let addresses := P.scopesComputes.andThen
    (Holant.LocalDrafts.Tractability.AffineMachine.WireLists.mapComputes
      P.unary encodingNatBool id UnaryBinary.computes)
  exact recode (pairComputes P.sizeComputes
    (pairComputes (constantComputes P.inputEncoding (R.labelsEncoding 0) []) addresses))
    id (fun _ => rfl) (fun x => by simp only [Function.comp_def,id_eq,List.map_id]; rfl)

def unused (x : P.Input) : ℕ := U.unused (record x)
def unusedComputes : Computes P.inputEncoding P.unary unused := recordComputes.andThen U.unusedComputes

theorem scopes_eq (x : P.Input) : P.scopes x = GeneralEOPairedCSPScan.NatScan.addresses (S.scope x.2) := by
  apply List.ext_getElem <;> simp [GeneralEOSignedParityProgram.scopes,
    GeneralEOPairedCSPScan.NatScan.addresses]

theorem unused_eq (x : P.Input) : unused x = GeneralCSPUnused.unusedCount (S.scope x.2) := by
  rw [GeneralEOPairedCSPScan.NatScan.unusedCount_filter]
  unfold unused GeneralEOPairedCSPFamilyUnused.unused record
  rw [scopes_eq]
  unfold GeneralEOPairedCSPScan.NatScan.unused GeneralCSPUnusedNat.unused
  congr 1
  apply List.filter_congr
  intro v _
  simp

abbrev contextEncoding := pairEncoding encodingBoolBool P.unary
local instance goodDecidable (x : P.Input) : Decidable (S.Good x.2) := by
  unfold GeneralEOSignedParityComponents.Good
  infer_instance

def context (x : P.Input) : Bool × ℕ := (decide (S.Good x.2),unused x)
def contextComputes : Computes P.inputEncoding contextEncoding context :=
  pairComputes P.goodComputes unusedComputes

variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {d : ℕ}

def normalize (p : K × (Bool × ℕ)) : K := if p.2.1 then p.1*(1/2)^p.2.2 else 0

def normalizeComputes (F : FixedField K d) :
    Computes (pairEncoding F.encoding contextEncoding) F.encoding normalize := by
  let ctx := Wiring.secondComputes F.encoding contextEncoding
  let good := ctx.andThen (Wiring.firstComputes encodingBoolBool P.unary)
  let exponent := ctx.andThen (Wiring.secondComputes encodingBoolBool P.unary)
  let answer := Wiring.firstComputes F.encoding contextEncoding
  let multiply : Computes (pairEncoding F.encoding P.unary) F.encoding
      (fun p : K × ℕ => p.1*(1/2)^p.2) :=
    congrComputes (ScalarPower.multiplyPower F (F.decode.symm (1/2 : K))) (fun _ => by simp)
  exact ifComputes good ((pairComputes answer exponent).andThen multiply)
    (constantComputes (pairEncoding F.encoding contextEncoding) F.encoding 0)

local instance consistentDecidable (x : P.Input) (a : Fin x.1 → Bool) :
    Decidable (S.Consistent x.2 a) := Classical.propDecidable _

theorem normalize_eq (x : P.Input) (w : (Fin x.1 → Bool) → K) :
    normalize ((∑ y : Fin (x.1*2) → Bool, w (S.reconstruct x.2 y)),context x) =
      ∑ a : Fin x.1 → Bool, if S.Consistent x.2 a then w a else 0 := by
  classical
  by_cases hg : S.Good x.2
  · simp only [normalize,context,decide_eq_true hg,ite_true]
    rw [S.assignment_sum x.2 hg,unused_eq]
    have hp : (2:K)^GeneralCSPUnused.unusedCount (S.scope x.2) *
        (1/2:K)^GeneralCSPUnused.unusedCount (S.scope x.2) = 1 := by
      rw [←mul_pow]
      norm_num
    calc
      _ = ((2:K)^GeneralCSPUnused.unusedCount (S.scope x.2) *
          (1/2:K)^GeneralCSPUnused.unusedCount (S.scope x.2)) *
          (∑ a : Fin x.1 → Bool, if S.Consistent x.2 a then w a else 0) := by ring
      _ = _ := by rw [hp,one_mul]
  · simp only [normalize,context,decide_eq_false hg,Bool.false_eq_true,ite_false]
    exact (S.inconsistent_sum_zero x.2 hg w).symm

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedParityUnused
