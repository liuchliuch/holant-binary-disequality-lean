import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPinValue
import Holant.Proofs.Algorithms.TraceQueryControl
import Holant.Complexity.FixedFieldMachines.Concrete

/-! Actual finite byte programmes for universal CSP reference pinning.
The complement-invariant branch and the distinguishing original row are fixed
family choices, not an unproved run-time recognizer or an oracle resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPinProgramme
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GeneralEOPairedCSPFamilyRaw UniversalPairReduction.SmoothingCompiler
open scoped BigOperators
namespace R
export GeneralEOPairedFamilyExtractionPinRaw
  (free merge augment freeComputes mergeComputes augmentComputes free_merge_wellFormed free_augment_wellFormed fixed)
end R
namespace V
export GeneralEOPairedFamilyExtractionPinValue (flip SelfDual recover_selfdual recover_distinguished)
end V
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
attribute [local instance] Classical.propDecidable

variable {s : ℕ} {arity : ℕ → ℕ} (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ} (F : FixedField K d)
variable (g : (i : Fin s) → Signature K (P i).count)

/-- This property is decided once for a fixed family; no synthesis is claimed. -/
def witness (h : ¬V.SelfDual P g) : Σi : Fin s, Fin (P i).count → Bool :=
  ⟨Classical.choose (not_forall.mp h),
    Classical.choose (not_forall.mp (Classical.choose_spec (not_forall.mp h)))⟩

omit [Field K] [Algebra ℚ K] in
theorem witness_unequal (h : ¬V.SelfDual P g) :
    g (witness P g h).1 (witness P g h).2 ≠
      g (witness P g h).1 (V.flip (witness P g h).2) :=
  Ne.symm (Classical.choose_spec (not_forall.mp (Classical.choose_spec (not_forall.mp h))))

def two (r : Raw s) : List (Raw s) := [R.free r,R.merge r]
def four (i : Fin s) (x : Fin (P i).count → Bool) (r : Raw s) : List (Raw s) :=
  [R.free (R.augment P i x r),R.merge (R.augment P i x r),R.free r,R.merge r]

def twoComputes : Computes (encoding s) (framedListEncoding (encoding s)) (two (s:=s)) := by
  let f : Raw s → Fin 2 → Raw s := fun r => ![R.free r,R.merge r]
  have each (i : Fin 2) : Computes (encoding s) (encoding s) (fun r => f r i) := by
    refine Fin.cases R.freeComputes (fun j => ?_) i
    exact Fin.cases R.mergeComputes (fun k => Fin.elim0 k) j
  exact FixedGadgetSubstitution.Compiler.fixedListComputes (encoding s) (encoding s) f each [0,1]

def fourComputes (i : Fin s) (x : Fin (P i).count → Bool) :
    Computes (encoding s) (framedListEncoding (encoding s)) (four P i x) := by
  let f : Raw s → Fin 4 → Raw s := fun r =>
    ![R.free (R.augment P i x r),R.merge (R.augment P i x r),R.free r,R.merge r]
  have each (j : Fin 4) : Computes (encoding s) (encoding s) (fun r => f r j) := by
    refine Fin.cases ((R.augmentComputes P i x).andThen R.freeComputes) (fun j => ?_) j
    refine Fin.cases ((R.augmentComputes P i x).andThen R.mergeComputes) (fun j => ?_) j
    refine Fin.cases R.freeComputes (fun j => ?_) j
    exact Fin.cases R.mergeComputes (fun k => Fin.elim0 k) j
  exact FixedGadgetSubstitution.Compiler.fixedListComputes (encoding s) (encoding s) f each [0,1,2,3]

def validQueries (r : Raw s) : List (Raw s) :=
  if hs : V.SelfDual P g then two r else four P (witness P g hs).1 (witness P g hs).2 r

def validQueriesComputes :
    Computes (encoding s) (framedListEncoding (encoding s)) (validQueries P g) := by
  classical
  by_cases hs : V.SelfDual P g
  · exact congrComputes (twoComputes (s:=s)) (fun r => by simp [validQueries,hs])
  · exact congrComputes (fourComputes P (witness P g hs).1 (witness P g hs).2)
      (fun r => by simp [validQueries,hs])

def queries (r : Raw s) : List (Raw s) :=
  if (R.free r).WellFormed P then validQueries P g r else []

def queriesComputes : Computes (encoding s) (framedListEncoding (encoding s)) (queries P g) :=
  congrComputes (ifComputes
    (R.freeComputes.andThen (GeneralEOPairedCSPFamilyValidation.validates P))
    (validQueriesComputes P g) (constantComputes (encoding s) (framedListEncoding (encoding s)) []))
    (fun r => by simp [queries])

def pre : Computes (encoding s)
    (OracleBatch.contextEncoding (encoding s) encodingBoolBool) (fun r => (queries P g r,false)) :=
  pairComputes (queriesComputes P g) (constantComputes (encoding s) encodingBoolBool false)

abbrev answerEncoding := OracleBatch.contextEncoding F.encoding encodingBoolBool

def answer (i : ℕ) : Computes (answerEncoding F) F.encoding (fun x : List K × Bool => x.1.getD i 0) :=
  (Wiring.firstComputes (framedListEncoding F.encoding) encodingBoolBool).andThen
    (FixedGadgetSubstitution.Compiler.getDComputes F.encoding i 0)

def scale {f : List K × Bool → K} (c : K) (a : Computes (answerEncoding F) F.encoding f) :
    Computes (answerEncoding F) F.encoding (fun x => c*f x) :=
  (pairComputes (constantComputes (answerEncoding F) F.encoding c) a).andThen
    (Concrete.fieldMultiplication F)

def add {f h : List K × Bool → K} (a : Computes (answerEncoding F) F.encoding f)
    (b : Computes (answerEncoding F) F.encoding h) :
    Computes (answerEncoding F) F.encoding (fun x => f x+h x) :=
  (pairComputes a b).andThen (Concrete.fieldAddition F)

def sub {f h : List K × Bool → K} (a : Computes (answerEncoding F) F.encoding f)
    (b : Computes (answerEncoding F) F.encoding h) :
    Computes (answerEncoding F) F.encoding (fun x => f x-h x) :=
  congrComputes (add F a (scale F (-1) b)) (fun _ => by ring)

def postValue (x : List K × Bool) : K :=
  if hs : V.SelfDual P g then (x.1.getD 0 0-x.1.getD 1 0)/2 else
    let w := witness P g hs
    let a := g w.1 w.2
    let b := g w.1 (V.flip w.2)
    ((x.1.getD 0 0-x.1.getD 1 0)-b*(x.1.getD 2 0-x.1.getD 3 0))/(a-b)

def post : Computes (answerEncoding F) F.encoding (postValue P g) := by
  classical
  by_cases hs : V.SelfDual P g
  · exact congrComputes (scale F ((2:K)⁻¹) (sub F (answer F 0) (answer F 1)))
      (fun x => by simp only [postValue, dite_eq_left hs]; ring)
  · let w := witness P g hs
    let a := g w.1 w.2
    let b := g w.1 (V.flip w.2)
    exact congrComputes (scale F (a-b)⁻¹
      (sub F (sub F (answer F 0) (answer F 1))
        (scale F b (sub F (answer F 2) (answer F 3)))))
      (fun x => by simp only [postValue, dite_eq_right hs]; change _ = _ / (a-b); ring)

omit [Algebra ℚ K] in
@[simp] theorem post_empty : postValue P g ([],false)=0 := by
  classical
  unfold postValue
  split <;> simp

omit [Field K] [Algebra ℚ K] in
theorem query_count (r : Raw s) : (queries P g r).length≤4 := by
  classical
  by_cases hr : (R.free r).WellFormed P <;> by_cases hs : V.SelfDual P g <;>
    simp [queries,validQueries,hr,hs,two,four]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPinProgramme
