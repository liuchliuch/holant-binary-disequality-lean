import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativePhaseBundleRaw
import Holant.Proofs.Tractability.AffineMachine.AccessPrograms
import Holant.Complexity.BinaryCompose.Arithmetic

/-! Concrete Boolean-stack byte programmes for the exact phase-bundle raw
substitution and its original cubic-copy count. Static phase lists compile
by fixed framed-list construction; runtime row streams use physical map and
flatten loops. Every scope lookup and address shift is performed on tape. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativePhaseBundleProgramme
open Holant Holant.Complexity Computability
open BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists
  (mapComputes flatten lengthComputes succComputes)
end W
namespace Access
export Holant.LocalDrafts.Tractability.AffineMachine.AccessPrograms (flatMap)
end Access
namespace R
export OrdinaryNegativePhaseBundleRaw
  (address phaseRows constantRows block guards raw copies)
end R
namespace S
export StableHigherCurrentOrdinarySquareProgramme (variablesComputes factorsComputes)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768

abbrev scopeEncoding := framedListEncoding encodingNatBool
abbrev factorsEncoding := framedListEncoding Raw.factorEncoding

def addTwoComputes : Computes encodingNatBool encodingNatBool (fun i => i+2) :=
  (pairComputes (identityComputes encodingNatBool)
    (constantComputes encodingNatBool encodingNatBool 2)).andThen FixedGadgetSubstitution.Compiler.addComputes

def unaryAddTwoComputes :
    Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding (fun i => i+2) :=
  W.succComputes.andThen W.succComputes

def labelComputes : Computes Raw.factorEncoding encodingNatBool Prod.fst :=
  recode (Wiring.firstComputes encodingNatBool scopeEncoding) id (fun _ => rfl) (fun _ => rfl)

def scopeComputes : Computes Raw.factorEncoding scopeEncoding Prod.snd :=
  recode (Wiring.secondComputes encodingNatBool scopeEncoding) id (fun _ => rfl) (fun _ => rfl)

def labelEqualsComputes (i : ℕ) :
    Computes Raw.factorEncoding encodingBoolBool (fun row => decide (row.1=i)) :=
  (pairComputes labelComputes (constantComputes Raw.factorEncoding encodingNatBool i)).andThen
    (equalComputes encodingNatBool)

/-- Compile-time constants and fixed lookups use the exact Raw default zero. -/
def addressComputes (p : Bool ⊕ Fin 3) :
    Computes scopeEncoding encodingNatBool (fun scope => R.address scope p) := by
  cases p with
  | inl b =>
      cases b
      · exact constantComputes scopeEncoding encodingNatBool 0
      · exact constantComputes scopeEncoding encodingNatBool 1
  | inr k => exact (getDComputes encodingNatBool k.val 0).andThen addTwoComputes

variable {n : ℕ}

def phaseScopeComputes (p : Fin n → Bool ⊕ Fin 3) :
    Computes scopeEncoding scopeEncoding (fun scope => List.ofFn (fun k => R.address scope (p k))) :=
  congrComputes (fixedListComputes scopeEncoding encodingNatBool
    (fun scope k => R.address scope (p k)) (fun k => addressComputes (p k)) (List.finRange n))
    (fun _ => List.ofFn_eq_map.symm)

def phaseRowComputes (j : ℕ) (p : Fin n → Bool ⊕ Fin 3) :
    Computes scopeEncoding Raw.factorEncoding
      (fun scope => (j,List.ofFn (fun k => R.address scope (p k)))) :=
  recode (pairComputes (constantComputes scopeEncoding encodingNatBool j) (phaseScopeComputes p))
    id (fun _ => rfl) (fun _ => rfl)

def phaseRowsComputes (j : ℕ) (ps : List (Fin n → Bool ⊕ Fin 3)) :
    Computes scopeEncoding factorsEncoding (R.phaseRows j ps) :=
  fixedListComputes scopeEncoding Raw.factorEncoding
    (fun scope (p : Fin n → Bool ⊕ Fin 3) => (j,List.ofFn (fun k : Fin n => R.address scope (p k))))
    (fun p => phaseRowComputes j p) ps

def shiftedScopeComputes : Computes Raw.factorEncoding scopeEncoding (fun row => row.2.map (·+2)) :=
  scopeComputes.andThen (W.mapComputes encodingNatBool encodingNatBool (fun i => i+2) addTwoComputes)

def nonphaseLabelComputes (e p₀ p₁ : ℕ) :
    Computes Raw.factorEncoding encodingNatBool
      (fun row => if row.1=1 then e else if row.1=2 then p₀ else p₁) :=
  congrComputes
    (ifComputes (labelEqualsComputes 1) (constantComputes Raw.factorEncoding encodingNatBool e)
      (ifComputes (labelEqualsComputes 2) (constantComputes Raw.factorEncoding encodingNatBool p₀)
        (constantComputes Raw.factorEncoding encodingNatBool p₁)))
    (fun row => by simp)

def nonphaseRowComputes (e p₀ p₁ : ℕ) :
    Computes Raw.factorEncoding Raw.factorEncoding
      (fun row => (if row.1=1 then e else if row.1=2 then p₀ else p₁,row.2.map (·+2))) :=
  recode (pairComputes (nonphaseLabelComputes e p₀ p₁) shiftedScopeComputes)
    id (fun _ => rfl) (fun _ => rfl)

def nonphaseRowsComputes (e p₀ p₁ : ℕ) :
    Computes Raw.factorEncoding factorsEncoding
      (fun row => let target := (if row.1=1 then e else if row.1=2 then p₀ else p₁,row.2.map (·+2))
        [target,target]) :=
  fixedListComputes Raw.factorEncoding Raw.factorEncoding
    (fun row (_ : Unit) =>
      (if row.1=1 then e else if row.1=2 then p₀ else p₁,row.2.map (·+2)))
    (fun _ => nonphaseRowComputes e p₀ p₁) [(),()]

/-- Runtime row selection tests its original label and emits the actual fixed
phase rows or the two shifted equality/pin rows. -/
def blockComputes (j e p₀ p₁ : ℕ) (ps : List (Fin n → Bool ⊕ Fin 3)) :
    Computes Raw.factorEncoding factorsEncoding (R.block j e p₀ p₁ ps) :=
  congrComputes
    (ifComputes (labelEqualsComputes 0)
      ((scopeComputes.andThen (phaseRowsComputes j ps)).andThen
        (appendComputes Raw.factorEncoding (R.constantRows p₀ p₁ ps)))
      (nonphaseRowsComputes e p₀ p₁))
    (fun row => by simp [R.block])

/-- No abstract substitution backend is assumed: this is a composition of
proved finite Boolean-stack programmes, retaining the full Raw wire codec. -/
def rawComputes (j e p₀ p₁ : ℕ) (ps : List (Fin n → Bool ⊕ Fin 3)) :
    Computes Raw.encoding Raw.encoding (R.raw j e p₀ p₁ ps) :=
  recode (pairComputes (S.variablesComputes.andThen unaryAddTwoComputes)
    ((S.factorsComputes.andThen (Access.flatMap Raw.factorEncoding Raw.factorEncoding
      (R.block j e p₀ p₁ ps) (blockComputes j e p₀ p₁ ps))).andThen
        (appendComputes Raw.factorEncoding (R.guards p₀ p₁))))
    id (fun _ => rfl) (fun _ => rfl)

/-- A physical singleton marker is emitted for each original cubic row. -/
def countChunk (row : Factor) : List ℕ := if row.1=0 then [0] else []

def countChunkComputes : Computes Raw.factorEncoding scopeEncoding countChunk :=
  congrComputes (ifComputes (labelEqualsComputes 0)
    (constantComputes Raw.factorEncoding scopeEncoding [0])
    (constantComputes Raw.factorEncoding scopeEncoding []))
    (fun row => by simp [countChunk])

theorem countChunk_length (rows : List Factor) :
    (rows.flatMap countChunk).length=(rows.filter (fun row => row.1=0)).length := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      by_cases h : row.1=0 <;> simp [countChunk,h,ih]

/-- Counting the physically emitted markers gives the exact exponent used
for the scalar correction, in unary encoding. -/
def copiesComputes : Computes Raw.encoding UnaryBinary.unaryEncoding R.copies :=
  congrComputes ((S.factorsComputes.andThen
    (Access.flatMap Raw.factorEncoding encodingNatBool countChunk countChunkComputes)).andThen
      (W.lengthComputes encodingNatBool))
    (fun r => countChunk_length r.factors)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativePhaseBundleProgramme
end
