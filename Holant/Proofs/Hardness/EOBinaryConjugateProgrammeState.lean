import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeRoots
import Holant.Proofs.Hardness.ThreeModeFilter

/-! One finite arithmetic controller for collision-safe mixed-conjugate
interpolation. Its outer accumulator stores a numerator/denominator pair; all
rounds use ring operations, and canonical division occurs only at the end. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeState
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open BinaryCSPProgrammeCore
open GraphPreprocessing FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

structure State (L : Type) where
  roots : List (L×L)
  moments : List L
  pending : List (L×L)
  remaining : List (L×L)
  values : List L
  denominator : L
  multiplicity : L
  numerator : L
  divisor : L
  fuel : ℕ

abbrev Fields (L : Type) :=
  List (L×L) × (List L × (List (L×L) × (List (L×L) × (List L ×
    (L × (L × (L × (L × ℕ))))))))

def State.fields {L : Type} (s : State L) : Fields L :=
  (s.roots,s.moments,s.pending,s.remaining,s.values,s.denominator,s.multiplicity,s.numerator,s.divisor,s.fuel)

def ofFields {L : Type} (p : Fields L) : State L :=
  ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2.1,
    p.2.2.2.2.2.2.1,p.2.2.2.2.2.2.2.1,p.2.2.2.2.2.2.2.2.1,p.2.2.2.2.2.2.2.2.2⟩

variable {L : Type} [Field L] [Algebra ℚ L] {d : ℕ}
variable (F : FixedField L d)

abbrev scalarsEncoding := pairEncoding F.encoding F.encoding
abbrev rootsEncoding := framedListEncoding (scalarsEncoding F)
abbrev valuesEncoding := framedListEncoding F.encoding
abbrev fieldsEncoding := pairEncoding (rootsEncoding F) (pairEncoding (valuesEncoding F)
  (pairEncoding (rootsEncoding F) (pairEncoding (rootsEncoding F) (pairEncoding (valuesEncoding F)
    (pairEncoding F.encoding (pairEncoding F.encoding (pairEncoding F.encoding (pairEncoding F.encoding unary))))))))

def encoding : Encoding (State L) Bool where
  encode s := (fieldsEncoding F).encode s.fields
  decode bits := ofFields <$> (fieldsEncoding F).decode bits
  decode_encode s := by rw [(fieldsEncoding F).decode_encode]; rfl

local instance : DecidableEq L := Classical.decEq L
variable (s : State L)

def desired : L×L := s.pending.getD 0 (0,0)
def nextDesired : L×L := s.pending.getD 1 (0,0)
def root : L := (s.remaining.getD 0 (0,0)).1

def scanEqual : State L := {s with remaining:=s.remaining.tail,multiplicity:=s.multiplicity+1}

def scanDifferent : State L :=
  {s with
    remaining:=s.remaining.tail
    values:=ThreeModeFilter.difference (root s) s.values
    denominator:=s.denominator*((desired s).1-root s)}

def advance : State L :=
  {s with
    pending:=s.pending.tail
    remaining:=s.roots
    values:=s.moments
    denominator:=(nextDesired s).1
    multiplicity:=0
    numerator:=s.numerator*(s.denominator*s.multiplicity)+
      ((desired s).2*s.values.getD 0 0)*s.divisor
    divisor:=s.divisor*(s.denominator*s.multiplicity)}

def step : State L :=
  if s.pending=[] then s else if s.remaining=[] then advance s else
    if root s=(desired s).1 then scanEqual s else scanDifferent s

def initial (roots : List (L×L)) (moments : List L) : State L where
  roots:=roots
  moments:=moments
  pending:=roots
  remaining:=roots
  values:=moments
  denominator:=(roots.getD 0 (0,0)).1
  multiplicity:=0
  numerator:=0
  divisor:=1
  fuel:=roots.length*(roots.length+1)

def fieldsComputes : Computes (encoding F) (fieldsEncoding F) State.fields :=
  recode (identityComputes (fieldsEncoding F)) State.fields (fun _=>rfl) (fun _=>rfl)

private def p₁ := (fieldsComputes F).andThen (Wiring.secondComputes _ _)
private def p₂ := (p₁ F).andThen (Wiring.secondComputes _ _)
private def p₃ := (p₂ F).andThen (Wiring.secondComputes _ _)
private def p₄ := (p₃ F).andThen (Wiring.secondComputes _ _)
private def p₅ := (p₄ F).andThen (Wiring.secondComputes _ _)
private def p₆ := (p₅ F).andThen (Wiring.secondComputes _ _)
private def p₇ := (p₆ F).andThen (Wiring.secondComputes _ _)
private def p₈ := (p₇ F).andThen (Wiring.secondComputes _ _)

def rootsComputes : Computes (encoding F) (rootsEncoding F) State.roots :=
  (fieldsComputes F).andThen (Wiring.firstComputes _ _)
def momentsComputes : Computes (encoding F) (valuesEncoding F) State.moments :=
  (p₁ F).andThen (Wiring.firstComputes _ _)
def pendingComputes : Computes (encoding F) (rootsEncoding F) State.pending :=
  (p₂ F).andThen (Wiring.firstComputes _ _)
def remainingComputes : Computes (encoding F) (rootsEncoding F) State.remaining :=
  (p₃ F).andThen (Wiring.firstComputes _ _)
def valuesComputes : Computes (encoding F) (valuesEncoding F) State.values :=
  (p₄ F).andThen (Wiring.firstComputes _ _)
def denominatorComputes : Computes (encoding F) F.encoding State.denominator :=
  (p₅ F).andThen (Wiring.firstComputes _ _)
def multiplicityComputes : Computes (encoding F) F.encoding State.multiplicity :=
  (p₆ F).andThen (Wiring.firstComputes _ _)
def numeratorComputes : Computes (encoding F) F.encoding State.numerator :=
  (p₇ F).andThen (Wiring.firstComputes _ _)
def divisorComputes : Computes (encoding F) F.encoding State.divisor :=
  (p₈ F).andThen (Wiring.firstComputes _ _)
def fuelComputes : Computes (encoding F) unary State.fuel :=
  (p₈ F).andThen (Wiring.secondComputes _ _)

def assemble {A : Type} {e : Encoding A Bool}
    {rs ps rem : A→List (L×L)} {ms vs : A→List L} {dn ct nm dv : A→L} {fuel : A→ℕ}
    (wrs : Computes e (rootsEncoding F) rs) (wms : Computes e (valuesEncoding F) ms)
    (wps : Computes e (rootsEncoding F) ps) (wrem : Computes e (rootsEncoding F) rem)
    (wvs : Computes e (valuesEncoding F) vs) (wdn : Computes e F.encoding dn)
    (wct : Computes e F.encoding ct) (wnm : Computes e F.encoding nm)
    (wdv : Computes e F.encoding dv) (wf : Computes e unary fuel) :
    Computes e (encoding F) (fun a=> (⟨rs a,ms a,ps a,rem a,vs a,dn a,ct a,nm a,dv a,fuel a⟩ : State L)) :=
  recode (pairComputes wrs (pairComputes wms (pairComputes wps (pairComputes wrem
    (pairComputes wvs (pairComputes wdn (pairComputes wct (pairComputes wnm (pairComputes wdv wf)))))))))
    id (fun _=>rfl) (fun _=>rfl)

def desiredComputes : Computes (encoding F) (scalarsEncoding F) desired :=
  (pendingComputes F).andThen (getDComputes (scalarsEncoding F) 0 (0,0))
def nextDesiredComputes : Computes (encoding F) (scalarsEncoding F) nextDesired :=
  (pendingComputes F).andThen (getDComputes (scalarsEncoding F) 1 (0,0))
def rootComputes : Computes (encoding F) F.encoding root :=
  ((remainingComputes F).andThen (getDComputes (scalarsEncoding F) 0 (0,0))).andThen
    (Wiring.firstComputes F.encoding F.encoding)

/-- The scalar pair is itself a fixed field for list-tail compilation only in
syntax: the generic tail writer uses dynamic lookup and scans a unary range. -/
def tailRoots : Computes (rootsEncoding F) (rootsEncoding F) List.tail := by
  let ctx := Wiring.firstComputes (rootsEncoding F) unary
  let k := Wiring.secondComputes (rootsEncoding F) unary
  exact congrComputes (WireLists.tabulate (rootsEncoding F) (scalarsEncoding F)
    (fun xs : List (L×L)=>xs.length-1)
    ((WireLists.lengthComputes (scalarsEncoding F)).andThen
      Endpoints.unaryPredecessorComputes)
    (fun xs k=>xs.getD (k+1) (0,0))
    (AccessPrograms.get (scalarsEncoding F) (0,0) ctx (k.andThen WireLists.succComputes)))
    (fun xs=>by
      apply List.ext_getElem
      · simp
      · intro i hi hj
        simp only [List.getElem_map,List.getElem_range]
        have hh : i<xs.length-1 := by simpa using hj
        rw [List.getD_eq_getElem _ _ (by omega)]
        simp)

def scanEqualComputes : Computes (encoding F) (encoding F) scanEqual :=
  assemble F (rootsComputes F) (momentsComputes F) (pendingComputes F)
    ((remainingComputes F).andThen (tailRoots F)) (valuesComputes F) (denominatorComputes F)
    ((pairComputes (multiplicityComputes F) (constantComputes (encoding F) F.encoding 1)).andThen
      (Concrete.fieldAddition F)) (numeratorComputes F) (divisorComputes F) (fuelComputes F)

def scanDifferentComputes : Computes (encoding F) (encoding F) scanDifferent :=
  assemble F (rootsComputes F) (momentsComputes F) (pendingComputes F)
    ((remainingComputes F).andThen (tailRoots F))
    ((pairComputes (rootComputes F) (valuesComputes F)).andThen (ThreeModeFilter.differenceComputes F))
    ((pairComputes (denominatorComputes F)
      ((pairComputes ((desiredComputes F).andThen (Wiring.firstComputes _ _)) (rootComputes F)).andThen
        (ThreeModeFilter.subtraction F))).andThen (Concrete.fieldMultiplication F))
    (multiplicityComputes F) (numeratorComputes F) (divisorComputes F) (fuelComputes F)

def advanceComputes : Computes (encoding F) (encoding F) advance := by
  let den := (pairComputes (denominatorComputes F) (multiplicityComputes F)).andThen
    (Concrete.fieldMultiplication F)
  let num := (pairComputes ((desiredComputes F).andThen (Wiring.secondComputes _ _))
    ((valuesComputes F).andThen (getDComputes F.encoding 0 0))).andThen (Concrete.fieldMultiplication F)
  let acc := (pairComputes
    ((pairComputes (numeratorComputes F) den).andThen (Concrete.fieldMultiplication F))
    ((pairComputes num (divisorComputes F)).andThen (Concrete.fieldMultiplication F))).andThen
      (Concrete.fieldAddition F)
  exact assemble F (rootsComputes F) (momentsComputes F)
    ((pendingComputes F).andThen (tailRoots F)) (rootsComputes F) (momentsComputes F)
    ((nextDesiredComputes F).andThen (Wiring.firstComputes _ _))
    (constantComputes (encoding F) F.encoding 0) acc
    ((pairComputes (divisorComputes F) den).andThen (Concrete.fieldMultiplication F)) (fuelComputes F)

def computes : Computes (encoding F) (encoding F) step := by
  classical
  let emptyPending := (pairComputes (pendingComputes F)
    (constantComputes (encoding F) (rootsEncoding F) [])).andThen (equalComputes (rootsEncoding F))
  let emptyRemaining := (pairComputes (remainingComputes F)
    (constantComputes (encoding F) (rootsEncoding F) [])).andThen (equalComputes (rootsEncoding F))
  let collision := (pairComputes (rootComputes F)
    ((desiredComputes F).andThen (Wiring.firstComputes _ _))).andThen (equalComputes F.encoding)
  exact congrComputes (ifComputes emptyPending (identityComputes (encoding F))
    (ifComputes emptyRemaining (advanceComputes F)
      (ifComputes collision (scanEqualComputes F) (scanDifferentComputes F)))) (fun s=>by simp [step])

def finishComputes : Computes (encoding F) F.encoding (fun s=>s.numerator/s.divisor) :=
  (pairComputes (numeratorComputes F) (divisorComputes F)).andThen (fieldDivisionComputes F)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeState
