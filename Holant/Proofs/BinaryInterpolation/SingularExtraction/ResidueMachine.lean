import Holant.Complexity.FixedGadgetSubstitution.Compiler.Compile
import Holant.Complexity.FixedFieldMachines.Constant
import Holant.Complexity.GraphPreprocessing.FiniteRecode
import Holant.Proofs.BinaryInterpolation.SingularExtraction.ResidueAnchors


noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.ResidueMachine
open Holant Holant.Complexity Turing Computability BinaryCompose StackProtocol
open Holant.Complexity.FixedFieldMachines
open Holant.Complexity.GraphPreprocessing

variable (k : ℕ) (hk : 0 < k)

def advance (r : Fin k) : Fin k := ⟨(r.val+1) % k, Nat.mod_lt _ hk⟩

def finish : ℕ → Fin k → Fin k
  | 0, r => r
  | n+1, r => finish n (advance k hk r)

theorem finish_val (n : ℕ) (r : Fin k) :
    (finish k hk n r).val = (r.val+n) % k := by
  induction n generalizing r with
  | zero => simp [finish, Nat.mod_eq_of_lt r.isLt]
  | succ n ih =>
    rw [finish, ih]
    change ((r.val+1) % k + n) % k = (r.val+(n+1)) % k
    simp [Nat.add_mod, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def scanStmt (out : Fin k → List Bool) (r : Fin k) : Stmt Unit (Fin k) Unit :=
  .pop () (fun _ bit => (bit, ()))
    (.branch (fun q => q.1.isSome)
      (.load (fun _ => (none, ())) (.goto (fun _ => advance k hk r)))
      (.load (fun _ => (none, ())) (Constant.pushWord () (out r) .halt)))

abbrev machine (out : Fin k → List Bool) : Machine where
  K := Unit
  input := ()
  output := ()
  Label := Fin k
  main := ⟨0, hk⟩
  State := Option Bool × Unit
  initial := (none, ())
  program := scanStmt k hk out

theorem step_cons (out : Fin k → List Bool) (r : Fin k) (bit : Bool) (word : List Bool) :
    (machine k hk out).computer.step (cfg r () (wordTape () (bit :: word))) =
      some (cfg (advance k hk r) () (wordTape () word)) := by
  simp [FinTM2.step, TM2.step, machine, scanStmt, cfg, TM2.stepAux,
    wordTape, Function.update_idem]

theorem step_nil (out : Fin k → List Bool) (r : Fin k) :
    (machine k hk out).computer.step (cfg r () (wordTape () [])) =
      some (haltList (machine k hk out).computer (out r)) := by
  rw [Machine.halt_eq]
  dsimp [FinTM2.step, TM2.step, machine, scanStmt, cfg]
  simp only [TM2.stepAux, wordTape_at, Option.isSome_none, cond_false]
  rw [Constant.pushWord_eval]
  simp [TM2.stepAux, wordTape, Function.update_idem]

/-- Exactly one transition per token, followed by one fixed emission step.
The emission syntax has a finite primitive budget, accounted separately. -/
theorem exact_run (out : Fin k → List Bool) (r : Fin k) (word : List Bool) :
    RunsExactly (machine k hk out).computer.step (cfg r () (wordTape () word))
      (haltList (machine k hk out).computer (out (finish k hk word.length r)))
      (word.length + 1) := by
  induction word generalizing r with
  | nil => exact runsExactly_one (step_nil k hk out r)
  | cons bit word ih =>
    simpa [finish, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (runsExactly_one (step_cons k hk out r bit word)).trans (ih (advance k hk r))

def remainder (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩

/-- Any fixed table indexed by the residue is compiled into literal push
syntax. The polynomial counts transitions on the actual unary input bytes. -/
def computes {A : Type} (e : Encoding A Bool) (f : Fin k → A) :
    Computes UnaryBinary.unaryEncoding e (fun n => f (remainder k hk n)) where
  machine := machine k hk (fun r => e.encode (f r))
  time := Polynomial.X + 1
  outputs n := by
    have h := exact_run k hk (fun r => e.encode (f r)) ⟨0, hk⟩
      (UnaryBinary.unaryEncoding.encode n)
    have hf : finish k hk (UnaryBinary.unaryEncoding.encode n).length ⟨0, hk⟩ =
        remainder k hk n := by
      apply Fin.ext
      simp [finish_val, remainder, UnaryBinary.unaryEncoding]
    rw [hf] at h
    refine { steps := (UnaryBinary.unaryEncoding.encode n).length + 1
             evals_in_steps := ?_
             steps_le_m := by simp }
    simp only [Machine.init_eq, RunsExactly, Function.flip_def, Option.map_some] at h ⊢
    exact h

theorem primitive_bound {A : Type} (e : Encoding A Bool) (f : Fin k → A) (n : ℕ) :
    primitiveCost (computes k hk e f).machine ((computes k hk e f).outputs n).steps
      (some (initList (computes k hk e f).machine.computer (UnaryBinary.unaryEncoding.encode n))) ≤
      (primitivePolynomial (computes k hk e f)).eval (UnaryBinary.unaryEncoding.encode n).length :=
  computes_primitive_cost (computes k hk e f) n

variable {s b : ℕ} {arity : ℕ → ℕ}

/-- Both counts are scanned from the original graph, with separate moduli.
This machine's input is the original faithful graph encoding. -/
def graphResiduesComputes (a c l : ℕ) (hl : 0 < l)
    (ek : Encoding (Fin k) Bool) (el : Encoding (Fin l) Bool) :
    Computes (RawClosedNetwork.validatedEncoding s b arity) (pairEncoding ek el)
      (ResidueAnchors.residue (s:=s) (b:=b) (arity:=arity) a c k l hk hl) :=
  pairComputes
    ((FixedGadgetSubstitution.Compiler.occurrencesComputes s b arity a).andThen
      (computes k hk ek id))
    ((FixedGadgetSubstitution.Compiler.occurrencesComputes s b arity c).andThen
      (computes l hl el id))

def finEncoding (m : ℕ) : Encoding (Fin m) Bool where
  encode r := UnaryBinary.unaryEncoding.encode r.val
  decode word := do
    let n ← UnaryBinary.unaryEncoding.decode word
    if h : n < m then some ⟨n, h⟩ else none
  decode_encode r := by simp [r.isLt]

@[simp] theorem finEncoding_length (m : ℕ) (r : Fin m) :
    ((finEncoding m).encode r).length = r.val := by
  simp [finEncoding, UnaryBinary.unaryEncoding]

def residueEncoding (k l : ℕ) : Encoding (Fin k × Fin l) Bool :=
  pairEncoding (finEncoding k) (finEncoding l)

theorem residueEncoding_length (k l : ℕ) (r : Fin k × Fin l) :
    ((residueEncoding k l).encode r).length ≤ 2*k+1+l := by
  simp only [residueEncoding, pairEncoding_length, finEncoding_length]
  have h₁ := r.1.isLt
  have h₂ := r.2.isLt
  omega

variable {L : Type} [Field L]

/-- Live/dead classification and the anchor graph form a fixed finite table.
`decide` is used when choosing that finite program, not as a runtime opcode. -/
def anchorEntry (F : Holant.Complexity.UniversalPairReduction.Surgery.Choice.Table L)
    (a c l : ℕ) (hl : 0 < l) (ρ : Fin k × Fin l) : Bool × RawClosedNetwork :=
  (decide (ResidueAnchors.Live (s:=s) (b:=b) (arity:=arity) F a c k l hk hl ρ),
   (ResidueAnchors.anchor F a c k l hk hl ρ : ResidueAnchors.Input s b arity).val)

def anchorEntryEncoding : Encoding (Bool × RawClosedNetwork) Bool :=
  pairEncoding encodingBoolBool RawClosedNetwork.encoding

/-- Actual scanning followed by actual finite decoding/emission of the fixed
anchor. The input is still the original graph, never an externally supplied
occurrence count, residue, anchor witness, or expanded graph. -/
def anchorComputes (F : Holant.Complexity.UniversalPairReduction.Surgery.Choice.Table L)
    (a c l : ℕ) (hl : 0 < l) :
    Computes (RawClosedNetwork.validatedEncoding s b arity) anchorEntryEncoding
      (fun r => anchorEntry (s:=s) (b:=b) (arity:=arity) k hk F a c l hl
        (ResidueAnchors.residue a c k l hk hl r)) :=
  (graphResiduesComputes (s:=s) (b:=b) (arity:=arity) k hk a c l hl
    (finEncoding k) (finEncoding l)).andThen
      (FiniteRecode.computes (residueEncoding k l) anchorEntryEncoding
        (anchorEntry (s:=s) (b:=b) (arity:=arity) k hk F a c l hl)
        (2*k+1+l) (residueEncoding_length k l))

/-- A concrete prefix of the final reduction: original graph plus its actual
live flag and anchor bytes, with a single polynomial in original input length. -/
def prepareComputes (F : Holant.Complexity.UniversalPairReduction.Surgery.Choice.Table L)
    (a c l : ℕ) (hl : 0 < l) :
    Computes (RawClosedNetwork.validatedEncoding s b arity)
      (pairEncoding (RawClosedNetwork.validatedEncoding s b arity) anchorEntryEncoding)
      (fun r => (r, anchorEntry (s:=s) (b:=b) (arity:=arity) k hk F a c l hl
        (ResidueAnchors.residue a c k l hk hl r))) :=
  pairComputes (identityComputes _) (anchorComputes k hk F a c l hl)

theorem prepare_primitive_bound
    (F : Holant.Complexity.UniversalPairReduction.Surgery.Choice.Table L)
    (a c l : ℕ) (hl : 0 < l) (r : ResidueAnchors.Input s b arity) :
    primitiveCost (prepareComputes (s:=s) (b:=b) (arity:=arity) k hk F a c l hl).machine
      ((prepareComputes (s:=s) (b:=b) (arity:=arity) k hk F a c l hl).outputs r).steps
      (some (initList (prepareComputes (s:=s) (b:=b) (arity:=arity) k hk F a c l hl).machine.computer
        ((RawClosedNetwork.validatedEncoding s b arity).encode r))) ≤
      (primitivePolynomial (prepareComputes (s:=s) (b:=b) (arity:=arity) k hk F a c l hl)).eval
        ((RawClosedNetwork.validatedEncoding s b arity).encode r).length :=
  computes_primitive_cost (prepareComputes (s:=s) (b:=b) (arity:=arity) k hk F a c l hl) r

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.ResidueMachine
