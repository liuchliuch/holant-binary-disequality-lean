import Holant.Complexity.WitnessCounting
import Holant.Complexity.FramedEncoding
import Mathlib.Data.Fin.Tuple.Basic


namespace Holant.LocalDrafts.CountingHardness

open Computability Holant.Complexity
open scoped BigOperators

inductive Circuit : ℕ → Type
  | output {n : ℕ} : Fin n → Circuit n
  | constant {n : ℕ} : Bool → Circuit (n + 1) → Circuit n
  | nand {n : ℕ} : Fin n → Fin n → Circuit (n + 1) → Circuit n

namespace Circuit

def gates {n : ℕ} : Circuit n → ℕ
  | .output _ => 0
  | .constant _ c => c.gates + 1
  | .nand _ _ c => c.gates + 1

def eval {n : ℕ} : Circuit n → (Fin n → Bool) → Bool
  | .output i, x => x i
  | .constant b c, x => c.eval (Fin.cons b x)
  | .nand a b c, x => c.eval (Fin.cons (!(x a && x b)) x)

/-- The actual chronological values of all introduced registers. -/
def trace {n : ℕ} (c : Circuit n) (x : Fin n → Bool) : Fin c.gates → Bool :=
  match c with
  | .output _ => Fin.elim0
  | .constant b c => Fin.cons b (c.trace (Fin.cons b x))
  | .nand a b c =>
    let v := !(x a && x b)
    Fin.cons v (c.trace (Fin.cons v x))

/-- Local gate constraints, with no unrestricted extra internal bits. -/
def consistent {n : ℕ} (c : Circuit n) (x : Fin n → Bool)
    (z : Fin c.gates → Bool) : Bool :=
  match c with
  | .output _ => true
  | .constant b c =>
    (z ⟨0, Nat.zero_lt_succ c.gates⟩ == b) &&
      c.consistent (Fin.cons (z ⟨0, Nat.zero_lt_succ c.gates⟩) x) (Fin.tail z)
  | .nand a b c =>
    (z ⟨0, Nat.zero_lt_succ c.gates⟩ == !(x a && x b)) &&
      c.consistent (Fin.cons (z ⟨0, Nat.zero_lt_succ c.gates⟩) x) (Fin.tail z)

def outputWith {n : ℕ} (c : Circuit n) (x : Fin n → Bool)
    (z : Fin c.gates → Bool) : Bool :=
  match c with
  | .output i => x i
  | .constant _ c =>
    c.outputWith (Fin.cons (z ⟨0, Nat.zero_lt_succ c.gates⟩) x) (Fin.tail z)
  | .nand _ _ c =>
    c.outputWith (Fin.cons (z ⟨0, Nat.zero_lt_succ c.gates⟩) x) (Fin.tail z)

theorem consistent_iff {n : ℕ} (c : Circuit n) (x : Fin n → Bool)
    (z : Fin c.gates → Bool) : c.consistent x z = true ↔ z = c.trace x := by
  induction c with
  | output i =>
    constructor
    · intro _
      funext i
      exact Fin.elim0 i
    · intro _
      rfl
  | constant b c ih =>
    simp only [consistent, Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨hz, ht⟩
      have htail :=
        (ih (Fin.cons (z ⟨0, Nat.zero_lt_succ c.gates⟩) x) (Fin.tail z)).mp ht
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hz
      · change z j.succ =
          Fin.cons (α := fun _ => Bool) b (c.trace (Fin.cons b x)) j.succ
        rw [Fin.cons_succ]
        have htj := congrFun htail j
        change z j.succ =
          c.trace (Fin.cons (z ⟨0, Nat.zero_lt_succ c.gates⟩) x) j at htj
        rw [hz] at htj
        exact htj
    · intro hz
      subst z
      constructor
      · rfl
      · change c.consistent (Fin.cons b x)
          (Fin.tail (Fin.cons (α := fun _ => Bool) b (c.trace (Fin.cons b x)))) = true
        rw [Fin.tail_cons]
        exact (ih (Fin.cons b x) (c.trace (Fin.cons b x))).mpr rfl
  | nand a b c ih =>
    simp only [consistent, Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨hz, ht⟩
      have htail :=
        (ih (Fin.cons (z ⟨0, Nat.zero_lt_succ c.gates⟩) x) (Fin.tail z)).mp ht
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hz
      · change z j.succ = Fin.cons (α := fun _ => Bool) (!(x a && x b))
          (c.trace (Fin.cons (!(x a && x b)) x)) j.succ
        rw [Fin.cons_succ]
        have htj := congrFun htail j
        change z j.succ =
          c.trace (Fin.cons (z ⟨0, Nat.zero_lt_succ c.gates⟩) x) j at htj
        rw [hz] at htj
        exact htj
    · intro hz
      subst z
      constructor
      · rfl
      · change c.consistent (Fin.cons (!(x a && x b)) x)
          (Fin.tail (Fin.cons (α := fun _ => Bool) (!(x a && x b))
            (c.trace (Fin.cons (!(x a && x b)) x)))) = true
        rw [Fin.tail_cons]
        exact (ih (Fin.cons (!(x a && x b)) x)
          (c.trace (Fin.cons (!(x a && x b)) x))).mpr rfl

@[simp] theorem outputWith_trace {n : ℕ} (c : Circuit n) (x : Fin n → Bool) :
    c.outputWith x (c.trace x) = c.eval x := by
  induction c with
  | output i => rfl
  | constant b c ih =>
    change c.outputWith (Fin.cons b x)
      (Fin.tail (Fin.cons (α := fun _ => Bool) b (c.trace (Fin.cons b x)))) =
        c.eval (Fin.cons b x)
    rw [Fin.tail_cons]
    exact ih (Fin.cons b x)
  | nand a b c ih =>
    change c.outputWith (Fin.cons (!(x a && x b)) x)
      (Fin.tail (Fin.cons (α := fun _ => Bool) (!(x a && x b))
        (c.trace (Fin.cons (!(x a && x b)) x)))) = c.eval (Fin.cons (!(x a && x b)) x)
    rw [Fin.tail_cons]
    exact ih (Fin.cons (!(x a && x b)) x)

def accepts {n : ℕ} (c : Circuit n) (x : Fin n → Bool)
    (z : Fin c.gates → Bool) : Bool := c.consistent x z && c.outputWith x z

theorem accepts_iff {n : ℕ} (c : Circuit n) (x : Fin n → Bool)
    (z : Fin c.gates → Bool) :
    c.accepts x z = true ↔ z = c.trace x ∧ c.eval x = true := by
  simp only [accepts, Bool.and_eq_true, consistent_iff]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, by simpa using h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, by simpa using h⟩

/-- Exactly one extension for a fixed accepted input, including unused inputs. -/
theorem count_extensions {n : ℕ} (c : Circuit n) (x : Fin n → Bool) :
    countAccepted (c.accepts x) = if c.eval x then 1 else 0 := by
  classical
  unfold countAccepted
  calc
    (∑ z, if c.accepts x z then 1 else 0) =
        ∑ z, if z = c.trace x then (if c.eval x then 1 else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z = c.trace x
      · subst z
        have hc := (c.consistent_iff x (c.trace x)).mpr rfl
        simp [accepts, hc]
      · have ha : c.accepts x z ≠ true := fun h => hz ((c.accepts_iff x z).mp h).1
        simp [hz, ha]
    _ = if c.eval x then 1 else 0 := by simp

/-- Adding gate variables preserves the complete count, without a power-of-two
normalization or an assumption of unique satisfying extensions. -/
theorem parsimonious {n : ℕ} (c : Circuit n) :
    countAccepted (fun xz : (Fin n → Bool) × (Fin c.gates → Bool) =>
      c.accepts xz.1 xz.2) = countAccepted c.eval := by
  unfold countAccepted
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  exact c.count_extensions x

abbrev Row := ℕ × (ℕ × ℕ)
abbrev Code := List Row × ℕ

/-- Tags 0/1 are Boolean constants; tag 2 is NAND. -/
def code {n : ℕ} : Circuit n → Code
  | .output i => ([], i.val)
  | .constant b c => ((if b then 1 else 0, (0, 0)) :: c.code.1, c.code.2)
  | .nand a b c => ((2, (a.val, b.val)) :: c.code.1, c.code.2)

def parse (n : ℕ) : List Row → ℕ → Option (Circuit n)
  | [], out => if h : out < n then some (.output ⟨out, h⟩) else none
  | (tag, a, b) :: rows, out => do
    let tail ← parse (n + 1) rows out
    if tag = 0 then
      if a = 0 ∧ b = 0 then some (.constant false tail) else none
    else if tag = 1 then
      if a = 0 ∧ b = 0 then some (.constant true tail) else none
    else if tag = 2 then
      if ha : a < n then
        if hb : b < n then some (.nand ⟨a, ha⟩ ⟨b, hb⟩ tail) else none
      else none
    else none

@[simp] theorem parse_code {n : ℕ} (c : Circuit n) :
    parse n c.code.1 c.code.2 = some c := by
  induction c with
  | output i => simp [parse, code, i.isLt]
  | constant b c ih => cases b <;> simp [code, parse, ih]
  | nand a b c ih => simp [code, parse, ih, a.isLt, b.isLt]

def rowEncoding : Encoding Row Bool :=
  framedProductEncoding encodingNatBool (framedProductEncoding encodingNatBool encodingNatBool)

def codeEncoding : Encoding Code Bool :=
  framedProductEncoding (framedListEncoding rowEncoding) encodingNatBool

/-- A decoder with range checks; invalid wire references cannot create cycles. -/
def encoding (n : ℕ) : Encoding (Circuit n) Bool where
  encode c := codeEncoding.encode c.code
  decode bits := (codeEncoding.decode bits).bind fun p => parse n p.1 p.2
  decode_encode c := by simp

@[simp] theorem code_rows_length {n : ℕ} (c : Circuit n) : c.code.1.length = c.gates := by
  induction c with
  | output i => rfl
  | constant b c ih => simpa [code, gates] using congrArg Nat.succ ih
  | nand a b c ih => simpa [code, gates] using congrArg Nat.succ ih

theorem gates_le_encoded_length {n : ℕ} (c : Circuit n) :
    c.gates ≤ ((encoding n).encode c).length := by
  have h := framedListEncoding_length_lower rowEncoding c.code.1
  simp only [code_rows_length] at h
  change c.gates ≤ (codeEncoding.encode c.code).length
  simp only [codeEncoding, framedProductEncoding_length]
  omega

end Circuit

structure CircuitInstance where
  inputs : ℕ
  circuit : Circuit inputs

namespace CircuitInstance

/-- Input slots are explicit, including unused slots. A binary encoded input
count alone would allow exponentially many witness bits in a short instance. -/
def codeEncoding : Encoding (List Bool × Circuit.Code) Bool :=
  framedProductEncoding (framedListEncoding encodingBoolBool) Circuit.codeEncoding

def encoding : Encoding CircuitInstance Bool where
  encode c := codeEncoding.encode (List.replicate c.inputs false, c.circuit.code)
  decode bits := do
    let (slots, rows, out) ← codeEncoding.decode bits
    let c ← Circuit.parse slots.length rows out
    pure ⟨slots.length, c⟩
  decode_encode c := by
    rcases c with ⟨n, c⟩
    simp [List.length_replicate]
    rw [List.length_replicate, Circuit.parse_code]
    rfl

def value (c : CircuitInstance) : ℕ := countAccepted c.circuit.eval

theorem inputs_le_encoded_length (c : CircuitInstance) :
    c.inputs ≤ (encoding.encode c).length := by
  have h := framedListEncoding_length_lower encodingBoolBool (List.replicate c.inputs false)
  simp only [List.length_replicate] at h
  change c.inputs ≤ (codeEncoding.encode (List.replicate c.inputs false, c.circuit.code)).length
  simp only [codeEncoding, framedProductEncoding_length]
  omega

theorem gates_le_encoded_length (c : CircuitInstance) :
    c.circuit.gates ≤ (encoding.encode c).length := by
  have h := c.circuit.gates_le_encoded_length
  change c.circuit.gates ≤ (Circuit.codeEncoding.encode c.circuit.code).length at h
  change c.circuit.gates ≤ (codeEncoding.encode (List.replicate c.inputs false, c.circuit.code)).length
  simp only [codeEncoding, framedProductEncoding_length]
  omega

end CircuitInstance
end Holant.LocalDrafts.CountingHardness
