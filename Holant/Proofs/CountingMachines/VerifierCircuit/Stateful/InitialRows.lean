import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.Reset

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
# Exact original-input row sequence and whole-circuit code formulas

Ported reference proof. See the task validation reports.
-/

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.InitialRows

open Holant.LocalDrafts.CountingHardness

open Turing Computability Holant.Complexity BitLayout
open scoped Classical

def boolMap {I : Type} (i : I) (f : Bool → Bool) : Rows.Run I Unit :=
  Rows.seq (Rows.parallel (Rows.route (fun _ : Unit => i))
    (Rows.parallel (Rows.constant (f true)) (Rows.constant (f false))))
    (Rows.mux (.inl ()) (.inr (.inl ())) (.inr (.inr ())))

theorem boolMap_exact {I : Type} (i : I) (f : Bool → Bool) :
    Rows.Exact (Initial.boolMap i f) (boolMap i f) :=
  Rows.seq_exact (Rows.parallel_exact (Rows.route_exact _)
    (Rows.parallel_exact (Rows.constant_exact _) (Rows.constant_exact _))) (Rows.mux_exact _ _ _)

variable (tm : FinTM2) (C : ℕ) [∀ k, Fintype (tm.Γ k)]
variable (e : tm.Γ tm.k₀ ≃ Bool ⊕ Bool) (word : List Bool) (W : ℕ)

def inputBit (i : Fin (C + 1)) (a : Option (tm.Γ tm.k₀)) : Rows.Run (Fin W) Unit :=
  match (Initial.tokens word W)[i.val]? with
  | none => Rows.constant (oneHot (none : Option (tm.Γ tm.k₀)) a)
  | some (.inl b) => Rows.constant (oneHot (some (e.symm (.inl b))) a)
  | some (.inr j) => boolMap j (fun b => oneHot (some (e.symm (.inr b))) a)

theorem inputBit_exact (i : Fin (C + 1)) (a : Option (tm.Γ tm.k₀)) :
    Rows.Exact (Initial.inputBit tm C e word W i a) (inputBit tm C e word W i a) := by
  unfold Initial.inputBit inputBit
  cases h : (Initial.tokens word W)[i.val]? with
  | none => exact Rows.constant_exact _
  | some token =>
    cases token with
    | inl b => exact Rows.constant_exact _
    | inr j => exact boolMap_exact _ _

def bit : Address tm C → Rows.Run (Fin W) Unit
  | .inl l => Rows.constant (oneHot (some tm.main) l)
  | .inr (.inl s) => Rows.constant (oneHot tm.initialState s)
  | .inr (.inr ⟨k, i, a⟩) =>
      if h : k = tm.k₀ then inputBit tm C e word W i (h ▸ a)
      else Rows.constant (oneHot (none : Option (tm.Γ k)) a)

theorem bit_exact (a : Address tm C) :
    Rows.Exact (Initial.bit tm C e word W a) (bit tm C e word W a) := by
  cases a with
  | inl l => exact Rows.constant_exact _
  | inr a =>
    cases a with
    | inl s => exact Rows.constant_exact _
    | inr a =>
      rcases a with ⟨k, i, a⟩
      by_cases hk : k = tm.k₀
      · subst k
        simpa [Initial.bit, bit] using inputBit_exact tm C e word W i a
      · simpa [Initial.bit, bit, hk] using (Rows.constant_exact (I := Fin W) (oneHot (none : Option (tm.Γ k)) a))

def initial : Rows.Run (Fin W) (Address tm C) :=
  Rows.tabulate (addresses tm C) (mem_addresses tm C) (bit tm C e word W)

theorem initial_exact : Rows.Exact (Initial.emit tm C e word W) (initial tm C e word W) :=
  Rows.tabulate_exact _ _ _ _ (bit_exact tm C e word W)

variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ} (w : SharpPWitness ea f)
local instance initialRowsAlphabets : ∀ k, Fintype (w.verifier.tm.Γ k) := w.verifier.finiteAlphabets

def initialResult (word : List Bool) : Rows.Result (Address w.verifier.tm (capacity w word)) :=
  initial w.verifier.tm (capacity w word) w.verifier.inputAlphabet word
    (w.witnessLength.eval word.length) Fin.val

def code (word : List Bool) : Circuit.Code :=
  let first := initialResult w word
  let rounds := StatementRows.unroll w.verifier.tm (capacity w word)
    ((VerifierRun.horizonPolynomial w).eval word.length) first.2
  (first.1 ++ rounds.1, rounds.2 (acceptance w word))

theorem compileWord_code (word : List Bool) : (compileWord w word).circuit.code = code w word := by
  have h := Rows.seq_exact (initial_exact w.verifier.tm (capacity w word) w.verifier.inputAlphabet word
    (w.witnessLength.eval word.length))
    (Rows.seq_exact (StatementRows.unroll_exact w.verifier.tm (capacity w word)
      ((VerifierRun.horizonPolynomial w).eval word.length)) (Rows.route_exact (fun _ : Unit => acceptance w word)))
  simpa [compileWord, body, code, initialResult, Rows.seq, Rows.route] using
    Rows.finish_code h (fun i => i)

theorem code_zero (word : List Bool) (hT : (VerifierRun.horizonPolynomial w).eval word.length = 0) :
    code w word = ((initialResult w word).1, (initialResult w word).2 (acceptance w word)) := by
  simp [code, hT, StatementRows.unroll, Rows.route]

theorem code_succ (word : List Bool) (T : ℕ)
    (hT : (VerifierRun.horizonPolynomial w).eval word.length = T + 1) :
    code w word =
      ((initialResult w word).1 ++
        (StatementRows.hold w.verifier.tm (capacity w word) (initialResult w word).2).1 ++
        (List.replicate T (Reset.steadyRows w.verifier.tm (capacity w word))).flatten,
        Reset.references w.verifier.tm (capacity w word) (acceptance w word)) := by
  simp [code, hT, Reset.unroll_rows, Reset.unroll_output, List.append_assoc]

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.InitialRows
