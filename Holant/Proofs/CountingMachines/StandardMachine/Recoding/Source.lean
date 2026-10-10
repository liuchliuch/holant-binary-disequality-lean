import Holant.Proofs.CountingMachines.StandardMachine.Recoding.Program

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Recoding
open Turing Computability Holant.Complexity
variable {Γ Δ : Type} [Fintype Γ] [Fintype Δ]

def run (code : Γ → List Δ) (n : ℕ) : Option (Cfg Γ Δ) → Option (Cfg Γ Δ) :=
  (fun c => c.bind (machine code).step)^[n]

theorem run_add (code : Γ → List Δ) (m n : ℕ) (c : Option (Cfg Γ Δ)) :
    run code (m+n) c = run code m (run code n c) := Function.iterate_add_apply _ _ _ _

theorem reverse_round (code : Γ → List Δ) (a : Γ) (source reverse : List Γ) (out : List Δ) :
    run code 2 (some (cfg (.inl false) none (a::source) reverse out)) =
      some (cfg (.inl false) none source (a::reverse) out) := by
  simp only [run,Function.iterate_succ_apply,Function.iterate_zero_apply,Option.bind_some,scan_cons,reverse_push]

theorem reverse_run (code : Γ → List Δ) (source reverse : List Γ) (out : List Δ) :
    run code (2*source.length+1) (some (cfg (.inl false) none source reverse out)) =
      some (cfg (.inl true) none [] (source.reverse++reverse) out) := by
  induction source generalizing reverse with
  | nil => exact scan_nil code reverse out
  | cons a source ih =>
      rw [show 2*(a::source).length+1 = (2*source.length+1)+2 by simp; omega,
        run_add,reverse_round,ih]
      simp [List.reverse_cons,List.append_assoc]

theorem emit_round (code : Γ → List Δ) (a : Γ) (reverse : List Γ) (out : List Δ) :
    run code 2 (some (cfg (.inl true) none [] (a::reverse) out)) =
      some (cfg (.inl true) none [] reverse (code a++out)) := by
  simp only [run,Function.iterate_succ_apply,Function.iterate_zero_apply,Option.bind_some,emit_cons,emit_push]

theorem emit_run (code : Γ → List Δ) (reverse : List Γ) (out : List Δ) :
    run code (2*reverse.length+1) (some (cfg (.inl true) none [] reverse out)) =
      some (haltList (machine code) (reverse.reverse.flatMap code++out)) := by
  induction reverse generalizing out with
  | nil => exact emit_nil code out
  | cons a reverse ih =>
      rw [show 2*(a::reverse).length+1 = (2*reverse.length+1)+2 by simp; omega,
        run_add,emit_round,ih]
      simp [List.reverse_cons,List.flatMap_append,List.append_assoc]

/-- Exact execution with input and scratch stacks empty and the register reset.
The output order is preserved, even for empty or varying-length code blocks. -/
theorem exact_run (code : Γ → List Δ) (word : List Γ) :
    run code (4*word.length+2) (some (initList (machine code) word)) =
      some (haltList (machine code) (word.flatMap code)) := by
  rw [show 4*word.length+2 = (2*word.reverse.length+1)+(2*word.length+1) by simp; omega,
    run_add,init_eq,reverse_run]
  simpa only [List.append_nil,List.reverse_reverse] using emit_run code word.reverse []

/-- A genuine heterogeneous finite-alphabet transducer. Its time is proved by
the exact scan/emission runs above, independently of any output-size argument. -/
def polyTime (code : Γ → List Δ) :
    PolyTime (encodingList Γ) (encodingList Δ) (fun word => word.flatMap code) where
  tm := machine code
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 4 * Polynomial.X + Polynomial.C 2
  outputsFun word := {
    steps := 4*word.length+2
    evals_in_steps := by
      change run code (4*word.length+2) (some (initList (machine code) (word.map id))) =
        some (haltList (machine code) ((word.flatMap code).map id))
      simpa only [List.map_id] using exact_run code word
    steps_le_m := by
      change 4*word.length+2 ≤ _
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
      exact Nat.le_refl _ }
  finiteAlphabets k := by
    rcases k with b | u
    · exact inferInstanceAs (Fintype Γ)
    · exact inferInstanceAs (Fintype Δ)

/-- The finite codebook's maximum total width is a static machine constant. -/
def width (code : Γ → List Δ) : ℕ := ∑ a, (code a).length

theorem code_length_le (code : Γ → List Δ) (a : Γ) : (code a).length ≤ width code := by
  classical
  exact Finset.single_le_sum (f := fun a => (code a).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem length_le (code : Γ → List Δ) (word : List Γ) :
    (word.flatMap code).length ≤ width code * word.length := by
  induction word with
  | nil => simp
  | cons a word ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_succ]
      have h := code_length_le code a
      omega

def taggedCode (code : Γ → List Δ) : Γ ⊕ Bool → List (Δ ⊕ Bool)
  | .inl a => (code a).map Sum.inl
  | .inr bit => [.inr bit]

/-- The input is physically recoded while the witness suffix and its order are
preserved exactly. There are no extra witness bits. -/
theorem tagged_word (code : Γ → List Δ) (word : List Γ) (bits : List Bool) :
    ((word.map Sum.inl)++bits.map Sum.inr).flatMap (taggedCode code) =
      (word.flatMap code).map Sum.inl ++ bits.map Sum.inr := by
  simp only [List.flatMap_append,List.flatMap_map]
  have hw : word.flatMap (fun a => taggedCode code (.inl a)) =
      (word.flatMap code).map Sum.inl := by
    induction word with
    | nil => rfl
    | cons a rest ih =>
        rw [List.flatMap_cons,List.flatMap_cons,List.map_append,ih]
        rfl
  have hb : bits.flatMap (fun b => taggedCode code (.inr b)) = bits.map Sum.inr := by
    induction bits with
    | nil => rfl
    | cons b rest ih =>
        rw [List.flatMap_cons,List.map_cons,ih]
        rfl
  exact congrArg₂ List.append hw hb

def taggedPolyTime (code : Γ → List Δ) :
    PolyTime (encodingList (Γ ⊕ Bool)) (encodingList (Δ ⊕ Bool))
      (fun word => word.flatMap (taggedCode code)) := polyTime (taggedCode code)

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Recoding
