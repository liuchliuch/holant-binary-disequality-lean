import Holant.OneHot.StackProgram.Machine.Rearrange
import Mathlib.Data.List.OfFn

/-! The fixed microcode actually implements every Fin8 copy/erase index and swap.
The proofs compare whole successful raw-word stacks and cleaned work buffers,
then invoke the concrete finite-machine execution theorem. -/
namespace Holant.OneHot.StackProgram.Machine.Rearrange
open Turing Computability Holant.Complexity StackProtocol

set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

/-- All eight cases share the same finite microinstruction compiler. -/
theorem copyCode_words (i : Fin 8) (words : Fin (i.val + 1) → List Bool) (tail : List (List Bool)) :
    (run (copyCode i) (clean (List.ofFn words ++ tail))).map Prod.fst =
      some (clean (words ⟨i.val, by omega⟩ :: (List.ofFn words ++ tail))) := by
  fin_cases i <;>
    simp [copyCode, slots, List.finRange, List.ofFn_succ, run, step, clean]
  all_goals
    funext j
    fin_cases j <;> rfl

theorem eraseCode_words (i : Fin 8) (words : Fin (i.val + 1) → List Bool) (tail : List (List Bool)) :
    (run (eraseCode i) (clean (List.ofFn words ++ tail))).map Prod.fst =
      some (clean (List.ofFn (fun j : Fin i.val => words j.castSucc) ++ tail)) := by
  fin_cases i <;>
    simp [eraseCode, slots, List.finRange, List.ofFn_succ, run, step, clean]
  all_goals
    funext j
    fin_cases j <;> rfl

theorem swapCode_words (x y : List Bool) (tail : List (List Bool)) :
    (run swapCode (clean (x :: y :: tail))).map Prod.fst = some (clean (y :: x :: tail)) := by
  simp [swapCode, run, step, clean]
  funext j
  fin_cases j <;> rfl

/-- No assumption about a machine cost is used: it follows from literal loops.
The fixed bound eighteen is the largest of the Fin8 microprogram sizes. -/
theorem clean_exact_bound (code : List Micro) (hlen : code.length ≤ 18)
    (s t : List (List Bool)) (W : ℕ) (hwords : ∀ word ∈ s, word.length ≤ W)
    (h : (run code (clean s)).map Prod.fst = some (clean t)) :
    ∃ time, time ≤ (2 * W + 4) * 2 ^ 18 + 1 ∧
      RunsExactly (machine code).computer.step
        (initList (machine code).computer ((stackEncoding wordEncoding).encode s))
        (haltList (machine code).computer ((stackEncoding wordEncoding).encode t)) time := by
  cases hr : run code (clean s) with
  | none => simp [hr] at h
  | some pair =>
    rcases pair with ⟨d, time⟩
    have hd : d = clean t := by simpa [hr] using h
    subst d
    have hsmall : Small W (clean s) := by
      exact ⟨hwords, fun _ => Nat.zero_le _⟩
    have ht := run_time_le code (clean s) (clean t) time W hsmall hr
    have hp := Nat.mul_le_mul_left (2 * W + 4) (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hlen)
    refine ⟨time + 1, by omega, run_clean_exact code s t time hr⟩

/-- Fieldword encodings are preserved literally when viewed as raw-word stacks. -/
theorem stackEncoding_map {V : Type} (e : Encoding V Bool) (s : List V) :
    (stackEncoding wordEncoding).encode (s.map e.encode) = (stackEncoding e).encode s := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    simpa [stackEncoding, framedListEncoding, framedListEncode, wordEncoding] using
      (congrArg (fun bits => true :: (Holant.Algebraic.frame (e.encode x) ++ bits)) ih)

/-- Copy reaches a clean halt through real finite Boolean instructions. -/
theorem copy_exact_bound (i : Fin 8) (words : Fin (i.val + 1) → List Bool)
    (tail : List (List Bool)) (W : ℕ)
    (hwords : ∀ word ∈ List.ofFn words ++ tail, word.length ≤ W) :
    ∃ time, time ≤ (2 * W + 4) * 2 ^ 18 + 1 ∧
      RunsExactly (machine (copyCode i)).computer.step
        (initList (machine (copyCode i)).computer
          ((stackEncoding wordEncoding).encode (List.ofFn words ++ tail)))
        (haltList (machine (copyCode i)).computer
          ((stackEncoding wordEncoding).encode
            (words ⟨i.val, by omega⟩ :: (List.ofFn words ++ tail)))) time :=
  clean_exact_bound _ (rearrangement_microinstructions_le i).1 _ _ W hwords
    (copyCode_words i words tail)

/-- Erase has the same uniform fixed-macro bound and leaves every buffer empty. -/
theorem erase_exact_bound (i : Fin 8) (words : Fin (i.val + 1) → List Bool)
    (tail : List (List Bool)) (W : ℕ)
    (hwords : ∀ word ∈ List.ofFn words ++ tail, word.length ≤ W) :
    ∃ time, time ≤ (2 * W + 4) * 2 ^ 18 + 1 ∧
      RunsExactly (machine (eraseCode i)).computer.step
        (initList (machine (eraseCode i)).computer
          ((stackEncoding wordEncoding).encode (List.ofFn words ++ tail)))
        (haltList (machine (eraseCode i)).computer
          ((stackEncoding wordEncoding).encode
            (List.ofFn (fun j : Fin i.val => words j.castSucc) ++ tail))) time :=
  clean_exact_bound _ (le_trans (rearrangement_microinstructions_le i).2 (by decide)) _ _ W hwords
    (eraseCode_words i words tail)

/-- Swap is the four-stage real pop/pop/push/push microprogram. -/
theorem swap_exact_bound (x y : List Bool) (tail : List (List Bool)) (W : ℕ)
    (hwords : ∀ word ∈ x :: y :: tail, word.length ≤ W) :
    ∃ time, time ≤ (2 * W + 4) * 2 ^ 18 + 1 ∧
      RunsExactly (machine swapCode).computer.step
        (initList (machine swapCode).computer ((stackEncoding wordEncoding).encode (x :: y :: tail)))
        (haltList (machine swapCode).computer ((stackEncoding wordEncoding).encode (y :: x :: tail))) time :=
  clean_exact_bound _ (by decide) _ _ W hwords (swapCode_words x y tail)

/-- A successful bounded lookup exposes its literal list prefix. -/
theorem lookup_prefix {V : Type} (n : ℕ) (s : List V) (x : V) (h : s[n]? = some x) :
    ∃ pre : Fin n → V, ∃ tail : List V, s = List.ofFn pre ++ x :: tail := by
  induction n generalizing s with
  | zero =>
    cases s with
    | nil => simp at h
    | cons y ys =>
      have hy : y = x := Option.some.inj h
      subst y
      exact ⟨Fin.elim0, ys, rfl⟩
  | succ n ih =>
    cases s with
    | nil => simp at h
    | cons y ys =>
      obtain ⟨pre, tail, ht⟩ := ih ys h
      refine ⟨Fin.cons y pre, tail, ?_⟩
      simp [List.ofFn_succ, ht]

/-- Every fieldword keeps the exact given codec throughout bounded copy. -/
theorem copy_encoded {V : Type} (e : Encoding V Bool) (i : Fin 8) (s : List V) (x : V)
    (hget : s[i.val]? = some x) (W : ℕ) (hwords : ∀ v ∈ s, (e.encode v).length ≤ W) :
    ∃ time, time ≤ (2 * W + 4) * 2 ^ 18 + 1 ∧
      RunsExactly (machine (copyCode i)).computer.step
        (initList (machine (copyCode i)).computer ((stackEncoding e).encode s))
        (haltList (machine (copyCode i)).computer ((stackEncoding e).encode (x :: s))) time := by
  obtain ⟨pre, tail, hs⟩ := lookup_prefix i.val s x hget
  let words : Fin (i.val + 1) → List Bool := fun j => e.encode (Fin.snoc (α := fun _ => V) pre x j)
  have hraw : List.ofFn words ++ tail.map e.encode = s.map e.encode := by
    rw [List.ofFn_succ' words]
    simp only [words, Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, hs,
      List.map_append, List.map_cons, List.map_ofFn, List.append_assoc, List.singleton_append, Function.comp_def]
  have hsmall : ∀ word ∈ List.ofFn words ++ tail.map e.encode, word.length ≤ W := by
    rw [hraw]
    intro word hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    exact hwords v hv
  obtain ⟨time, ht, hr⟩ := copy_exact_bound i words (tail.map e.encode) W hsmall
  refine ⟨time, ht, ?_⟩
  rw [hraw] at hr
  have hx : words ⟨i.val, by omega⟩ = e.encode x := by
    change e.encode (Fin.snoc (α := fun _ => V) pre x (Fin.last i.val)) = _
    rw [Fin.snoc_last]
  rw [hx] at hr
  simpa only [← List.map_cons, stackEncoding_map] using hr

/-- Erasing a present element exposes the same prefix before and after deletion. -/
theorem erase_prefix {V : Type} (n : ℕ) (s t : List V) (h : eraseAt n s = some t) :
    ∃ pre : Fin n → V, ∃ x : V, ∃ tail : List V,
      s = List.ofFn pre ++ x :: tail ∧ t = List.ofFn pre ++ tail := by
  induction n generalizing s t with
  | zero =>
    cases s with
    | nil => simp [eraseAt] at h
    | cons x xs =>
      cases Option.some.inj h
      exact ⟨Fin.elim0, x, t, rfl, rfl⟩
  | succ n ih =>
    cases s with
    | nil => simp [eraseAt] at h
    | cons y ys =>
      cases hh : eraseAt n ys with
      | none => simp [eraseAt, hh] at h
      | some tail' =>
        have ht : y :: tail' = t := by simpa [eraseAt, hh] using h
        subst t
        obtain ⟨pre, x, tail, hs, ht⟩ := ih ys tail' hh
        refine ⟨Fin.cons y pre, x, tail, ?_, ?_⟩ <;> simp [List.ofFn_succ, hs, ht]

theorem erase_encoded {V : Type} (e : Encoding V Bool) (i : Fin 8) (s t : List V)
    (herase : eraseAt i.val s = some t) (W : ℕ) (hwords : ∀ v ∈ s, (e.encode v).length ≤ W) :
    ∃ time, time ≤ (2 * W + 4) * 2 ^ 18 + 1 ∧
      RunsExactly (machine (eraseCode i)).computer.step
        (initList (machine (eraseCode i)).computer ((stackEncoding e).encode s))
        (haltList (machine (eraseCode i)).computer ((stackEncoding e).encode t)) time := by
  obtain ⟨pre, x, tail, hs, ht⟩ := erase_prefix i.val s t herase
  let words : Fin (i.val + 1) → List Bool := fun j => e.encode (Fin.snoc (α := fun _ => V) pre x j)
  have hraw : List.ofFn words ++ tail.map e.encode = s.map e.encode := by
    rw [List.ofFn_succ' words]
    simp only [words, Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, hs,
      List.map_append, List.map_cons, List.map_ofFn, List.append_assoc, List.singleton_append, Function.comp_def]
  have hsmall : ∀ word ∈ List.ofFn words ++ tail.map e.encode, word.length ≤ W := by
    rw [hraw]
    intro word hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    exact hwords v hv
  obtain ⟨time, htime, hr⟩ := erase_exact_bound i words (tail.map e.encode) W hsmall
  refine ⟨time, htime, ?_⟩
  have hout : List.ofFn (fun j : Fin i.val => words j.castSucc) ++ tail.map e.encode = t.map e.encode := by
    simp [words, ht, List.map_append, List.map_ofFn, Function.comp_def]
  rw [hraw, hout] at hr
  simpa only [stackEncoding_map] using hr

end Holant.OneHot.StackProgram.Machine.Rearrange
