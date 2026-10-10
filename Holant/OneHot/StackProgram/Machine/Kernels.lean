import Holant.OneHot.StackProgram.Machine.VerifiedStages

/-! A finite family of actual opcode machines, with the exact fieldword codec.
All value operations are supplied by real Boolean-stack programs. -/
namespace Holant.OneHot.StackProgram.Machine.Kernels
open Turing Computability Holant.Complexity StackProtocol

variable {A V : Type} [CommSemiring V]

/-- The three sources of literal words are fixed before execution. -/
structure Literals (e : Encoding V Bool) (coeff : A → V) where
  table : Constants.Table A V e coeff
  zeroWord : List Bool
  oneWord : List Bool
  zero_correct : zeroWord = e.encode 0
  one_correct : oneWord = e.encode 1

abbrev literalMachine (word : List Bool) : BinaryCompose.Machine :=
  Constants.machine (fun _ : Fin 1 => word) 0

/-- Every branch is a finite machine; no semantic field operation is a callback. -/
abbrev machine {e : Encoding V Bool} {coeff : A → V}
    (lits : Literals e coeff) (providers : Operator.Providers e) : Op A → BinaryCompose.Machine
  | .literal a => literalMachine (lits.table.words a)
  | .zero => literalMachine lits.zeroWord
  | .one => literalMachine lits.oneWord
  | .copy i => Rearrange.machine (Rearrange.copyCode i)
  | .erase i => Rearrange.machine (Rearrange.eraseCode i)
  | .swap => Rearrange.machine Rearrange.swapCode
  | .add => Operator.machine providers.add.machine
  | .mul => Operator.machine providers.mul.machine

/-- The fixed-degree bound charges provider execution and every bit-level wrapper. -/
def timeBound {e : Encoding V Bool} (providers : Operator.Providers e) (W : ℕ) : ℕ :=
  providers.add.time.eval (3 * W + 1) + providers.mul.time.eval (3 * W + 1) +
    14 * W + 18 + (2 * W + 4) * 2 ^ 18 + 3

/-- Exact clean execution, also for machines with arbitrary finite state type. -/
def Executes (m : BinaryCompose.Machine) (input output : List Bool) (time : ℕ) : Prop :=
  (fun c => c.bind m.computer.step)^[time] (some (initList m.computer input)) =
    some (haltList m.computer output)

omit [CommSemiring V] in
private theorem literal_exact (e : Encoding V Bool) (word : List Bool) (v : V)
    (hv : word = e.encode v) (s : List V) :
    RunsExactly (literalMachine word).computer.step
      (initList (literalMachine word).computer ((stackEncoding e).encode s))
      (haltList (literalMachine word).computer ((stackEncoding e).encode (v :: s))) 2 := by
  simpa only [hv, stackEncoding, framedListEncoding, framedListEncode, List.cons_append] using
    Constants.machine_exact (fun _ : Fin 1 => word) 0 ((stackEncoding e).encode s)

omit [CommSemiring V] in
private theorem swap_encoded (e : Encoding V Bool) (x y : V) (s : List V) (W : ℕ)
    (hs : ∀ v ∈ x :: y :: s, (e.encode v).length ≤ W) :
    ∃ time, time ≤ (2 * W + 4) * 2 ^ 18 + 1 ∧
      RunsExactly (Rearrange.machine Rearrange.swapCode).computer.step
        (initList (Rearrange.machine Rearrange.swapCode).computer
          ((stackEncoding e).encode (x :: y :: s)))
        (haltList (Rearrange.machine Rearrange.swapCode).computer
          ((stackEncoding e).encode (y :: x :: s))) time := by
  have hw : ∀ w ∈ e.encode x :: e.encode y :: s.map e.encode, w.length ≤ W := by
    intro w hw
    have : w ∈ (x :: y :: s).map e.encode := hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp this
    exact hs v hv
  obtain ⟨time, ht, hr⟩ := Rearrange.swap_exact_bound (e.encode x) (e.encode y) (s.map e.encode) W hw
  refine ⟨time, ht, ?_⟩
  simpa only [← List.map_cons, Rearrange.stackEncoding_map] using hr

/-- Uniform clean success simulation. The width bound includes both boundary
stacks; arithmetic operands and results therefore all satisfy the provider bound. -/
theorem run_exact (e : Encoding V Bool) (coeff : A → V)
    (lits : Literals e coeff) (providers : Operator.Providers e)
    (op : Op A) (s t event : List V) (h : step coeff op s = some (t, event))
    (W : ℕ) (hs : ∀ v ∈ s, (e.encode v).length ≤ W)
    (ht : ∀ v ∈ t, (e.encode v).length ≤ W) :
    ∃ time, time ≤ timeBound providers W ∧
      Executes (machine lits providers op) ((stackEncoding e).encode s)
        ((stackEncoding e).encode t) time := by
  cases op with
  | literal a =>
    cases Option.some.inj h
    exact ⟨2, by simp [timeBound],
      literal_exact e _ _ (lits.table.correct a) s⟩
  | zero =>
    cases Option.some.inj h
    exact ⟨2, by simp [timeBound], literal_exact e _ _ lits.zero_correct s⟩
  | one =>
    cases Option.some.inj h
    exact ⟨2, by simp [timeBound], literal_exact e _ _ lits.one_correct s⟩
  | copy i =>
    cases hh : s[i.val]? with
    | none => simp [step, hh] at h
    | some x =>
      have hp : (x :: s, []) = (t, event) := by simpa [step, hh] using h
      cases hp
      obtain ⟨time, hb, hr⟩ := Rearrange.copy_encoded e i s x hh W hs
      exact ⟨time, by dsimp [timeBound]; omega, hr⟩
  | erase i =>
    cases hh : eraseAt i.val s with
    | none => simp [step, hh] at h
    | some u =>
      have hp : (u, []) = (t, event) := by simpa [step, hh] using h
      cases hp
      obtain ⟨time, hb, hr⟩ := Rearrange.erase_encoded e i s t hh W hs
      exact ⟨time, by dsimp [timeBound]; omega, hr⟩
  | swap =>
    cases s with
    | nil => simp [step] at h
    | cons x s =>
      cases s with
      | nil => simp [step] at h
      | cons y s =>
        cases Option.some.inj h
        obtain ⟨time, hb, hr⟩ := swap_encoded e x y s W hs
        exact ⟨time, by dsimp [timeBound]; omega, hr⟩
  | add =>
    cases s with
    | nil => simp [step] at h
    | cons x s =>
      cases s with
      | nil => simp [step] at h
      | cons y s =>
        cases Option.some.inj h
        let hr := Operator.provider_timed e _ providers.add x y s W
          (hs x (by simp)) (hs y (by simp)) (ht _ (by simp))
        refine ⟨hr.steps, le_trans hr.steps_le_m (by dsimp [timeBound]; omega), ?_⟩
        exact hr.evals_in_steps
  | mul =>
    cases s with
    | nil => simp [step] at h
    | cons x s =>
      cases s with
      | nil => simp [step] at h
      | cons y s =>
        cases Option.some.inj h
        let hr := Operator.provider_timed e _ providers.mul x y s W
          (hs x (by simp)) (hs y (by simp)) (ht _ (by simp))
        refine ⟨hr.steps, le_trans hr.steps_le_m (by dsimp [timeBound]; omega), ?_⟩
        exact hr.evals_in_steps

end Holant.OneHot.StackProgram.Machine.Kernels
