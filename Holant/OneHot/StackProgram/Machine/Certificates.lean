import Holant.OneHot.StackProgram.Machine.RearrangeMacros

/-! Bounds on every stack boundary of an actual execution. Initial words,
literal-table words, zero and one are explicit hypotheses alongside the ordered
arithmetic trace. Code length alone is deliberately not a word-size bound. -/
namespace Holant.OneHot.StackProgram.Machine
open Computability

variable {A V : Type} [CommSemiring V]

omit [CommSemiring V] in
theorem eraseAt_sublist {n : ℕ} {s t : List V} (h : eraseAt n s = some t) :
    t.Sublist s := by
  obtain ⟨pre, x, tail, rfl, rfl⟩ := Rearrange.erase_prefix n s t h
  exact (List.Sublist.cons x (List.Sublist.refl tail)).append_left _

/-- A single opcode introduces values only from fixed literals or its own event. -/
theorem step_preserves (coeff : A → V) (P : V → Prop)
    (hc : ∀ a, P (coeff a)) (hzero : P 0) (hone : P 1)
    (op : Op A) (s t event : List V) (h : step coeff op s = some (t, event))
    (hs : ∀ x ∈ s, P x) (he : ∀ x ∈ event, P x) : ∀ x ∈ t, P x := by
  cases op with
  | literal a => cases Option.some.inj h; simpa using And.intro (hc a) hs
  | zero => cases Option.some.inj h; simpa using And.intro hzero hs
  | one => cases Option.some.inj h; simpa using And.intro hone hs
  | copy i =>
    cases hg : s[i.val]? with
    | none => simp [step, hg] at h
    | some x =>
      have ht : (x :: s, []) = (t, event) := by simpa [step, hg] using h
      cases ht
      simpa using And.intro (hs x (List.mem_of_getElem? hg)) hs
  | erase i =>
    cases hh : eraseAt i.val s with
    | none => simp [step, hh] at h
    | some u =>
      have ht : (u, []) = (t, event) := by simpa [step, hh] using h
      cases ht
      exact fun x hx => hs x ((eraseAt_sublist hh).subset hx)
  | swap =>
    cases s with
    | nil => simp [step] at h
    | cons x s =>
      cases s with
      | nil => simp [step] at h
      | cons y s =>
        cases Option.some.inj h
        simpa only [List.mem_cons, forall_eq_or_imp] using
          And.intro (hs y (by simp)) (And.intro (hs x (by simp)) (fun z hz => hs z (by simp [hz])))
  | add | mul =>
    cases s with
    | nil => simp [step] at h
    | cons x s =>
      cases s with
      | nil => simp [step] at h
      | cons y s =>
        cases Option.some.inj h
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact he _ (by simp)
        · exact hs z (by simp [hz])

theorem step_height (coeff : A → V) (op : Op A) (s t event : List V)
    (h : step coeff op s = some (t, event)) : t.length ≤ s.length + 1 := by
  cases op with
  | literal a | zero | one => cases Option.some.inj h; simp
  | copy i =>
    cases hg : s[i.val]? with
    | none => simp [step, hg] at h
    | some x =>
      have ht : (x :: s, []) = (t, event) := by simpa [step, hg] using h
      cases ht; simp
  | erase i =>
    cases hh : eraseAt i.val s with
    | none => simp [step, hh] at h
    | some u =>
      have ht : (u, []) = (t, event) := by simpa [step, hh] using h
      cases ht
      exact le_trans (eraseAt_sublist hh).length_le (Nat.le_succ _)
  | swap | add | mul =>
    cases s with
    | nil => simp [step] at h
    | cons x s =>
      cases s with
      | nil => simp [step] at h
      | cons y s => cases Option.some.inj h; simp

/-- A proof-only execution certificate for the actual semantic run. The finite
machine neither carries these lists as control state nor calls this relation. -/
inductive Certified (e : Encoding V Bool) (coeff : A → V) (W H : ℕ) :
    Code A → List V → List V → List V → Prop
  | nil (s) (width : ∀ x ∈ s, (e.encode x).length ≤ W) (height : s.length ≤ H) :
      Certified e coeff W H [] s s []
  | cons (op code s mid out event trace)
      (exec : step coeff op s = some (mid, event))
      (width : ∀ x ∈ s, (e.encode x).length ≤ W)
      (height : s.length ≤ H)
      (next : Certified e coeff W H code mid out trace) :
      Certified e coeff W H (op :: code) s out (event ++ trace)

theorem Certified.input_width {e : Encoding V Bool} {coeff : A → V} {W H : ℕ}
    {code : Code A} {s out trace : List V} (h : Certified e coeff W H code s out trace) :
    ∀ x ∈ s, (e.encode x).length ≤ W := by
  cases h <;> assumption

theorem Certified.input_height {e : Encoding V Bool} {coeff : A → V} {W H : ℕ}
    {code : Code A} {s out trace : List V} (h : Certified e coeff W H code s out trace) :
    s.length ≤ H := by
  cases h <;> assumption

theorem Certified.output_width {e : Encoding V Bool} {coeff : A → V} {W H : ℕ}
    {code : Code A} {s out trace : List V} (h : Certified e coeff W H code s out trace) :
    ∀ x ∈ out, (e.encode x).length ≤ W := by
  induction h <;> assumption

/-- The exact trace, together with fixed and initial word bounds, certifies every
intermediate stack; the height grows by at most one per executed instruction. -/
theorem certified_of_run (e : Encoding V Bool) (coeff : A → V) (W H : ℕ)
    (hc : ∀ a, (e.encode (coeff a)).length ≤ W)
    (hzero : (e.encode 0).length ≤ W) (hone : (e.encode 1).length ≤ W)
    (code : Code A) (s out trace : List V)
    (hr : run coeff code s = some (out, trace))
    (hs : ∀ x ∈ s, (e.encode x).length ≤ W)
    (ht : ∀ x ∈ trace, (e.encode x).length ≤ W)
    (hh : s.length + code.length ≤ H) : Certified e coeff W H code s out trace := by
  induction code generalizing s out trace with
  | nil =>
    have hpair : (s, []) = (out, trace) := Option.some.inj hr
    cases hpair
    exact .nil s hs (by simpa using hh)
  | cons op code ih =>
    cases hp : step coeff op s with
    | none => simp [run, hp] at hr
    | some p =>
      rcases p with ⟨mid, event⟩
      cases hq : run coeff code mid with
      | none => simp [run, hp, hq] at hr
      | some q =>
        rcases q with ⟨out', trace'⟩
        have hpair : (out', event ++ trace') = (out, trace) := by
          simpa [run, hp, hq] using hr
        cases hpair
        have hev : ∀ x ∈ event, (e.encode x).length ≤ W := fun x hx => ht x (by simp [hx])
        have htr : ∀ x ∈ trace', (e.encode x).length ≤ W := fun x hx => ht x (by simp [hx])
        have hm := step_preserves coeff (fun x => (e.encode x).length ≤ W)
          hc hzero hone op s mid event hp hs hev
        have hheight := step_height coeff op s mid event hp
        exact .cons op code s mid out event trace' hp hs (by simp at hh; omega)
          (ih mid out trace' hq hm htr (by simp at hh; omega))

omit [CommSemiring V] in
/-- Physical framed-stack length, including every marker and the terminator. -/
theorem stack_bits_le (e : Encoding V Bool) (s : List V) (W : ℕ)
    (h : ∀ x ∈ s, (e.encode x).length ≤ W) :
    ((stackEncoding e).encode s).length ≤ (2 * W + 2) * s.length + 1 := by
  induction s with
  | nil => simp [stackEncoding, Holant.Complexity.framedListEncoding,
      Holant.Complexity.framedListEncode]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hi := ih (fun y hy => h y (by simp [hy]))
    simp only [stackEncoding, Holant.Complexity.framedListEncoding,
      Holant.Complexity.framedListEncode, List.length_cons, List.length_append,
      Holant.Algebraic.frame_length] at hi ⊢
    nlinarith

end Holant.OneHot.StackProgram.Machine
