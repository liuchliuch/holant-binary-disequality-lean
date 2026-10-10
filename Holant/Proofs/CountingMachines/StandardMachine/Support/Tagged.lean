import Holant.Complexity.BinaryCompose.Transfer
import Holant.Complexity.FixedFieldMachines.PrimitiveCost

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. The SharpPWitness product codec is two tagged streams,
whereas the existing Boolean-stack programs read a framed graph plus a raw
witness. This file implements that conversion and structurally embeds the actual
Boolean program. Neither a decoder nor a word-valued callback is a TM2 command. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Tagged
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
open scoped BigOperators

abbrev Symbol := Bool ⊕ Bool
abbrev outputEncoding := taggedBoolEncoding Bool

variable (m : Machine)
abbrev Keys := m.K ⊕ Bool
abbrev Labels := m.Label ⊕ Fin 3
abbrev State := Option Symbol × m.State
abbrev Config := TM2.Cfg (fun _ : Keys m => Symbol) (Labels m) (State m)
abbrev Statement := TM2.Stmt (fun _ : Keys m => Symbol) (Labels m) (State m)

def source : Keys m := .inr false
def temporary : Keys m := .inr true
def destination : Keys m := .inl m.input

/-- Total scratch projection; valid embedded runs contain only right-tag bits. -/
def rightBit (o : Option Symbol) : Option Bool := o.bind Sum.getRight?

def embed : TM2.Stmt (fun _ : m.K => Bool) m.Label m.State → Statement m
  | .push k f q => .push (.inl k) (fun v => .inr (f v.2)) (embed q)
  | .pop k f q => .pop (.inl k) (fun v b => (none, f v.2 (rightBit b))) (embed q)
  | .peek k f q => .peek (.inl k) (fun v b => (none, f v.2 (rightBit b))) (embed q)
  | .load f q => .load (fun v => (none, f v.2)) (embed q)
  | .branch f a b => .branch (fun v => f v.2) (embed a) (embed b)
  | .goto f => .goto (fun v => .inl (f v.2))
  | .halt => .halt

def liftTapes (tapes : m.K → List Bool) : Keys m → List Symbol :=
  Sum.elim (fun k => (tapes k).map Sum.inr) (fun _ => [])
def liftCfg (c : m.Config) : Config m :=
  ⟨c.l.map Sum.inl, (none, c.var), liftTapes m c.stk⟩

@[simp] theorem lift_lookup (tapes : m.K → List Bool) (k : m.K) :
    liftTapes m tapes (.inl k) = (tapes k).map Sum.inr := rfl

theorem lift_update (tapes : m.K → List Bool) (k : m.K) (word : List Bool) :
    Function.update (liftTapes m tapes) (.inl k) (word.map Sum.inr) =
      liftTapes m (Function.update tapes k word) := by
  funext key
  cases key with
  | inl j => by_cases h : j = k <;> simp [liftTapes, Function.update, h]
  | inr b => simp [liftTapes, Function.update]

@[simp] theorem rightBit_head (word : List Bool) :
    rightBit ((word.map (Sum.inr : Bool → Symbol)).head?) = word.head? := by
  cases word <;> rfl

@[simp] theorem tagged_tail (word : List Bool) :
    (word.map (Sum.inr : Bool → Symbol)).tail = word.tail.map Sum.inr := by
  cases word <;> rfl

theorem tagged_reverse (word : List Bool) :
    (word.map (Sum.inr : Bool → Symbol)).reverse = word.reverse.map Sum.inr := by
  simp only [List.map_reverse]

theorem embed_stepAux (q : TM2.Stmt (fun _ : m.K => Bool) m.Label m.State)
    (v : m.State) (tapes : m.K → List Bool) :
    TM2.stepAux (embed m q) (none, v) (liftTapes m tapes) =
      liftCfg m (TM2.stepAux q v tapes) := by
  induction q generalizing v tapes with
  | push k f q ih =>
    simpa only [embed, TM2.stepAux, lift_lookup, List.map_cons,
      ← lift_update] using ih v (Function.update tapes k (f v :: tapes k))
  | pop k f q ih =>
    simpa only [embed, TM2.stepAux, lift_lookup, rightBit_head,
      tagged_tail, ← lift_update] using
      ih (f v (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | peek k f q ih =>
    simpa only [embed, TM2.stepAux, lift_lookup, rightBit_head] using
      ih (f v (tapes k).head?) tapes
  | load f q ih => simpa only [embed, TM2.stepAux] using ih (f v) tapes
  | branch f a b ha hb => cases h : f v <;> simp [embed, TM2.stepAux, h, ha, hb]
  | goto f => rfl
  | halt => rfl

theorem embed_budget (q : TM2.Stmt (fun _ : m.K => Bool) m.Label m.State) :
    TM2Cost.budget (embed m q) = TM2Cost.budget q := by
  induction q <;> simp [embed, TM2Cost.budget, *]

def reset (next : Labels m) : Statement m :=
  load (fun v => (none, v.2)) (goto (fun _ => next))

/-- One original graph symbol emits its two actual frame symbols. The first
witness symbol emits the delimiter and itself; EOF also emits a delimiter. -/
def graphStmt : Statement m :=
  pop (source m) (fun v b => (b, v.2))
    (branch (fun v => (v.1.bind Sum.getLeft?).isSome)
      (push (temporary m) (fun _ => .inr true)
        (push (temporary m) (fun v => .inr ((v.1.bind Sum.getLeft?).getD false))
          (reset m (.inr 0))))
      (branch (fun v => v.1.isSome)
        (push (temporary m) (fun _ => .inr false)
          (push (temporary m) (fun v => .inr ((rightBit v.1).getD false))
            (reset m (.inr 1))))
        (push (temporary m) (fun _ => .inr false) (reset m (.inr 2)))))

def witnessStmt : Statement m :=
  pop (source m) (fun v b => (b, v.2))
    (branch (fun v => v.1.isSome)
      (push (temporary m) (fun v => .inr ((rightBit v.1).getD false)) (reset m (.inr 1)))
      (reset m (.inr 2)))

def restoreStmt : Statement m :=
  pop (temporary m) (fun v b => (b, v.2))
    (branch (fun v => v.1.isSome)
      (push (destination m) (fun v => v.1.getD (.inr false)) (reset m (.inr 2)))
      (reset m (.inl m.main)))

def program : Labels m → Statement m
  | .inl l => embed m (m.program l)
  | .inr l => if l = 0 then graphStmt m else if l = 1 then witnessStmt m else restoreStmt m

abbrev computer : FinTM2 where
  K := Keys m
  k₀ := source m
  k₁ := .inl m.output
  Γ _ := Symbol
  Λ := Labels m
  main := .inr 0
  σ := State m
  initialState := (none, m.initial)
  m := program m

def tapes (src tmp out : List Symbol) : Keys m → List Symbol :=
  Sum.elim (fun k => if k = m.input then out else []) (fun b => if b then tmp else src)
def cfg (l : Labels m) (src tmp out : List Symbol) : Config m :=
  ⟨some l, (none, m.initial), tapes m src tmp out⟩

@[simp] theorem tapes_source (src tmp out : List Symbol) :
    tapes m src tmp out (source m) = src := rfl
@[simp] theorem tapes_temporary (src tmp out : List Symbol) :
    tapes m src tmp out (temporary m) = tmp := rfl
@[simp] theorem tapes_destination (src tmp out : List Symbol) :
    tapes m src tmp out (destination m) = out := by simp [tapes, destination]

@[simp] theorem update_source (src tmp out word : List Symbol) :
    Function.update (tapes m src tmp out) (source m) word = tapes m word tmp out := by
  funext k
  cases k with
  | inl k => simp [tapes, source, Function.update]
  | inr b => cases b <;> simp [tapes, source, Function.update]

@[simp] theorem update_temporary (src tmp out word : List Symbol) :
    Function.update (tapes m src tmp out) (temporary m) word = tapes m src word out := by
  funext k
  cases k with
  | inl k => simp [tapes, temporary, Function.update]
  | inr b => cases b <;> simp [tapes, temporary, Function.update]

@[simp] theorem update_destination (src tmp out word : List Symbol) :
    Function.update (tapes m src tmp out) (destination m) word = tapes m src tmp word := by
  funext key
  cases key with
  | inl k => by_cases h : k = m.input <;> simp [tapes, destination, Function.update, h]
  | inr b => simp [tapes, destination, Function.update]

@[simp] theorem graph_step (b : Bool) (rest tmp : List Symbol) :
    (computer m).step (cfg m (.inr 0) (.inl b :: rest) tmp []) =
      some (cfg m (.inr 0) rest (.inr b :: .inr true :: tmp) []) := by
  simp [computer, FinTM2.step, TM2.step, TM2.stepAux, program, graphStmt,
    reset, cfg] <;> rfl

@[simp] theorem boundary_step (b : Bool) (rest tmp : List Symbol) :
    (computer m).step (cfg m (.inr 0) (.inr b :: rest) tmp []) =
      some (cfg m (.inr 1) rest (.inr b :: .inr false :: tmp) []) := by
  simp [computer, FinTM2.step, TM2.step, TM2.stepAux, program, graphStmt,
    reset, rightBit, cfg] <;> rfl

@[simp] theorem graph_end_step (tmp : List Symbol) :
    (computer m).step (cfg m (.inr 0) [] tmp []) =
      some (cfg m (.inr 2) [] (.inr false :: tmp) []) := by
  simp [computer, FinTM2.step, TM2.step, TM2.stepAux, program, graphStmt,
    reset, cfg] <;> rfl

@[simp] theorem witness_step (b : Bool) (rest tmp : List Symbol) :
    (computer m).step (cfg m (.inr 1) (.inr b :: rest) tmp []) =
      some (cfg m (.inr 1) rest (.inr b :: tmp) []) := by
  simp [computer, FinTM2.step, TM2.step, TM2.stepAux, program, witnessStmt,
    reset, rightBit, cfg] <;> rfl

@[simp] theorem witness_end_step (tmp : List Symbol) :
    (computer m).step (cfg m (.inr 1) [] tmp []) = some (cfg m (.inr 2) [] tmp []) := by
  simp [computer, FinTM2.step, TM2.step, TM2.stepAux, program, witnessStmt,
    reset, cfg] <;> rfl

@[simp] theorem restore_step (b : Symbol) (rest out : List Symbol) :
    (computer m).step (cfg m (.inr 2) [] (b :: rest) out) =
      some (cfg m (.inr 2) [] rest (b :: out)) := by
  simp [computer, FinTM2.step, TM2.step, TM2.stepAux, program, restoreStmt,
    reset, cfg] <;> rfl

@[simp] theorem restore_end_step (out : List Symbol) :
    (computer m).step (cfg m (.inr 2) [] [] out) = some (cfg m (.inl m.main) [] [] out) := by
  simp [computer, FinTM2.step, TM2.step, TM2.stepAux, program, restoreStmt,
    reset, cfg] <;> rfl

def stepper := fun c : Option (Config m) => c.bind (computer m).step

theorem witness_run (w : List Bool) (tmp : List Symbol) :
    (stepper m)^[w.length + 1] (some (cfg m (.inr 1) (w.map Sum.inr) tmp [])) =
      some (cfg m (.inr 2) [] (w.reverse.map Sum.inr ++ tmp) []) := by
  induction w generalizing tmp with
  | nil => simpa [stepper] using witness_end_step m tmp
  | cons b w ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [stepper, List.map_cons, Option.bind_some, witness_step]
    simpa [List.reverse_cons, List.map_append, List.append_assoc] using ih (.inr b :: tmp)

theorem graph_run (g w : List Bool) (tmp : List Symbol) :
    (stepper m)^[g.length + w.length + 1]
      (some (cfg m (.inr 0) (g.map Sum.inl ++ w.map Sum.inr) tmp [])) =
      some (cfg m (.inr 2) []
        (((Holant.Algebraic.frame g ++ w).reverse.map Sum.inr) ++ tmp) []) := by
  induction g generalizing tmp with
  | nil =>
    cases w with
    | nil => simpa [stepper, Holant.Algebraic.frame] using graph_end_step m tmp
    | cons b w =>
      rw [List.length_nil, zero_add, List.length_cons, Function.iterate_succ_apply]
      simp only [List.map_nil, List.nil_append, List.map_cons, stepper,
        Option.bind_some, boundary_step]
      simpa [Holant.Algebraic.frame, List.reverse_cons, List.map_append,
        List.append_assoc] using witness_run m w (.inr b :: .inr false :: tmp)
  | cons b g ih =>
    have ht : (b :: g).length + w.length + 1 = (g.length + w.length + 1) + 1 := by simp; omega
    rw [ht, Function.iterate_succ_apply]
    simp only [List.map_cons, List.cons_append, stepper, Option.bind_some, graph_step]
    simpa [Holant.Algebraic.frame, List.reverse_cons, List.reverse_append,
      List.map_append, List.append_assoc] using ih (.inr b :: .inr true :: tmp)

theorem restore_run (word out : List Symbol) :
    (stepper m)^[word.length + 1] (some (cfg m (.inr 2) [] word out)) =
      some (cfg m (.inl m.main) [] [] (word.reverse ++ out)) := by
  induction word generalizing out with
  | nil => simpa [stepper] using restore_end_step m out
  | cons b word ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [stepper, Option.bind_some, restore_step]
    simpa [List.reverse_cons, List.append_assoc] using ih (b :: out)

theorem parser_start (g w : List Bool) :
    initList (computer m) (g.map Sum.inl ++ w.map Sum.inr) =
      cfg m (.inr 0) (g.map Sum.inl ++ w.map Sum.inr) [] [] := by
  simp [initList, computer, cfg, tapes, source]
  all_goals
    congr 1
    funext k
    cases k <;> simp [Function.update]
    case inr b => cases b <;> rfl

theorem parser_end (word : List Bool) :
    cfg m (.inl m.main) [] [] (word.map Sum.inr) =
      liftCfg m (initList m.computer word) := by
  rw [m.init_eq]
  simp [cfg, tapes, liftCfg, liftTapes, wordTape, Function.update]
  funext k
  cases k with
  | inl k => by_cases h : k = m.input <;> simp [h]
  | inr b => rfl

/-- Exact physical preprocessing, preserving both stream orders and resetting
all additional stacks. In particular an empty witness still emits its boundary. -/
theorem parse_exact (g w : List Bool) :
    (stepper m)^[3 * g.length + 2 * w.length + 3]
      (some (initList (computer m) (g.map Sum.inl ++ w.map Sum.inr))) =
      some (liftCfg m (initList m.computer (Holant.Algebraic.frame g ++ w))) := by
  rw [parser_start]
  have ha := graph_run m g w []
  have hb := restore_run m ((Holant.Algebraic.frame g ++ w).reverse.map Sum.inr) []
  have hlen : 3 * g.length + 2 * w.length + 3 =
      ((Holant.Algebraic.frame g ++ w).reverse.map (Sum.inr : Bool → Symbol)).length + 1 +
        (g.length + w.length + 1) := by simp; omega
  rw [hlen, Function.iterate_add_apply, ha]
  simpa only [List.append_nil,List.map_reverse,List.reverse_reverse,parser_end] using hb

theorem lift_step (c d : m.Config) (h : m.computer.step c = some d) :
    (computer m).step (liftCfg m c) = some (liftCfg m d) := by
  rcases c with ⟨l, state, tapes⟩
  cases l with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
    have hd : TM2.stepAux (m.program l) state tapes = d := Option.some.inj h
    subst d
    simp only [computer, FinTM2.step, TM2.step, liftCfg, Option.map_some, program, embed_stepAux]

theorem lift_run (c d : m.Config) (n : ℕ)
    (h : (fun q => q.bind m.computer.step)^[n] (some c) = some d) :
    (stepper m)^[n] (some (liftCfg m c)) = some (liftCfg m d) := by
  induction n generalizing d with
  | zero => cases Option.some.inj h; rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hp : (fun q => q.bind m.computer.step)^[n] (some c) with
    | none => simp only [hp, Option.bind_none] at h; cases h
    | some p =>
      have hs : m.computer.step p = some d := by simpa only [hp, Option.bind_some] using h
      rw [Function.iterate_succ_apply', ih p hp]
      exact lift_step m p d hs

theorem lift_halt (out : List Bool) :
    liftCfg m (haltList m.computer out) = haltList (computer m) (out.map Sum.inr) := by
  rw [m.halt_eq]
  simp [liftCfg, liftTapes, haltList, computer, wordTape, Function.update]
  all_goals
    congr 1
    funext k
    cases k with
    | inl k => by_cases h : k = m.output <;> simp [h]
    | inr b => rfl

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Tagged
