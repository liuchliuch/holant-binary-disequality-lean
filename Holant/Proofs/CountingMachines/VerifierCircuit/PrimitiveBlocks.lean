import Holant.Proofs.CountingMachines.VerifierCircuit.BitLayout

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
# Actual NAND blocks for bounded-stack primitives

Ported reference proof. See the task validation reports.

Copies and shifts route existing registers. Only fixed finite-control tables,
fixed empty-cell bits and per-coordinate multiplexers emit new gates.
-/

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.PrimitiveBlocks


open Turing BitLayout
open scoped Classical
private theorem denotes_value_congr {I O : Type} {p : Emit I O}
    {f g : (I → Bool) → (O → Bool)} (h : Emit.Denotes p f)
    (he : ∀ x o, f x o = g x o) : Emit.Denotes p g := by
  have hf : f = g := funext (fun x => funext (he x))
  rw [← hf]
  exact h

variable (tm : FinTM2) (C : ℕ) [∀ k, Fintype (tm.Γ k)]

abbrev Addr := Address tm C

def stateRoute : tm.σ → Addr tm C := stateAddr tm C
def headRoute (k : tm.K) : tm.σ ⊕ Option (tm.Γ k) → Addr tm C :=
  Sum.elim (stateAddr tm C) (cellAddr tm C k 0)

def stateOutput : Addr tm C → Addr tm C ⊕ tm.σ
  | .inr (.inl s) => .inr s
  | a => .inl a

def labelOutput : Addr tm C → Addr tm C ⊕ Option tm.Λ
  | .inl l => .inr l
  | a => .inl a

def pushOutput (k : tm.K) : Addr tm C → Addr tm C ⊕ Option (tm.Γ k)
  | .inr (.inr ⟨j, i, a⟩) =>
    if h : j = k then
      if hi : i.val = 0 then .inr (h ▸ a)
      else .inl (cellAddr tm C j ⟨i.val - 1, by omega⟩ a)
    else .inl (cellAddr tm C j i a)
  | a => .inl a

def popOutput (k : tm.K) : Addr tm C → Addr tm C ⊕ Option (tm.Γ k)
  | .inr (.inr ⟨j, i, a⟩) =>
    if h : j = k then
      if hi : i.val + 1 < C + 1 then .inl (cellAddr tm C j ⟨i.val + 1, hi⟩ a)
      else .inr (h ▸ a)
    else .inl (cellAddr tm C j i a)
  | a => .inl a

def load (f : tm.σ → tm.σ) : Emit (Addr tm C) (Addr tm C) :=
  Emit.renameOutput (Emit.parallel (Emit.id _) (Emit.renameInput (stateRoute tm C) (Emit.table f)))
    (stateOutput tm C)

def loadValue (f : tm.σ → tm.σ) (x : Bits tm C) : Bits tm C :=
  replaceState tm C x (Emit.tableValue f (fun s => x (stateAddr tm C s)))

theorem load_denotes (f : tm.σ → tm.σ) : Emit.Denotes (load tm C f) (loadValue tm C f) := by
  have h := Emit.renameOutput_denotes
    (Emit.parallel_denotes (Emit.route_denotes (fun a : Addr tm C => a))
      (Emit.renameInput_denotes (stateRoute tm C) (Emit.table_denotes f))) (stateOutput tm C)
  refine denotes_value_congr h ?_
  intro x a
  cases a with
  | inl a => rfl
  | inr a => cases a <;> rfl

theorem load_encode (f : tm.σ → tm.σ) (p : PackedStep.Packed tm C) :
    loadValue tm C f (encode tm C p) = encode tm C (PackedStep.state tm C p (f p.2.1)) := by
  unfold loadValue
  change replaceState tm C (encode tm C p) (Emit.tableValue f (oneHot p.2.1)) = _
  rw [Emit.tableValue_oneHot]
  exact replaceState_encode tm C p _

def readState (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) : Emit (Addr tm C) (Addr tm C) :=
  Emit.renameOutput (Emit.parallel (Emit.id _) (Emit.renameInput (headRoute tm C k) (Emit.table₂ f)))
    (stateOutput tm C)

def readStateValue (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) (x : Bits tm C) : Bits tm C :=
  replaceState tm C x (Emit.tableValue (fun sa : tm.σ × Option (tm.Γ k) => f sa.1 sa.2)
    (fun sa => x (stateAddr tm C sa.1) && x (cellAddr tm C k 0 sa.2)))

theorem readState_denotes (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) :
    Emit.Denotes (readState tm C k f) (readStateValue tm C k f) := by
  have h := Emit.renameOutput_denotes
    (Emit.parallel_denotes (Emit.route_denotes (fun a : Addr tm C => a))
      (Emit.renameInput_denotes (headRoute tm C k) (Emit.table₂_denotes f))) (stateOutput tm C)
  refine denotes_value_congr h ?_
  intro x a
  cases a with
  | inl a => rfl
  | inr a => cases a <;> rfl

theorem readState_encode (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ)
    (p : PackedStep.Packed tm C) :
    readStateValue tm C k f (encode tm C p) =
      encode tm C (PackedStep.state tm C p (f p.2.1 (PackedStep.head tm C p k))) := by
  unfold readStateValue
  have hpair : (fun sa : tm.σ × Option (tm.Γ k) =>
      encode tm C p (stateAddr tm C sa.1) && encode tm C p (cellAddr tm C k 0 sa.2)) =
        oneHot (p.2.1, PackedStep.head tm C p k) := by
    funext sa
    rcases sa with ⟨s, a⟩
    by_cases hs : p.2.1 = s <;> by_cases ha : p.2.2 k 0 = a <;>
      simp [encode, stateAddr, cellAddr, PackedStep.head, oneHot, hs, ha]
  rw [hpair, Emit.tableValue_oneHot]
  exact replaceState_encode tm C p _

def push (k : tm.K) (f : tm.σ → tm.Γ k) : Emit (Addr tm C) (Addr tm C) :=
  Emit.renameOutput (Emit.parallel (Emit.id _)
    (Emit.renameInput (stateRoute tm C) (Emit.table (fun s => some (f s))))) (pushOutput tm C k)

def pushValue (k : tm.K) (f : tm.σ → tm.Γ k) (x : Bits tm C) : Bits tm C :=
  replacePush tm C x k (Emit.tableValue (fun s => some (f s)) (fun s => x (stateAddr tm C s)))

theorem push_denotes (k : tm.K) (f : tm.σ → tm.Γ k) :
    Emit.Denotes (push tm C k f) (pushValue tm C k f) := by
  have h := Emit.renameOutput_denotes (Emit.parallel_denotes
    (Emit.route_denotes (fun a : Addr tm C => a))
    (Emit.renameInput_denotes (stateRoute tm C) (Emit.table_denotes (fun s => some (f s)))))
      (pushOutput tm C k)
  refine denotes_value_congr h ?_
  intro x a
  cases a with
  | inl a => rfl
  | inr a =>
    cases a with
    | inl a => rfl
    | inr a =>
      rcases a with ⟨j, i, a⟩
      by_cases hj : j = k
      · subst j
        by_cases hi : i.val = 0 <;> simp [pushValue, replacePush, pushOutput, stateRoute, hi]
      · simp [pushValue, replacePush, pushOutput, stateRoute, hj]

theorem push_encode (k : tm.K) (f : tm.σ → tm.Γ k) (p : PackedStep.Packed tm C) :
    pushValue tm C k f (encode tm C p) = encode tm C (PackedStep.push tm C p k (f p.2.1)) := by
  unfold pushValue
  change replacePush tm C (encode tm C p) k (Emit.tableValue _ (oneHot p.2.1)) = _
  rw [Emit.tableValue_oneHot]
  exact replacePush_encode tm C p k _

def emptyCell (k : tm.K) : Emit (Addr tm C) (Option (tm.Γ k)) :=
  Emit.tabulate (fixedEnum (Option (tm.Γ k))) mem_fixedEnum
    (fun a => Emit.constant (oneHot (none : Option (tm.Γ k)) a))

theorem emptyCell_denotes (k : tm.K) :
    Emit.Denotes (emptyCell tm C k) (fun _ => oneHot (none : Option (tm.Γ k))) :=
  Emit.tabulate_denotes _ _ _ _ (fun _ => Emit.constant_denotes _)

def pop (k : tm.K) : Emit (Addr tm C) (Addr tm C) :=
  Emit.renameOutput (Emit.parallel (Emit.id _) (emptyCell tm C k)) (popOutput tm C k)

theorem pop_denotes (k : tm.K) : Emit.Denotes (pop tm C k) (fun x => replacePop tm C x k) := by
  have h := Emit.renameOutput_denotes
    (Emit.parallel_denotes (Emit.route_denotes (fun a : Addr tm C => a)) (emptyCell_denotes tm C k))
      (popOutput tm C k)
  refine denotes_value_congr h ?_
  intro x a
  cases a with
  | inl a => rfl
  | inr a =>
    cases a with
    | inl a => rfl
    | inr a =>
      rcases a with ⟨j, i, a⟩
      by_cases hj : j = k
      · subst j
        by_cases hi : i.val + 1 < C + 1 <;> simp [replacePop, popOutput, hi]
      · simp [replacePop, popOutput, hj]

def goto (f : tm.σ → tm.Λ) : Emit (Addr tm C) (Addr tm C) :=
  Emit.renameOutput (Emit.parallel (Emit.id _)
    (Emit.renameInput (stateRoute tm C) (Emit.table (fun s => some (f s))))) (labelOutput tm C)

def gotoValue (f : tm.σ → tm.Λ) (x : Bits tm C) : Bits tm C :=
  replaceLabel tm C x (Emit.tableValue (fun s => some (f s)) (fun s => x (stateAddr tm C s)))

theorem goto_denotes (f : tm.σ → tm.Λ) : Emit.Denotes (goto tm C f) (gotoValue tm C f) := by
  have h := Emit.renameOutput_denotes (Emit.parallel_denotes (Emit.route_denotes (fun a : Addr tm C => a))
    (Emit.renameInput_denotes (stateRoute tm C) (Emit.table_denotes (fun s => some (f s)))))
      (labelOutput tm C)
  refine denotes_value_congr h ?_
  intro x a
  cases a with
  | inl a => rfl
  | inr a => cases a <;> rfl

theorem goto_encode (f : tm.σ → tm.Λ) (p : PackedStep.Packed tm C) :
    gotoValue tm C f (encode tm C p) = encode tm C (PackedStep.label tm C p (some (f p.2.1))) := by
  unfold gotoValue
  change replaceLabel tm C (encode tm C p) (Emit.tableValue _ (oneHot p.2.1)) = _
  rw [Emit.tableValue_oneHot]
  exact replaceLabel_encode tm C p _

def halt : Emit (Addr tm C) (Addr tm C) :=
  Emit.renameOutput (Emit.parallel (Emit.id _)
    (Emit.tabulate (fixedEnum (Option tm.Λ)) mem_fixedEnum
      (fun l => Emit.constant (oneHot (none : Option tm.Λ) l)))) (labelOutput tm C)

theorem halt_denotes : Emit.Denotes (halt tm C)
    (fun x => replaceLabel tm C x (oneHot (none : Option tm.Λ))) := by
  have h := Emit.renameOutput_denotes (Emit.parallel_denotes (Emit.route_denotes (fun a : Addr tm C => a))
    (Emit.tabulate_denotes (fixedEnum (Option tm.Λ)) mem_fixedEnum
      (fun l => Emit.constant (I := Addr tm C) (oneHot (none : Option tm.Λ) l))
      (fun _ => oneHot (none : Option tm.Λ))
      (fun _ => Emit.constant_denotes _))) (labelOutput tm C)
  refine denotes_value_congr h ?_
  intro x a
  cases a with
  | inl a => rfl
  | inr a => cases a <;> rfl

def test (f : tm.σ → Bool) : Emit (Addr tm C) Unit :=
  Emit.renameOutput (Emit.renameInput (stateRoute tm C) (Emit.table f)) (fun _ => true)

def testValue (f : tm.σ → Bool) (x : Bits tm C) : Bool :=
  Emit.tableValue f (fun s => x (stateAddr tm C s)) true

theorem test_denotes (f : tm.σ → Bool) : Emit.Denotes (test tm C f) (fun x _ => testValue tm C f x) :=
  Emit.renameOutput_denotes (Emit.renameInput_denotes (stateRoute tm C) (Emit.table_denotes f)) _

theorem test_encode (f : tm.σ → Bool) (p : PackedStep.Packed tm C) :
    testValue tm C f (encode tm C p) = f p.2.1 := by
  change Emit.tableValue f (oneHot p.2.1) true = _
  rw [Emit.tableValue_oneHot]
  simp [oneHot]

/-- The two arms receive the same original configuration, and the select bit
is retained as a wire while both arms are emitted. -/
def choose (t : Emit (Addr tm C) Unit) (p q : Emit (Addr tm C) (Addr tm C)) :
    Emit (Addr tm C) (Addr tm C) :=
  Emit.seq (Emit.parallel t (Emit.parallel p q))
    (Emit.tabulate (addresses tm C) (mem_addresses tm C)
      (fun a => Emit.mux (.inl ()) (.inr (.inl a)) (.inr (.inr a))))

theorem choose_denotes {t : Emit (Addr tm C) Unit} {p q : Emit (Addr tm C) (Addr tm C)}
    {f : Bits tm C → Bool} {g h : Bits tm C → Bits tm C}
    (ht : Emit.Denotes t (fun x _ => f x)) (hp : Emit.Denotes p g) (hq : Emit.Denotes q h) :
    Emit.Denotes (choose tm C t p q) (fun x a => if f x then g x a else h x a) :=
  Emit.seq_denotes (Emit.parallel_denotes ht (Emit.parallel_denotes hp hq))
    (Emit.tabulate_denotes _ _ _ _ (fun a => Emit.mux_denotes _ _ _))

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.PrimitiveBlocks
