import Holant.Proofs.CountingMachines.StandardMachine.Recoding.Embedding
import Holant.Complexity.OutputSize

set_option backward.isDefEq.respectTransparency false
/-! Sequential heterogeneous finite-stack compilation. The first clean output
stack is identified with the second input stack using a fixed symbol equivalence.
All remaining stack spaces are disjoint. This is static wiring: no transition
performs a host operation on a list. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Recoding.Composition
open Turing Computability Holant.Complexity
open _root_.Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Recoding.Embedding

variable (a b : FinTM2)
local instance : Fintype a.K := a.kFin
local instance : Fintype b.K := b.kFin
local instance : Fintype a.Λ := a.ΛFin
local instance : Fintype b.Λ := b.ΛFin
local instance : Fintype a.σ := a.σFin
local instance : Fintype b.σ := b.σFin

abbrev Other := {k : b.K // k ≠ b.k₀}
abbrev Keys := a.K ⊕ Other b
abbrev Alphabet : Keys a b → Type
  | .inl k => a.Γ k
  | .inr k => b.Γ k.val
abbrev Labels := a.Λ ⊕ b.Λ
abbrev State := a.σ × b.σ

def splitTapes (left : ∀ k, List (a.Γ k)) (right : ∀ k : Other b, List (b.Γ k.val)) :
    ∀ k, List (Alphabet a b k)
  | .inl k => left k
  | .inr k => right k

def leftLayout : Layout a.Γ (Alphabet a b) where
  key := Sum.inl
  symbol _ := Equiv.refl _
  lift tapes := splitTapes a b tapes (fun _ => [])
  lookup _ _ := by simp [splitTapes]
  update tapes k word := by
    simp only [Equiv.coe_refl,List.map_id]
    funext j
    cases j with
    | inl i =>
        by_cases h : i=k
        · subst i; simp [splitTapes,Function.update]
        · simp [splitTapes,Function.update,h]
    | inr i => simp [splitTapes,Function.update]

def rightPoint (e : b.Γ b.k₀ ≃ a.Γ a.k₁) (k : b.K) :
    Σ j : Keys a b, b.Γ k ≃ Alphabet a b j :=
  if h : k = b.k₀ then
    ⟨.inl a.k₁, (Equiv.cast (congrArg b.Γ h)).trans e⟩
  else ⟨.inr ⟨k,h⟩, Equiv.refl _⟩

@[simp] theorem rightPoint_input (e : b.Γ b.k₀ ≃ a.Γ a.k₁) :
    rightPoint a b e b.k₀ = ⟨.inl a.k₁,e⟩ := by
  simp [rightPoint]

@[simp] theorem rightPoint_other (e : b.Γ b.k₀ ≃ a.Γ a.k₁) (k : b.K) (h : k ≠ b.k₀) :
    rightPoint a b e k = ⟨.inr ⟨k,h⟩,Equiv.refl _⟩ := by
  simp [rightPoint,h]

def rightKey (e : b.Γ b.k₀ ≃ a.Γ a.k₁) (k : b.K) : Keys a b :=
  (rightPoint a b e k).1

def rightSymbol (e : b.Γ b.k₀ ≃ a.Γ a.k₁) (k : b.K) : b.Γ k ≃ Alphabet a b (rightKey a b e k) :=
  (rightPoint a b e k).2

def rightLayout (e : b.Γ b.k₀ ≃ a.Γ a.k₁) : Layout b.Γ (Alphabet a b) where
  key := rightKey a b e
  symbol := rightSymbol a b e
  lift tapes := splitTapes a b
    (Function.update (fun _ => []) a.k₁ ((tapes b.k₀).map e)) (fun k => tapes k.val)
  lookup tapes k := by
    by_cases h : k = b.k₀
    · subst k
      dsimp +instances only [rightKey,rightSymbol]
      rw [rightPoint_input]
      simp [splitTapes]
    · dsimp +instances only [rightKey,rightSymbol]
      rw [rightPoint_other a b e k h]
      simp [splitTapes]
  update tapes k word := by
    dsimp +instances only [rightKey,rightSymbol]
    by_cases h : k = b.k₀
    · subst k
      rw [rightPoint_input]
      funext j
      cases j with
      | inl i =>
          by_cases hi : i=a.k₁
          · subst i; simp [splitTapes,Function.update]
          · simp [splitTapes,Function.update,hi]
      | inr i => simp [splitTapes,Function.update,i.property]
    · rw [rightPoint_other a b e k h]
      funext j
      cases j with
      | inl i => simp [splitTapes,Function.update,Ne.symm h]
      | inr i =>
          by_cases hi : i.val=k
          · have he : i = ⟨k,h⟩ := Subtype.ext hi
            subst i
            simp [splitTapes,Function.update]
          · have he : i ≠ ⟨k,h⟩ := fun he => hi (congrArg Subtype.val he)
            simp [splitTapes,Function.update,hi,he]

def leftStates : States a.σ (State a b) := ⟨fun v => (v,b.initialState),Prod.fst,fun _ => rfl⟩
def rightStates : States b.σ (State a b) := ⟨fun v => (a.initialState,v),Prod.snd,fun _ => rfl⟩

def program (e : b.Γ b.k₀ ≃ a.Γ a.k₁) : Labels a b → TM2.Stmt (Alphabet a b) (Labels a b) (State a b)
  | .inl l => Embedding.stmt (leftLayout a b) (leftStates a b) Sum.inl (some (.inr b.main)) (a.m l)
  | .inr l => Embedding.stmt (rightLayout a b e) (rightStates a b) Sum.inr none (b.m l)

abbrev machine (e : b.Γ b.k₀ ≃ a.Γ a.k₁) : FinTM2 where
  K := Keys a b
  k₀ := .inl a.k₀
  k₁ := rightKey a b e b.k₁
  Γ := Alphabet a b
  Λ := Labels a b
  main := .inl a.main
  σ := State a b
  initialState := (a.initialState,b.initialState)
  Γk₀Fin := a.Γk₀Fin
  m := program a b e

def leftCfg (c : a.Cfg) := Embedding.cfg (leftLayout a b) (leftStates a b) Sum.inl (some (.inr b.main)) c
def rightCfg (e : b.Γ b.k₀ ≃ a.Γ a.k₁) (c : b.Cfg) : TM2.Cfg (Alphabet a b) (Labels a b) (State a b) :=
  Embedding.cfg (rightLayout a b e) (rightStates a b) Sum.inr none c

theorem init_single (m : FinTM2) (word : List (m.Γ m.k₀)) :
    initList m word = ⟨some m.main,m.initialState,Function.update (fun _ => []) m.k₀ word⟩ := by
  unfold initList
  congr 1
  funext k
  by_cases h : k=m.k₀
  · subst k; simp [Function.update]
  · simp [Function.update,h]

theorem halt_single (m : FinTM2) (word : List (m.Γ m.k₁)) :
    haltList m word = ⟨none,m.initialState,Function.update (fun _ => []) m.k₁ word⟩ := by
  unfold haltList
  congr 1
  funext k
  by_cases h : k=m.k₁
  · subst k; simp [Function.update]
  · simp [Function.update,h]

theorem left_empty : (leftLayout a b).lift (fun _ => []) = (fun _ => []) := by
  funext k
  cases k <;> rfl

theorem right_empty (e : b.Γ b.k₀ ≃ a.Γ a.k₁) :
    (rightLayout a b e).lift (fun _ => []) = (fun _ => []) := by
  funext k
  cases k with
  | inl k => simp [rightLayout,splitTapes]
  | inr k => rfl

theorem left_init (e : b.Γ b.k₀ ≃ a.Γ a.k₁) (word : List (a.Γ a.k₀)) :
    leftCfg a b (initList a word) = initList (machine a b e) word := by
  rw [init_single,init_single]
  unfold leftCfg Embedding.cfg
  simp only [Option.elim_some,leftStates]
  rw [← (leftLayout a b).update, left_empty]
  simp [leftLayout]

theorem handoff (e : b.Γ b.k₀ ≃ a.Γ a.k₁) (word : List (a.Γ a.k₁)) :
    leftCfg a b (haltList a word) = rightCfg a b e (initList b (word.map e.symm)) := by
  rw [halt_single,init_single]
  unfold leftCfg rightCfg Embedding.cfg
  simp only [Option.elim_none,Option.elim_some,leftStates,rightStates]
  rw [← (leftLayout a b).update,← (rightLayout a b e).update,left_empty,right_empty]
  dsimp +instances only [leftLayout,rightLayout,rightKey,rightSymbol]
  rw [rightPoint_input]
  simp

theorem right_halt (e : b.Γ b.k₀ ≃ a.Γ a.k₁) (word : List (b.Γ b.k₁)) :
    rightCfg a b e (haltList b word) =
      haltList (machine a b e) (word.map (rightSymbol a b e b.k₁)) := by
  rw [halt_single,halt_single]
  unfold rightCfg Embedding.cfg
  simp only [Option.elim_none,rightStates]
  rw [← (rightLayout a b e).update,right_empty]
  rfl

/-- Two clean component runs compose with no hidden transfer operation. Only
the first final halt is replaced by a jump into the second finite program. -/
theorem exact_run (e : b.Γ b.k₀ ≃ a.Γ a.k₁) (input : List (a.Γ a.k₀))
    (middle : List (a.Γ a.k₁)) (output : List (b.Γ b.k₁)) (n t : ℕ)
    (ha : (fun p => p.bind a.step)^[n] (some (initList a input)) = some (haltList a middle))
    (hb : (fun p => p.bind b.step)^[t] (some (initList b (middle.map e.symm))) = some (haltList b output)) :
    (fun p => p.bind (machine a b e).step)^[t+n] (some (initList (machine a b e) input)) =
      some (haltList (machine a b e) (output.map (rightSymbol a b e b.k₁))) := by
  have hl := Embedding.run (leftLayout a b) (leftStates a b) Sum.inl (some (.inr b.main))
    a.m (program a b e) (fun _ => rfl) _ _ n ha
  have hr := Embedding.run (rightLayout a b e) (rightStates a b) Sum.inr none
    b.m (program a b e) (fun _ => rfl) _ _ t hb
  change (fun p => p.bind (machine a b e).step)^[n]
      (some (leftCfg a b (initList a input))) = some (leftCfg a b (haltList a middle)) at hl
  change (fun p => p.bind (machine a b e).step)^[t]
      (some (rightCfg a b e (initList b (middle.map e.symm)))) =
        some (rightCfg a b e (haltList b output)) at hr
  rw [left_init a b e,handoff a b e] at hl
  rw [right_halt a b e] at hr
  rw [Function.iterate_add_apply]
  exact (congrArg ((fun p => p.bind (machine a b e).step)^[t]) hl).trans hr

/-- The ordinary clean-output semantics follows from the exact sum of the two
component runs. There is no transition hidden between the two runs. -/
def outputs (e : b.Γ b.k₀ ≃ a.Γ a.k₁) (input : List (a.Γ a.k₀))
    (middle : List (a.Γ a.k₁)) (output : List (b.Γ b.k₁)) (n t : ℕ)
    (ha : TM2OutputsInTime a input (some middle) n)
    (hb : TM2OutputsInTime b (middle.map e.symm) (some output) t) :
    TM2OutputsInTime (machine a b e) input
      (some (output.map (rightSymbol a b e b.k₁))) (n+t) where
  steps := hb.steps + ha.steps
  evals_in_steps := exact_run a b e input middle output ha.steps hb.steps
    ha.evals_in_steps hb.evals_in_steps
  steps_le_m := by have := ha.steps_le_m; have := hb.steps_le_m; omega

/-- Natural-coefficient polynomial evaluation is monotone in word length. -/
theorem eval_mono (p : Polynomial ℕ) {m n : ℕ} (h : m ≤ n) : p.eval m ≤ p.eval n := by
  simp only [Polynomial.eval_eq_sum,Polynomial.sum_def]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i))

/-- Sequential compilation of arbitrary finite-alphabet polynomial-time
machines. The intermediate size bound charges the second machine against the
original input size; correctness and running time follow from actual component
runs. The intermediate bound does not assert a bound for the constructed run. -/
def comp {α β γ Γ₀ Γ₁ Γ₂ : Type} [Fintype Γ₀] [Fintype Γ₁] [Fintype Γ₂]
    {ea : Encoding α Γ₀} {eb : Encoding β Γ₁} {ec : Encoding γ Γ₂}
    {f : α → β} {g : β → γ}
    (a : PolyTime ea eb f) (b : PolyTime eb ec g)
    (size : PolynomialOutputBound ea eb f) : PolyTime ea ec (g ∘ f) := by
  let e : b.tm.Γ b.tm.k₀ ≃ a.tm.Γ a.tm.k₁ := b.inputAlphabet.trans a.outputAlphabet.symm
  refine {
    tm := machine a.tm b.tm e
    inputAlphabet := a.inputAlphabet
    outputAlphabet := (rightSymbol a.tm b.tm e b.tm.k₁).symm.trans b.outputAlphabet
    time := a.time + b.time.comp size.bound
    outputsFun := ?_
    finiteAlphabets := ?_ }
  · intro x
    have ha := a.outputsFun x
    have hb := b.outputsFun (f x)
    have hm : ((eb.encode (f x)).map a.outputAlphabet.invFun).map e.symm =
        (eb.encode (f x)).map b.inputAlphabet.invFun := by
      simp [e,List.map_map]
    have h := outputs a.tm b.tm e
      ((ea.encode x).map a.inputAlphabet.invFun)
      ((eb.encode (f x)).map a.outputAlphabet.invFun)
      ((ec.encode (g (f x))).map b.outputAlphabet.invFun)
      (a.time.eval (ea.encode x).length) (b.time.eval (eb.encode (f x)).length)
      ha (by rw [hm]; exact hb)
    refine { steps := h.steps, evals_in_steps := ?_, steps_le_m := ?_ }
    · simpa +instances only [Function.comp_apply,Equiv.trans,Equiv.symm,List.map_map,Equiv.coe_fn_mk,Equiv.toFun_as_coe] using h.evals_in_steps
    · apply le_trans h.steps_le_m
      have ht := eval_mono b.time (size.length_le x)
      simp only [Polynomial.eval_add,Polynomial.eval_comp]
      omega
  · intro k
    cases k with
    | inl k => exact a.finiteAlphabets k
    | inr k => exact b.finiteAlphabets k.val

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Recoding.Composition
