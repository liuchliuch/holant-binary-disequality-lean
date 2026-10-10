import Holant.Proofs.CountingMachines.VerifierCircuit.RuntimeRows

set_option backward.isDefEq.respectTransparency false

/-!
# Exact row extraction from the existing continuation emitter

Ported reference proof. See the task validation reports.

`Result` contains the existing `Circuit.Row` records and natural register
references. It is not another circuit syntax. Reference functions below are
mathematical specifications; `Environment` serializes them as actual lists.
-/

namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Rows


abbrev Result (O : Type) := List Circuit.Row × (O → ℕ)
abbrev Run (I O : Type) := (I → ℕ) → Result O

def «prefix» (rows : List Circuit.Row) (code : Circuit.Code) : Circuit.Code :=
  (rows ++ code.1, code.2)

@[simp] theorem prefix_nil (code : Circuit.Code) : «prefix» [] code = code := by cases code; rfl
@[simp] theorem prefix_prefix (r s : List Circuit.Row) (code : Circuit.Code) :
    «prefix» r («prefix» s code) = «prefix» (r ++ s) code := by simp [«prefix», List.append_assoc]

def shift {I : Type} (g : ℕ) (env : I → ℕ) : I → ℕ := fun i => env i + g

@[simp] theorem shift_zero {I : Type} (env : I → ℕ) : shift 0 env = env := by
  funext i
  simp [shift]

def route {I O : Type} (f : O → I) : Run I O := fun env => ([], fun o => env (f o))
def constant {I : Type} (b : Bool) : Run I Unit := fun _ => ([(if b then 1 else 0, (0, 0))], fun _ => 0)
def nand {I : Type} (a b : I) : Run I Unit := fun env => ([(2, (env a, env b))], fun _ => 0)

def seq {I O P : Type} (p : Run I O) (q : Run O P) : Run I P := fun env =>
  let first := p env
  let second := q first.2
  (first.1 ++ second.1, second.2)

/-- The right side receives the shifted original input; the retained left
outputs are shifted by precisely the right side's emitted row count. -/
def parallel {I O P : Type} (p : Run I O) (q : Run I P) : Run I (O ⊕ P) := fun env =>
  let first := p env
  let second := q (shift first.1.length env)
  (first.1 ++ second.1, Sum.elim (shift second.1.length first.2) second.2)

def renameInput {I J O : Type} (r : I → J) (p : Run I O) : Run J O := fun env => p (fun i => env (r i))
def renameOutput {I O P : Type} (p : Run I O) (r : P → O) : Run I P := seq p (route r)

/-- Equality of all emitted rows and of the continuation's references. Unlike
value semantics, this records the precise existing codec's register indices.
The witnesses are obtained from the actual emitter, not supplied to compile. -/
def Exact {I O : Type} (p : Emit I O) (run : Run I O) : Prop :=
  ∀ (A : Type) (n : ℕ) (ctx : A → Fin n) (input : I → Fin n),
    let r := run (fun i => (input i).val)
    ∃ (m : ℕ) (ctx' : A → Fin m) (out : O → Fin m),
      m = n + r.1.length ∧
      (∀ a, (ctx' a).val = (ctx a).val + r.1.length) ∧
      (∀ o, (out o).val = r.2 o) ∧
      ∀ k : Continuation A O, (p ctx input k).code = «prefix» r.1 (k ctx' out).code

theorem route_exact {I O : Type} (f : O → I) : Exact (Emit.route f) (route f) := by
  intro A n ctx input
  refine ⟨n, ctx, (fun o => input (f o)), ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

theorem constant_exact {I : Type} (b : Bool) : Exact (Emit.constant (I := I) b) (constant b) := by
  intro A n ctx input
  refine ⟨n + 1, (fun a => (ctx a).succ), (fun _ => 0), rfl, ?_, ?_, ?_⟩
  · intro a; rfl
  · intro o; rfl
  · intro k; rfl

theorem nand_exact {I : Type} (a b : I) : Exact (Emit.nand a b) (nand a b) := by
  intro A n ctx input
  refine ⟨n + 1, (fun a => (ctx a).succ), (fun _ => 0), rfl, ?_, ?_, ?_⟩
  · intro a; rfl
  · intro o; rfl
  · intro k; rfl

theorem seq_exact {I O P : Type} {p : Emit I O} {q : Emit O P} {rp : Run I O} {rq : Run O P}
    (hp : Exact p rp) (hq : Exact q rq) : Exact (Emit.seq p q) (seq rp rq) := by
  intro A n ctx input
  obtain ⟨m, middleCtx, middle, hm, hc, ho, he⟩ := hp A n ctx input
  obtain ⟨m', finalCtx, out, hm', hc', ho', he'⟩ := hq A m middleCtx middle
  have hout : (fun o => (middle o).val) = (rp (fun i => (input i).val)).2 := funext ho
  rw [hout] at hm' hc' ho' he'
  refine ⟨m', finalCtx, out, ?_, ?_, ho', ?_⟩
  · simp only [seq, List.length_append]; omega
  · intro a
    rw [hc', hc]
    simp [seq, Nat.add_assoc]
  · intro k
    change (p ctx input (fun c o => q c o k)).code = _
    rw [he, he']
    exact prefix_prefix _ _ _

theorem parallel_exact {I O P : Type} {p : Emit I O} {q : Emit I P} {rp : Run I O} {rq : Run I P}
    (hp : Exact p rp) (hq : Exact q rq) : Exact (Emit.parallel p q) (parallel rp rq) := by
  intro A n ctx input
  obtain ⟨m, saved, left, hm, hs, hl, hpcode⟩ := hp (A ⊕ I) n (Sum.elim ctx input) input
  obtain ⟨m', saved', right, hm', hs', hr, hqcode⟩ :=
    hq (A ⊕ O) m (Sum.elim (fun a => saved (.inl a)) left) (fun i => saved (.inr i))
  have hin : (fun i => (saved (.inr i)).val) = shift (rp (fun i => (input i).val)).1.length
      (fun i => (input i).val) := funext (fun i => hs (.inr i))
  rw [hin] at hm' hs' hr hqcode
  refine ⟨m', (fun a => saved' (.inl a)), Sum.elim (fun o => saved' (.inr o)) right, ?_, ?_, ?_, ?_⟩
  · simp only [parallel, List.length_append]; omega
  · intro a
    rw [hs']
    simp only [Sum.elim_inl]
    rw [hs]
    simp [parallel, Nat.add_assoc]
  · intro o
    cases o with
    | inl o => simpa [parallel, shift, hl] using hs' (.inr o)
    | inr o => exact hr o
  · intro k
    change (p (Sum.elim ctx input) input _).code = _
    rw [hpcode, hqcode]
    exact prefix_prefix _ _ _

theorem renameInput_exact {I J O : Type} (r : I → J) {p : Emit I O} {rp : Run I O}
    (hp : Exact p rp) : Exact (Emit.renameInput r p) (renameInput r rp) := by
  intro A n ctx input
  exact hp A n ctx (fun i => input (r i))

theorem renameOutput_exact {I O P : Type} {p : Emit I O} {rp : Run I O}
    (hp : Exact p rp) (r : P → O) : Exact (Emit.renameOutput p r) (renameOutput rp r) :=
  seq_exact hp (route_exact r)

theorem finish_code {I : Type} {p : Emit I Unit} {rp : Run I Unit} (hp : Exact p rp)
    {n : ℕ} (input : I → Fin n) :
    (Emit.finish p input).code = ((rp (fun i => (input i).val)).1, (rp (fun i => (input i).val)).2 ()) := by
  obtain ⟨m, ctx, out, hm, hc, ho, he⟩ := hp Empty n (fun e => nomatch e) input
  calc
    (Emit.finish p input).code =
        (p (fun e : Empty => nomatch e) input (fun _ o => .output (o ()))).code := by
      unfold Emit.finish
      congr 2
    _ = _ := by simpa [«prefix», Circuit.code, ho] using he (fun _ o => .output (o ()))

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Rows
