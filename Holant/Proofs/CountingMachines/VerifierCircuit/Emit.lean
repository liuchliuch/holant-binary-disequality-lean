import Holant.Proofs.CountingMachines.CircuitNative.Circuit

/-!
# Direct continuation-based emission into the existing NAND syntax

Ported reference proof. See the task validation reports.

`Emit` is a function that builds the existing `Circuit`, not a second circuit
language. An arbitrary live context is shifted at each emitted node; this lets
two computations share their original inputs without copying syntax or losing
register references. All concrete emitters below have direct proof bodies.
-/

namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit


abbrev Continuation (A O : Type) := ∀ {n : ℕ}, (A → Fin n) → (O → Fin n) → Circuit n

abbrev Emit (I O : Type) := ∀ {A : Type} {n : ℕ},
  (A → Fin n) → (I → Fin n) → Continuation A O → Circuit n

namespace Emit

def route {I O : Type} (f : O → I) : Emit I O :=
  fun ctx input k => k ctx (fun o => input (f o))

def id (I : Type) : Emit I I := route (fun i => i)

def constant {I : Type} (b : Bool) : Emit I Unit :=
  fun ctx _ k => .constant b (k (fun a => (ctx a).succ) (fun _ => 0))

def nand {I : Type} (a b : I) : Emit I Unit :=
  fun ctx input k => .nand (input a) (input b)
    (k (fun i => (ctx i).succ) (fun _ => 0))

def seq {I O P : Type} (p : Emit I O) (q : Emit O P) : Emit I P :=
  fun ctx input k => p ctx input (fun ctx' middle => q ctx' middle k)

/-- Both subcircuits see the original inputs. The left output is carried as
live context while the right subcircuit emits fresh registers. -/
def parallel {I O P : Type} (p : Emit I O) (q : Emit I P) : Emit I (O ⊕ P) :=
  fun ctx input k =>
    p (Sum.elim ctx input) input (fun saved left =>
      q (Sum.elim (fun a => saved (.inl a)) left) (fun i => saved (.inr i))
        (fun saved' right => k (fun a => saved' (.inl a))
          (Sum.elim (fun o => saved' (.inr o)) right)))

def renameInput {I J O : Type} (f : I → J) (p : Emit I O) : Emit J O :=
  fun ctx input k => p ctx (fun i => input (f i)) k

def renameOutput {I O P : Type} (p : Emit I O) (f : P → O) : Emit I P :=
  seq p (route f)

def not {I : Type} (a : I) : Emit I Unit := nand a a

def and {I : Type} (a b : I) : Emit I Unit := seq (nand a b) (not ())

def or {I : Type} (a b : I) : Emit I Unit :=
  seq (parallel (not a) (not b)) (nand (.inl ()) (.inr ()))

/-- Four NAND gates, even when one or more operands coincide. -/
def mux {I : Type} (s t e : I) : Emit I Unit :=
  seq (parallel (nand s t) (seq (parallel (not s) (route (fun _ : Unit => e)))
    (nand (.inl ()) (.inr ())))) (nand (.inl ()) (.inr ()))

def finish {I : Type} (p : Emit I Unit) {n : ℕ} (input : I → Fin n) : Circuit n :=
  p (fun a : Empty => nomatch a) input (fun _ out => .output (out ()))

/-- Internal composition rule. Its continuation premise concerns only the
already constructed suffix; no simulator/circuit-existence premise is accepted
by the actual verifier compiler. -/
def Denotes {I O : Type} (p : Emit I O) (f : (I → Bool) → (O → Bool)) : Prop :=
  ∀ (A : Type) (n : ℕ) (ctx : A → Fin n) (input : I → Fin n) (x : Fin n → Bool)
    (k : Continuation A O) (result : (A → Bool) → (O → Bool) → Bool),
    (∀ (m : ℕ) (c : A → Fin m) (o : O → Fin m) (y : Fin m → Bool),
      (k c o).eval y = result (fun a => y (c a)) (fun i => y (o i))) →
    (p ctx input k).eval x = result (fun a => x (ctx a)) (f (fun i => x (input i)))

theorem route_denotes {I O : Type} (f : O → I) :
    Denotes (route f) (fun x o => x (f o)) := by
  intro A n ctx input x k result hk
  exact hk n ctx (fun o => input (f o)) x

theorem constant_denotes {I : Type} (b : Bool) :
    Denotes (constant (I := I) b) (fun _ _ => b) := by
  intro A n ctx input x k result hk
  simpa [constant, Circuit.eval] using
    hk (n + 1) (fun a => (ctx a).succ) (fun _ => 0) (Fin.cons b x)

theorem nand_denotes {I : Type} (a b : I) :
    Denotes (nand a b) (fun x _ => !(x a && x b)) := by
  intro A n ctx input x k result hk
  simpa [nand, Circuit.eval] using
    hk (n + 1) (fun i => (ctx i).succ) (fun _ => 0)
      (Fin.cons (!(x (input a) && x (input b))) x)

theorem seq_denotes {I O P : Type} {p : Emit I O} {q : Emit O P}
    {f : (I → Bool) → (O → Bool)} {g : (O → Bool) → (P → Bool)}
    (hp : Denotes p f) (hq : Denotes q g) : Denotes (seq p q) (fun x => g (f x)) := by
  intro A n ctx input x k result hk
  apply hp A n ctx input x _ (fun c o => result c (g o))
  intro m c o y
  exact hq A m c o y k result hk

theorem parallel_denotes {I O P : Type} {p : Emit I O} {q : Emit I P}
    {f : (I → Bool) → (O → Bool)} {g : (I → Bool) → (P → Bool)}
    (hp : Denotes p f) (hq : Denotes q g) :
    Denotes (parallel p q) (fun x => Sum.elim (f x) (g x)) := by
  intro A n ctx input x k result hk
  apply hp (A ⊕ I) n (Sum.elim ctx input) input x _
    (fun saved left => result (fun a => saved (.inl a))
      (Sum.elim left (g (fun i => saved (.inr i)))))
  intro m saved left y
  apply hq (A ⊕ O) m (Sum.elim (fun a => saved (.inl a)) left)
    (fun i => saved (.inr i)) y _
    (fun saved' right => result (fun a => saved' (.inl a))
      (Sum.elim (fun o => saved' (.inr o)) right))
  intro m' saved' right y'
  have he : (fun i => y' (Sum.elim (fun o => saved' (.inr o)) right i)) =
      Sum.elim (fun o => y' (saved' (.inr o))) (fun i => y' (right i)) := by
    funext i
    cases i <;> rfl
  simpa only [he] using
    hk m' (fun a => saved' (.inl a)) (Sum.elim (fun o => saved' (.inr o)) right) y'

theorem renameInput_denotes {I J O : Type} (r : I → J) {p : Emit I O}
    {f : (I → Bool) → (O → Bool)} (hp : Denotes p f) :
    Denotes (renameInput r p) (fun x => f (fun i => x (r i))) := by
  intro A n ctx input x k result hk
  exact hp A n ctx (fun i => input (r i)) x k result hk

theorem renameOutput_denotes {I O P : Type} {p : Emit I O}
    {f : (I → Bool) → (O → Bool)} (hp : Denotes p f) (r : P → O) :
    Denotes (renameOutput p r) (fun x o => f x (r o)) :=
  seq_denotes hp (route_denotes r)

theorem not_denotes {I : Type} (a : I) : Denotes (not a) (fun x _ => !(x a)) := by
  simpa only [not, Bool.and_self] using nand_denotes a a

theorem and_denotes {I : Type} (a b : I) : Denotes (and a b) (fun x _ => x a && x b) := by
  simpa [and] using seq_denotes (nand_denotes a b) (not_denotes ())

theorem or_denotes {I : Type} (a b : I) : Denotes (or a b) (fun x _ => x a || x b) := by
  have h := seq_denotes (parallel_denotes (not_denotes a) (not_denotes b))
    (nand_denotes (.inl ()) (.inr ()))
  simpa [or, Bool.not_and] using h

theorem mux_denotes {I : Type} (s t e : I) :
    Denotes (mux s t e) (fun x _ => if x s then x t else x e) := by
  have h := seq_denotes (parallel_denotes (nand_denotes s t)
    (seq_denotes (parallel_denotes (not_denotes s) (route_denotes (fun _ : Unit => e)))
      (nand_denotes (.inl ()) (.inr ())))) (nand_denotes (.inl ()) (.inr ()))
  have hb (x : I → Bool) :
      (!( !(x s && x t) && !(!(x s) && x e))) = if x s then x t else x e := by
    cases x s <;> cases x t <;> cases x e <;> rfl
  simpa only [mux, Sum.elim_inl, Sum.elim_inr, hb] using h

theorem finish_eval {I : Type} {p : Emit I Unit} {f : (I → Bool) → (Unit → Bool)}
    (hp : Denotes p f) {n : ℕ} (input : I → Fin n) (x : Fin n → Bool) :
    (finish p input).eval x = f (fun i => x (input i)) () := by
  apply hp Empty n _ input x _ (fun _ o => o ())
  intros
  rfl

/-- Exact structural gate accounting for emitters. This is explicitly not a
time bound for a physical machine that writes the circuit's bytes. -/
def Adds {I O : Type} (p : Emit I O) (g : ℕ) : Prop :=
  ∀ (A : Type) (n : ℕ) (ctx : A → Fin n) (input : I → Fin n)
    (k : Continuation A O) (t : ℕ),
    (∀ (m : ℕ) (c : A → Fin m) (o : O → Fin m), (k c o).gates = t) →
    (p ctx input k).gates = g + t

theorem route_adds {I O : Type} (r : O → I) : Adds (route r) 0 := by
  intro A n ctx input k t hk
  simpa [route] using hk n ctx (fun o => input (r o))

theorem constant_adds {I : Type} (b : Bool) : Adds (constant (I := I) b) 1 := by
  intro A n ctx input k t hk
  simp [constant, Circuit.gates, hk, Nat.add_comm]

theorem nand_adds {I : Type} (a b : I) : Adds (nand a b) 1 := by
  intro A n ctx input k t hk
  simp [nand, Circuit.gates, hk, Nat.add_comm]

theorem seq_adds {I O P : Type} {p : Emit I O} {q : Emit O P} {a b : ℕ}
    (hp : Adds p a) (hq : Adds q b) : Adds (seq p q) (a + b) := by
  intro A n ctx input k t hk
  simpa only [seq, Nat.add_assoc] using hp A n ctx input _ (b + t)
    (fun m c o => hq A m c o k t hk)

theorem parallel_adds {I O P : Type} {p : Emit I O} {q : Emit I P} {a b : ℕ}
    (hp : Adds p a) (hq : Adds q b) : Adds (parallel p q) (a + b) := by
  intro A n ctx input k t hk
  apply (hp (A ⊕ I) n (Sum.elim ctx input) input _ (b + t) ?_).trans (Nat.add_assoc _ _ _).symm
  intro m saved left
  exact hq (A ⊕ O) m (Sum.elim (fun a => saved (.inl a)) left)
    (fun i => saved (.inr i)) _ t
    (fun m' saved' right => hk m' (fun a => saved' (.inl a))
      (Sum.elim (fun o => saved' (.inr o)) right))

theorem finish_gates {I : Type} {p : Emit I Unit} {g : ℕ} (hp : Adds p g)
    {n : ℕ} (input : I → Fin n) : (finish p input).gates = g := by
  simpa only [finish, Nat.add_zero] using hp Empty n _ input _ 0 (by intros; rfl)

end Emit
end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit
