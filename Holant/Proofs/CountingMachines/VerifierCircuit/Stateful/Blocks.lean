import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.Environment

set_option backward.isDefEq.respectTransparency false

/-!
# Exact gate records for Boolean blocks and ordered tabulation

Ported reference proof. See the task validation reports.

All records use the old Circuit tags. In particular `mux_rows` records the
actual four-gate order, including the intermediate shifts of original inputs.
-/

namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Rows


def not {I : Type} (a : I) : Run I Unit := nand a a
def and {I : Type} (a b : I) : Run I Unit := seq (nand a b) (not ())
def or {I : Type} (a b : I) : Run I Unit :=
  seq (parallel (not a) (not b)) (nand (.inl ()) (.inr ()))
def mux {I : Type} (s t e : I) : Run I Unit :=
  seq (parallel (nand s t) (seq (parallel (not s) (route (fun _ : Unit => e)))
    (nand (.inl ()) (.inr ())))) (nand (.inl ()) (.inr ()))

theorem not_exact {I : Type} (a : I) : Exact (Emit.not a) (not a) := nand_exact a a
theorem and_exact {I : Type} (a b : I) : Exact (Emit.and a b) (and a b) :=
  seq_exact (nand_exact a b) (not_exact ())
theorem or_exact {I : Type} (a b : I) : Exact (Emit.or a b) (or a b) :=
  seq_exact (parallel_exact (not_exact a) (not_exact b)) (nand_exact _ _)
theorem mux_exact {I : Type} (s t e : I) : Exact (Emit.mux s t e) (mux s t e) :=
  seq_exact (parallel_exact (nand_exact s t)
    (seq_exact (parallel_exact (not_exact s) (route_exact (fun _ : Unit => e)))
      (nand_exact _ _))) (nand_exact _ _)

theorem mux_rows {I : Type} (s t e : I) (env : I → ℕ) :
    (mux s t e env).1 =
      [(2, (env s, env t)), (2, (env s + 1, env s + 1)),
        (2, (0, env e + 2)), (2, (2, 0))] := by
  simp [mux, seq, parallel, not, nand, route, shift, Nat.add_assoc]

@[simp] theorem mux_length {I : Type} (s t e : I) (env : I → ℕ) : (mux s t e env).1.length = 4 := by
  rw [mux_rows]; rfl
@[simp] theorem mux_output {I : Type} (s t e : I) (env : I → ℕ) (u : Unit) :
    (mux s t e env).2 u = 0 := rfl

def gather {I J : Type} (p : J → Run I Unit) : (xs : List J) → Run I (Fin xs.length)
  | [] => route (fun i => Fin.elim0 i)
  | j :: xs => renameOutput (parallel (p j) (gather p xs))
      (Fin.cases (.inl ()) (fun i => .inr i))

theorem gather_exact {I J : Type} (p : J → Emit I Unit) (rp : J → Run I Unit)
    (hp : ∀ j, Exact (p j) (rp j)) (xs : List J) : Exact (Emit.gather p xs) (gather rp xs) := by
  induction xs with
  | nil => exact route_exact _
  | cons j xs ih => exact renameOutput_exact (parallel_exact (hp j) ih) _

def tabulate {I O : Type} [DecidableEq O] (xs : List O) (covers : ∀ o, o ∈ xs)
    (p : O → Run I Unit) : Run I O :=
  renameOutput (gather p xs) (fun o => ⟨xs.idxOf o, List.idxOf_lt_length_iff.mpr (covers o)⟩)

theorem tabulate_exact {I O : Type} [DecidableEq O] (xs : List O) (covers : ∀ o, o ∈ xs)
    (p : O → Emit I Unit) (rp : O → Run I Unit) (hp : ∀ o, Exact (p o) (rp o)) :
    Exact (Emit.tabulate xs covers p) (tabulate xs covers rp) :=
  renameOutput_exact (gather_exact p rp hp xs) _

theorem gather_length {I J : Type} (p : J → Run I Unit) (cost : J → ℕ)
    (hp : ∀ j env, (p j env).1.length = cost j) (xs : List J) (env : I → ℕ) :
    (gather p xs env).1.length = (xs.map cost).sum := by
  induction xs generalizing env with
  | nil => rfl
  | cons j xs ih => simp [gather, renameOutput, seq, parallel, route, hp, ih]

/-- Since each gathered result is the last gate of its own block, its final
index is exactly the number of rows emitted for all subsequent blocks. -/
theorem gather_output {I J : Type} (p : J → Run I Unit) (cost : J → ℕ)
    (hp : ∀ j env, (p j env).1.length = cost j) (hz : ∀ j env, (p j env).2 () = 0)
    (xs : List J) (env : I → ℕ) (i : Fin xs.length) :
    (gather p xs env).2 i = ((xs.drop (i.val + 1)).map cost).sum := by
  induction xs generalizing env with
  | nil => exact Fin.elim0 i
  | cons j xs ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [gather, renameOutput, seq, parallel, route, shift, hz, gather_length p cost hp]
    · simpa [gather, renameOutput, seq, parallel, route, shift] using
        ih (shift (p j env).1.length env) i

theorem tabulate_output {I O : Type} [DecidableEq O] (xs : List O) (covers : ∀ o, o ∈ xs)
    (p : O → Run I Unit) (cost : O → ℕ)
    (hp : ∀ j env, (p j env).1.length = cost j) (hz : ∀ j env, (p j env).2 () = 0)
    (env : I → ℕ) (o : O) :
    (tabulate xs covers p env).2 o = ((xs.drop (xs.idxOf o + 1)).map cost).sum :=
  gather_output p cost hp hz xs env _

def listOr {I : Type} : List I → Run I Unit
  | [] => constant false
  | a :: xs => seq (parallel (route (fun _ : Unit => a)) (listOr xs)) (or (.inl ()) (.inr ()))

theorem listOr_exact {I : Type} (xs : List I) : Exact (Emit.listOr xs) (listOr xs) := by
  induction xs with
  | nil => exact constant_exact false
  | cons a xs ih => exact seq_exact (parallel_exact (route_exact _) ih) (or_exact _ _)

noncomputable def table {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (f : A → B) : Run A B :=
  tabulate (fixedEnum B) mem_fixedEnum (fun b => listOr ((fixedEnum A).filter (fun a => decide (f a = b))))

theorem table_exact {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (f : A → B) :
    Exact (Emit.table f) (table f) := tabulate_exact _ _ _ _ (fun _ => listOr_exact _)

noncomputable def cross {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    Run (A ⊕ B) (A × B) :=
  tabulate (fixedEnum (A × B)) mem_fixedEnum (fun ab => and (.inl ab.1) (.inr ab.2))

noncomputable def table₂ {A B D : Type} [Fintype A] [Fintype B] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq D] (f : A → B → D) : Run (A ⊕ B) D :=
  seq cross (table (fun ab : A × B => f ab.1 ab.2))

theorem table₂_exact {A B D : Type} [Fintype A] [Fintype B] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq D] (f : A → B → D) :
    Exact (Emit.table₂ f) (table₂ f) :=
  seq_exact (tabulate_exact _ _ _ _ (fun _ => and_exact _ _)) (table_exact _)

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Rows
