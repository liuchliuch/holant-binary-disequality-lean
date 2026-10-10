import Holant.Proofs.CountingMachines.VerifierCircuit.Emit
import Mathlib.Data.Fintype.EquivFin

/-!
# Fixed finite truth tables and explicit list-indexed bit bundles

Ported reference proof. See the task validation reports.

Only label/state/symbol alphabets use `fixedEnum`. Capacity-dependent bundles
must supply their explicit list of coordinates to `tabulate`; no configuration
space is enumerated. Outputs are all existing NAND/constant Circuit nodes.
-/

namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit


namespace Emit

def gather {I J : Type} (p : J → Emit I Unit) : (xs : List J) → Emit I (Fin xs.length)
  | [] => route (fun i => Fin.elim0 i)
  | j :: xs => renameOutput (parallel (p j) (gather p xs))
      (Fin.cases (.inl ()) (fun i => .inr i))

theorem gather_denotes {I J : Type} (p : J → Emit I Unit)
    (f : J → (I → Bool) → Bool) (hp : ∀ j, Denotes (p j) (fun x _ => f j x))
    (xs : List J) : Denotes (gather p xs) (fun x i => f (xs.get i) x) := by
  induction xs with
  | nil =>
    have he : (fun (x : I → Bool) (i : Fin 0) => f (([] : List J).get i) x) =
        (fun (x : I → Bool) (i : Fin 0) => x (Fin.elim0 i)) := by
      funext x i
      exact Fin.elim0 i
    change Denotes (route (fun i : Fin 0 => Fin.elim0 i))
      (fun (x : I → Bool) (i : Fin 0) => f (([] : List J).get i) x)
    rw [he]
    exact route_denotes (fun i : Fin 0 => Fin.elim0 i)
  | cons j xs ih =>
    have h := renameOutput_denotes (parallel_denotes (hp j) ih)
      (Fin.cases (.inl ()) (fun i => .inr i))
    have he : (fun (x : I → Bool) (i : Fin (xs.length + 1)) => f ((j :: xs).get i) x) =
        (fun (x : I → Bool) (i : Fin (xs.length + 1)) =>
          Sum.elim (fun _ : Unit => f j x) (fun i => f (xs.get i) x)
            (Fin.cases (.inl ()) (fun i => .inr i) i)) := by
      funext x i
      refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    change Denotes (renameOutput (parallel (p j) (gather p xs))
      (Fin.cases (.inl ()) (fun i => .inr i)))
      (fun (x : I → Bool) (i : Fin (xs.length + 1)) => f ((j :: xs).get i) x)
    rw [he]
    exact h

def tabulate {I O : Type} [DecidableEq O] (xs : List O) (covers : ∀ o, o ∈ xs)
    (p : O → Emit I Unit) : Emit I O :=
  renameOutput (gather p xs) (fun o => ⟨xs.idxOf o, List.idxOf_lt_length_iff.mpr (covers o)⟩)

theorem tabulate_denotes {I O : Type} [DecidableEq O]
    (xs : List O) (covers : ∀ o, o ∈ xs) (p : O → Emit I Unit)
    (f : (I → Bool) → (O → Bool)) (hp : ∀ o, Denotes (p o) (fun x _ => f x o)) :
    Denotes (tabulate xs covers p) f := by
  have h := renameOutput_denotes (gather_denotes p (fun o x => f x o) hp xs)
    (fun o => (⟨xs.idxOf o, List.idxOf_lt_length_iff.mpr (covers o)⟩ : Fin xs.length))
  simpa [tabulate, List.get_eq_getElem] using h

theorem gather_adds {I J : Type} (p : J → Emit I Unit) (cost : J → ℕ)
    (hp : ∀ j, Adds (p j) (cost j)) (xs : List J) :
    Adds (gather p xs) ((xs.map cost).sum) := by
  induction xs with
  | nil => exact route_adds _
  | cons j xs ih =>
    simpa [gather, renameOutput] using seq_adds (parallel_adds (hp j) ih) (route_adds _)

theorem tabulate_adds {I O : Type} [DecidableEq O] (xs : List O) (covers : ∀ o, o ∈ xs)
    (p : O → Emit I Unit) (cost : O → ℕ) (hp : ∀ o, Adds (p o) (cost o)) :
    Adds (tabulate xs covers p) ((xs.map cost).sum) := by
  simpa [tabulate, renameOutput] using seq_adds (gather_adds p cost hp xs) (route_adds _)

def listOr {I : Type} : List I → Emit I Unit
  | [] => constant false
  | a :: as => seq (parallel (route (fun _ : Unit => a)) (listOr as)) (or (.inl ()) (.inr ()))

theorem listOr_denotes {I : Type} (xs : List I) :
    Denotes (listOr xs) (fun x _ => xs.any x) := by
  induction xs with
  | nil => exact constant_denotes false
  | cons a as ih =>
    simpa [listOr] using seq_denotes (parallel_denotes (route_denotes (fun _ : Unit => a)) ih)
      (or_denotes (.inl ()) (.inr ()))

theorem not_adds {I : Type} (a : I) : Adds (not a) 1 := nand_adds a a
theorem and_adds {I : Type} (a b : I) : Adds (and a b) 2 :=
  seq_adds (nand_adds a b) (not_adds ())
theorem or_adds {I : Type} (a b : I) : Adds (or a b) 3 := by
  unfold or
  exact seq_adds (parallel_adds (not_adds a) (not_adds b))
    (nand_adds (I := Unit ⊕ Unit) (.inl ()) (.inr ()))
theorem mux_adds {I : Type} (s t e : I) : Adds (mux s t e) 4 := by
  unfold mux
  exact seq_adds (parallel_adds (nand_adds s t)
    (seq_adds (parallel_adds (not_adds s) (route_adds (fun _ : Unit => e)))
      (nand_adds (I := Unit ⊕ Unit) (.inl ()) (.inr ()))))
    (nand_adds (I := Unit ⊕ Unit) (.inl ()) (.inr ()))

theorem listOr_adds {I : Type} (xs : List I) : Adds (listOr xs) (3 * xs.length + 1) := by
  induction xs with
  | nil => exact constant_adds false
  | cons a as ih =>
    simpa [listOr, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      seq_adds (parallel_adds (route_adds (fun _ : Unit => a)) ih)
        (or_adds (.inl ()) (.inr ()))

end Emit

noncomputable def fixedEnum (A : Type) [Fintype A] : List A :=
  List.ofFn (Fintype.equivFin A).symm

theorem mem_fixedEnum {A : Type} [Fintype A] (a : A) : a ∈ fixedEnum A := by
  apply List.mem_ofFn.mpr
  exact ⟨Fintype.equivFin A a, (Fintype.equivFin A).symm_apply_apply a⟩

@[simp] theorem fixedEnum_length (A : Type) [Fintype A] :
    (fixedEnum A).length = Fintype.card A := List.length_ofFn

def oneHot {A : Type} [DecidableEq A] (a : A) : A → Bool := fun b => decide (a = b)

theorem oneHot_injective {A : Type} [DecidableEq A] : Function.Injective (@oneHot A _) := by
  intro a b h
  have hh := congrFun h a
  have hba : b = a := by simpa [oneHot] using hh.symm
  exact hba.symm

namespace Emit

noncomputable def table {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) : Emit A B :=
  tabulate (fixedEnum B) mem_fixedEnum
    (fun b => listOr ((fixedEnum A).filter (fun a => decide (f a = b))))

noncomputable def tableValue {A B : Type} [Fintype A] [DecidableEq B] (f : A → B) (x : A → Bool) :
    B → Bool := fun b => ((fixedEnum A).filter (fun a => decide (f a = b))).any x

theorem table_denotes {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (f : A → B) :
    Denotes (table f) (tableValue f) :=
  tabulate_denotes _ _ _ _ (fun _ => listOr_denotes _)

theorem tableValue_oneHot {A B : Type} [Fintype A] [DecidableEq A] [DecidableEq B]
    (f : A → B) (a : A) : tableValue f (oneHot a) = oneHot (f a) := by
  funext b
  apply Bool.eq_iff_iff.mpr
  simp [tableValue, oneHot, List.any_eq_true, mem_fixedEnum]

/-- Two finite-control operands only; neither includes an entire tape. -/
noncomputable def cross {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    Emit (A ⊕ B) (A × B) :=
  tabulate (fixedEnum (A × B)) mem_fixedEnum (fun ab => and (.inl ab.1) (.inr ab.2))

theorem cross_denotes {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    Denotes (cross (A := A) (B := B)) (fun x ab => x (.inl ab.1) && x (.inr ab.2)) :=
  tabulate_denotes _ _ _ _ (fun _ => and_denotes _ _)

theorem cross_oneHot {A B : Type} [DecidableEq A] [DecidableEq B] (a : A) (b : B) :
    (fun ab : A × B => Sum.elim (oneHot a) (oneHot b) (.inl ab.1) &&
      Sum.elim (oneHot a) (oneHot b) (.inr ab.2)) = oneHot (a, b) := by
  funext ab
  rcases ab with ⟨a',b'⟩
  apply Bool.eq_iff_iff.mpr
  simp [oneHot,Prod.mk.injEq]

noncomputable def table₂ {A B D : Type} [Fintype A] [Fintype B] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq D] (f : A → B → D) : Emit (A ⊕ B) D :=
  seq cross (table (fun ab : A × B => f ab.1 ab.2))

theorem table₂_denotes {A B D : Type} [Fintype A] [Fintype B] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq D] (f : A → B → D) :
    Denotes (table₂ f)
      (fun x => tableValue (fun ab : A × B => f ab.1 ab.2)
        (fun ab => x (.inl ab.1) && x (.inr ab.2))) :=
  seq_denotes cross_denotes (table_denotes _)

end Emit
end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit
