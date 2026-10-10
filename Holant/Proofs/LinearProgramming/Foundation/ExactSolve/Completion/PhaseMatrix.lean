import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.PhaseOne
import Mathlib.Data.List.OfFn

open Holant.LocalDrafts.TraversalCompletion.RationalLP

/-! Rational LP foundation adapted into the exclusive task namespace.
The complete integer phase-I matrix in the existing bounded-LP codec.
Variables are ordered x,u,v,r,s,t; rows are Ax-Mu+Mv=b, u+r-t=0,
v+s-t=0. All variables retain the existing unit-box bounds.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion.PhaseMatrix
open Codec
open scoped BigOperators

def width (d : Raw) : ℕ := d.dimension+d.rowCount+d.rowCount+d.rowCount+d.rowCount+1
def height (d : Raw) : ℕ := d.rowCount+d.rowCount+d.rowCount
def blocks {α : Type} {n m : ℕ} (x : Fin n → α) (u v r s : Fin m → α) (t : α) :
    Fin (n+m+m+m+m+1) → α := Fin.snoc (Fin.append (Fin.append (Fin.append (Fin.append x u) v) r) s) t

def unit (m : ℕ) (i : Fin m) (a : ℤ) : Fin m → ℤ := fun j => if j=i then a else 0
def balance (d : Raw) (i : Fin d.rowCount) : Fin (width d) → ℤ :=
  blocks (d.coefficient i) (unit _ i (-(PhaseOne.scale d : ℤ)))
    (unit _ i (PhaseOne.scale d : ℤ)) (fun _ => 0) (fun _ => 0) 0
def positive (d : Raw) (i : Fin d.rowCount) : Fin (width d) → ℤ :=
  blocks (fun _ => 0) (unit _ i 1) (fun _ => 0) (unit _ i 1) (fun _ => 0) (-1)
def negative (d : Raw) (i : Fin d.rowCount) : Fin (width d) → ℤ :=
  blocks (fun _ => 0) (fun _ => 0) (unit _ i 1) (fun _ => 0) (unit _ i 1) (-1)
def coefficients (d : Raw) : Fin (height d) → Fin (width d) → ℤ :=
  Fin.append (Fin.append (balance d) (positive d)) (negative d)
def constants (d : Raw) : Fin (height d) → ℤ :=
  Fin.append (Fin.append d.constant (fun _ => 0)) (fun _ => 0)
def value (d : Raw) : Input := pack (height d) (width d) (coefficients d) (constants d)

def vector (d : Raw) (p : PhaseOne.Point d) : Fin (width d) → ℚ :=
  blocks p.original p.positive p.negative p.slackPositive p.slackNegative p.objective
def objective (d : Raw) : Fin (width d) := Fin.last _

def left {α : Type} {n m : ℕ} (z : Fin (n+m) → α) : Fin n → α := fun i => z (i.castAdd m)
def right {α : Type} {n m : ℕ} (z : Fin (n+m) → α) : Fin m → α := fun i => z (i.natAdd n)

theorem append_split {α : Type} {n m : ℕ} (z : Fin (n+m) → α) :
    Fin.append (left z) (right z)=z := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left, left]
  · simp only [Fin.append_right, right]

def point (d : Raw) (y : Fin (width d) → ℚ) : PhaseOne.Point d where
  original := left (left (left (left (Fin.init y))))
  positive := right (left (left (left (Fin.init y))))
  negative := right (left (left (Fin.init y)))
  slackPositive := right (left (Fin.init y))
  slackNegative := right (Fin.init y)
  objective := y (objective d)

theorem vector_point (d : Raw) (y : Fin (width d) → ℚ) : vector d (point d y)=y := by
  dsimp only [vector,point,blocks,objective]
  rw [append_split,append_split,append_split,append_split]
  change Fin.snoc (Fin.init y) (y (Fin.last _)) = y
  exact Fin.snoc_init_self y

theorem point_vector (d : Raw) (p : PhaseOne.Point d) : point d (vector d p)=p := by
  ext i <;> simp [point,vector,blocks,left,right,objective]

theorem forall_append {α : Type} {n m : ℕ} (a : Fin n → α) (b : Fin m → α) (P : α → Prop) :
    (∀ i, P (Fin.append a b i)) ↔ (∀ i, P (a i)) ∧ ∀ i, P (b i) := by
  constructor
  · intro h
    exact ⟨fun i => by simpa only [Fin.append_left] using h (i.castAdd m),
      fun i => by simpa only [Fin.append_right] using h (i.natAdd n)⟩
  · rintro ⟨ha,hb⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using ha j
    · simpa only [Fin.append_right] using hb j

theorem forall_snoc {α : Type} {n : ℕ} (a : Fin n → α) (b : α) (P : α → Prop) :
    (∀ i, P ((Fin.snoc a b : Fin (n+1) → α) i)) ↔ (∀ i, P (a i)) ∧ P b := by
  constructor
  · intro h
    exact ⟨fun i => by simpa only [Fin.snoc_castSucc] using h i.castSucc,
      by simpa only [Fin.snoc_last] using h (Fin.last n)⟩
  · rintro ⟨ha,hb⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hb
    · simpa only [Fin.snoc_castSucc] using ha j

theorem balance_eval (d : Raw) (p : PhaseOne.Point d) (i : Fin d.rowCount) :
    (∑ j, (balance d i j : ℚ)*vector d p j) =
      (∑ j, (d.coefficient i j : ℚ)*p.original j) -
        (PhaseOne.scale d : ℚ)*p.positive i + (PhaseOne.scale d : ℚ)*p.negative i := by
  unfold balance vector blocks width
  simp only [Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,
    Fin.sum_univ_add,Fin.append_left,Fin.append_right]
  simp [unit] <;> ring

theorem positive_eval (d : Raw) (p : PhaseOne.Point d) (i : Fin d.rowCount) :
    (∑ j, (positive d i j : ℚ)*vector d p j)=p.positive i+p.slackPositive i-p.objective := by
  unfold positive vector blocks width
  simp only [Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,
    Fin.sum_univ_add,Fin.append_left,Fin.append_right]
  simp [unit] <;> ring

theorem negative_eval (d : Raw) (p : PhaseOne.Point d) (i : Fin d.rowCount) :
    (∑ j, (negative d i j : ℚ)*vector d p j)=p.negative i+p.slackNegative i-p.objective := by
  unfold negative vector blocks width
  simp only [Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,
    Fin.sum_univ_add,Fin.append_left,Fin.append_right]
  simp [unit] <;> ring

theorem equations (d : Raw) (p : PhaseOne.Point d) :
    (∀ i, ∑ j, (coefficients d i j : ℚ)*vector d p j=(constants d i : ℚ)) ↔
      (∀ i, (∑ j, (d.coefficient i j : ℚ)*p.original j)-(d.constant i : ℚ)=
        (PhaseOne.scale d : ℚ)*(p.positive i-p.negative i)) ∧
      (∀ i, p.positive i+p.slackPositive i=p.objective) ∧
      (∀ i, p.negative i+p.slackNegative i=p.objective) := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro i
      have he := h ((i.castAdd d.rowCount).castAdd d.rowCount)
      simp only [coefficients,constants,Fin.append_left,balance_eval] at he
      nlinarith
    · intro i
      have he := h ((i.natAdd d.rowCount).castAdd d.rowCount)
      simp only [coefficients,constants,Fin.append_left,Fin.append_right,positive_eval,Int.cast_zero] at he
      linarith
    · intro i
      have he := h (i.natAdd (d.rowCount+d.rowCount))
      simp only [coefficients,constants,Fin.append_right,negative_eval,Int.cast_zero] at he
      linarith
  · rintro ⟨ha,hu,hv⟩ i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
      · simp only [coefficients,constants,Fin.append_left,balance_eval]
        nlinarith [ha k]
      · simp only [coefficients,constants,Fin.append_left,Fin.append_right,positive_eval,Int.cast_zero]
        linarith [hu k]
    · simp only [coefficients,constants,Fin.append_right,negative_eval,Int.cast_zero]
      linarith [hv k]

private theorem bounds_vector (d : Raw) (p : PhaseOne.Point d) :
    (∀ j, 0 ≤ vector d p j ∧ vector d p j ≤ 1) ↔
      (∀ j, 0 ≤ p.original j ∧ p.original j ≤ 1) ∧
      (∀ i, 0 ≤ p.positive i ∧ p.positive i ≤ 1) ∧
      (∀ i, 0 ≤ p.negative i ∧ p.negative i ≤ 1) ∧
      (∀ i, 0 ≤ p.slackPositive i ∧ p.slackPositive i ≤ 1) ∧
      (∀ i, 0 ≤ p.slackNegative i ∧ p.slackNegative i ≤ 1) ∧
      (0 ≤ p.objective ∧ p.objective ≤ 1) := by
  change (∀ j, 0 ≤ blocks p.original p.positive p.negative p.slackPositive
    p.slackNegative p.objective j ∧ blocks p.original p.positive p.negative
    p.slackPositive p.slackNegative p.objective j ≤ 1) ↔ _
  unfold blocks
  rw [forall_snoc _ _ (fun q : ℚ => 0 ≤ q ∧ q ≤ 1),
    forall_append _ _ (fun q : ℚ => 0 ≤ q ∧ q ≤ 1),
    forall_append _ _ (fun q : ℚ => 0 ≤ q ∧ q ≤ 1),
    forall_append _ _ (fun q : ℚ => 0 ≤ q ∧ q ≤ 1),
    forall_append _ _ (fun q : ℚ => 0 ≤ q ∧ q ≤ 1)]
  tauto

theorem feasible_vector (d : Raw) (p : PhaseOne.Point d) :
    Codec.Feasible (value d).val (vector d p) ↔ PhaseOne.Feasible d p := by
  change Codec.Feasible (pack (height d) (width d) (coefficients d) (constants d)).val
    (vector d p) ↔ PhaseOne.Feasible d p
  rw [pack_feasible,equations,bounds_vector]
  unfold PhaseOne.Feasible
  constructor
  · rintro ⟨⟨ha,hu,hv⟩,hx,hp,hn,hs,ht,ho⟩
    exact ⟨hx,fun i => ⟨(hp i).1,(hp i).2,(hn i).1,(hn i).2,
      (hs i).1,(hs i).2,(ht i).1,(ht i).2⟩,ho.1,ho.2,ha,hu,hv⟩
  · rintro ⟨hx,hp,ho0,ho1,ha,hu,hv⟩
    exact ⟨⟨ha,hu,hv⟩,hx,
      fun i => ⟨(hp i).1,(hp i).2.1⟩,
      fun i => ⟨(hp i).2.2.1,(hp i).2.2.2.1⟩,
      fun i => ⟨(hp i).2.2.2.2.1,(hp i).2.2.2.2.2.1⟩,
      fun i => ⟨(hp i).2.2.2.2.2.2.1,(hp i).2.2.2.2.2.2.2⟩,ho0,ho1⟩

theorem feasible_point (d : Raw) (y : Fin (width d) → ℚ) :
    Codec.Feasible (value d).val y ↔ PhaseOne.Feasible d (point d y) := by
  rw [← feasible_vector,vector_point]

theorem nonempty (d : Raw) : ∃ y, Codec.Feasible (value d).val y :=
  ⟨vector d (PhaseOne.start d),(feasible_vector d _).mpr (PhaseOne.start_feasible d)⟩

theorem zero_iff (d : Raw) : (∃ y, Codec.Feasible (value d).val y ∧ y (objective d)=0) ↔
    ∃ x, Codec.Feasible d x := by
  constructor
  · rintro ⟨y,hy,ht⟩
    exact ⟨(point d y).original,PhaseOne.recover_zero d _ ((feasible_point d y).mp hy) ht⟩
  · rintro ⟨x,hx⟩
    refine ⟨vector d (PhaseOne.embed d x),(feasible_vector d _).mpr (PhaseOne.embed_feasible d x hx),?_⟩
    simp [vector,blocks,objective,PhaseOne.embed]

end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion.PhaseMatrix
