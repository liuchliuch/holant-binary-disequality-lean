import Holant.OneHot.Decomposition.Rooted
import Mathlib.Combinatorics.Quiver.Arborescence

/-!
# Exact descendant partitions of an extracted rooted tree

This file gives the finite, disjoint recursive vertex partition needed to
unfold the extracted parent structure into the existing ordered tree datatype.
Its paths use only selected original parent edges.
-/

namespace Holant.OneHot.Decomposition.RootedSpanning

variable {V E : Type*} {endpoint : E → Bool → V} {root : V}
variable (t : RootedSpanning endpoint root)

open scoped Classical

/-- A total parent function; only the root maps to itself. -/
noncomputable def parent (v : V) : V :=
  if h : v = root then root else endpoint (t.parentEnd ⟨v, h⟩).1 (!(t.parentEnd ⟨v, h⟩).2)

@[simp] theorem parent_root : t.parent root = root := by simp [parent]

theorem parent_lt (v : V) (h : v ≠ root) : t.depth (t.parent v) < t.depth v := by
  simpa only [parent, dite_eq_right h] using t.parent_depth_lt ⟨v, h⟩

/-- Genuine children, each identified by its own original non-root vertex. -/
abbrev Child (v : V) := {u : V // u ≠ root ∧ t.parent u = v}

/-- The quiver of selected parent arrows, directed away from the root. -/
@[instance_reducible] def quiver : Quiver V where
  Hom u v := PLift (v ≠ root ∧ t.parent v = u)

/-- Paths in the selected rooted tree; no surplus edges occur. -/
abbrev Path (u v : V) := @Quiver.Path V t.quiver u v

/-- Rank descent and the unique original parent certify an arborescence. -/
@[instance_reducible] noncomputable def arborescence : @Quiver.Arborescence V t.quiver := by
  let := t.quiver
  apply Quiver.arborescenceMk root t.depth
  · intro a b e
    have h := t.parent_lt b e.down.1
    simpa only [e.down.2] using h
  · intro a b c e f
    have h : a = b := e.down.2.symm.trans f.down.2
    subst b
    refine ⟨rfl, ?_⟩
    cases e; cases f; rfl
  · intro v
    by_cases hv : v = root
    · exact Or.inl hv
    · exact Or.inr ⟨t.parent v, ⟨⟨hv, rfl⟩⟩⟩

/-- There is a unique path from the extracted root to each original vertex. -/
noncomputable def rootPath (v : V) : t.Path root v :=
  (t.arborescence.uniquePath v).default

instance pathSubsingleton (u v : V) : Subsingleton (t.Path u v) := by
  let := t.quiver
  refine ⟨fun p q => ?_⟩
  apply (t.rootPath u).comp_injective_right
  exact (t.arborescence.uniquePath v).uniq _ |>.trans
    ((t.arborescence.uniquePath v).uniq _).symm

/-- Along every downward path the original shortest-walk rank is nondecreasing. -/
theorem path_depth_le {u v : V} (p : t.Path u v) : t.depth u ≤ t.depth v := by
  induction p with
  | nil => exact le_rfl
  | @cons b c p e ih =>
    have h := t.parent_lt c e.down.1
    rw [e.down.2] at h
    exact Nat.le_trans ih h.le

/-- All original vertices below a specified root, with no duplicate addresses. -/
def Descendant (v : V) := {w : V // Nonempty (t.Path v w)}

noncomputable instance descendantFintype [Fintype V] (v : V) : Fintype (t.Descendant v) := by
  classical
  unfold Descendant
  infer_instance

/-- The descendants of the original root include every original vertex exactly once. -/
noncomputable def rootDescendantEquiv : t.Descendant root ≃ V :=
  Equiv.subtypeUnivEquiv (fun v => ⟨t.rootPath v⟩)

/-- List the target vertex of each path arrow, in reverse traversal order. -/
def pathTargets {u v : V} (p : t.Path u v) : List V := by
  let := t.quiver
  induction p with
  | nil => exact []
  | @cons b c p e ih => exact c :: ih

@[simp] theorem pathTargets_comp {u v w : V} (p : t.Path u v) (q : t.Path v w) :
    t.pathTargets (@Quiver.Path.comp V t.quiver _ _ _ p q) =
      t.pathTargets q ++ t.pathTargets p := by
  induction q with
  | nil => rfl
  | @cons b c q e ih =>
    change c :: t.pathTargets (@Quiver.Path.comp V t.quiver _ _ _ p q) =
      c :: (t.pathTargets q ++ t.pathTargets p)
    rw [ih]

private def descendantSplitMap (v : V) :
    (Unit ⊕ Σ u : t.Child v, t.Descendant u.1) → t.Descendant v
  | .inl _ => ⟨v, ⟨@Quiver.Path.nil V t.quiver v⟩⟩
  | .inr ⟨u, w⟩ => ⟨w.1, by
      obtain ⟨p⟩ := w.2
      let e : @Quiver.Hom V t.quiver v u.1 := ⟨u.2⟩
      exact ⟨@Quiver.Path.comp V t.quiver _ _ _
        (@Quiver.Hom.toPath V t.quiver _ _ e) p⟩⟩

private theorem descendantSplitMap_injective (v : V) :
    Function.Injective (t.descendantSplitMap v) := by
  let := t.quiver
  intro x y h
  have hval := congrArg Subtype.val h
  cases x with
  | inl a =>
    cases y with
    | inl b => cases a; cases b; rfl
    | inr y =>
      obtain ⟨u, w⟩ := y
      obtain ⟨p⟩ := w.2
      have h₁ := t.parent_lt u.1 u.2.1
      have h₂ := t.path_depth_le p
      rw [u.2.2] at h₁
      change v = w.1 at hval
      rw [← hval] at h₂
      exact (Nat.not_lt_of_ge h₂ h₁).elim
  | inr x =>
    obtain ⟨u, w⟩ := x
    cases y with
    | inl b =>
      obtain ⟨p⟩ := w.2
      have h₁ := t.parent_lt u.1 u.2.1
      have h₂ := t.path_depth_le p
      rw [u.2.2] at h₁
      change w.1 = v at hval
      rw [hval] at h₂
      exact (Nat.not_lt_of_ge h₂ h₁).elim
    | inr y =>
      obtain ⟨u', w'⟩ := y
      change w.1 = w'.1 at hval
      obtain ⟨z, hz⟩ := w
      obtain ⟨z', hz'⟩ := w'
      dsimp at hval
      subst z'
      obtain ⟨p⟩ := hz
      obtain ⟨q⟩ := hz'
      let e : @Quiver.Hom V t.quiver v u.1 := ⟨u.2⟩
      let f : @Quiver.Hom V t.quiver v u'.1 := ⟨u'.2⟩
      have hp : e.toPath.comp p = f.toPath.comp q := Subsingleton.elim _ _
      have hl := congrArg (fun r : t.Path v z => (t.pathTargets r).getLast?) hp
      rw [t.pathTargets_comp, t.pathTargets_comp] at hl
      change (t.pathTargets p ++ [u.1]).getLast? = (t.pathTargets q ++ [u'.1]).getLast? at hl
      have hu : u = u' := by
        apply Subtype.ext
        simpa only [List.getLast?_concat, Option.some.injEq] using hl
      subst u'
      rfl

private theorem descendantSplitMap_surjective (v : V) :
    Function.Surjective (t.descendantSplitMap v) := by
  let := t.quiver
  rintro ⟨w, ⟨p⟩⟩
  cases hlen : p.length with
  | zero =>
    have h := p.eq_of_length_zero hlen
    subst w
    exact ⟨.inl (), rfl⟩
  | succ n =>
    obtain ⟨u, e, q, _, _⟩ := p.eq_toPath_comp_of_length_eq_succ hlen
    exact ⟨.inr ⟨⟨u, e.down⟩, ⟨w, ⟨q⟩⟩⟩, rfl⟩

/-- The descendant set is exactly one root plus a disjoint child-subtree family.
This is proved from the extracted parent arrows, not assumed as tree input. -/
noncomputable def descendantSplit (v : V) :
    (Unit ⊕ Σ u : t.Child v, t.Descendant u.1) ≃ t.Descendant v :=
  Equiv.ofBijective (t.descendantSplitMap v)
    ⟨t.descendantSplitMap_injective v, t.descendantSplitMap_surjective v⟩

@[simp] theorem descendantSplit_inl (v : V) :
    t.descendantSplit v (.inl ()) = ⟨v, ⟨@Quiver.Path.nil V t.quiver v⟩⟩ := rfl

@[simp] theorem descendantSplit_inr (v : V) (u : t.Child v) (w : t.Descendant u.1) :
    (t.descendantSplit v (.inr ⟨u, w⟩)).1 = w.1 := rfl

/-- Each child subtree is strictly smaller than the current descendant set. -/
theorem descendant_card_child_lt [Fintype V] (v : V) (u : t.Child v) :
    Fintype.card (t.Descendant u.1) < Fintype.card (t.Descendant v) := by
  have hc := Fintype.card_congr (t.descendantSplit v)
  rw [Fintype.card_sum, Fintype.card_sigma, Fintype.card_unit] at hc
  have hu : Fintype.card (t.Descendant u.1) ≤
      Fintype.card (Σ c : t.Child v, t.Descendant c.1) :=
    Fintype.card_le_of_injective
      (fun x : t.Descendant u.1 => (⟨u, x⟩ : Σ c : t.Child v, t.Descendant c.1))
      (by intro x y h; exact (Sigma.mk.inj h).2.eq)
  rw [Fintype.card_sigma] at hu
  omega

end Holant.OneHot.Decomposition.RootedSpanning
