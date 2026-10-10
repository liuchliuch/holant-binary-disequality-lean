import Holant.Proofs.Traversal.ArityTwo.PortWalk


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortWalk
open Holant Holant.Complexity
variable {s b : ℕ} {arity : ℕ → ℕ}
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)

def Covered (seen : List (r.Ports arity)) (p : r.Ports arity) : Prop :=
  ∃ q ∈ seen, q.1 = p.1

@[simp] theorem covered_nil (p : r.Ports arity) : ¬ Covered r [] p := by simp [Covered]

@[simp] theorem covered_cons (p : r.Ports arity) (seen : List (r.Ports arity)) (q : r.Ports arity) :
    Covered r (p::seen) q ↔ p.1 = q.1 ∨ Covered r seen q := by
  simp [Covered,or_and_right,exists_or]

@[simp] theorem covered_append (xs ys : List (r.Ports arity)) (p : r.Ports arity) :
    Covered r (xs++ys) p ↔ Covered r xs p ∨ Covered r ys p := by
  simp [Covered,or_and_right,exists_or]

theorem covered_of_mem {seen : List (r.Ports arity)} {p : r.Ports arity} (hp : p ∈ seen) :
    Covered r seen p := ⟨p,hp,rfl⟩

theorem covered_same {seen : List (r.Ports arity)} {p q : r.Ports arity}
    (hp : Covered r seen p) (hv : p.1 = q.1) : Covered r seen q := by
  rcases hp with ⟨u,hu,he⟩
  exact ⟨u,hu,he.trans hv⟩

theorem other_ne (p q : r.Ports arity) (ho : other r p = some q) : q ≠ p := by
  have hh := other_some r p q ho
  intro he
  have hi := p.2.isLt
  change p.2.val < degree (arity := arity) r p.1 at hi
  have hv : q.2.val = p.2.val := congrArg (fun x : r.Ports arity => x.2.val) he
  omega

theorem binary_ports (p out q : r.Ports arity) (ho : other r p = some out)
    (hv : q.1 = p.1) : q = p ∨ q = out := by
  have hs := other_some r p out ho
  rcases p with ⟨v,i⟩
  rcases out with ⟨w,j⟩
  rcases q with ⟨u,k⟩
  dsimp only at hv hs
  obtain ⟨hw,hj,hd⟩ := hs
  subst w
  subst u
  by_cases hk : k.val = i.val
  · left
    have hi : k = i := Fin.ext hk
    cases hi
    rfl
  · right
    have hi := i.isLt
    have hk' := k.isLt
    change arity (r.vertices.get v).1 = 2 at hd
    have he : k = j := Fin.ext (by omega)
    cases he
    rfl

/-- All earlier vertices are fully processed. `boundary` is absent for a
unary-started path, and is the unused entry port of the first cycle vertex. -/
structure Frontier (boundary : Option (r.Ports arity)) (seen : List (r.Ports arity))
    (p : r.Ports arity) : Prop where
  fresh : ¬ Covered r seen p
  back : Covered r seen (cross r h p)
  pending : ∀ q, Covered r seen q →
    boundary = some q ∨ Covered r seen (cross r h q) ∨ cross r h q = p
  boundary_mem : ∀ q, boundary = some q → q ∈ seen

theorem Frontier.not_mem {boundary : Option (r.Ports arity)} {seen : List (r.Ports arity)}
    {p : r.Ports arity} (F : Frontier r h boundary seen p) : p ∉ seen :=
  fun hp => F.fresh (covered_of_mem r hp)

theorem Frontier.other_fresh {boundary : Option (r.Ports arity)} {seen : List (r.Ports arity)}
    {p out : r.Ports arity} (F : Frontier r h boundary seen p) (ho : other r p = some out) :
    ¬ Covered r seen out := by
  intro hout
  exact F.fresh (covered_same r hout (other_some r p out ho).1)

/-- An attempted return to an old vertex can only be the protected initial
entry. In particular it cannot hit the opposite port of an interior vertex. -/
theorem Frontier.next_fresh_or_boundary {boundary : Option (r.Ports arity)}
    {seen : List (r.Ports arity)} {p out : r.Ports arity}
    (F : Frontier r h boundary seen p) (ho : other r p = some out) :
    ¬ Covered r (p::seen) (cross r h out) ∨ boundary = some (cross r h out) := by
  by_cases hn : Covered r (p::seen) (cross r h out)
  · right
    rcases (covered_cons r p seen _).mp hn with hv | hold
    · rcases binary_ports r p out (cross r h out) ho hv.symm with he | he
      · have hb := F.back
        rw [← he,cross_cross] at hb
        exact (F.other_fresh r h ho hb).elim
      · exact (cross_ne r h out he).elim
    · rcases F.pending _ hold with he | he | he
      · exact he
      · rw [cross_cross] at he
        exact (F.other_fresh r h ho he).elim
      · rw [cross_cross] at he
        exact (other_ne r p out ho he).elim
  · exact Or.inl hn

theorem Frontier.extend {boundary : Option (r.Ports arity)} {seen : List (r.Ports arity)}
    {p out : r.Ports arity} (F : Frontier r h boundary seen p) (ho : other r p = some out)
    (hn : ¬ Covered r (p::seen) (cross r h out)) :
    Frontier r h boundary (p::seen) (cross r h out) := by
  refine ⟨hn,?_,?_,?_⟩
  · rw [cross_cross,covered_cons]
    exact Or.inl (other_some r p out ho).1.symm
  · intro q hq
    rcases (covered_cons r p seen q).mp hq with hv | hold
    · rcases binary_ports r p out q ho hv.symm with hqp | hqo
      · subst q
        exact Or.inr (Or.inl ((covered_cons r p seen _).mpr (Or.inr F.back)))
      · subst q
        exact Or.inr (Or.inr rfl)
    · rcases F.pending q hold with hb | hc | hc
      · exact Or.inl hb
      · exact Or.inr (Or.inl ((covered_cons r p seen _).mpr (Or.inr hc)))
      · exact Or.inr (Or.inl (by rw [hc]; simp))
  · intro q hq
    exact List.mem_cons_of_mem p (F.boundary_mem q hq)

def Closed (seen : List (r.Ports arity)) : Prop :=
  ∀ p, Covered r seen p → Covered r seen (cross r h p)

def AlmostClosed (boundary : Option (r.Ports arity)) (seen : List (r.Ports arity)) : Prop :=
  ∀ p, Covered r seen p → boundary = some p ∨ Covered r seen (cross r h p)

theorem Frontier.finish_unary {boundary : Option (r.Ports arity)} {seen : List (r.Ports arity)}
    {p : r.Ports arity} (F : Frontier r h boundary seen p) (hp : degree (arity := arity) r p.1 = 1) :
    AlmostClosed r h boundary (p::seen) := by
  intro q hq
  rcases (covered_cons r p seen q).mp hq with hv | hold
  · have he := same_unary_vertex r p q hp hv.symm
    subst q
    exact Or.inr ((covered_cons r p seen _).mpr (Or.inr F.back))
  · rcases F.pending q hold with hb | hc | hc
    · exact Or.inl hb
    · exact Or.inr ((covered_cons r p seen _).mpr (Or.inr hc))
    · exact Or.inr (by rw [hc]; simp)

theorem Frontier.finish_cycle {boundary : Option (r.Ports arity)} {seen : List (r.Ports arity)}
    {p out : r.Ports arity} (F : Frontier r h boundary seen p) (ho : other r p = some out)
    (hb : boundary = some (cross r h out)) : Closed r h (p::seen) := by
  intro q hq
  rcases (covered_cons r p seen q).mp hq with hv | hold
  · rcases binary_ports r p out q ho hv.symm with hqp | hqo
    · subst q
      exact (covered_cons r p seen _).mpr (Or.inr F.back)
    · subst q
      exact (covered_cons r p seen _).mpr (Or.inr (covered_of_mem r (F.boundary_mem _ hb)))
  · rcases F.pending q hold with hq | hc | hc
    · have he : q = cross r h out := Option.some.inj (hq.symm.trans hb)
      rw [he,cross_cross,covered_cons]
      exact Or.inl (other_some r p out ho).1.symm
    · exact (covered_cons r p seen _).mpr (Or.inr hc)
    · rw [hc]
      simp

end Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortWalk
