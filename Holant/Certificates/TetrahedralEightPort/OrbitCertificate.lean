import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite

/-! Finite certificates for genuine generated orbits. Closure alone only gives
an upper bound: the separate decreasing predecessor certificate below proves
that every listed point is reached from the specified base. -/
namespace Holant.Certificates.TetrahedralEightPort

inductive Generated {α γ : Type*} (step : γ → α → α) (base : α) : α → Prop
  | base : Generated step base base
  | next (g : γ) {x : α} : Generated step base x → Generated step base (step g x)

namespace Generated

theorem trans {α γ : Type*} {step : γ → α → α} {a b c : α}
    (hab : Generated step a b) (hbc : Generated step b c) : Generated step a c := by
  induction hbc with
  | base => exact hab
  | next g h ih => exact .next g ih

theorem monotone {α γ δ : Type*} {step : γ → α → α} {other : δ → α → α}
    {base : α} (h : ∀ g x, Generated other x (step g x)) {x : α}
    (hx : Generated step base x) : Generated other base x := by
  induction hx with
  | base => exact .base
  | @next g x hx ih => exact ih.trans (h g x)

end Generated

/-- The data may be produced externally. Every property required for the orbit
identification remains an explicit Lean proposition. -/
structure OrbitCertificate {α γ : Type*} (step : γ → α → α) (base : α) (n : ℕ) where
  point : Fin n → α
  root : Fin n
  successor : γ → Fin n → Fin n
  rank : Fin n → ℕ
  predecessor : Fin n → Fin n
  predecessorGenerator : Fin n → γ
  base_eq : point root = base
  closed : ∀ g i, step g (point i) = point (successor g i)
  decreases : ∀ i, i ≠ root → rank (predecessor i) < rank i
  predecessor_eq : ∀ i, i ≠ root →
    step (predecessorGenerator i) (point (predecessor i)) = point i

namespace OrbitCertificate

variable {α γ : Type*} {step : γ → α → α} {base : α} {n : ℕ}

theorem reachable (C : OrbitCertificate step base n) (i : Fin n) :
    Generated step base (C.point i) := by
  have h : ∀ r, ∀ i : Fin n, C.rank i = r → Generated step base (C.point i) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro i hi
      by_cases he : i = C.root
      · subst i
        rw [C.base_eq]
        exact .base
      · rw [← C.predecessor_eq i he]
        apply Generated.next
        exact ih (C.rank (C.predecessor i)) (hi ▸ C.decreases i he) _ rfl
  exact h (C.rank i) i rfl

theorem complete (C : OrbitCertificate step base n) {x : α}
    (hx : Generated step base x) : ∃ i, C.point i = x := by
  induction hx with
  | base => exact ⟨C.root,C.base_eq⟩
  | next g h ih =>
    obtain ⟨i,rfl⟩ := ih
    exact ⟨C.successor g i,(C.closed g i).symm⟩

theorem generated_iff (C : OrbitCertificate step base n) (x : α) :
    Generated step base x ↔ ∃ i, C.point i = x :=
  ⟨C.complete,fun ⟨i,hi⟩ => hi ▸ C.reachable i⟩

/-- Injectivity of the represented points, rather than merely the certificate
indices, is what turns the finite list into the exact orbit cardinality. -/
noncomputable def equiv (C : OrbitCertificate step base n) (hi : Function.Injective C.point) :
    Fin n ≃ {x // Generated step base x} :=
  Equiv.ofBijective (fun i => ⟨C.point i,C.reachable i⟩) ⟨
    fun i j h => hi (congrArg Subtype.val h),
    fun x => by obtain ⟨i,he⟩ := C.complete x.property; exact ⟨i,Subtype.ext he⟩⟩

theorem card (C : OrbitCertificate step base n) (hi : Function.Injective C.point) :
    Nat.card {x // Generated step base x} = n := by
  rw [← Nat.card_congr (C.equiv hi),Nat.card_fin]

end OrbitCertificate
end Holant.Certificates.TetrahedralEightPort
