import Holant.Certificates.NormalizedDihedralQ6.Data

namespace Holant.Certificates.NormalizedDihedralQ6
abbrev Remaining (p : Pair) := {i : Port // i ≠ p.1 ∧ i ≠ p.2}
def restrict (p : Pair) (x : Word) : Remaining p → Bool := fun i => x i.val

/-- A genuine deleted pair leaves exactly four original Boolean ports. -/
theorem remaining_card : ∀ p : Pair, p.1 ≠ p.2 → Fintype.card (Remaining p) = 4 := by decide

theorem restrict_project (p : Pair) (x : Word) : restrict p (project p x) = restrict p x := by
  funext i
  simp [restrict,project,i.property.1,i.property.2]

/-- The zero-coordinate representation retains exactly the remaining-port information. -/
theorem project_eq_iff_restrict_eq (p : Pair) (x y : Word) :
    project p x = project p y ↔ restrict p x = restrict p y := by
  constructor
  · intro h
    simpa only [restrict_project] using congrArg (restrict p) h
  · intro h
    funext i
    by_cases hi : i = p.1 ∨ i = p.2
    · simp [project,hi]
    · have h1 : i ≠ p.1 := fun h => hi (.inl h)
      have h2 : i ≠ p.2 := fun h => hi (.inr h)
      simpa [restrict,project,hi] using congrFun h ⟨i,h1,h2⟩

theorem injectiveProjection_restriction (S : Support) (p : Pair) (γ : Bool) :
    injectiveProjection S p γ ↔ Set.InjOn (restrict p) (slice S p γ : Set Word) := by
  constructor
  · intro h x hx y hy he
    exact h hx hy ((project_eq_iff_restrict_eq p x y).mpr he)
  · intro h x hx y hy he
    exact h hx hy ((project_eq_iff_restrict_eq p x y).mp he)

/-- Equality of projected support sizes with literal deletion of the selected ports. -/
theorem projected_card_restriction (S : Support) (p : Pair) (γ : Bool) :
    (projected S p γ).card = ((slice S p γ).image (restrict p)).card := by
  have hi : Set.InjOn (restrict p) (projected S p γ : Set Word) := by
    intro x hx y hy he
    rcases Finset.mem_image.mp hx with ⟨a,ha,rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b,hb,rfl⟩
    apply (project_eq_iff_restrict_eq p a b).mpr
    simpa only [restrict_project] using he
  have hc := Finset.card_image_of_injOn hi
  have hm : (projected S p γ).image (restrict p) = (slice S p γ).image (restrict p) := by
    simp only [projected,Finset.image_image]
    congr 1
    funext x
    exact restrict_project p x
  rw [hm] at hc
  exact hc.symm

end Holant.Certificates.NormalizedDihedralQ6
