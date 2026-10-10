import Holant.Dihedral.CompatibleCoefficientLine.MatchingAlignment

/-! Equality of the actual original partner functions constructs the edge-ID
bijection and endpoint flips used by the source compatibility bridge. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Dihedral.CompatibleCoefficientLine
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Dihedral.EndpointParallelogram

/-- No enumeration or alignment certificate is assumed beyond literal equality
of the original perfect matching. -/
def MatchingAlignment.ofMate {r : ℕ}
    (p₀ p₁ : (Fin (r+1) × Bool) ≃ Fin (2*r+2))
    (h : ∀ u, (Pairing.ofPorts p₀).mate u = (Pairing.ofPorts p₁).mate u) :
    MatchingAlignment p₀ p₁ := by
  let edge : Fin (r+1) → Fin (r+1) := fun e => (p₁.symm (p₀ (e,false))).1
  let flip : Fin (r+1) → Bool := fun e => (p₁.symm (p₀ (e,false))).2
  have h₀ (e : Fin (r+1)) : p₁ (edge e,flip e)=p₀ (e,false) := by
    exact p₁.apply_symm_apply _
  have h₁ (e : Fin (r+1)) : p₁ (edge e,!(flip e))=p₀ (e,true) := by
    have hh := h (p₀ (e,false))
    simpa only [Pairing.ofPorts,Equiv.symm_apply_apply,Bool.not_false] using hh.symm
  have hinj : Function.Injective edge := by
    intro e f hef
    by_cases hh : flip e=flip f
    · have hp : p₀ (e,false)=p₀ (f,false) := by rw [← h₀ e,← h₀ f,hef,hh]
      exact congrArg Prod.fst (p₀.injective hp)
    · have hh' : flip e=!(flip f) := by
        cases he : flip e <;> cases hf : flip f <;> simp_all
      have hp : p₀ (e,false)=p₀ (f,true) := by rw [← h₀ e,← h₁ f,hef,hh']
      have hp' := congrArg Prod.snd (p₀.injective hp)
      cases hp'
  refine {
    edge := Equiv.ofBijective edge ⟨hinj,Finite.surjective_of_injective hinj⟩
    flip := flip
    endpoints := ?_ }
  intro e b
  cases b
  · change p₁ (edge e,false ^^ flip e)=p₀ (e,false)
    simpa using h₀ e
  · change p₁ (edge e,true ^^ flip e)=p₀ (e,true)
    simpa using h₁ e

end Holant.Dihedral.CompatibleCoefficientLine
