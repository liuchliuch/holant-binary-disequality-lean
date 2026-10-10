import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.BooleanAlgebra

/-! A finite branching certificate for containment of an arbitrary pairwise
orthogonal set in one of the supplied literal matching codes. The semantic set
is never enumerated or assumed to be one of the candidates. -/
namespace Holant.ReedMuller.LowArity

inductive Certificate (V M : Type*) where
  | leaf : M → Certificate V M
  | split : V → Certificate V M → Certificate V M → Certificate V M
  deriving Repr

variable {V M : Type*} [DecidableEq V]

def check (orth : V → V → Bool) (fits : M → V → Bool)
    (allowed : Finset V) : Certificate V M → Bool
  | .leaf m => decide (∀ v ∈ allowed, fits m v = true)
  | .split v yes no =>
      check orth fits (allowed.filter fun w => orth v w) yes &&
      check orth fits (allowed.erase v) no

theorem check_sound (orth : V → V → Bool) (fits : M → V → Bool)
    (T : Certificate V M) (allowed : Finset V) (hc : check orth fits allowed T = true)
    (D : V → Prop) (hD : ∀ v, D v → v ∈ allowed)
    (horth : ∀ v, D v → ∀ w, D w → orth v w = true) :
    ∃ m, ∀ v, D v → fits m v = true := by
  classical
  induction T generalizing allowed with
  | leaf m =>
    simp only [check,decide_eq_true_eq] at hc
    exact ⟨m,fun v hv => hc v (hD v hv)⟩
  | split v yes no ihY ihN =>
    simp only [check,Bool.and_eq_true] at hc
    by_cases hv : D v
    · apply ihY _ hc.1
      intro w hw
      exact Finset.mem_filter.mpr ⟨hD w hw,horth v hv w hw⟩
    · apply ihN _ hc.2
      intro w hw
      exact Finset.mem_erase.mpr ⟨(fun e => hv (e ▸ hw)),hD w hw⟩

end Holant.ReedMuller.LowArity
