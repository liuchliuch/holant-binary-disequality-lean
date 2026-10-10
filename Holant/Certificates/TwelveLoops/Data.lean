import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

/-! The exact finite state space and twelve ordered coefficient pairs in
Proposition A.1. Gaussian integers use explicit integer coordinates. No numerical
approximation, external verifier result, or implicit state restriction is used. -/
namespace Holant.Certificates.TwelveLoops

abbrev Gaussian := ℤ × ℤ
def gadd (a b : Gaussian) : Gaussian := (a.1+b.1,a.2+b.2)
def gmul (a b : Gaussian) : Gaussian := (a.1*b.1-a.2*b.2,a.1*b.2+a.2*b.1)
def gnorm (a : Gaussian) : ℤ := a.1*a.1+a.2*a.2
def fourthRoot : Fin 4 → Gaussian := ![(1,0),(0,1),(-1,0),(0,-1)]

abbrev AState := Fin 4 × Fin 4 × Fin 4
abbrev BState := Fin 4 × Fin 4 × Fin 4 × Fin 4
abbrev State := AState × BState

def alpha (s : State) : Fin 4 → Fin 4 := ![0,s.1.1,s.1.2.1,s.1.2.2]
def beta (s : State) : Fin 4 → Fin 4 := ![s.2.1,s.2.2.1,s.2.2.2.1,s.2.2.2.2]
def a (s : State) (j : Fin 4) : Gaussian := fourthRoot (alpha s j)
def b (s : State) (j : Fin 4) : Gaussian := fourthRoot (beta s j)

def pairs : Fin 6 → Fin 4 × Fin 4 := ![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def complements : Fin 6 → Fin 4 × Fin 4 := ![(2,3),(1,3),(1,2),(0,3),(0,2),(0,1)]

def nativePair (s : State) (p : Fin 6) : Gaussian × Gaussian :=
  let ij := pairs p
  (gadd (a s ij.1) (a s ij.2),gadd (b s ij.1) (b s ij.2))
def equalityPair (s : State) (p : Fin 6) : Gaussian × Gaussian :=
  let kl := complements p
  (gadd (a s kl.2) (b s kl.1),gadd (a s kl.1) (b s kl.2))
def loopPairs (s : State) : List (Gaussian × Gaussian) :=
  (List.ofFn (nativePair s)) ++ List.ofFn (equalityPair s)

def rankOneTest (p : Gaussian × Gaussian) : Bool := (p.1 == (0,0)) != (p.2 == (0,0))
def infiniteTest (p : Gaussian × Gaussian) : Bool :=
  p.1 != (0,0) && p.2 != (0,0) && gnorm p.1 != gnorm p.2

inductive Route where
  | rankOne | infiniteOrder | remaining
  deriving DecidableEq, Repr

def classify (s : State) : Route :=
  if (loopPairs s).any rankOneTest then .rankOne
  else if (loopPairs s).any infiniteTest then .infiniteOrder else .remaining

@[simp] theorem loopPairs_length (s : State) : (loopPairs s).length = 12 := by
  simp [loopPairs]

theorem state_count : Fintype.card State = 16384 := by simp [State,AState,BState]

theorem complete_pair_list : ∀ i j : Fin 4, i < j ↔ ∃ p, pairs p = (i,j) := by decide

theorem complement_correct : ∀ p : Fin 6,
    (pairs p).1 < (pairs p).2 ∧ (complements p).1 < (complements p).2 ∧
    ∀ j : Fin 4, (j = (complements p).1 ∨ j = (complements p).2) ↔
      j ≠ (pairs p).1 ∧ j ≠ (pairs p).2 := by decide

theorem rankOne_iff (s : State) : classify s = .rankOne ↔
    ∃ p ∈ loopPairs s,
      (p.1 = (0,0) ∧ p.2 ≠ (0,0)) ∨ (p.1 ≠ (0,0) ∧ p.2 = (0,0)) := by
  have htest (p : Gaussian × Gaussian) : rankOneTest p = true ↔
      (p.1 = (0,0) ∧ p.2 ≠ (0,0)) ∨ (p.1 ≠ (0,0) ∧ p.2 = (0,0)) := by
    by_cases h₁ : p.1 = (0,0) <;> by_cases h₂ : p.2 = (0,0) <;> simp [rankOneTest,h₁,h₂]
  have hc (u v : Bool) :
      (if u then Route.rankOne else if v then .infiniteOrder else .remaining) = .rankOne ↔ u=true := by
    cases u <;> cases v <;> decide
  change (if (loopPairs s).any rankOneTest then Route.rankOne
    else if (loopPairs s).any infiniteTest then .infiniteOrder else .remaining) = _ ↔ _
  rw [hc,List.any_eq_true]
  simp only [htest]

theorem remaining_iff (s : State) : classify s = .remaining ↔
    (∀ p ∈ loopPairs s, p.1 = (0,0) ↔ p.2 = (0,0)) ∧
    (∀ p ∈ loopPairs s, p.1 ≠ (0,0) → p.2 ≠ (0,0) → gnorm p.1 = gnorm p.2) := by
  have hc (u v : Bool) :
      (if u then Route.rankOne else if v then .infiniteOrder else .remaining) = .remaining ↔
      u≠true ∧ v≠true := by cases u <;> cases v <;> decide
  change (if (loopPairs s).any rankOneTest then Route.rankOne
    else if (loopPairs s).any infiniteTest then .infiniteOrder else .remaining) = _ ↔ _
  rw [hc]
  have hr (p : Gaussian × Gaussian) : rankOneTest p ≠ true ↔ (p.1 = (0,0) ↔ p.2 = (0,0)) := by
    by_cases h₁ : p.1 = (0,0) <;> by_cases h₂ : p.2 = (0,0) <;> simp [rankOneTest,h₁,h₂]
  have hi (p : Gaussian × Gaussian) : infiniteTest p ≠ true ↔
      (p.1 ≠ (0,0) → p.2 ≠ (0,0) → gnorm p.1 = gnorm p.2) := by
    by_cases h₁ : p.1 = (0,0) <;> by_cases h₂ : p.2 = (0,0) <;>
      by_cases h₃ : gnorm p.1 = gnorm p.2 <;> simp [infiniteTest,h₁,h₂,h₃]
  simp only [ne_eq,List.any_eq_true,not_exists,not_and]
  exact and_congr
    (forall_congr' fun p => forall_congr' fun _ => hr p)
    (forall_congr' fun p => forall_congr' fun _ => hi p)

theorem infiniteOrder_iff (s : State) : classify s = .infiniteOrder ↔
    (loopPairs s).any rankOneTest ≠ true ∧ ∃ p∈loopPairs s, infiniteTest p=true := by
  have hc (u v : Bool) :
      (if u then Route.rankOne else if v then .infiniteOrder else .remaining) = .infiniteOrder ↔
      u≠true ∧ v=true := by cases u <;> cases v <;> decide
  change (if (loopPairs s).any rankOneTest then Route.rankOne
    else if (loopPairs s).any infiniteTest then .infiniteOrder else .remaining) = _ ↔ _
  rw [hc,List.any_eq_true]

/-- Exact correspondence with seven freely chosen source exponents. -/
def sourceStateEquiv : State ≃ {u : (Fin 4 → Fin 4) × (Fin 4 → Fin 4) // u.1 0=0} where
  toFun s := ⟨(alpha s,beta s),rfl⟩
  invFun u := ((u.val.1 1,u.val.1 2,u.val.1 3),
    (u.val.2 0,u.val.2 1,u.val.2 2,u.val.2 3))
  left_inv s := rfl
  right_inv u := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [alpha,u.property]
    · funext i
      fin_cases i <;> rfl

end Holant.Certificates.TwelveLoops
