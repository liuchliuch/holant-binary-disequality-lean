import Holant.Proofs.Closure.ClosureExoticFiberFull

/-! Reversing one literal matching edge is an exact fibre re-expression. The
ancestor table is unchanged; original transpose coefficients remain recorded. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticFiberCounts
noncomputable section
open scoped BigOperators
open Holant Holant.Pauli.ExoticKlein
variable {P : Type*} [Fintype P] [LinearOrder P] {r : ℕ}

def flipped (M : Matching P r) (e : Fin r) : Matching P r :=
  ⟨(Equiv.swap (e,false) (e,true)).trans M.ports⟩

def flipLabels (labels : Label → Fin r → Label) (e : Fin r) (a : Label) (d : Fin r) : Label :=
  if d=e then theta (labels a d) else labels a d

def flipWeight (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (e : Fin r) (a : Label) : ℂ := weight a*transposeScalar (labels a e)

theorem flipWeight_live (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (e : Fin r) (a : Label) : flipWeight weight labels e a≠0 ↔ weight a≠0 := by
  exact ⟨fun h => (mul_ne_zero_iff.mp h).1,
    fun h => mul_ne_zero h (transposeScalar_ne_zero _)⟩

theorem flip_fiber (M : Matching P r) (weight : Label → ℂ)
    (labels : Label → Fin r → Label) (e : Fin r) :
    Fiber.tensor M weight labels=
      Fiber.tensor (flipped M e) (flipWeight weight labels e) (flipLabels labels e) := by
  classical
  funext x
  apply Finset.sum_congr rfl
  intro a ha
  have factors (d : Fin r) :
      E (labels a d) (x (M.ports (d,false))) (x (M.ports (d,true)))=
      (if d=e then transposeScalar (labels a e) else 1)*
        E (flipLabels labels e a d) (x ((flipped M e).ports (d,false)))
          (x ((flipped M e).ports (d,true))) := by
    by_cases hd : d=e
    · subst d
      simp only [flipLabels,flipped,ite_true,Equiv.trans_apply,
        Equiv.swap_apply_left,Equiv.swap_apply_right]
      have hh := congrFun (congrFun (transpose_E (labels a e))
        (x (M.ports (e,true)))) (x (M.ports (e,false)))
      exact hh
    · have hleft : (d,false)≠(e,false) := fun h => hd (congrArg Prod.fst h)
      have hright : (d,true)≠(e,true) := fun h => hd (congrArg Prod.fst h)
      have hcross : (d,false)≠(e,true) := by intro h;exact Bool.false_ne_true (congrArg Prod.snd h)
      have hcross' : (d,true)≠(e,false) := by intro h;exact Bool.false_ne_true (congrArg Prod.snd h).symm
      simp only [flipLabels,flipped,hd,ite_false,one_mul,Equiv.trans_apply,
        Equiv.swap_apply_of_ne_of_ne hleft hcross,Equiv.swap_apply_of_ne_of_ne hcross' hright]
  change weight a*M.tensor (labels a) x=
    flipWeight weight labels e a*(flipped M e).tensor (flipLabels labels e a) x
  simp only [Matching.tensor]
  rw [show (∏ d,E (labels a d) (x (M.ports (d,false))) (x (M.ports (d,true))))=
      ∏ d,(if d=e then transposeScalar (labels a e) else 1)*
        E (flipLabels labels e a d) (x ((flipped M e).ports (d,false)))
          (x ((flipped M e).ports (d,true))) from Finset.prod_congr rfl (fun d _ => factors d)]
  rw [Finset.prod_mul_distrib]
  have hp : (∏ d : Fin r,if d=e then transposeScalar (labels a e) else 1)=
      transposeScalar (labels a e) := by simp
  rw [hp]
  exact (mul_assoc _ _ _).symm

theorem flip_distinguished (labels : Label → Fin r → Label) (d e : Fin r)
    (hne : d≠e) (hlabel : ∀ a,labels a d=a) : ∀ a,flipLabels labels e a d=a := by
  intro a
  simp only [flipLabels,hne,ite_false,hlabel]

theorem flip_injective (labels : Label → Fin r → Label) (e d : Fin r)
    (h : Function.Injective (fun a => labels a d)) :
    Function.Injective (fun a => flipLabels labels e a d) := by
  intro a b he
  by_cases hd : d=e
  · simp only [flipLabels,hd,ite_true] at he
    exact h (by simpa only [hd,theta_theta] using congrArg theta he)
  · exact h (by simpa only [flipLabels,hd,ite_false] using he)

end
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticFiberCounts
