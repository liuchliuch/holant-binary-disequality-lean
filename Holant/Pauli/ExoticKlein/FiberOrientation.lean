import Holant.Pauli.ExoticKlein.FiberSurgery

/-! Literal reversal of one original factor edge. The physical tensor stays
equal after inserting the exact nonzero transpose scalar in every summand. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Holant.Certificates.MatchingContractionClosure
namespace Fiber
variable {P : Type*} {r : ℕ}

def reversedMatching (M : Matching P r) (e : Fin r) : Matching P r :=
  ⟨(flipSlots (fun j => decide (j = e))).trans M.ports⟩

def reversedLabels (labels : Label → Fin r → Label) (e : Fin r) (a : Label) : Fin r → Label :=
  fun j => if j = e then theta (labels a e) else labels a j

def reversedWeight (weight : Label → ℂ) (labels : Label → Fin r → Label) (e : Fin r) (a : Label) : ℂ :=
  weight a*transposeScalar (labels a e)

theorem reversedWeight_nonzero (weight : Label → ℂ) (labels : Label → Fin r → Label) (e : Fin r)
    (hw : ∀ a, weight a ≠ 0) : ∀ a, reversedWeight weight labels e a ≠ 0 :=
  fun a => mul_ne_zero (hw a) (transposeScalar_ne_zero _)

theorem reverse_matching_tensor (M : Matching P r) (labels : Fin r → Label) (e : Fin r) :
    M.tensor labels = fun x => transposeScalar (labels e)*
      (reversedMatching M e).tensor (fun j => if j = e then theta (labels e) else labels j) x := by
  classical
  funext x
  have hl (j : Fin r) :
      E (labels j) (x (M.ports (j,false))) (x (M.ports (j,true))) =
        (if j = e then transposeScalar (labels e) else 1)*
          E (if j = e then theta (labels e) else labels j)
            (x ((reversedMatching M e).ports (j,false)))
            (x ((reversedMatching M e).ports (j,true))) := by
    by_cases hj : j = e
    · subst j
      have hh := congrFun (congrFun (transpose_E (labels e)) (x (M.ports (e,true)))) (x (M.ports (e,false)))
      simpa only [Kernel.transpose,scale,reversedMatching,Equiv.trans_apply,flipSlots,
        Equiv.coe_fn_mk,decide_true,Bool.false_xor,Bool.true_xor,Bool.not_true,ite_true] using hh
    · simp [hj,reversedMatching,flipSlots]
  unfold Matching.tensor
  simp_rw [hl]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq',Finset.mem_univ,ite_true]

theorem reverse_fiber (M : Matching P r) (weight : Label → ℂ) (labels : Label → Fin r → Label) (e : Fin r) :
    tensor M weight labels =
      tensor (reversedMatching M e) (reversedWeight weight labels e) (reversedLabels labels e) := by
  funext x
  unfold tensor
  apply Finset.sum_congr rfl
  intro a ha
  rw [reverse_matching_tensor M (labels a) e]
  change weight a*(transposeScalar (labels a e)*_) = (weight a*transposeScalar (labels a e))*_
  exact (mul_assoc _ _ _).symm

/-- The two actual cross orientations cannot both have constant fused labels.
Only bijectivity of the first original label map is needed. -/
theorem one_fused_map_varies (p q : Equiv.Perm Label) :
    (∃ a b, p a+q a ≠ p b+q b) ∨
    (∃ a b, theta (p a)+q a ≠ theta (p b)+q b) := by
  classical
  by_contra hn
  push_neg at hn
  let a := p.symm 0
  let b := p.symm yLabel
  have h0 := hn.1 a b
  have h1 := hn.2 a b
  have hs := congrArg₂ (fun x y : Label => x+y) h0 h1
  have hc (s t : Label) : (s+t)+(theta s+t) = s+theta s := by
    calc
      (s+t)+(theta s+t) = (s+theta s)+(t+t) := by abel
      _ = s+theta s := by rw [label_add_self,add_zero]
  rw [hc,hc] at hs
  simp only [a,b,Equiv.apply_symm_apply,theta_zero,theta_y,add_zero] at hs
  exact (by decide : (0 : Label) ≠ yLabel+zLabel) hs

end Fiber
end
end Holant.Pauli.ExoticKlein
