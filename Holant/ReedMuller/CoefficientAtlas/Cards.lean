import Holant.ReedMuller.CoefficientAtlas.Character
import Holant.Signature
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace Holant.ReedMuller.CoefficientAtlas
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Exact support, including nonzero values at every one of the sixteen words. -/
def SupportRM (q : Signature ℂ 8) : Prop :=
  ∀ x, q x≠0 ↔ ∃ a : Param, word a=x

def plusCard (q : Signature ℂ 8) (p : Fin 28) : Signature ℂ 6 :=
  fun y => 2*(q (fill p false y)+q (fill p true y))

theorem coefficient_nonzero {q : Signature ℂ 8} (hq : SupportRM q) (a : Param) :
    q (word a)≠0 := (hq _).mpr ⟨a,rfl⟩

theorem outside_zero {q : Signature ℂ 8} (hq : SupportRM q) (x : Point → Bool)
    (hx : ∀ a : Param, x≠word a) : q x=0 := by
  by_contra h
  obtain ⟨a,ha⟩ := (hq x).mp h
  exact hx a ha.symm

theorem plusCard_repeated {q : Signature ℂ 8} (hq : SupportRM q) (p : Fin 28) (t : Fin 3 → Bool) :
    plusCard q p (repeatedWord t)=2*q (word (lift p t)) := by
  rcases unique_card_lift p t with ⟨h,hz⟩ | ⟨h,hz⟩
  · simp only [plusCard,h,outside_zero hq _ hz,add_zero]
  · simp only [plusCard,h,outside_zero hq _ hz,zero_add]

theorem plusCard_repeated_nonzero {q : Signature ℂ 8} (hq : SupportRM q)
    (p : Fin 28) (t : Fin 3 → Bool) : plusCard q p (repeatedWord t)≠0 := by
  rw [plusCard_repeated hq]
  exact mul_ne_zero (by norm_num) (coefficient_nonzero hq _)

def coefficientUnit (q : Signature ℂ 8) (hq : SupportRM q) (a : Param) : ℂˣ :=
  Units.mk0 (q (word a)/q (word 0)) (div_ne_zero (coefficient_nonzero hq a) (coefficient_nonzero hq 0))

@[simp] theorem coefficientUnit_val (q : Signature ℂ 8) (hq : SupportRM q) (a : Param) :
    (coefficientUnit q hq a : ℂ)=q (word a)/q (word 0) := rfl

@[simp] theorem coefficientUnit_zero (q : Signature ℂ 8) (hq : SupportRM q) :
    coefficientUnit q hq 0=1 := by
  apply Units.ext
  simp [coefficient_nonzero hq 0]

structure WeightedMatching where
  ports : (Fin 3 × Fin 2) ≃ Fin 6
  scalar : ℂˣ
  ratio : Fin 3 → ℂˣ

def WeightedMatching.value (M : WeightedMatching) : Signature ℂ 6 := fun y =>
  (M.scalar:ℂ) * ∏ e : Fin 3,
    if y (M.ports (e,0))=y (M.ports (e,1)) then (M.ratio e:ℂ)^(if y (M.ports (e,0)) then 1 else 0 : ℕ) else 0

def logicalIndex (i : Fin 6) : Fin 3 := ⟨i.val/2,by omega⟩

theorem repeatedWord_apply : ∀ t : Fin 3 → Bool, ∀ i : Fin 6,
    repeatedWord t i=t (logicalIndex i) := by decide

def WeightedMatching.logicalRatio (M : WeightedMatching) (i : Fin 3) : ℂˣ :=
  ∏ e : Fin 3, if logicalIndex (M.ports (e,0))=i then M.ratio e else 1

theorem regroup_product {G : Type*} [CommGroup G] (rho : Fin 3 → G)
    (index : Fin 3 → Fin 3) (t : Fin 3 → Bool) :
    (∏ i, (∏ e, if index e=i then rho e else 1)^(if t i then 1 else 0 : ℕ))=
      ∏ e, rho e^(if t (index e) then 1 else 0 : ℕ) := by
  simp_rw [←Finset.prod_pow]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro e _
  calc
    _ = ∏ i : Fin 3, if index e=i then rho e^(if t i then 1 else 0 : ℕ) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : index e=i <;> simp [hi]
    _ = _ := by simp

/-- No matching coordinate identification is assumed: nonzero actual values
on every repeated word remove the support indicators, and the original edge
ratios are explicitly regrouped by their original first endpoint. -/
theorem WeightedMatching.repeated_value (M : WeightedMatching)
    (hne : ∀ t : Fin 3 → Bool, M.value (repeatedWord t)≠0) (t : Fin 3 → Bool) :
    M.value (repeatedWord t) = (M.scalar:ℂ) *
      ∏ i : Fin 3, (M.logicalRatio i:ℂ)^(if t i then 1 else 0 : ℕ) := by
  have hall : ∀ e : Fin 3, repeatedWord t (M.ports (e,0))=repeatedWord t (M.ports (e,1)) := by
    by_contra hn
    have hz : M.value (repeatedWord t)=0 := by
      simp only [WeightedMatching.value,Fintype.prod_ite_zero,hn,ite_false,mul_zero]
    exact hne t hz
  rw [WeightedMatching.value,Fintype.prod_ite_zero,if_pos hall]
  simp only [repeatedWord_apply]
  congr 1
  have H := regroup_product M.ratio (fun e => logicalIndex (M.ports (e,0))) t
  have HC := congrArg (fun u : ℂˣ => (u:ℂ)) H
  simpa only [WeightedMatching.logicalRatio,Units.coe_prod,Units.val_pow_eq_pow_val] using HC.symm

/-- The literal plus cards suffice; zero cases are admitted and eliminated
only after the actual RM support proves the relevant card is nonzero. -/
theorem cubeProducts_of_cards {q : Signature ℂ 8} (hq : SupportRM q)
    (hcards : ∀ p : Fin 28, plusCard q p=0 ∨ ∃ M : WeightedMatching, M.value=plusCard q p) :
    CubeProducts (coefficientUnit q hq) := by
  intro p t
  have hn := plusCard_repeated_nonzero hq p
  obtain hz | ⟨M,hM⟩ := hcards p
  · have hbad := hn (fun _ => false)
    rw [hz] at hbad
    exact (hbad rfl).elim
  have hmne : ∀ t, M.value (repeatedWord t)≠0 := by intro t; rw [hM]; exact hn t
  have H := M.repeated_value hmne t
  have H0 := M.repeated_value hmne (fun _ => false)
  rw [hM,plusCard_repeated hq] at H H0
  simp only [lift_zero,Bool.false_eq_true,ite_false,pow_zero,Finset.prod_const_one,mul_one] at H0
  have Hs (i : Fin 3) : coefficientUnit q hq (generators p i)=M.logicalRatio i := by
    have Hi := M.repeated_value hmne (fun j => decide (j=i))
    rw [hM,plusCard_repeated hq,lift_single] at Hi
    have Hp : (∏ j : Fin 3, (M.logicalRatio j:ℂ)^(if decide (j=i) then 1 else 0 : ℕ)) =
        (M.logicalRatio i:ℂ) := by
      fin_cases i <;> simp [Fin.prod_univ_three]
    rw [Hp] at Hi
    apply Units.ext
    simp only [coefficientUnit_val]
    rw [←H0] at Hi
    apply (div_eq_iff (coefficient_nonzero hq 0)).mpr
    linear_combination Hi / 2
  apply Units.ext
  simp only [coefficientUnit_val]
  simp only [Hs]
  rw [←H0] at H
  apply (div_eq_iff (coefficient_nonzero hq 0)).mpr
  simp only [Units.coe_prod,Units.val_pow_eq_pow_val]
  linear_combination H / 2

end
end Holant.ReedMuller.CoefficientAtlas
