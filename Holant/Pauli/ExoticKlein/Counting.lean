import Holant.Pauli.ExoticKlein.Recoupling

/-! Exact label counts for alternating cycles. Each label occurs once through
an actual additive bijection, so all but one labels are freely selectable. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
open scoped BigOperators

def thetaEquiv : Label ≃+ Label where
  toFun := theta
  invFun := theta
  left_inv := theta_theta
  right_inv := theta_theta
  map_add' := theta_add

/-- A dual M-factor contributes theta unless its original orientation reverses. -/
def dualLabelMap (reverse : Bool) : Label ≃+ Label := if reverse then AddEquiv.refl Label else thetaEquiv
/-- An N-factor contributes its label unless its original orientation reverses. -/
def directLabelMap (reverse : Bool) : Label ≃+ Label := if reverse then thetaEquiv else AddEquiv.refl Label

@[simp] theorem card_label : Fintype.card Label = 4 := by simp [Label]

def headLabel {n : ℕ} (maps : Fin (n+1) → Label ≃+ Label) (target : Label) (tail : Fin n → Label) : Label :=
  (maps 0).symm (target-∑ i : Fin n, maps i.succ (tail i))

/-- Explicit parametrization of every solution, using the original tail labels.
The one remaining label is uniquely solved, not counted by a supplied oracle. -/
def affineSolutions {n : ℕ} (maps : Fin (n+1) → Label ≃+ Label) (target : Label) :
    {a : Fin (n+1) → Label // ∑ i, maps i (a i) = target} ≃ (Fin n → Label) where
  toFun a := fun i => a.val i.succ
  invFun tail := ⟨Fin.cons (headLabel maps target tail) tail,by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,headLabel,AddEquiv.apply_symm_apply]
    exact sub_add_cancel _ _⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change headLabel maps target (fun j => a.val j.succ) = a.val 0
      apply (maps 0).injective
      simp only [headLabel,AddEquiv.apply_symm_apply]
      have hh := a.property
      rw [Fin.sum_univ_succ] at hh
      exact ((eq_sub_iff_add_eq).mpr hh).symm
    · rfl
  right_inv tail := by funext i; rfl

theorem affineSolutions_card (n : ℕ) (maps : Fin (n+1) → Label ≃+ Label) (target : Label) :
    Fintype.card {a : Fin (n+1) → Label // ∑ i, maps i (a i) = target} = 4^n := by
  rw [Fintype.card_congr (affineSolutions maps target)]
  simp

end
end Holant.Pauli.ExoticKlein
