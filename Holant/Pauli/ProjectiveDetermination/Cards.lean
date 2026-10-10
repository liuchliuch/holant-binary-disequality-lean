import Holant.Pauli.ProjectiveDetermination.Bell
import Holant.Pauli.ProjectiveDetermination.Ports

/-! Actual four-term Pauli contractions, and their exact action on the
antisymmetric double tensor regrouped by original physical port. -/
namespace Holant.Pauli.ProjectiveDetermination
noncomputable section
open scoped BigOperators ComplexConjugate
variable {ι : Type*} [DecidableEq ι]

def card (r s : ι) (g : Label) (u : Tensor ℂ ι) : Tensor ℂ (Rest r s) :=
  fun z => ∑ a : Bool, ∑ b : Bool, kernel g a b*u (fill r s a b z)

def doubleTensor (u v : Tensor ℂ ι) (x : ι → Local) : ℂ :=
  u (fun i => (x i).1)*v (fun i => (x i).2)-v (fun i => (x i).1)*u (fun i => (x i).2)

def doubleCard (r s : ι) (g : Label) (W : (ι → Local) → ℂ) (z : Rest r s → Local) : ℂ :=
  ∑ x : Local, ∑ y : Local, kernel g x.1 y.1*kernel g x.2 y.2*W (fill r s x y z)

theorem fill_fst (r s : ι) (a b : Local) (z : Rest r s → Local) :
    (fun i => (fill r s a b z i).1) = fill r s a.1 b.1 (fun i => (z i).1) := by
  funext i
  unfold fill
  split <;> rename_i h
  · rfl
  · split <;> rfl

theorem fill_snd (r s : ι) (a b : Local) (z : Rest r s → Local) :
    (fun i => (fill r s a b z i).2) = fill r s a.2 b.2 (fun i => (z i).2) := by
  funext i
  unfold fill
  split <;> rename_i h
  · rfl
  · split <;> rfl

/-- This equality links the source hypothesis to the real pair-contraction
operator on W; no Bell-coordinate vanishing condition is supplied by the caller. -/
theorem doubleCard_wedge (r s : ι) (g : Label) (u v : Tensor ℂ ι) (z : Rest r s → Local) :
    doubleCard r s g (doubleTensor u v) z =
      wedge (card r s g u) (card r s g v) (fun i => (z i).1) (fun i => (z i).2) := by
  simp only [doubleCard,doubleTensor,Fintype.sum_prod_type,Fintype.sum_bool,fill_fst,fill_snd,wedge,card]
  ring

theorem dependent_cards_zero (r s : ι) (g : Label) (u v : Tensor ℂ ι)
    (h : Dependent (card r s g u) (card r s g v)) :
    ∀ z, doubleCard r s g (doubleTensor u v) z = 0 := by
  intro z
  rw [doubleCard_wedge]
  exact (dependent_iff_wedge_zero _ _).mp h _ _

@[simp] theorem card_conjugate (r s : ι) (g : Label) (u : Tensor ℂ ι) (z : Rest r s → Bool) :
    card r s g (fun x => conj (u x)) z = conj (card r s g u z) := by
  simp only [card,map_sum,map_mul,kernel_conj]

theorem doubleTensor_zero_iff (u v : Tensor ℂ ι) :
    doubleTensor u v = 0 ↔ Dependent u v := by
  rw [dependent_iff_wedge_zero]
  constructor
  · intro h x y
    have hh := congrFun h (fun i => (x i,y i))
    exact hh
  · intro h
    funext x
    exact h (fun i => (x i).1) (fun i => (x i).2)

end
end Holant.Pauli.ProjectiveDetermination
