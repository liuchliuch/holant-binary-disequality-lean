import Holant.Dihedral.CompatibleClosure.Interface

/-! Ordered source cards, with the protected pair retained after any number of
other original matching pairs. Every contraction is a literal Boolean sum. -/
noncomputable section
namespace Holant.Dihedral.CompatibleCoefficientLine
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure

abbrev pair {n : ℕ} (a b : Bool) (x : Fin n → Bool) : Fin (n+2) → Bool :=
  Fin.cons a (Fin.cons b x)
abbrev tail {n : ℕ} (x : Fin (n+2) → Bool) : Fin n → Bool := fun i => x i.succ.succ

/-- Insert the original deleted pair immediately before the retained edge. -/
def insertDeleted : (r : ℕ) → Bool → Bool → (Fin (2*r+2) → Bool) → (Fin (2*r+4) → Bool)
  | 0,a,b,x => pair a b x
  | r+1,a,b,x => pair (x 0) (x 1) (insertDeleted r a b (tail x))

def card (r : ℕ) (q : Signature Scalar (2*r+4)) (K : Mat) : Signature Scalar (2*r+2) :=
  fun x => ∑ a : Bool, ∑ b : Bool, K a b * q (insertDeleted r a b x)

/-- A literal ordered matching product, including the designated last edge. -/
def product : (r : ℕ) → (Fin r → Mat) → Mat → Signature Scalar (2*r+2)
  | 0,_,B => fun x => B (x 0) (x 1)
  | r+1,A,B => fun x => A 0 (x 0) (x 1) * product r (fun i => A i.succ) B (tail x)

@[simp] theorem card_zero (q : Signature Scalar 4) (K : Mat) :
    card 0 q K = Signature.contract K q := rfl

@[simp] theorem card_smul (r : ℕ) (c : Scalar) (q : Signature Scalar (2*r+4)) (K : Mat) :
    card r (c • q) K = c • card r q K := by
  funext x
  simp only [card,Pi.smul_apply,smul_eq_mul,Fintype.sum_bool]
  ring

/-- Closures on other original pairs commute with the two inherited cards. -/
theorem card_close (r : ℕ) (q : Signature Scalar (2*(r+1)+4)) (K : Mat)
    (γ : Bool) (t : Scalar) :
    card r (close γ t q) K = close γ t (card (r+1) q K) := by
  funext x
  have hi (a b c d : Bool) : insertDeleted (r+1) c d (pair a b x) =
      pair a b (insertDeleted r c d x) := rfl
  simp only [card,close,Fintype.sum_bool,hi]
  ring

 theorem close_product (r : ℕ) (A : Fin (r+1) → Mat) (B : Mat) (γ : Bool) (t : Scalar) :
    close γ t (product (r+1) A B) = trace (A 0) (M γ t) • product r (fun i => A i.succ) B := by
  funext x
  change (∑ a : Bool, ∑ b : Bool, M γ t a b *
    (A 0 a b * product r (fun i => A i.succ) B x)) = _
  simp only [trace,Pi.smul_apply,smul_eq_mul,Fintype.sum_bool]
  ring

@[simp] theorem close_smul {n : ℕ} (γ : Bool) (t c : Scalar) (q : Signature Scalar (n+2)) :
    close γ t (c • q) = c • close γ t q := by
  funext x
  simp only [close,Pi.smul_apply,smul_eq_mul,Fintype.sum_bool]
  ring

/-- Exact support parity and nonzero ordered coefficients, with no supplied
phase choice or projective proportionality. -/
def HasParity (α : Bool) (A : Mat) : Prop :=
  ∃ w : Bool → Scalar, (∀ a,w a ≠ 0) ∧ A = monomial α w

theorem HasParity.normal_form {α : Bool} {A : Mat} (h : HasParity α A) :
    ∃ a c : Scalar, a ≠ 0 ∧ c ≠ 0 ∧ A = scale c (M α a) := by
  obtain ⟨w,hw,rfl⟩ := h
  refine ⟨w true / w false,w false,div_ne_zero (hw true) (hw false),hw false,?_⟩
  funext x y
  cases x <;> cases y <;> cases α <;>
    simp [monomial,M,scale,hw] <;> field_simp [hw false]

/-- The source compatibility condition gives a simultaneous actual finite-grid
trace even when the two coefficient lines on this closed edge differ. -/
theorem compatible_trace {m : ℕ} (hm : 3 ≤ m) {α : Bool} {A B : Mat}
    (hA : HasParity α A) (hB : HasParity α B) :
    ∃ t : {t : Scalar // Roots m t}, trace A (M α t.val) ≠ 0 ∧ trace B (M α t.val) ≠ 0 := by
  obtain ⟨a,c,ha,hc,rfl⟩ := hA.normal_form
  obtain ⟨b,d,hb,hd,rfl⟩ := hB.normal_form
  obtain ⟨t,ht,hta,htb⟩ := simultaneous_phase hm a b ha hb
  refine ⟨⟨t,ht⟩,?_,?_⟩
  · have hh := trace_scale c 1 (M α a) (M α t)
    have hs : scale 1 (M α t) = M α t := by funext u v; simp [Marked.scale]
    rw [hs,mul_one,trace_M] at hh
    rw [hh]
    exact mul_ne_zero hc hta
  · have hh := trace_scale d 1 (M α b) (M α t)
    have hs : scale 1 (M α t) = M α t := by funext u v; simp [Marked.scale]
    rw [hs,mul_one,trace_M] at hh
    rw [hh]
    exact mul_ne_zero hd htb

end Holant.Dihedral.CompatibleCoefficientLine
