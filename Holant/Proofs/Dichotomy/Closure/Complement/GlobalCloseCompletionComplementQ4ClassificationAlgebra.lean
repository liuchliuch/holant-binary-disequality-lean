import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Series
import Mathlib.Tactic

/-! Exhaustive polynomial alternatives for the three rotational charts.
The factorization of each outer determinant keeps the paired-square cases
explicit; it does not substitute a singleton tractability conclusion. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationAlgebra
open Holant
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

def outerLeft (a b c d : K) : K := 4*a*d*(b^2+c^2)
def outerRight (a b c d : K) : K := 4*b*c*(a^2+d^2)
def middle (a b c d : K) : K := 2*a^2*d^2+2*b^2*c^2+(a^2+d^2)*(b^2+c^2)
def outerDet (b c d : K) : K := d^2*(b^2+c^2)^2-b^2*c^2*(1+d^2)^2

theorem determinant (b c d : K) :
    outerLeft 1 b c d ^ 2-outerRight 1 b c d ^ 2=16*outerDet b c d := by
  unfold outerLeft outerRight outerDet
  ring

theorem factor (b c d : K) :
    outerDet b c d=(b^2*d^2-c^2)*(b^2-c^2*d^2) := by
  unfold outerDet
  ring

def Paired (b c d : K) : Prop :=
  (b^4=1 ∧ c^2=b^2*d^2) ∨ (c^4=1 ∧ b^2=c^2*d^2) ∨ (d^4=1 ∧ b^2=d^2*c^2)

theorem paired_of_zero (b c d : K) (hb : b≠0) (hd : d≠0)
    (h0 : outerDet b c d=0) (h1 : outerDet d c b=0) (h2 : outerDet b d c=0) :
    Paired b c d := by
  have xy : (b^2*d^2-c^2)*(b^2-c^2*d^2)=0 := by simpa only [factor] using h0
  have xz : (b^2*d^2-c^2)*(d^2-b^2*c^2)=0 := by
    calc
      _=outerDet d c b := by rw [factor];ring
      _=0 := h1
  have yz : (b^2-c^2*d^2)*(d^2-b^2*c^2)=0 := by
    calc
      _= -(outerDet b d c) := by rw [factor];ring
      _=0 := by rw [h2,neg_zero]
  by_cases hx : b^2*d^2-c^2=0
  · rcases mul_eq_zero.mp yz with hy|hz
    · right;right
      have h : b^2*(d^4-1)=0 := by linear_combination d^2*hx-hy
      exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hb)),
        (sub_eq_zero.mp hy).trans (mul_comm _ _)⟩
    · left
      have h : d^2*(b^4-1)=0 := by linear_combination b^2*hx-hz
      exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hd)),
        (sub_eq_zero.mp hx).symm⟩
  · have hy := (mul_eq_zero.mp xy).resolve_left hx
    have hz := (mul_eq_zero.mp xz).resolve_left hx
    right;left
    have h : d^2*(c^4-1)=0 := by linear_combination -c^2*hy-hz
    exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hd)),sub_eq_zero.mp hy⟩

/-- A nonzero outer determinant gives either the three-mode spectral source
or an actual nonsingular two-block resource. Otherwise paired squares hold. -/
theorem alternatives (b c d : K) (hb : b≠0) (hd : d≠0) :
    Paired b c d ∨
      ∃u v w : K, (u=b ∧ v=c ∧ w=d ∨ u=d ∧ v=c ∧ w=b ∨ u=b ∧ v=d ∧ w=c) ∧
        outerLeft 1 u v w ^ 2≠outerRight 1 u v w ^ 2 := by
  classical
  by_cases h0 : outerDet b c d=0
  · by_cases h1 : outerDet d c b=0
    · by_cases h2 : outerDet b d c=0
      · exact Or.inl (paired_of_zero b c d hb hd h0 h1 h2)
      · right
        refine ⟨b,d,c,Or.inr (Or.inr ⟨rfl,rfl,rfl⟩),?_⟩
        intro e
        have h:=determinant b d c
        rw [e,sub_self] at h
        exact h2 ((mul_eq_zero.mp h.symm).resolve_left (by norm_num))
    · right
      refine ⟨d,c,b,Or.inr (Or.inl ⟨rfl,rfl,rfl⟩),?_⟩
      intro e
      have h:=determinant d c b
      rw [e,sub_self] at h
      exact h1 ((mul_eq_zero.mp h.symm).resolve_left (by norm_num))
  · right
    refine ⟨b,c,d,Or.inl ⟨rfl,rfl,rfl⟩,?_⟩
    intro e
    have h:=determinant b c d
    rw [e,sub_self] at h
    exact h0 ((mul_eq_zero.mp h.symm).resolve_left (by norm_num))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationAlgebra
end
