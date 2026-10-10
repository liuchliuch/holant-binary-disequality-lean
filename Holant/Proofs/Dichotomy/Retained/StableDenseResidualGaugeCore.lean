import Holant.Proofs.Reductions.EightVertexNonexception.Coefficients
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Algebraic description of the remaining full even-parity locus. The
unary factors describe coefficients; this does not assert free unary gadgets
or a common holographic basis for an entire family. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualGaugeCore
open Holant Holant.LocalDrafts.Hardness.EightVertexNonexception
open scoped BigOperators
variable {K : Type} [Field K]

/-- The same literal complementary-product equations, isolated from source programmes. -/
def Products (M : Signature K 4) : Prop :=
  (entries M).a*(entries M).x=(entries M).b*(entries M).y ∧
  (entries M).a*(entries M).x=(entries M).c*(entries M).z ∧
  (entries M).a*(entries M).x=(entries M).d*(entries M).w

def weighted (a : K) (u : Fin 4→K) : Signature K 4 :=
  table ⟨a,a*u 2*u 3,a*u 1*u 3,a*u 1*u 2,
    a*u 0*u 3,a*u 0*u 2,a*u 0*u 1,a*u 0*u 1*u 2*u 3⟩

theorem weighted_products (a : K) (u : Fin 4→K) :
    Products (weighted a u) := by
  constructor
  · change a*(a*u 0*u 1*u 2*u 3)=(a*u 2*u 3)*(a*u 0*u 1)
    ring
  constructor
  · change a*(a*u 0*u 1*u 2*u 3)=(a*u 1*u 3)*(a*u 0*u 2)
    ring
  · change a*(a*u 0*u 1*u 2*u 3)=(a*u 1*u 2)*(a*u 0*u 3)
    ring

/-- The formula is literally unary weights times the even-parity indicator. -/
theorem weighted_value (a : K) (u : Fin 4→K) (x : Fin 4→Bool) :
    weighted a u x=if weight x%2=0 then a*∏i,if x i then u i else 1 else 0 := by
  rw [word_eta x]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3
  all_goals first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
  all_goals norm_num [weighted,table,Fin.prod_univ_four] <;> ring

/-- A chosen nonzero square root yields a coefficient factorization.
No access to any of the resulting unaries is inferred. -/
theorem factor_with_root (M : Signature K 4) (he : EvenSupport M)
    (hp : Products M)
    (ha : (entries M).a≠0) (hb : (entries M).b≠0) (hc : (entries M).c≠0)
    (hd : (entries M).d≠0) (t : K) (ht : t≠0)
    (hsq : t^2=(entries M).b*(entries M).c/((entries M).a*(entries M).d)) :
    M=weighted (entries M).a
      ![(entries M).w/((entries M).a*t),(entries M).c/((entries M).a*t),
        (entries M).b/((entries M).a*t),t] := by
  let p := entries M
  let u : Fin 4→K := ![p.w/(p.a*t),p.c/(p.a*t),p.b/(p.a*t),t]
  have hpa : p.a≠0 := ha
  have hs : p.a*p.d*t^2=p.b*p.c := by
    have h := (eq_div_iff (mul_ne_zero ha hd)).mp hsq
    dsimp [p]
    linear_combination h
  have hu_b : p.a*u 2*u 3=p.b := by dsimp [u]; field_simp [hpa,ht]
  have hu_c : p.a*u 1*u 3=p.c := by dsimp [u]; field_simp [hpa,ht]
  have hu_w : p.a*u 0*u 3=p.w := by dsimp [u]; field_simp [hpa,ht]
  have hu_d : p.a*u 1*u 2=p.d := by
    dsimp [u]
    field_simp [hpa,ht]
    linear_combination -hs
  have hpw := weighted_products p.a u
  have hx : p.a*u 0*u 1*u 2*u 3=p.x := by
    apply mul_left_cancel₀ ha
    change p.a*(p.a*u 0*u 1*u 2*u 3)=p.a*p.x
    have h := hpw.2.2
    change p.a*(p.a*u 0*u 1*u 2*u 3)=(p.a*u 1*u 2)*(p.a*u 0*u 3) at h
    rw [h,hu_d,hu_w]
    exact hp.2.2.symm
  have hy : p.a*u 0*u 1=p.y := by
    apply mul_left_cancel₀ hb
    have h := hpw.1
    change p.a*(p.a*u 0*u 1*u 2*u 3)=(p.a*u 2*u 3)*(p.a*u 0*u 1) at h
    rw [hu_b,hx] at h
    exact h.symm.trans hp.1
  have hz : p.a*u 0*u 2=p.z := by
    apply mul_left_cancel₀ hc
    have h := hpw.2.1
    change p.a*(p.a*u 0*u 1*u 2*u 3)=(p.a*u 1*u 3)*(p.a*u 0*u 2) at h
    rw [hu_c,hx] at h
    exact h.symm.trans hp.2.1
  have htabled : weighted p.a u=table p := by
    unfold weighted
    rw [hx,hu_b,hu_c,hu_d,hu_w,hz,hy]
  exact (table_entries M he).symm.trans htabled.symm

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualGaugeCore
