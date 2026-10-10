import Holant.Proofs.Dichotomy.Retained.StableDenseResidualPencil

/-! The odd-cap part of a finite cyclic deck, without an equality kernel.
Orders one and two force a common complementary sign. Larger orders force
equality of the three middle opposite products; the corner product is not
constrained by binary self-caps. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeFiniteCaps
open Holant Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.Projective.CyclicPhasePencil
set_option maxHeartbeats 1000000
set_option Elab.async false

variable {K : Type} [Field K] [CharZero K]

structure Samples (m : ℕ) (e : Entries K) : Prop where
  first : ∀t : K,t^m=1→ScalarSample m (e.w+t*e.c) (e.z+t*e.d)
  second : ∀t : K,t^m=1→ScalarSample m (e.w+t*e.b) (e.y+t*e.d)
  opposite : ∀t : K,t^m=1→ScalarSample m (e.c+t*e.d) (e.w+t*e.z)

def MiddleProducts (e : Entries K) : Prop := e.b*e.y=e.d*e.w ∧ e.c*e.z=e.d*e.w

theorem sample_power {m : ℕ} (hm : 0<m) (u v : K) (h : ScalarSample m u v) : v^m=u^m := by
  rcases h with ⟨rfl,rfl⟩ | ⟨hu,_hv,h⟩
  · rfl
  · rw [div_pow] at h
    exact (div_eq_one_iff_eq (pow_ne_zero _ hu)).mp h

theorem order_one (e : Entries K) (samples : Samples 1 e) :
    e.b=e.y ∧ e.c=e.z ∧ e.d=e.w := by
  have first := sample_power (K:=K) (m:=1) (by omega) _ _ (samples.first 1 (by simp))
  have second := sample_power (K:=K) (m:=1) (by omega) _ _ (samples.second 1 (by simp))
  have opposite := sample_power (K:=K) (m:=1) (by omega) _ _ (samples.opposite 1 (by simp))
  simp only [pow_one,one_mul] at first second opposite
  constructor
  · linear_combination (first - opposite)/2 - second
  constructor
  · linear_combination -(first+opposite)/2
  · linear_combination (first-opposite)/2

private theorem pencil_product (a b c d : K)
    (samples : ∀t : K,t^2=1→ScalarSample 2 (a+t*c) (b+t*d)) : a*c=b*d := by
  have pos := sample_power (K:=K) (m:=2) (by omega) _ _ (samples 1 (by norm_num))
  have neg := sample_power (K:=K) (m:=2) (by omega) _ _ (samples (-1) (by norm_num))
  linear_combination (neg-pos)/4

theorem order_two (e : Entries K) (hw : e.w≠0) (hz : e.z≠0)
    (samples : Samples 2 e) :
    ∃ε : K,ε^2=1 ∧ e.b=ε*e.y ∧ e.c=ε*e.z ∧ e.d=ε*e.w := by
  have first := pencil_product e.w e.z e.c e.d samples.first
  have second := pencil_product e.w e.y e.b e.d samples.second
  have opposite := pencil_product e.c e.w e.d e.z samples.opposite
  have squares : e.c^2=e.z^2 := by
    apply (mul_left_cancel₀ hw)
    linear_combination e.c*first+e.z*opposite
  have third : e.d=(e.c/e.z)*e.w := by
    apply (mul_left_cancel₀ hz)
    field_simp
    linear_combination -first
  refine ⟨e.c/e.z,?_,?_,?_,third⟩
  · rw [div_pow,squares,div_self (pow_ne_zero _ hz)]
  · apply (mul_left_cancel₀ hw)
    rw [third] at second
    linear_combination second
  · field_simp

theorem large_order {m : ℕ} (hm : 3≤m) (e : Entries ℂ)
    (hw : e.w≠0) (hb : e.b≠0) (hc : e.c≠0) (samples : Samples m e) :
    MiddleProducts e := by
  obtain ⟨α,_root,first,last⟩ := StableDenseResidualPencil.dense_scalar_pencil hm
    e.w e.z e.c e.d hw hc samples.first
  obtain ⟨β,_root,second,last'⟩ := StableDenseResidualPencil.dense_scalar_pencil hm
    e.w e.y e.b e.d hw hb samples.second
  constructor
  · rw [second,last'];ring
  · rw [first,last];ring


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeFiniteCaps
end
