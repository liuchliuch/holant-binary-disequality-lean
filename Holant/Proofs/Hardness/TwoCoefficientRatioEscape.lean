import Holant.Proofs.Hardness.DenseTwoCoefficientEscape
import Holant.Proofs.Hardness.TwoCoefficientData
import Holant.Algebraic.FixedField
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Scalar escape inside an installed finite field.
The finite rational basis in F proves algebraicity, so the complex embedding
is constructed internally. It only chooses a fixed depth0/1/2. Actual stage
coefficients remain the original polynomial iteration in K; this is not a
change of presentation, an oracle algorithm, or a caller-supplied embedding. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.TwoCoefficientRatioEscape
open Holant.Algebraic
namespace C
export DenseTwoCoefficientEscape
  (step depth selectedRatio depth_spec depth_lt_three selected_nonzero selected_infinite
   executed_denominator selected_nodes_injective)
end C
namespace D
export TwoCoefficientData (step stage ratio InfiniteRatio)
end D
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d)
local instance fieldCharZero : CharZero K := algebraRat.charZero K

/-- No embedding, number-field instance or algebraicity witness is supplied. -/
def embedding : K →ₐ[ℚ] ℂ := by
  letI : Module.Finite ℚ K := Module.Finite.of_basis F.basis
  exact IsAlgClosed.lift

theorem embedding_injective : Function.Injective (embedding F) := (embedding F).injective

theorem ratio_nonzero (a b : K) (ha : a≠0) (hb : b≠0) : D.ratio (a,b)≠0 :=
  div_ne_zero ha (mul_ne_zero (by norm_num) hb)

def complexRatio (a b : K) : ℂ := embedding F (D.ratio (a,b))

theorem complexRatio_nonzero (a b : K) (ha : a≠0) (hb : b≠0) : complexRatio F a b≠0 := by
  intro h
  apply ratio_nonzero a b ha hb
  apply embedding_injective F
  simpa only [complexRatio,map_zero] using h

def depth (a b : K) : Fin 3 := C.depth (complexRatio F a b)
def selected (a b : K) : K×K := D.stage a b (depth F a b).val

theorem depth_le_two (a b : K) : (depth F a b).val≤2 := Nat.le_of_lt_succ (depth F a b).isLt

private theorem ratio_denominator (p : K×K) (hb : p.2≠0) :
    2*D.ratio p+1=(p.1+p.2)/p.2 := by
  unfold D.ratio
  field_simp
  <;> ring

private theorem ratio_step (p : K×K) (hb : p.2≠0) (hs : p.1+p.2≠0) :
    D.ratio (D.step p)=D.ratio p/(2*D.ratio p+1) := by
  rw [ratio_denominator p hb]
  unfold D.ratio D.step
  field_simp
  <;> ring

/-- Exact polynomial-stage coefficients and their actual embedded ratio,
for every prefix of the finite selected stage. -/
theorem stage_spec (a b : K) (ha : a≠0) (hb : b≠0) (i : ℕ)
    (hi : i≤(depth F a b).val) :
    (D.stage a b i).1≠0 ∧ (D.stage a b i).2≠0 ∧
      embedding F (D.ratio (D.stage a b i))=(C.step^[i]) (complexRatio F a b) := by
  induction i with
  | zero => exact ⟨ha,hb,rfl⟩
  | succ i ih =>
    obtain ⟨ha',hb',he⟩ := ih (by omega)
    have hd := C.executed_denominator (complexRatio F a b) (complexRatio_nonzero F a b ha hb) i (by
      change i<(depth F a b).val
      omega)
    have hdK : 2*D.ratio (D.stage a b i)+1≠0 := by
      intro hz
      apply hd
      have h := congrArg (embedding F) hz
      simpa only [map_add,map_mul,map_ofNat,map_one,map_zero,he] using h
    have hs : (D.stage a b i).1+(D.stage a b i).2≠0 := by
      intro hz
      apply hdK
      rw [ratio_denominator _ hb',hz,zero_div]
    refine ⟨mul_ne_zero ha' hb',mul_ne_zero hb' hs,?_⟩
    change embedding F (D.ratio (D.step (D.stage a b i)))=_
    rw [ratio_step _ hb' hs]
    simp only [map_div₀,map_add,map_mul,map_ofNat,map_one,he,
      Function.iterate_succ_apply',C.step]

/-- Denominator safety is transported back, rather than requested as a
separate successful-normalization certificate. -/
theorem executed_denominator (a b : K) (ha : a≠0) (hb : b≠0) (i : ℕ)
    (hi : i<(depth F a b).val) : 2*D.ratio (D.stage a b i)+1≠0 := by
  have he := (stage_spec F a b ha hb i (Nat.le_of_lt hi)).2.2
  have hd := C.executed_denominator (complexRatio F a b) (complexRatio_nonzero F a b ha hb) i hi
  intro hz
  apply hd
  have h := congrArg (embedding F) hz
  simpa only [map_add,map_mul,map_ofNat,map_one,map_zero,he] using h

theorem executed_sum_nonzero (a b : K) (ha : a≠0) (hb : b≠0) (i : ℕ)
    (hi : i<(depth F a b).val) : (D.stage a b i).1+(D.stage a b i).2≠0 := by
  intro hz
  apply executed_denominator F a b ha hb i hi
  rw [ratio_denominator _ (stage_spec F a b ha hb i (Nat.le_of_lt hi)).2.1,hz,zero_div]

theorem selected_nonzero (a b : K) (ha : a≠0) (hb : b≠0) :
    (selected F a b).1≠0 ∧ (selected F a b).2≠0 := by
  have h := stage_spec F a b ha hb (depth F a b).val le_rfl
  exact ⟨h.1,h.2.1⟩

theorem selected_ratio_map (a b : K) (ha : a≠0) (hb : b≠0) :
    embedding F (D.ratio (selected F a b))=C.selectedRatio (complexRatio F a b) :=
  (stage_spec F a b ha hb (depth F a b).val le_rfl).2.2

theorem selected_infinite (a b : K) (ha : a≠0) (hb : b≠0) : D.InfiniteRatio (selected F a b) := by
  intro n hn hp
  have hc := C.selected_infinite (complexRatio F a b) (complexRatio_nonzero F a b ha hb) n hn
  apply hc
  rw [←selected_ratio_map F a b ha hb]
  simpa only [map_pow,map_one] using congrArg (embedding F) hp

/-- Actual geometric nodes are distinct, with all original-ratio nonzero
and selected-stage obligations derived from a≠0 and b≠0. -/
theorem selected_nodes_injective (a b : K) (ha : a≠0) (hb : b≠0) (m : ℕ) :
    Function.Injective (fun i : Fin (m+1)=>D.ratio (selected F a b)^(i.val+1)) := by
  intro i j hij
  apply C.selected_nodes_injective (complexRatio F a b) (complexRatio_nonzero F a b ha hb) m
  simpa only [map_pow,selected_ratio_map F a b ha hb] using congrArg (embedding F) hij

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.TwoCoefficientRatioEscape
