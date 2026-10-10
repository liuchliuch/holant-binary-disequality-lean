import Holant.Proofs.Algorithms.TransformRecognition.SparseEvaluation


namespace Holant.LocalDrafts.MainChain.TransformRecognition.SparseLocalAffineTemplate
open Holant Holant.Algebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.Sparse
open SparseTransform
variable {n v d : ℕ}
abbrev Word (n : ℕ) := Fin n → Bool

def supportRow (D : ArithmeticData d) (f : Word n → Poly v d)
    (mask : Word n → Bool) (inverseAddress : Word n → Fin v) (x : Word n) : Poly v d :=
  if mask x then sub (mul D (f x) (variableCode D (inverseAddress x))) (one D)
  else f x

def twistRow (D : ArithmeticData d) (f : Word n → Poly v d)
    (phaseWeight affinePhase : Word n → Word n → Coefficient d)
    (scaleAddress : Word n → Fin v) (a x : Word n) : Poly v d :=
  sub (mul D (constant (phaseWeight a x)) (f x))
    (mul D (variableCode D (scaleAddress a)) (constant (affinePhase a x)))

def rows (D : ArithmeticData d) (f : Word n → Poly v d) (mask : Word n → Bool)
    (phaseWeight affinePhase : Word n → Word n → Coefficient d)
    (scaleAddress inverseAddress : Word n → Fin v) : List (Poly v d) :=
  (allWords n).map (supportRow D f mask inverseAddress) ++
    ((allWords n).filter mask).flatMap (fun a =>
      (allWords n).map (twistRow D f phaseWeight affinePhase scaleAddress a))

variable {K E : Type*} [Field K] [Algebra ℚ K] [Field E]
  (F : FixedField K d) (φ : K →+* E)
noncomputable section

theorem supportRow_eval (f : Word n → Poly v d) (mask : Word n → Bool)
    (inverseAddress : Word n → Fin v) (z : Fin v → E) (x : Word n) :
    SparseEvaluation.evaluate F φ z (supportRow F.toArithmeticData f mask inverseAddress x) =
      if mask x then SparseEvaluation.evaluate F φ z (f x) * z (inverseAddress x) - 1
      else SparseEvaluation.evaluate F φ z (f x) := by
  cases hx : mask x <;> simp [supportRow,hx]

theorem twistRow_eval (f : Word n → Poly v d)
    (phaseWeight affinePhase : Word n → Word n → Coefficient d)
    (scaleAddress : Word n → Fin v) (z : Fin v → E) (a x : Word n) :
    SparseEvaluation.evaluate F φ z
      (twistRow F.toArithmeticData f phaseWeight affinePhase scaleAddress a x) =
      φ (F.decode (phaseWeight a x)) * SparseEvaluation.evaluate F φ z (f x) -
        z (scaleAddress a) * φ (F.decode (affinePhase a x)) := by
  simp [twistRow]

theorem rows_zero_iff (f : Word n → Poly v d) (mask : Word n → Bool)
    (phaseWeight affinePhase : Word n → Word n → Coefficient d)
    (scaleAddress inverseAddress : Word n → Fin v) (z : Fin v → E) :
    (∀ p ∈ rows F.toArithmeticData f mask phaseWeight affinePhase scaleAddress inverseAddress,
      SparseEvaluation.evaluate F φ z p=0) ↔
    (∀ x, if mask x then SparseEvaluation.evaluate F φ z (f x) * z (inverseAddress x)=1
      else SparseEvaluation.evaluate F φ z (f x)=0) ∧
    (∀ a, mask a=true → ∀ x,
      φ (F.decode (phaseWeight a x)) * SparseEvaluation.evaluate F φ z (f x) =
        z (scaleAddress a) * φ (F.decode (affinePhase a x))) := by
  constructor
  · intro h
    constructor
    · intro x
      have hx := h _ (List.mem_append_left _
        (List.mem_map.mpr ⟨x,mem_allWords x,rfl⟩))
      rw [supportRow_eval] at hx
      cases hm : mask x <;> simp_all [sub_eq_zero]
    · intro a ha x
      have hx := h _ (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨a,List.mem_filter.mpr ⟨mem_allWords a,ha⟩,
          List.mem_map.mpr ⟨x,mem_allWords x,rfl⟩⟩))
      rw [twistRow_eval] at hx
      exact sub_eq_zero.mp hx
  · rintro ⟨hs,ht⟩ p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨x,_,rfl⟩ := List.mem_map.mp hp
      rw [supportRow_eval]
      have hx := hs x
      cases hm : mask x <;> simp_all [sub_eq_zero]
    · obtain ⟨a,ha,hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hp
      rw [twistRow_eval]
      exact sub_eq_zero.mpr (ht a (List.mem_filter.mp ha).2 x)

/-- Exact support is a CONSEQUENCE of all emitted equations, not supplied
as a branch-correctness premise. -/
theorem support_exact (f : Word n → Poly v d) (mask : Word n → Bool)
    (phaseWeight affinePhase : Word n → Word n → Coefficient d)
    (scaleAddress inverseAddress : Word n → Fin v) (z : Fin v → E)
    (h : ∀ p ∈ rows F.toArithmeticData f mask phaseWeight affinePhase scaleAddress inverseAddress,
      SparseEvaluation.evaluate F φ z p=0) (x : Word n) :
    SparseEvaluation.evaluate F φ z (f x) ≠ 0 ↔ mask x=true := by
  have hs := ((rows_zero_iff F φ f mask phaseWeight affinePhase scaleAddress inverseAddress z).mp h).1 x
  cases hm : mask x with
  | false =>
    have hz : SparseEvaluation.evaluate F φ z (f x)=0 := by simpa [hm] using hs
    simp [hm,hz]
  | true =>
    have hv : SparseEvaluation.evaluate F φ z (f x) * z (inverseAddress x)=1 := by simpa [hm] using hs
    have hn : SparseEvaluation.evaluate F φ z (f x) ≠ 0 := by
      intro hz
      simp [hz] at hv
    simp [hm,hn]

end
end Holant.LocalDrafts.MainChain.TransformRecognition.SparseLocalAffineTemplate
