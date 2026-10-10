import Holant.Proofs.Algorithms.TransformRecognition.OriginalTensorRows
import Holant.Proofs.Algorithms.TransformRecognition.ExtensionLocalAffine
import Holant.Proofs.Algorithms.TransformRecognition.SparseLocalAffineTemplate


namespace Holant.LocalDrafts.MainChain.TransformRecognition.SymbolicLocalAffineRows
set_option backward.isDefEq.respectTransparency false
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.Sparse
variable {n v : ℕ}
abbrev Word (n : ℕ) := Fin n → Bool

def supportRow (f : Word n → Poly v 1) (B : LocalAffineNormalForm.Code n)
    (inverseAddress : Word n → Fin v) (x : Word n) : Poly v 1 :=
  SparseLocalAffineTemplate.supportRow RationalCompiler.data f
    (fun a => decide (a ∈ B.1)) inverseAddress x

def twistRow (f : Word n → Poly v 1) (B : LocalAffineNormalForm.Code n)
    (imaginary eighth : Fin v) (scaleAddress : Word n → Fin v)
    (a x : Word n) : Poly v 1 :=
  sub (mul RationalCompiler.data
      (SymbolicPhaseCoefficients.twistCoefficient eighth a x) (f x))
    (mul RationalCompiler.data
      (SparseTransform.variableCode RationalCompiler.data (scaleAddress a))
      (SymbolicPhaseCoefficients.affineCoefficient imaginary (B.2 a) x))

def rows (f : Word n → Poly v 1) (B : LocalAffineNormalForm.Code n)
    (imaginary eighth : Fin v) (scaleAddress inverseAddress : Word n → Fin v) :
    List (Poly v 1) :=
  (SparseTransform.allWords n).map (supportRow f B inverseAddress) ++
    ((SparseTransform.allWords n).filter (fun a => decide (a ∈ B.1))).flatMap
      (fun a => (SparseTransform.allWords n).map (twistRow f B imaginary eighth scaleAddress a))

noncomputable section
abbrev ev (z : Fin v → ℂ) (p : Poly v 1) :=
  SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p

theorem supportRow_eval (f : Word n → Poly v 1) (B : LocalAffineNormalForm.Code n)
    (inverseAddress : Word n → Fin v) (z : Fin v → ℂ) (x : Word n) :
    ev z (supportRow f B inverseAddress x) =
      if x ∈ B.1 then ev z (f x) * z (inverseAddress x) - 1 else ev z (f x) := by
  simpa only [supportRow, ev, decide_eq_true_eq, RationalCompiler.field] using
    (SparseLocalAffineTemplate.supportRow_eval RationalCompiler.field (algebraMap ℚ ℂ)
      f (fun a => decide (a ∈ B.1)) inverseAddress z x)

theorem twistRow_eval (f : Word n → Poly v 1) (B : LocalAffineNormalForm.Code n)
    (imaginary eighth : Fin v) (scaleAddress : Word n → Fin v)
    (z : Fin v → ℂ) (hi : z imaginary=Complex.I) (hu : z eighth=(zetaEight : ℂ))
    (a x : Word n) :
    ev z (twistRow f B imaginary eighth scaleAddress a x) =
      (LocalAffineTwists.phaseWeight a x : ℂ)*ev z (f x) -
        z (scaleAddress a)*(ExtensionAffine.coefficient (B.2 a) x : ℂ) := by
  unfold twistRow ev
  change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
    (sub (mul RationalCompiler.field.toArithmeticData _ _)
      (mul RationalCompiler.field.toArithmeticData
        (SparseTransform.variableCode RationalCompiler.field.toArithmeticData _) _)) = _
  rw [SparseEvaluation.sub_eval,SparseEvaluation.mul_eval,SparseEvaluation.mul_eval,
    SparseEvaluation.variable_eval,
    SymbolicPhaseCoefficients.twistCoefficient_eval _ _ _ _ hu,
    SymbolicPhaseCoefficients.affineCoefficient_eval _ _ _ _ hi,
    OriginalAffineSystem.coefficient_one]

theorem rows_zero_iff (f : Word n → Poly v 1) (B : LocalAffineNormalForm.Code n)
    (imaginary eighth : Fin v) (scaleAddress inverseAddress : Word n → Fin v)
    (z : Fin v → ℂ) (hi : z imaginary=Complex.I) (hu : z eighth=(zetaEight : ℂ)) :
    (∀ p ∈ rows f B imaginary eighth scaleAddress inverseAddress, ev z p=0) ↔
      (∀ x, if x ∈ B.1 then ev z (f x)*z (inverseAddress x)=1 else ev z (f x)=0) ∧
      ∀ a ∈ B.1, ∀ x, (LocalAffineTwists.phaseWeight a x : ℂ)*ev z (f x) =
        z (scaleAddress a)*(ExtensionAffine.coefficient (B.2 a) x : ℂ) := by
  constructor
  · intro h
    constructor
    · intro x
      have hx := h _ (List.mem_append_left _
        (List.mem_map.mpr ⟨x,SparseTransform.mem_allWords x,rfl⟩))
      rw [supportRow_eval] at hx
      by_cases hm : x ∈ B.1 <;> simpa [hm,sub_eq_zero] using hx
    · intro a ha x
      have hx := h _ (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨a,List.mem_filter.mpr ⟨SparseTransform.mem_allWords a,by simp [ha]⟩,
          List.mem_map.mpr ⟨x,SparseTransform.mem_allWords x,rfl⟩⟩))
      rw [twistRow_eval f B imaginary eighth scaleAddress z hi hu] at hx
      exact sub_eq_zero.mp hx
  · rintro ⟨hs,ht⟩ p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨x,_,rfl⟩ := List.mem_map.mp hp
      rw [supportRow_eval]
      have hx := hs x
      by_cases hm : x ∈ B.1 <;> simpa [hm,sub_eq_zero] using hx
    · obtain ⟨a,ha,hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hp
      rw [twistRow_eval f B imaginary eighth scaleAddress z hi hu]
      exact sub_eq_zero.mpr (ht a (by simpa using (List.mem_filter.mp ha).2) x)

/-- The original support and all supported local twists follow from the
emitted equations; no correct-support premise is accepted. -/
theorem matches_of_zero (f : Word n → Poly v 1) (B : LocalAffineNormalForm.Code n)
    (imaginary eighth : Fin v) (scaleAddress inverseAddress : Word n → Fin v)
    (z : Fin v → ℂ) (hi : z imaginary=Complex.I) (hu : z eighth=(zetaEight : ℂ))
    (h : ∀ p ∈ rows f B imaginary eighth scaleAddress inverseAddress, ev z p=0) :
    ExtensionLocalAffine.Matches (algebraMap AlgebraicComplex ℂ) B
      (fun a => z (scaleAddress a)) (fun x => ev z (f x)) := by
  obtain ⟨hs,ht⟩ := (rows_zero_iff f B imaginary eighth scaleAddress inverseAddress z hi hu).mp h
  apply (ExtensionLocalAffine.entry_constraints _ _ _ _).mpr
  refine ⟨?_,?_,ht⟩
  · intro x hx hz
    have he : ev z (f x)*z (inverseAddress x)=1 := by simpa [hx] using hs x
    simp [hz] at he
  · intro x hx
    simpa [hx] using hs x

/-- Completeness uses the reciprocal of the actual evaluated entry. These
values are proof witnesses, not required inputs to the row compiler. -/
theorem zero_of_matches (f : Word n → Poly v 1) (B : LocalAffineNormalForm.Code n)
    (imaginary eighth : Fin v) (scaleAddress inverseAddress : Word n → Fin v)
    (z : Fin v → ℂ) (hi : z imaginary=Complex.I) (hu : z eighth=(zetaEight : ℂ))
    (h : ExtensionLocalAffine.Matches (algebraMap AlgebraicComplex ℂ) B
      (fun a => z (scaleAddress a)) (fun x => ev z (f x)))
    (hinv : ∀ x ∈ B.1, z (inverseAddress x)=(ev z (f x))⁻¹) :
    ∀ p ∈ rows f B imaginary eighth scaleAddress inverseAddress, ev z p=0 := by
  obtain ⟨hn,hz,ht⟩ := (ExtensionLocalAffine.entry_constraints _ _ _ _).mp h
  apply (rows_zero_iff f B imaginary eighth scaleAddress inverseAddress z hi hu).mpr
  refine ⟨?_,ht⟩
  intro x
  by_cases hx : x ∈ B.1
  · simpa [hx,hinv x hx] using mul_inv_cancel₀ (hn x hx)
  · simpa [hx] using hz x hx

end
end Holant.LocalDrafts.MainChain.TransformRecognition.SymbolicLocalAffineRows
