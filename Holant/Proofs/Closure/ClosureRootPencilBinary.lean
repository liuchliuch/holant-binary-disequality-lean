import Holant.Proofs.Closure.ClosureRootPencilFactors

/-! The reconstructed varying binary inherits the exact zero-safe root
condition from the genuine sampled four-port products. Its parity and ordered
entry ratios are derived from the same actual anchor coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
open Holant Holant.Projective
namespace Product
variable {m : ℕ} {f q : Signature ℂ 4} (P : Product m f)

theorem leftVariable_root (E : Product m q) (supported : support f ⊆ support q) :
    IsRootMonomial m (P.leftVariable q) := by
  have h0 : coordinates P q false false ≠ 0 :=
    (mem_support q _).mp (supported ((mem_support f _).mpr (P.word_supported (bits false false))))
  have h1 : coordinates P q false true ≠ 0 :=
    (mem_support q _).mp (supported ((mem_support f _).mpr (P.word_supported (bits false true))))
  rw [leftVariable,isRootMonomial_parityCoordinates_iff]
  refine ⟨div_ne_zero h0 (P.weight_nonzero 0 false),div_ne_zero h1 (P.weight_nonzero 0 false),?_⟩
  have ratio : (coordinates P q false true/P.weight 0 false)/
      (coordinates P q false false/P.weight 0 false)=
      coordinates P q false true/coordinates P q false false := by
    field_simp [P.weight_nonzero 0 false,h0]
  rw [ratio]
  exact E.ratio_roots (P.word (bits false true)) (P.word (bits false false)) h1 h0

theorem rightVariable_root (E : Product m q) (supported : support f ⊆ support q) :
    IsRootMonomial m (P.rightVariable q) := by
  have h0 : coordinates P q false false ≠ 0 :=
    (mem_support q _).mp (supported ((mem_support f _).mpr (P.word_supported (bits false false))))
  have h1 : coordinates P q true false ≠ 0 :=
    (mem_support q _).mp (supported ((mem_support f _).mpr (P.word_supported (bits true false))))
  rw [rightVariable,isRootMonomial_parityCoordinates_iff]
  refine ⟨div_ne_zero h0 (P.weight_nonzero 1 false),div_ne_zero h1 (P.weight_nonzero 1 false),?_⟩
  have ratio : (coordinates P q true false/P.weight 1 false)/
      (coordinates P q false false/P.weight 1 false)=
      coordinates P q true false/coordinates P q false false := by
    field_simp [P.weight_nonzero 1 false,h0]
  rw [ratio]
  exact E.ratio_roots (P.word (bits true false)) (P.word (bits false false)) h1 h0

@[simp] theorem leftVariable_zero : P.leftVariable 0=0 := by
  funext a b
  cases h : P.parity 1 <;> cases a <;> cases b <;>
    simp [leftVariable,coordinates,parityCoordinates,parityAxis,h]

@[simp] theorem rightVariable_zero : P.rightVariable 0=0 := by
  funext a b
  cases h : P.parity 0 <;> cases a <;> cases b <;>
    simp [rightVariable,coordinates,parityCoordinates,parityAxis,h]

theorem leftVariable_pencil (U V : Signature ℂ 4) (t : ℂ) :
    P.leftVariable (pencil U V t)=binaryPencil (P.leftVariable U) (P.leftVariable V) t := by
  rw [leftVariable,leftVariable,leftVariable,binaryPencil_parityCoordinates]
  congr 1
  all_goals
    change (_+t*_)/P.weight 0 false = _/P.weight 0 false+t*(_/P.weight 0 false)
    dsimp only [coordinates]
    simp only [div_eq_mul_inv]
    ring

theorem rightVariable_pencil (U V : Signature ℂ 4) (t : ℂ) :
    P.rightVariable (pencil U V t)=binaryPencil (P.rightVariable U) (P.rightVariable V) t := by
  rw [rightVariable,rightVariable,rightVariable,binaryPencil_parityCoordinates]
  congr 1
  all_goals
    change (_+t*_)/P.weight 1 false = _/P.weight 1 false+t*(_/P.weight 1 false)
    dsimp only [coordinates]
    simp only [div_eq_mul_inv]
    ring

theorem leftVariable_samples (U V : Signature ℂ 4)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t))
    (anchorSubset : ∀ t : ℂ, t^m=1 → pencil U V t≠0 → support f ⊆ support (pencil U V t)) :
    ∀ t : ℂ, t^m=1 → binaryPencil (P.leftVariable U) (P.leftVariable V) t=0 ∨
      IsRootMonomial m (binaryPencil (P.leftVariable U) (P.leftVariable V) t) := by
  intro t ht
  rw [←P.leftVariable_pencil]
  rcases samples t ht with zero | actual
  · left
    rw [zero,P.leftVariable_zero]
  · right
    obtain ⟨E⟩ := actual
    exact P.leftVariable_root E (anchorSubset t ht E.nonzero_tensor)

theorem rightVariable_samples (U V : Signature ℂ 4)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t))
    (anchorSubset : ∀ t : ℂ, t^m=1 → pencil U V t≠0 → support f ⊆ support (pencil U V t)) :
    ∀ t : ℂ, t^m=1 → binaryPencil (P.rightVariable U) (P.rightVariable V) t=0 ∨
      IsRootMonomial m (binaryPencil (P.rightVariable U) (P.rightVariable V) t) := by
  intro t ht
  rw [←P.rightVariable_pencil]
  rcases samples t ht with zero | actual
  · left
    rw [zero,P.rightVariable_zero]
  · right
    obtain ⟨E⟩ := actual
    exact P.rightVariable_root E (anchorSubset t ht E.nonzero_tensor)

end Product
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
