import Holant.Proofs.Closure.ClosureCyclicCurrentDoubledFactor

/-! The concrete extracted doubled binary is nonsingular and hence prime.
Singular outside binaries are not covered by this conclusion; their actual
saved factor trees are inspected by the separate unary-exposure adapter. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
open Holant Holant.Tractable Holant.Algebraic
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain

/-- Every genuine ordered 1+1 split of a binary has determinant zero. -/
theorem binary_split_singular {L : Type*} [Field L] (f : Signature L 2)
    {a b : AnySignature L} (s : ProperSplit ⟨2,f⟩ a b) : Matrix.det (binaryMatrix f) = 0 := by
  obtain ⟨na,u⟩ := a
  obtain ⟨nb,v⟩ := b
  have ha : na = 1 := by have h := s.arity; have hp := s.left_pos; have hq := s.right_pos; change na+nb=2 at h; change 0<na at hp; change 0<nb at hq; omega
  have hb : nb = 1 := by have h := s.arity; have hp := s.left_pos; have hq := s.right_pos; change na+nb=2 at h; change 0<na at hp; change 0<nb at hq; omega
  subst na
  subst nb
  have different : s.ports (.inl 0) ≠ s.ports (.inr 0) := by
    intro h
    have h' := s.ports.injective h
    cases h'
  have coordinate (i : Fin 2) : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases coordinate (s.ports (.inl 0)) with h0 | h0 <;>
    rcases coordinate (s.ports (.inr 0)) with h1 | h1
  · exact False.elim (different (h0.trans h1.symm))
  · have left (i : Fin 1) : s.ports (.inl i) = 0 := by have : i=0 := Fin.eq_zero i; simpa only [this] using h0
    have right (i : Fin 1) : s.ports (.inr i) = 1 := by have : i=0 := Fin.eq_zero i; simpa only [this] using h1
    have eqn := s.equation
    change f = _ at eqn
    rw [binary_det_formula]
    simp [binaryMatrix,eqn,left,right] <;> ring
  · have left (i : Fin 1) : s.ports (.inl i) = 1 := by have : i=0 := Fin.eq_zero i; simpa only [this] using h0
    have right (i : Fin 1) : s.ports (.inr i) = 0 := by have : i=0 := Fin.eq_zero i; simpa only [this] using h1
    have eqn := s.equation
    change f = _ at eqn
    rw [binary_det_formula]
    simp [binaryMatrix,eqn,left,right] <;> ring
  · exact False.elim (different (h0.trans h1.symm))

theorem nonsingular_binary_prime {L : Type*} [Field L] (f : Signature L 2)
    (det : Matrix.det (binaryMatrix f) ≠ 0) : Prime (⟨2,f⟩ : AnySignature L) := by
  refine ⟨?_,?_⟩
  · intro zero
    apply det
    change f = 0 at zero
    rw [zero]
    rw [binary_det_formula]
    simp [binaryMatrix]
  · rintro ⟨a,b,⟨s⟩⟩
    exact det (binary_split_singular f s)

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) {m : ℕ}
variable (d : CyclicBoundary.NonsquareExit.DoubledOutside
  (RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) P.family) m)

def wordsTwo : (Fin 2 → Bool) ≃ Bool × Bool where
  toFun x := (x 0,x 1)
  invFun x := ![x.1,x.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

theorem sum_wordsTwo (f : (Fin 2 → Bool) → ℂ) :
    (∑ x, f x) = ∑ a : Bool,∑ b : Bool, f ![a,b] := by
  rw [← wordsTwo.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

theorem doubledBinary_det : Matrix.det (binaryMatrix (doubledBinary G P d)) = -4*d.ratio := by
  rw [binary_det_formula]
  simp [binaryMatrix,doubledBinary,CyclicBoundary.ActualCards.physical₂,
    CyclicBoundary.PhysicalAttachments.binary,Signature.coordinateAction,Fin.prod_univ_succ,
    CyclicBoundary.ZeroEndpointDressing.hadamard,CyclicBoundary.DihedralFactor.anti,
    sum_wordsTwo,Fintype.sum_bool]
  ring

theorem doubleFactor_nonsingular : Matrix.det (binaryMatrix (doubleFactors G P d).left) ≠ 0 := by
  obtain ⟨c,hc,he⟩ := doubleFactor_projective G P d
  have matrix : (binaryMatrix (doubleFactors G P d).left).map (ClosurePhysicalBridge.complexEmbedding G) =
      c • binaryMatrix (doubledBinary G P d) := by
    funext a b
    exact congrFun he ![a,b]
  intro zero
  have mapped := congrArg (ClosurePhysicalBridge.complexEmbedding G) zero
  rw [map_zero,RingHom.map_det] at mapped
  change Matrix.det ((binaryMatrix (doubleFactors G P d).left).map (ClosurePhysicalBridge.complexEmbedding G)) = 0 at mapped
  rw [matrix,Matrix.det_smul,doubledBinary_det] at mapped
  exact (mul_ne_zero (pow_ne_zero _ hc) (mul_ne_zero (by norm_num) d.ratio_nonzero)) mapped

theorem doubleFactor_prime : Prime (⟨2,(doubleFactors G P d).left⟩ : AnySignature (OI.K G)) :=
  nonsingular_binary_prime _ (doubleFactor_nonsingular G P d)
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
