import Holant.Proofs.Closure.ClosureCyclicCurrentAccess

/-! Nonzero projective corrections preserve the actual cyclic dispatch domains.
The correction scalar of a descended graph is kept ambient until a literal
original tensor supplies a pivot; no analytic scalar preimage is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
open Holant Holant.Tractable Holant.Marked
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.Pauli.ExoticKlein.Fiber

/-- Exact scalar transport of a proper split keeps its ports and factors. -/
def unscaleSplit {L : Type*} [Field L] {f a b : AnySignature L}
    (c : L) (hc : c ≠ 0) (s : ProperSplit ⟨f.1,c • f.2⟩ a b) : ProperSplit f a b where
  left_pos := s.left_pos
  right_pos := s.right_pos
  ports := s.ports
  scale := (Units.mk0 c hc)⁻¹ * s.scale
  equation := by
    funext x
    have he := congrFun s.equation x
    change c * f.2 x = (s.scale:L) * (a.2 _ * b.2 _) at he
    calc
      f.2 x = c⁻¹ * (c * f.2 x) := by rw [← mul_assoc,inv_mul_cancel₀ hc,one_mul]
      _ = c⁻¹ * ((s.scale:L) * (a.2 _ * b.2 _)) := congrArg (c⁻¹ * ·) he
      _ = _ := by simp only [Units.val_mul,Units.val_inv_eq_inv_val,Units.val_mk0,mul_assoc]

theorem prime_scaled {L : Type*} [Field L] (f : AnySignature L) (prime : Prime f)
    (c : L) (hc : c ≠ 0) : Prime (⟨f.1,c • f.2⟩ : AnySignature L) := by
  refine ⟨smul_ne_zero hc prime.1,?_⟩
  rintro ⟨a,b,⟨s⟩⟩
  exact prime.2 ⟨a,b,⟨unscaleSplit c hc s⟩⟩

theorem complex_phase_scaled (m : ℕ) (c : ℂ) (hc : c ≠ 0) (T : Kernel ℂ) :
    CP.IsPhase m (c • T) ↔ CP.IsPhase m T := by
  constructor
  · rintro ⟨t,d,ht,hd,he⟩
    refine ⟨t,c⁻¹*d,ht,mul_ne_zero (inv_ne_zero hc) hd,?_⟩
    have h := congrArg (fun M : Kernel ℂ => c⁻¹ • M) he
    simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using h
  · rintro ⟨t,d,ht,hd,he⟩
    exact ⟨t,c*d,ht,mul_ne_zero hc hd,by rw [he,smul_smul]⟩

theorem walshTransfer_scaled (c : ℂ) (B : Signature ℂ 2) :
    CyclicBoundary.ActualCards.walshTransfer (c • B) =
      c • CyclicBoundary.ActualCards.walshTransfer B := by
  funext u v
  simp [CyclicBoundary.ActualCards.walshTransfer,Signature.coordinateAction,
    Kernel.mul,Pi.smul_apply,smul_eq_mul,mul_assoc,mul_left_comm]
  simp_rw [← Finset.mul_sum]
  ring

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

/-- Original output is prime whenever the real endpoint is prime; the graph's
nonzero ambient scale is handled before injective original-field descent. -/
theorem ProjectiveOutput.source_prime {n : ℕ} (target : Signature ℂ n)
    (d : ProjectiveOutput G P target) (prime : Prime (⟨n,target⟩ : AnySignature ℂ)) :
    Prime (⟨n,d.output⟩ : AnySignature (OI.K G)) := by
  apply (prime_mapSignature_iff (ClosurePhysicalBridge.complexEmbedding G) _).mp
  change Prime (⟨n,RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) d.output⟩ : AnySignature ℂ)
  rw [d.mapped]
  exact prime_scaled _ prime _ d.multiplierNonzero

/-- The outside test concerns the SAME exact descended physical table. -/
theorem ProjectiveOutput.source_outside {m : ℕ} (target : Signature ℂ 2)
    (d : ProjectiveOutput G P target)
    (outside : ¬CP.IsPhase m (CyclicBoundary.ActualCards.walshTransfer target)) :
    ¬CP.IsPhase m (CyclicBoundary.ActualCards.walshTransfer
      (RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) d.output)) := by
  rw [d.mapped,walshTransfer_scaled,complex_phase_scaled _ _ d.multiplierNonzero]
  exact outside

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
