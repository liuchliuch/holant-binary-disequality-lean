import Holant.Proofs.Closure.ClosureCyclicCurrentDoubled

/-! The charged ORIGINAL-field factor of the actual doubled output is on the
same computed outside binary line. Its original table is constructed by pivot
factor descent; the ambient projective comparison scalar is explicit and never
asserted to lie in the original field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) {m : ℕ}
variable (d : CyclicBoundary.NonsquareExit.DoubledOutside
  (RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) P.family) m)

/-- The descended split keeps the original doubled partition and scale one,
so its two exact source factors have the original complex bilinear equation. -/
theorem doubleFactors_equation (x y : Fin 2 → Bool) :
    ClosurePhysicalBridge.complexEmbedding G ((doubleFactors G P d).left x) *
      ClosurePhysicalBridge.complexEmbedding G ((doubleFactors G P d).right y) =
    (doubledOutput G P d).multiplier * doubledBinary G P d x * doubledBinary G P d y := by
  let join : Fin 4 → Bool := fun i => Sum.elim x y
    ((CyclicBoundary.ZeroEndpointFactor.ports 0).symm i)
  have source := congrFun (doubleFactors G P d).split.equation join
  rw [(doubleFactors G P d).unit] at source
  simp only [Units.val_one,one_mul,(doubleFactors G P d).samePorts,join,
    Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr] at source
  have ambient := congrFun ((doubledOutput G P d).mapped) join
  change ClosurePhysicalBridge.complexEmbedding G ((ProjectiveOutput.output G P (doubledTensor G P d) (doubledOutput G P d)) join) = _ at ambient
  rw [source,map_mul] at ambient
  simpa only [Pi.smul_apply,smul_eq_mul,doubledTensor,CyclicBoundary.NonsquareExit.doubled,
    Tensor.reindex,Tensor.tensor,join,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,mul_assoc] using ambient

/-- A nonzero exact source-factor pivot recovers the projective line. This is
a comparison scalar in C, not a newly installed foreign source coefficient. -/
theorem doubleFactor_projective : ∃ c : ℂ, c ≠ 0 ∧
    RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) (doubleFactors G P d).left =
      c • doubledBinary G P d := by
  have nonzero := (doubleFactors G P d).split.factors_nonzero
    (ProjectiveOutput.source_nonzero G P (doubledTensor G P d) (doubledOutput G P d) (doubledTensor_nonzero G P d))
  obtain ⟨x,hx⟩ : ∃ x, (doubleFactors G P d).left x ≠ 0 := by
    by_contra h
    push_neg at h
    exact nonzero.1 (funext h)
  obtain ⟨y,hy⟩ : ∃ y, (doubleFactors G P d).right y ≠ 0 := by
    by_contra h
    push_neg at h
    exact nonzero.2 (funext h)
  have hv : ClosurePhysicalBridge.complexEmbedding G ((doubleFactors G P d).right y) ≠ 0 :=
    (map_ne_zero (ClosurePhysicalBridge.complexEmbedding G)).mpr hy
  have hu : ClosurePhysicalBridge.complexEmbedding G ((doubleFactors G P d).left x) ≠ 0 :=
    (map_ne_zero (ClosurePhysicalBridge.complexEmbedding G)).mpr hx
  have hB : doubledBinary G P d y ≠ 0 := by
    intro zero
    have h := doubleFactors_equation G P d x y
    rw [zero,mul_zero] at h
    exact (mul_ne_zero hu hv) h
  let c := (doubledOutput G P d).multiplier * doubledBinary G P d y /
    ClosurePhysicalBridge.complexEmbedding G ((doubleFactors G P d).right y)
  refine ⟨c,div_ne_zero (mul_ne_zero (doubledOutput G P d).multiplierNonzero hB) hv,?_⟩
  funext z
  change ClosurePhysicalBridge.complexEmbedding G ((doubleFactors G P d).left z) = c * doubledBinary G P d z
  calc
    _ = ((doubledOutput G P d).multiplier * doubledBinary G P d z * doubledBinary G P d y) /
        ClosurePhysicalBridge.complexEmbedding G ((doubleFactors G P d).right y) :=
      (eq_div_iff hv).mpr (doubleFactors_equation G P d z y)
    _ = _ := by dsimp [c]; ring

/-- The separate charged factor boundary is genuinely outside the OLD cyclic
phase group. Access is proved; direct realizability over P is not assumed. -/
theorem doubleFactor_outside : ¬CP.IsPhase m (CyclicBoundary.ActualCards.walshTransfer
    (RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) (doubleFactors G P d).left)) := by
  obtain ⟨c,hc,he⟩ := doubleFactor_projective G P d
  rw [he,walshTransfer_scaled,complex_phase_scaled _ _ hc]
  exact d.binary_outside

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
