import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedMask
import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedActiveBlocks

/-! The actual shifted current prime has no active complementary block.
The selected mask, nonzero endpoints and root ratio are outputs of the full
current deck; the original sector table is proved Product in the same basis. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedEqualityMask
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.Marked.SupportAtlas Holant.Certificates.EqualityQuaternary
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace M
export GlobalCloseCompletionShiftedMask
  (basis selected parameters phi reps ambient normalized originalMask originalMask_map dressed_safe masked_prime atlas)
end M
namespace CQ
export Holant.Projective.CyclicQuaternary (ofCoordinates)
end CQ
namespace A
export GlobalCloseCompletionShiftedActiveBlocks (prime_is_equality flipped_equality_product)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (native : GlobalCloseCompletionShiftedMarking.Native G P torsion)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

include core literal stable in
theorem equality_mask : ∃mask : Word,∃a h : Scalar,a≠0 ∧ h≠0 ∧
    Roots (M.selected G P torsion native).m (h/a) ∧
    (M.basis G P torsion native).symm.action
      (RingHomRealization.mapSignature (M.phi G) (M.originalMask G P torsion native q mask))=
      CQ.ofCoordinates a h (fun _=>(0,0)) := by
  obtain ⟨mask,form⟩ := M.atlas G P torsion native q core literal stable
  have hd : (delta (M.parameters G P torsion native) : ℂ)≠0 := by
    exact_mod_cast delta_ne_zero (M.parameters G P torsion native)
  have hr : (((delta (M.parameters G P torsion native) : ℂ)^2)^(M.selected G P torsion native).m)=1 := by
    exact_mod_cast delta_root (M.parameters G P torsion native)
  have hn : (delta (M.parameters G P torsion native) : ℂ)^(M.selected G P torsion native).m≠1 := by
    have even : Even (M.selected G P torsion native).m :=
      native.reflection.selected_even P.equality native.axis native.notTwo native.notFour
    have notroot : (delta (M.parameters G P torsion native))^(M.selected G P torsion native).m≠1 := by
      change (-native.reflection.eta⁻¹)^(M.selected G P torsion native).m≠1
      intro h
      have hi : (native.reflection.eta^(M.selected G P torsion native).m)⁻¹=1 := by
        simpa only [even.neg_pow,inv_pow] using h
      exact native.reflection.eta_not_root native.axis native.notTwo native.notFour native.noZ (inv_eq_one.mp hi)
    exact_mod_cast notroot
  obtain ⟨a,h,ha,hh,root,exact⟩ := A.prime_is_equality (M.selected G P torsion native).range
    _ hd hr hn _ form (M.masked_prime G P torsion native q core literal mask)
    (M.dressed_safe G P torsion native q core literal stable
      (HistorySectorNormalized.flipDelta G P torsion (M.basis G P torsion native)
        (M.selected G P torsion native) mask))
  exact ⟨mask,a,h,ha,hh,root,exact⟩

include core literal stable in
theorem sector_product : Product (M.normalized G P torsion native q) := by
  obtain ⟨mask,a,h,ha,hh,root,he⟩ := equality_mask G P torsion native q core literal stable
  let reps := M.reps G P torsion native
  let c := dressingMultiplier (reps.multiplier true (phaseOne (M.selected G P torsion native).m)) mask
  have hc : c≠0 := dressingMultiplier_ne_zero _ (reps.multiplier_ne_zero _ _) mask
  have hd : (M.basis G P torsion native).symm.action
      (RingHomRealization.mapSignature (M.phi G) (M.originalMask G P torsion native q mask))=
      c • Flip.value (M.normalized G P torsion native q) mask := by
    rw [M.originalMask_map]
    funext x
    exact sector_dressMask _ _ _ _ reps.x_transfer mask x
  have back : M.normalized G P torsion native q=
      fun x=>c⁻¹*Flip.value (CQ.ofCoordinates a h (fun _=>(0,0))) mask x := by
    have hflip := congrArg (fun f=>Flip.value f mask) (hd.symm.trans he)
    have hinv := flip_twice (M.normalized G P torsion native q) mask
    funext x
    have hx := congrFun hflip x
    have hi := congrFun hinv x
    simp only [Flip.value,Pi.smul_apply,smul_eq_mul] at hx hi
    rw [hi] at hx
    change _=c⁻¹*CQ.ofCoordinates a h (fun _=>(0,0)) (xorWord x mask)
    rw [←hx,←mul_assoc,inv_mul_cancel₀ hc,one_mul]
  rw [back]
  exact (A.flipped_equality_product a h ha mask).scale c⁻¹

structure Choice : Type where
  mask : Word
  left : Scalar
  right : Scalar
  left_nonzero : left≠0
  right_nonzero : right≠0
  ratio : Roots (M.selected G P torsion native).m (right/left)
  exact : (M.basis G P torsion native).symm.action
      (RingHomRealization.mapSignature (M.phi G) (M.originalMask G P torsion native q mask))=
    CQ.ofCoordinates left right (fun _=>(0,0))

def choose : Choice G P torsion native q := Classical.choice (by
  obtain ⟨mask,a,h,ha,hh,root,he⟩ := equality_mask G P torsion native q core literal stable
  exact ⟨⟨mask,a,h,ha,hh,root,he⟩⟩)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedEqualityMask
end
