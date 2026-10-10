import Holant.Proofs.Algorithms.CyclicBoundary.PhysicalAttachments
import Holant.Proofs.Algorithms.RingHomRealization
import Holant.Projective.CyclicDressing.Action


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.AlgebraicRepresentatives
open Holant.Tractable Holant.Projective
open ZeroEndpointDressing PhysicalAttachments RingHomRealization
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev inclusion : AlgebraicComplex →+* ℂ := (algebraicClosure ℚ ℂ).subtype

def liftRoot {N : ℕ} (hN : 0 < N) (s : {s : ℂ // s^N=1}) :
    CyclicQuaternary.Physical.Root N := by
  have hi : IsIntegral ℚ s.val := by
    apply IsIntegral.of_pow (n := N) hN
    rw [s.property]
    exact isIntegral_one
  refine ⟨⟨s.val,hi⟩,?_⟩
  apply Subtype.ext
  exact s.property

@[simp] theorem liftRoot_value {N : ℕ} (hN : 0 < N) (s : {s : ℂ // s^N=1}) :
    ((liftRoot hN s).val : ℂ) = s.val := rfl

theorem algebraic_action {N : ℕ} {F : SignatureFamily AlgebraicComplex}
    (R : CyclicQuaternary.Physical.Representatives F N)
    (s : CyclicQuaternary.Physical.Root N) :
    Kernel.mul (Kernel.mul (R.matrix s) Signature.disequality) CyclicQuaternary.Physical.P =
      Kernel.mul CyclicQuaternary.Physical.P
        ((2*R.scalar s) • CyclicPhasePencil.phase s.val) := by
  have h := congrArg (Kernel.mul CyclicQuaternary.Physical.P)
    (CyclicDressing.local_phase_attachment (R.matrix s) s.val (R.scalar s) (R.walsh_form s))
  simpa only [←Kernel.mul_assoc,CyclicQuaternary.Physical.P_Pinv,Kernel.equality_mul] using h

/-- A derived interface, not an added assumption about the desired output. -/
def ofSource {N : ℕ} (hN : 0 < N) {F : SignatureFamily AlgebraicComplex}
    (R : CyclicQuaternary.Physical.Representatives F N) :
    Representatives (mapFamily inclusion F) N where
  matrix := fun s u v => inclusion (R.matrix (liftRoot hN s) u v)
  scalar := fun s => inclusion (R.scalar (liftRoot hN s))
  scalar_ne_zero := by
    intro s hz
    exact R.scalar_ne_zero (liftRoot hN s) (Subtype.ext (show ((R.scalar (liftRoot hN s) : AlgebraicComplex) : ℂ) = 0 from hz))
  actual := by
    intro s
    exact realizes_map inclusion (R.actual (liftRoot hN s))
  action := by
    intro s
    have h := algebraic_action R (liftRoot hN s)
    funext u v
    have hh := congrArg (fun A : Kernel AlgebraicComplex => inclusion (A u v)) h
    cases u <;> cases v <;>
      norm_num [Kernel.mul,CyclicQuaternary.Physical.P,hadamard,
        CyclicPhasePencil.phase,CyclicPhasePencil.diagonal,
        PhysicalAttachments.phase,TwoCopyKernels.diagonal,Signature.disequality,
        inclusion,liftRoot] at hh ⊢ <;> exact hh

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.AlgebraicRepresentatives
