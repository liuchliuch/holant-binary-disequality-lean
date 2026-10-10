import Holant.Certificates.IcosahedralSeparator.StructuralInterface
import Holant.Certificates.IcosahedralSeparator.UniformChecks
import Holant.Certificates.IcosahedralSeparator.OppositeNative

/-! Lemma9.29, the complete icosahedral bridge and uniform separator.
Source: paper1.tex14673–14706,17290–17400,18733–18757.
All maps and tensors are literal complex-linear maps and tensors; all ranks
are Mathlib matrix ranks; both physical displays use actual native-X networks. -/
namespace Holant.Certificates.IcosahedralSeparator
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

def binaryCard (q : FourTensor) : Matrix Bool Bool ℂ :=
  fun a b => Signature.contract subsequentKernel q ![a,b]

def transfer (q : FourTensor) : Matrix Bool Bool ℂ := binaryCard q * Matrix.of X

theorem uniform_subsequent_transfer (i : Fin 30) :
    transfer (uniformOutput i) = Kernel.mul (subsequentOutput i) Signature.disequality := by
  ext a b
  simp [transfer,binaryCard,subsequentOutput,Kernel.mul,Matrix.mul_apply,X,add_comm]

theorem uniform_full_rank_separator (Φ : Binary →ₗ[ℂ] FourTensor)
    (hN : Normalized Φ) (hR : mapRank Φ = 4) :
    (∀ r : Fin 3, (flatten r (Φ uniformKernel)).rank = 3) ∧
    (binaryCard (Φ uniformKernel)).det ≠ 0 ∧
    ¬groupDirection .icosahedral (transfer (Φ uniformKernel)) := by
  obtain ⟨i,rfl⟩ := (full_rank_iff Φ hN).mp hR
  rw [uniformOutput_map]
  refine ⟨uniform_output_ranks i,uniform_subsequent_nonsingular i,?_⟩
  rw [uniform_subsequent_transfer]
  exact uniform_subsequent_outside i

theorem source_uniform_separator (Φ : Binary →ₗ[ℂ] FourTensor)
    (hN : (Φ TetrahedralBridge.normalPlus = A ∧ Φ TetrahedralBridge.normalMinus = -B) ∧
      ∀ j : Fin 3, bridgeConditions .icosahedral (Φ (quaternionBasis j.succ)))
    (hR : mapRank Φ = 4) :
    (∀ r : Fin 3, (flatten r (Φ uniformKernel)).rank = 3) ∧
    (binaryCard (Φ uniformKernel)).det ≠ 0 ∧
    ¬groupDirection .icosahedral (transfer (Φ uniformKernel)) :=
  uniform_full_rank_separator Φ ((normalized_iff_source Φ).mpr hN) hR

theorem standard_native_separator (h : Signature ℂ 6)
    (hN : Normalized (actualMap h)) (hR : mapRank (actualMap h) = 4) :
    (∀ r : Fin 3, (flatten r (Signature.contract uniformKernel h)).rank = 3) ∧
    (binaryCard (Signature.contract uniformKernel h)).det ≠ 0 ∧
    ¬groupDirection .icosahedral (transfer (Signature.contract uniformKernel h)) ∧
    Gadget.Realizes (Native.resources h) .disequality (Signature.contract uniformKernel h) ∧
    Gadget.Realizes (Native.resources h) .disequality
      (Signature.contract subsequentKernel (Signature.contract uniformKernel h)) := by
  obtain ⟨hr,hd,ho⟩ := uniform_full_rank_separator (actualMap h) hN hR
  exact ⟨hr,hd,ho,Native.first_realizes h _ uniformKernel_group,
    Native.sequential_realizes h _ _ uniformKernel_group subsequentKernel_group⟩

theorem opposite_kernels_actual :
    OppositeIcosahedral.Direction Opposite.firstKernel ∧
    OppositeIcosahedral.Direction Opposite.secondKernel :=
  ⟨(OppositeIcosahedral.kernel_membership_iff _).mpr uniformKernel_group,
   (OppositeIcosahedral.kernel_membership_iff _).mpr subsequentKernel_group⟩

theorem opposite_output_ranks (i : Fin 30) (r : Fin 3) :
    (flatten r (Opposite.output i)).rank = 3 := by
  rw [Opposite.output,Opposite.flatten_rank]
  exact uniform_output_ranks i r

theorem opposite_output_nonsingular (i : Fin 30) : (Opposite.finalOutput i).det ≠ 0 :=
  (Opposite.final_nonsingular_iff i).mpr (uniform_subsequent_nonsingular i)

theorem opposite_output_outside (i : Fin 30) :
    ¬OppositeIcosahedral.Direction (Opposite.finalOutput i * OppositeIcosahedral.X) := by
  apply (Opposite.final_outside_iff i).mpr
  have ht : Matrix.of (subsequentOutput i)*OppositeIcosahedral.X = transfer (uniformOutput i) := rfl
  rw [ht,uniform_subsequent_transfer]
  exact uniform_subsequent_outside i

/-- The arbitrary original tensor h stays unchanged on the left. The analytical
normalization is used only to find its complete full-rank case. Both κ kernels
are actual members of the literal opposite group; retained I is never gauged. -/
theorem opposite_native_separator (h : Signature ℂ 6)
    (hN : Normalized (actualMap (OppositeIcosahedral.analytical h)))
    (hR : mapRank (actualMap (OppositeIcosahedral.analytical h)) = 4) :
    ∃ i : Fin 30,
      Signature.contract Opposite.firstKernel h = Opposite.output i ∧
      (fun a b => Signature.contract Opposite.secondKernel
        (Signature.contract Opposite.firstKernel h) ![a,b]) = Opposite.finalOutput i ∧
      (∀ r : Fin 3, (flatten r (Opposite.output i)).rank = 3) ∧
      (Opposite.finalOutput i).det ≠ 0 ∧
      ¬OppositeIcosahedral.Direction (Opposite.finalOutput i * OppositeIcosahedral.X) ∧
      Gadget.Realizes (Opposite.resources h) .disequality (Signature.contract Opposite.firstKernel h) ∧
      Gadget.Realizes (Opposite.resources h) .disequality
        (Signature.contract Opposite.secondKernel (Signature.contract Opposite.firstKernel h)) := by
  obtain ⟨i,hi⟩ := actual_full_rank_output (OppositeIcosahedral.analytical h) hN hR
  exact ⟨i,Opposite.original_first h i hi,Opposite.original_second h i hi,
    opposite_output_ranks i,opposite_output_nonsingular i,opposite_output_outside i,
    Opposite.first_realizes h _ opposite_kernels_actual.1,
    Opposite.sequential_realizes h _ _ opposite_kernels_actual.1 opposite_kernels_actual.2⟩

structure IcosahedralSeparatorCertificate : Prop where
  bridge : IcosahedralBridgeCertificate
  first_kernel_actual : groupDirection .icosahedral uniformKernel
  second_kernel_actual : groupDirection .icosahedral subsequentKernel
  all_full_rank_maps : ∀ Φ : Binary →ₗ[ℂ] FourTensor, Normalized Φ → mapRank Φ = 4 →
    (∀ r : Fin 3, (flatten r (Φ uniformKernel)).rank = 3) ∧
      (binaryCard (Φ uniformKernel)).det ≠ 0 ∧
      ¬groupDirection .icosahedral (transfer (Φ uniformKernel))
  opposite_first_actual : OppositeIcosahedral.Direction Opposite.firstKernel
  opposite_second_actual : OppositeIcosahedral.Direction Opposite.secondKernel
  opposite_ranks : ∀ i : Fin 30, ∀ r : Fin 3, (flatten r (Opposite.output i)).rank = 3
  opposite_nonsingular : ∀ i : Fin 30, (Opposite.finalOutput i).det ≠ 0
  opposite_outside : ∀ i : Fin 30,
    ¬OppositeIcosahedral.Direction (Opposite.finalOutput i * OppositeIcosahedral.X)
  standard_native : ∀ h : Signature ℂ 6,
    Gadget.Realizes (Native.resources h) .disequality (Signature.contract uniformKernel h) ∧
      Gadget.Realizes (Native.resources h) .disequality
        (Signature.contract subsequentKernel (Signature.contract uniformKernel h))
  opposite_native : ∀ h : Signature ℂ 6,
    Gadget.Realizes (Opposite.resources h) .disequality (Signature.contract Opposite.firstKernel h) ∧
      Gadget.Realizes (Opposite.resources h) .disequality
        (Signature.contract Opposite.secondKernel (Signature.contract Opposite.firstKernel h))

/-- Complete Lemma9.29. All unrestricted cone, scale, count, rank, outsider,
actual-kernel and native original-coordinate obligations are discharged. -/
theorem icosahedral_bridge_and_uniform_separator : IcosahedralSeparatorCertificate where
  bridge := icosahedral_bridge
  first_kernel_actual := uniformKernel_group
  second_kernel_actual := subsequentKernel_group
  all_full_rank_maps := uniform_full_rank_separator
  opposite_first_actual := opposite_kernels_actual.1
  opposite_second_actual := opposite_kernels_actual.2
  opposite_ranks := opposite_output_ranks
  opposite_nonsingular := opposite_output_nonsingular
  opposite_outside := opposite_output_outside
  standard_native h := ⟨Native.first_realizes h _ uniformKernel_group,
    Native.sequential_realizes h _ _ uniformKernel_group subsequentKernel_group⟩
  opposite_native h := ⟨Opposite.first_realizes h _ opposite_kernels_actual.1,
    Opposite.sequential_realizes h _ _ opposite_kernels_actual.1 opposite_kernels_actual.2⟩

end
end Holant.Certificates.IcosahedralSeparator
