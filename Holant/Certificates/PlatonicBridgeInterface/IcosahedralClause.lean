import Holant.Certificates.PlatonicBridgeInterface.ProjectiveGroup
import Holant.Certificates.IcosahedralSeparator.Interface

/-! A.27(iii), including the genuine projective A5 identification, unrestricted
complex bridge classification, and both original-coordinate physical displays. -/
namespace Holant.Certificates.PlatonicBridgeInterface
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
namespace Icosahedral

structure Clause : Prop where
  sixty_actual_projective_points : Fintype.card ProjectiveClass = 60
  isomorphic_to_A5 : Nonempty (ProjectiveClass ≃* alternatingGroup (Fin 5))
  induced_product : ∀ U V : Matrix Bool Bool ℂ,
    ∀ hU : groupDirection .icosahedral U, ∀ hV : groupDirection .icosahedral V,
    matrixClass (U*V) (RainbowOrbit.groupDirection_mul .icosahedral hU hV) =
      matrixClass U hU * matrixClass V hV
  induced_inverse : ∀ U : Matrix Bool Bool ℂ, ∀ hU : groupDirection .icosahedral U,
    matrixClass U⁻¹ (groupDirection_inverse .icosahedral hU) = (matrixClass U hU)⁻¹
  closed_operations : ∀ U V : Matrix Bool Bool ℂ,
    groupDirection .icosahedral U → groupDirection .icosahedral V →
      groupDirection .icosahedral (U*V) ∧
        groupDirection .icosahedral (U⁻¹ : Matrix Bool Bool ℂ) ∧
        groupDirection .icosahedral U.transpose
  complete_bridge_and_separator : IcosahedralSeparator.IcosahedralSeparatorCertificate
  standard_original : ∀ h : Signature ℂ 6,
    IcosahedralSeparator.Normalized (IcosahedralSeparator.actualMap h) →
    IcosahedralSeparator.mapRank (IcosahedralSeparator.actualMap h) = 4 →
    (∀ r : Fin 3, (flatten r (Signature.contract IcosahedralSeparator.uniformKernel h)).rank = 3) ∧
    (IcosahedralSeparator.binaryCard (Signature.contract IcosahedralSeparator.uniformKernel h)).det ≠ 0 ∧
    ¬groupDirection .icosahedral
      (IcosahedralSeparator.transfer (Signature.contract IcosahedralSeparator.uniformKernel h)) ∧
    Gadget.Realizes (IcosahedralSeparator.Native.resources h) .disequality
      (Signature.contract IcosahedralSeparator.uniformKernel h) ∧
    Gadget.Realizes (IcosahedralSeparator.Native.resources h) .disequality
      (Signature.contract IcosahedralSeparator.subsequentKernel
        (Signature.contract IcosahedralSeparator.uniformKernel h))
  opposite_original : ∀ h : Signature ℂ 6,
    IcosahedralSeparator.Normalized (IcosahedralSeparator.actualMap (OppositeIcosahedral.analytical h)) →
    IcosahedralSeparator.mapRank (IcosahedralSeparator.actualMap (OppositeIcosahedral.analytical h)) = 4 →
    ∃ i : Fin 30,
      Signature.contract IcosahedralSeparator.Opposite.firstKernel h = IcosahedralSeparator.Opposite.output i ∧
      (fun a b => Signature.contract IcosahedralSeparator.Opposite.secondKernel
        (Signature.contract IcosahedralSeparator.Opposite.firstKernel h) ![a,b]) =
        IcosahedralSeparator.Opposite.finalOutput i ∧
      (∀ r : Fin 3, (flatten r (IcosahedralSeparator.Opposite.output i)).rank = 3) ∧
      (IcosahedralSeparator.Opposite.finalOutput i).det ≠ 0 ∧
      ¬OppositeIcosahedral.Direction
        (IcosahedralSeparator.Opposite.finalOutput i * OppositeIcosahedral.X) ∧
      Gadget.Realizes (IcosahedralSeparator.Opposite.resources h) .disequality
        (Signature.contract IcosahedralSeparator.Opposite.firstKernel h) ∧
      Gadget.Realizes (IcosahedralSeparator.Opposite.resources h) .disequality
        (Signature.contract IcosahedralSeparator.Opposite.secondKernel
          (Signature.contract IcosahedralSeparator.Opposite.firstKernel h))

theorem complete_clause : Clause where
  sixty_actual_projective_points := projective_card_sixty
  isomorphic_to_A5 := ⟨projective_iso_A5⟩
  induced_product := matrixClass_mul
  induced_inverse := matrixClass_inverse
  closed_operations := projective_closed_operations
  complete_bridge_and_separator := IcosahedralSeparator.icosahedral_bridge_and_uniform_separator
  standard_original := IcosahedralSeparator.standard_native_separator
  opposite_original := IcosahedralSeparator.opposite_native_separator

end Icosahedral
end
end Holant.Certificates.PlatonicBridgeInterface
