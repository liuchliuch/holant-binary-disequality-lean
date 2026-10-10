import Holant.Platonic.StabilizerErasure.SemanticCodeNormalization
import Holant.Platonic.StabilizerErasure.PauliNormalizerInverse

/-! Convert arbitrary source-primary stabilizer isometry evidence into an
actual Clifford encoder followed by one actual logical Clifford. Neither
the encoder presentation nor the logical change is a supplied hypothesis. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase Holant.Platonic.StabilizerLine
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

theorem semantic_encoder_clifford_factorization
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) (hU : IsStabilizerIsometry U) :
    ∃V : StabilizerIsometry k n,∃L : AnalyticClifford k,U=V.map.comp L.operator.toLinearMap := by
  obtain ⟨V,hV⟩ := semantic_exists_same_range_encoder U hU
  let L := V.adjoint.comp U
  have hfactor (f : Signature ℂ k) : V.map (L f)=U f := by
    have hm : U f∈LinearMap.range V.map := by rw [hV];exact ⟨f,rfl⟩
    obtain ⟨g,hg⟩ := hm
    change V.map (V.adjoint (U f))=U f
    rw [←hg,V.adjoint_map]
  have hUi := isometry_injective U hU.1
  have hi : Function.Injective L := by
    intro f g he
    apply hUi
    rw [←hfactor f,←hfactor g,he]
  have hs : Function.Surjective L := by
    intro g
    have hm : V.map g∈LinearMap.range U := by rw [←hV];exact ⟨g,rfl⟩
    obtain ⟨f,hf⟩ := hm
    refine ⟨f,?_⟩
    change V.adjoint (U f)=g
    rw [hf,V.adjoint_map]
  let E := LinearEquiv.ofBijective L ⟨hi,hs⟩
  have hunit (f g : Signature ℂ k) : hermitian (E f) (E g)=hermitian f g := by
    change hermitian (L f) (L g)=_
    rw [←V.isometry,hfactor,hfactor,hU.1]
  have hnormal : NormalizesPauli E := by
    intro Q
    obtain ⟨P,hP⟩ := hU.2.2 Q
    rcases V.pauli_compression P with hz|⟨R,hR⟩
    · have he := congrArg V.adjoint (hP (fun _ => 1))
      change V.adjoint (P.run (U (fun _ => 1)))=L (Q.run (fun _ => 1)) at he
      rw [←hfactor,hz] at he
      have hq : Q.run (fun _ => 1)=0 := hi (by simpa using he.symm)
      exact (pauli_one_ne_zero Q hq).elim
    · refine ⟨R,?_⟩
      intro f
      change V.adjoint (U (Q.run f))=R.run (L f)
      rw [←hP,←hfactor,hR]
  refine ⟨V,cliffordOfForwardNormalizer E hunit hnormal,?_⟩
  apply LinearMap.ext
  intro f
  exact (hfactor f).symm

end
end Holant.Platonic.StabilizerErasure
