import Holant.Platonic.StabilizerErasure.DiagonalCodeSupport
import Holant.Platonic.StabilizerErasure.PauliPostselection

/-! Normalize the exact image of an arbitrary source-semantic stabilizer
isometry to a supported binary code using a constructed Clifford. The
dimension is derived from actual Hilbert isometry, not supplied as data. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

theorem semantic_image_codeSpace (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (hU : IsStabilizerIsometry U) :
    ∃C : AnalyticClifford n,∃D : BinaryCode n,LinearMap.range U=codeSpace C D := by
  obtain ⟨hiso,⟨t,P,hcomm,hcode⟩,hl⟩ := hU
  have hi := isometry_injective U hiso
  have hfix (j : Fin t) (f : Signature ℂ k) : (P j).run (U f)=U f :=
    (hcode _).mp ⟨f,rfl⟩ j
  obtain ⟨C,s,b,hC,hb⟩ := exists_commuting_pauli_alignment P hcomm
    (fun i => fixing_pauli_involution U hi (P i) (hfix i))
  have hmem (f : Signature ℂ n) : f∈LinearMap.range U ↔
      ∀i,sign (s i) • standardPauli 0 0 (b i) (C.operator f)=C.operator f := by
    rw [hcode]
    apply forall_congr'
    intro i
    constructor
    · intro hf
      have he := congrArg C.operator hf
      simpa only [hC] using he
    · intro hf
      apply C.operator.injective
      rw [hC,hf]
  have hn : C.operator (U (fun _ => 1))≠0 := by
    intro hz
    have hu : U (fun _ => 1)=0 := C.operator.injective (by simpa using hz)
    exact one_signature_ne_zero (hi (by simpa using hu))
  have hex : ∃w,C.operator (U (fun _ => 1)) w≠0 := by
    by_contra hh
    apply hn
    ext w
    simpa using not_exists.mp hh w
  obtain ⟨w₀,hw₀⟩ := hex
  have hx := (signedZ_fixed_iff_support s b _).mp ((hmem _).mp ⟨(fun _ => 1),rfl⟩) w₀ hw₀
  refine ⟨alignmentCompose (Program.translate (vectorWord w₀)).clifford C,diagonalCode b,?_⟩
  ext f
  rw [hmem,signedZ_fixed_iff_support,translated_diagonal_support s b (vectorWord w₀) hx]
  rfl

theorem semantic_code_dimension (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (hU : IsStabilizerIsometry U) (C : AnalyticClifford n) (D : BinaryCode n)
    (h : LinearMap.range U=codeSpace C D) : Module.finrank (ZMod 2) D=k := by
  have hi := isometry_injective U hU.1
  have hd := U.finrank_range_add_finrank_ker
  rw [LinearMap.ker_eq_bot.mpr hi] at hd
  have hr : Module.finrank ℂ (LinearMap.range U)=2^k := by
    simpa [Signature,Word] using hd
  rw [h,codeSpace_finrank] at hr
  exact Nat.pow_right_injective (by decide : 2≤2) hr

theorem semantic_exists_same_range_encoder (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (hU : IsStabilizerIsometry U) :
    ∃V : StabilizerIsometry k n,LinearMap.range V.map=LinearMap.range U := by
  obtain ⟨C,D,hD⟩ := semantic_image_codeSpace U hU
  have hd := semantic_code_dimension U hU C D hD
  subst k
  obtain ⟨V,hV⟩ := exists_code_encoder C D
  exact ⟨V,hV.trans hD.symm⟩

end
end Holant.Platonic.StabilizerErasure
