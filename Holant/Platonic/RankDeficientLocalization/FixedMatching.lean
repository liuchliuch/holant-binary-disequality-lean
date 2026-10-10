import Holant.Platonic.RankDeficientLocalization.MatchingCoordinates
import Holant.Platonic.RankDeficientLocalization.DomainSemantics
import Holant.Platonic.RainbowLocalization.PhysicalCards

/-! Complete proper-factor branch from the original common-matching cards.
Coefficient transport is precomposition of a linear map and is undone before
literal original-port reconstruction; it is never declared a gadget. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Platonic.RankDeficientLocalization
open Holant
open Holant.Pauli.ExoticKlein (Matching)
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.MatchingProductBridge (PlatonicModel tetrahedralBase groupDirection modelBase)
open Holant.Certificates.PlatonicIncidence Holant.Certificates.RainbowOrbit
open Holant.Platonic.RainbowLocalization
open scoped BigOperators
variable {P : Type*} [Fintype P] [DecidableEq P] {n : ℕ}

def matchingOriginalOrder (M : Presentation ℂ P) (p : Bool⊕P≃Fin n) :
    (Bool ⊕ ((j : Fin M.edges) × Fin 2)) ≃ Fin n :=
  (Equiv.sumCongr (Equiv.refl Bool) (matchingBlockPorts M)).trans p

theorem matching_insert (M : Presentation ℂ P) (p : Bool⊕P≃Fin n)
    (a b : Bool) (x : Fin M.edges→Fin 2→Bool) :
    FixedMatchingRuling.Physical.insert (fun _ : Fin M.edges => 2) (matchingOriginalOrder M p) a b x =
      Physical.pairAssignment p a b (matchingBlockAssignment M x) := by
  funext q
  obtain ⟨z,rfl⟩ := p.surjective q
  cases z with
  | inl t => cases t <;> simp [FixedMatchingRuling.Physical.insert,matchingOriginalOrder,Physical.pairAssignment]
  | inr q => simp [FixedMatchingRuling.Physical.insert,matchingOriginalOrder,Physical.pairAssignment,matchingBlockAssignment]

theorem matching_block_card_coordinates (M : Presentation ℂ P) (p : Bool⊕P≃Fin n)
    (f : Signature ℂ n) (K : Kernel ℂ) (x : Fin M.edges→Fin 2→Bool) :
    FixedMatchingRuling.Physical.blockCoordinates (fun _ : Fin M.edges => 2)
      (FixedMatchingRuling.Physical.cardMap (fun _ : Fin M.edges => 2) (matchingOriginalOrder M p) f K) x =
        Physical.cardMap p f K (matchingBlockAssignment M x) := by
  rw [FixedMatchingRuling.Physical.blockCoordinates_cardMap]
  simp only [FixedMatchingRuling.Physical.cardCoefficients,Physical.cardMap,LinearMap.coe_mk,AddHom.coe_mk,matching_insert]

theorem matching_block_card_pure (M : Presentation ℂ P) (hM : 0<M.edges)
    (p : Bool⊕P≃Fin n) (f : Signature ℂ n) (K : Kernel ℂ)
    (hcard : Physical.cardMap p f K=0 ∨ Nonempty (NonsingularCard (Physical.cardMap p f K)))
    (hsame : ∀C : NonsingularCard (Physical.cardMap p f K),
      C.matching=(presentationMatching M).mate) :
    FixedMatchingRuling.Segre.TensorPureOrZero
      (FixedMatchingRuling.Physical.cardMap (fun _ : Fin M.edges => 2) (matchingOriginalOrder M p) f K) := by
  apply (FixedMatchingRuling.Segre.tensorPureOrZero_coordinates (fun _ : Fin M.edges => Pi.basisFun ℂ (Fin 2→Bool)) _).mpr
  change FixedMatchingRuling.Segre.IsPureOrZero (FixedMatchingRuling.Physical.blockCoordinates (fun _ : Fin M.edges => 2) _)
  have he : FixedMatchingRuling.Physical.blockCoordinates (fun _ : Fin M.edges => 2)
      (FixedMatchingRuling.Physical.cardMap (fun _ : Fin M.edges => 2) (matchingOriginalOrder M p) f K) =
      fun x => Physical.cardMap p f K (matchingBlockAssignment M x) :=
    funext (matching_block_card_coordinates M p f K)
  rw [he]
  rcases hcard with hz | hC
  · exact Or.inl (by rw [hz]; rfl)
  · obtain ⟨C⟩ := hC
    rw [C.value]
    exact sameMatching_pure M C.presentation hM (hsame C).symm

def CommonMatching (Φ : Mat→ₗ[ℂ]Tensor ℂ P) (g : PlatonicModel) (e : Mat≃ₗ[ℂ]Mat) : Prop :=
  ∃m : Equiv.Perm P,∀i,∀C : NonsingularCard (Φ (e (representative g i))),C.matching=m

/-- Actual tetrahedral tests are contained projectively in every standard
Platonic configuration, using its exact completeness theorem. -/
theorem tetrahedral_test_representative (g : PlatonicModel) (K : Mat)
    (hK : tetrahedralBase K) : ∃i : Fin (size g),∃c : ℂ,c≠0 ∧ K=c • representative g i := by
  apply (complete g K).mp
  refine ⟨1,one_ne_zero,K,?_,by simp⟩
  cases g
  · exact hK
  · exact Or.inl hK
  · exact Or.inl hK

/-- The full source proper-factor branch. Both deleted original ports remain
in the varying factor; the nonempty fixed complement is a genuine tensor factor. -/
theorem common_matching_proper_factor (g : PlatonicModel) (e : Mat≃ₗ[ℂ]Mat)
    (p : Bool⊕P≃Fin n) (f : Signature ℂ n) (hf : f≠0) (hn : 6≤n)
    (hr : 2≤Module.finrank ℂ (Physical.cardMap p f).range)
    (hcards : ∀i,Physical.cardMap p f (e (representative g i))=0 ∨
      Nonempty (NonsingularCard (Physical.cardMap p f (e (representative g i)))))
    (hcommon : CommonMatching (Physical.cardMap p f) g e) :
    Holant.Pauli.ExoticKlein.Fiber.HasProperTensorFactor f := by
  classical
  obtain ⟨m,hm⟩ := hcommon
  have hc := transformed_kernel_deleted_connected g e (Physical.cardMap p f).ker
    (kernel_dimension_le_two _ hr)
  obtain ⟨i⟩ := hc.nonempty
  have hi : Physical.cardMap p f (e (representative g i.val))≠0 := by
    intro hz
    apply i.property
    exact hz
  obtain ⟨C⟩ := (hcards i.val).resolve_left hi
  let M := C.presentation
  have hMmate : (presentationMatching M).mate=m := hm i.val C
  have hM2 : 2≤M.edges := by
    have hmc := (presentationMatching M).port_card
    have hpc := Fintype.card_congr p
    simp only [Fintype.card_sum,Fintype.card_bool,Fintype.card_fin] at hpc
    omega
  letI : Nonempty (Fin M.edges) := ⟨⟨0,by omega⟩⟩
  let ℓ := fun _ : Fin M.edges => 2
  let p' := matchingOriginalOrder M p
  let Ψ := FixedMatchingRuling.Physical.cardMap ℓ p' f
  have hΨ : Ψ≠0 := fun hz => hf ((FixedMatchingRuling.Physical.cardMap_eq_zero_iff ℓ p' f).mp hz)
  let Ψe := Ψ.comp e.toLinearMap
  have hΨe : Ψe≠0 := by
    intro hz
    apply hΨ
    apply LinearMap.ext
    intro K
    obtain ⟨J,rfl⟩ := e.surjective K
    exact congrArg (fun T => T J) hz
  have htest : ∀K,tetrahedralBase K→FixedMatchingRuling.Segre.TensorPureOrZero (Ψe K) := by
    intro K hK
    obtain ⟨j,c,hc,hjc⟩ := tetrahedral_test_representative g K hK
    have hj : FixedMatchingRuling.Segre.TensorPureOrZero (Ψ (e (representative g j))) := by
      apply matching_block_card_pure M (by omega) p f _ (hcards j)
      intro E
      exact (hm j E).trans hMmate.symm
    change FixedMatchingRuling.Segre.TensorPureOrZero (Ψ (e K))
    rw [hjc,map_smul,map_smul]
    exact FixedMatchingRuling.tensorPureOrZero_smul c hj
  obtain ⟨j,U,ψ,hU,hruling⟩ := FixedMatchingRuling.tetrahedral_fixed_matching_ruling Ψe hΨe htest
  apply FixedMatchingRuling.Physical.proper_factor_of_ruling ℓ (fun _ => by decide) p' f hΨ
    (by simpa only [Fintype.card_fin] using hM2) j U (ψ.comp e.symm.toLinearMap)
  intro K
  have h := hruling (e.symm K)
  change Ψ (e (e.symm K)) = PiTensorProduct.tprod ℂ (Function.update U j (ψ (e.symm K))) at h
  rw [e.apply_symm_apply] at h
  exact h

end Holant.Platonic.RankDeficientLocalization
