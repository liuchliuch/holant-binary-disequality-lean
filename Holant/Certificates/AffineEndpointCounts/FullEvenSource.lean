import Holant.Certificates.AffineEndpointCounts.FullEvenPriority
import Holant.Certificates.AffineEndpointCounts.FullEvenSemantics

/-! Source A.2(iv), including first-witness priority, actual signature counts,
physical crossed wiring, and the extracted fourth-root histogram. -/
namespace Holant.Certificates.AffineEndpointCounts
open Holant Holant.Tractable Holant.Certificates.TwelveLoops
open Holant.Certificates.FourthRootOdd Holant.Certificates.AffineReference
open Holant.EightVertex.ProductAnchor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 200000

def ActualEvenWitness (p : EvenParameters) : EvenWitness → Prop
  | .dense _ _ => DenseForm (evenAlg p)
  | .rankOne e => ¬DenseForm (evenAlg p) ∧ (complexLoopMatrix p e).rank=1 ∧
      Gadget.Realizes ({⟨4,evenAlg p⟩} : SignatureFamily AlgebraicComplex) .disequality
        (nativeContract (evenAlg p) e)
  | .product e b r => ¬DenseForm (evenAlg p) ∧
      (∀ j : Fin 6,(complexLoopMatrix p j).rank≠1) ∧
      (∀ j : Fin 3,j<e → ¬ActualSupportFourProduct (crossedCopies (evenAlg p) j)) ∧
      ActualSupportFourProduct (crossedCopies (evenAlg p) e) ∧
      ∃ c : AlgebraicComplex,c≠0 ∧ (algEmbed (fourthRoot r))^4=1 ∧
        crossedCopies (evenAlg p) e=equalCopiesTensor c (algEmbed (fourthRoot r)) b ∧
        Gadget.Realizes ({⟨4,evenAlg p⟩} : SignatureFamily AlgebraicComplex) .disequality
          (crossedCopies (evenAlg p) e)

theorem full_even_first_actual (p : EvenParameters) : ActualEvenWitness p (evenWitness p) := by
  have hv := evenWitness_valid p
  have hf := evenWitness_first p
  cases hw : evenWitness p with
  | dense u m =>
    rw [hw] at hv
    exact even_dense_exit p u m hv
  | rankOne e =>
    rw [hw] at hv hf
    exact ⟨fun h => hf ((hasEvenDense_iff p).mpr h),even_rank_one_exit p e hv⟩
  | product e b r =>
    rw [hw] at hv hf
    refine ⟨fun h => hf.1 ((hasEvenDense_iff p).mpr h),?_,?_,
      even_product_actual p e b r hv,algEmbed (crossedTable p e (fun _ => false)),
      (not_congr (algEmbed_zero_iff _)).mpr hv.1,?_,?_,crossedCopies_realizes _ _⟩
    · intro j hj
      exact hf.2.1 ((hasEvenRankOne_iff p).mpr ⟨j,hj⟩)
    · intro j hj hh
      exact hf.2.2 j hj ((rawCrossed_iff p j).mpr hh)
    · rw [algEmbed_fourthRoot]
      exact fourthRootPhase_pow_four _
    · funext x
      rw [←algEmbed_crossedTable,hv.2 x,algEmbed_equalProduct]

theorem full_even_reference_first (h : Signature AlgebraicComplex 4) (ha : Affine h)
    (hs : ∀ x,h x≠0 ↔ evenWord x=true) (h0 : h (fun _ => false)=1) :
    ∃ p : EvenParameters,h=evenAlg p ∧ ActualEvenWitness p (evenWitness p) := by
  obtain ⟨p,hp⟩ := full_even_coverage h ha hs h0
  exact ⟨p,hp,full_even_first_actual p⟩

/-- Finite sets consist of actual normalized algebraic signatures. -/
def evenRouteReferences (r : Fin 5) : Finset (Signature AlgebraicComplex 4) := by
  classical
  exact ((Finset.univ : Finset EvenParameters).filter (fun p => evenRoute p=r)).image evenAlg

def evenPhaseReferences (r : Fin 4) : Finset (Signature AlgebraicComplex 4) := by
  classical
  exact ((Finset.univ : Finset EvenParameters).filter (fun p => evenWitnessPhase p=some r)).image evenAlg

theorem evenRouteReferences_card (r : Fin 5) : (evenRouteReferences r).card=evenRouteCount r := by
  classical
  exact Finset.card_image_of_injective _ evenAlg_injective

theorem evenPhaseReferences_card (r : Fin 4) : (evenPhaseReferences r).card=evenPhaseCount r := by
  classical
  exact Finset.card_image_of_injective _ evenAlg_injective

theorem evenRouteReferences_disjoint (r s : Fin 5) (h : r≠s) :
    Disjoint (evenRouteReferences r) (evenRouteReferences s) := by
  classical
  apply Finset.disjoint_left.mpr
  intro f hf hg
  obtain ⟨p,hp,hpf⟩ := Finset.mem_image.mp hf
  obtain ⟨q,hq,hqf⟩ := Finset.mem_image.mp hg
  have hpq : p=q := evenAlg_injective (hpf.trans hqf.symm)
  subst q
  exact h ((Finset.mem_filter.mp hp).2.symm.trans (Finset.mem_filter.mp hq).2)

theorem evenRouteReferences_coverage (f : Signature AlgebraicComplex 4) :
    f∈fullEvenReferences ↔ ∃ r : Fin 5,f∈evenRouteReferences r := by
  classical
  rw [fullEvenReferences_eq_range]
  constructor
  · rintro ⟨p,rfl⟩
    refine ⟨evenRoute p,Finset.mem_image.mpr ⟨p,?_,rfl⟩⟩
    simp
  · rintro ⟨r,h⟩
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp h
    exact ⟨p,hp⟩

/-- The printed disjoint first-witness count, over actual Affine references. -/
theorem full_even_actual_partition : fullEvenReferences.ncard=512 ∧
    (evenRouteReferences 0).card=16 ∧ (evenRouteReferences 1).card=336 ∧
    (evenRouteReferences 2).card=96 ∧ (evenRouteReferences 3).card=48 ∧
    (evenRouteReferences 4).card=16 := by
  simpa only [evenRouteReferences_card] using
    And.intro full_even_actual_count full_even_first_histogram

/-- In the paper's order 1,-1,i,-i, counting actual first outputs. -/
theorem full_even_actual_phase_histogram :
    (evenPhaseReferences 0).card=56 ∧ (evenPhaseReferences 2).card=56 ∧
    (evenPhaseReferences 1).card=24 ∧ (evenPhaseReferences 3).card=24 := by
  simpa only [evenPhaseReferences_card] using full_even_ratio_histogram

end
end Holant.Certificates.AffineEndpointCounts
