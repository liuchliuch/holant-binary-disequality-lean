import Holant.Certificates.AffineEndpointCounts.TotalCounts
import Holant.Certificates.AffineEndpointCounts.InputCounts
import Holant.Certificates.AffineEndpointCounts.OrbitClasses
import Holant.Certificates.AffineEndpointCounts.SupportFour
import Holant.Certificates.AffineEndpointCounts.FullEvenSource
import Holant.Certificates.AffineEndpointCounts.OddSource
import Holant.Certificates.AffineEndpoint.Source

/-! Full Proposition A.2, authoritative paper1.tex lines15533–15688.
The five clauses use actual normalized signatures, literal source matrices,
complex diagonal orbits and physical native-X contractions. Finite checks
are tied to arbitrary-input coverage and coefficient semantics. -/
namespace Holant.Certificates.AffineEndpointCounts
open Holant Holant.Tractable Holant.EightVertex.ProductAnchor
open Holant.Certificates.AffineEndpoint Holant.Certificates.AffineReference
open Holant.Certificates.TwelveLoops Holant.Certificates.FourthRootOdd
open AffineEndpoint.SupportCatalog
noncomputable section

structure SourceA2InputCounts : Prop where
  normalized : normalizedAffineSet.ncard=36720
  supportDimensions :
    ((affineCatalog 4).filter (fun S => S.card=1)).card=16 ∧
    ((affineCatalog 4).filter (fun S => S.card=2)).card=120 ∧
    ((affineCatalog 4).filter (fun S => S.card=4)).card=140 ∧
    ((affineCatalog 4).filter (fun S => S.card=8)).card=30 ∧
    ((affineCatalog 4).filter (fun S => S.card=16)).card=1
  signatureDimensions :
    (normalizedDimensionSet 0).ncard=16 ∧ (normalizedDimensionSet 1).ncard=480 ∧
    (normalizedDimensionSet 2).ncard=4480 ∧ (normalizedDimensionSet 3).ncard=15360 ∧
    (normalizedDimensionSet 4).ncard=16384
  cores : {K : Matrix Bool Bool AlgebraicComplex | SourceCore K}.ncard=18
  inputPairs : allCoreInputPairs.ncard=660960
  retained : actualRetainedPairs.ncard=4200
  perCore : ∀k : Fin 18,(retainedInputs (numberedCore k)).ncard=coreRetainedCount k
  coreHistogram : (coresRetaining 612).ncard=6 ∧ (coresRetaining 44).ncard=12

structure SourceA2Diagonal : Prop where
  normalForm : ∀f : Signature AlgebraicComplex 4,Affine f → f≠0 → CanonicalNormalized f →
    ∀K : Matrix Bool Bool AlgebraicComplex,SourceCore K →
    EndpointEven (Signature.coordinateAction (fun _ => K) f) →
    EndpointNormalForm (Signature.coordinateAction (fun _ => K) f)
  referenceCount : normalizedReferenceSet.ncard=612
  supportHistogram : (referenceSizeSet 2).ncard=4 ∧ (referenceSizeSet 4).ncard=96 ∧ (referenceSizeSet 8).ncard=512
  orbitHistogram : (referenceOrbits 2).ncard=1 ∧ (referenceOrbits 4).ncard=24 ∧ (referenceOrbits 8).ncard=256
  invariantComplete : ∀g h : Signature AlgebraicComplex 4,EndpointEven g → EndpointEven h →
    (diagonalInvariant g=diagonalInvariant h ↔ DiagonalOrbit g h)

structure SourceA2FullEven : Prop where
  firstWitness : ∀h : Signature AlgebraicComplex 4,Affine h →
    (∀x,h x≠0 ↔ evenWord x=true) → h (fun _ => false)=1 →
    ∃p : EvenParameters,h=evenAlg p ∧ ActualEvenWitness p (evenWitness p)
  partition : fullEvenReferences.ncard=512 ∧
    (evenRouteReferences 0).card=16 ∧ (evenRouteReferences 1).card=336 ∧
    (evenRouteReferences 2).card=96 ∧ (evenRouteReferences 3).card=48 ∧ (evenRouteReferences 4).card=16
  disjoint : ∀r s : Fin 5,r≠s → Disjoint (evenRouteReferences r) (evenRouteReferences s)
  exhaustive : ∀f : Signature AlgebraicComplex 4,f∈fullEvenReferences ↔ ∃r : Fin 5,f∈evenRouteReferences r
  phases : (evenPhaseReferences 0).card=56 ∧ (evenPhaseReferences 2).card=56 ∧
    (evenPhaseReferences 1).card=24 ∧ (evenPhaseReferences 3).card=24

structure SourceA2Odd : Prop where
  counts : Fintype.card State=16384 ∧ routeCount .rankOne=15792 ∧
    routeCount .infiniteOrder=224 ∧ routeCount .remaining=368 ∧
    ((Finset.univ : Finset State).filter Exceptional).card=64 ∧
    oddRemainingStates.card=304 ∧
    (oddRemainingStates.filter (fun s => oddValidShifts s={0,2})).card=176 ∧
    (oddRemainingStates.filter (fun s => oddValidShifts s={1,3})).card=128 ∧
    oddFamilyStates.card=512 ∧ oddNativeRankStates.card=336 ∧ oddDenseResidueStates.card=176
  actualTables : oddNormalizedTables.card=16384 ∧ oddAffineFamilyTables.card=512 ∧
    oddNativeRankTables.card=336 ∧ oddDenseResidueTables.card=176
  normalizedClassification : ∀f : Signature ℂ 4,NormalizedOdd f →
    ∃s : State,f=complexOdd s ∧
      (classify s=.rankOne → RankOneExit f) ∧
      (classify s=.infiniteOrder → InfiniteExit f) ∧
      (classify s=.remaining →
        (Exceptional s ∧ SupportSixExit f) ∨
        (s∈oddRemainingStates ∧ (oddValidShifts s).card=2 ∧
          (oddValidShifts s={0,2} ∨ oddValidShifts s={1,3}) ∧
          ∀δ,δ∈oddValidShifts s ↔ Affine (shiftedOdd s δ)))
  exceptional : ∀s,Exceptional s → classify s=.remaining ∧ SupportSixExit (complexOdd s)
  shifts : ∀s : State,s∈oddRemainingStates →
    (oddValidShifts s).card=2 ∧ (oddValidShifts s={0,2} ∨ oddValidShifts s={1,3}) ∧
    (∀δ,δ∈oddValidShifts s ↔ Affine (shiftedOdd s δ)) ∧
    (∀δ,δ∈oddValidShifts s →
      (∃p : FamilyParameters,shiftedOdd s δ=shiftedOdd (familyState p) 0) ∧
      NativeRankOrDense (phaseShift (complexOdd s) δ))
  rankOutputs : ∀f : Signature ℂ 4,f∈oddNativeRankTables →
    ∃e : Fin 6,Matrix.rank (fun x y : Bool => nativeContract f e ![x,y])=1 ∧
      Gadget.Realizes ({⟨4,f⟩} : SignatureFamily ℂ) .disequality (nativeContract f e)
  denseOutputs : ∀f : Signature ℂ 4,f∈oddDenseResidueTables →
    (¬∃e : Fin 6,Matrix.rank (fun x y : Bool => nativeContract f e ![x,y])=1) ∧
    ∃e : Fin 3,DenseProduct (twoCopyNative f (initialPair e)) ∧
      Gadget.Realizes ({⟨4,f⟩} : SignatureFamily ℂ) .disequality (twoCopyNative f (initialPair e))

structure SourceA2Certificate : Prop where
  inputs : SourceA2InputCounts
  diagonal : SourceA2Diagonal
  supportFour : SourceA2SupportFour
  fullEven : SourceA2FullEven
  odd : SourceA2Odd

theorem source_A2_inputs : SourceA2InputCounts :=
  ⟨normalized_affine_count,affine_support_dimension_counts,actual_normalized_dimension_counts,
    source_core_count,all_core_input_pair_count,actual_retained_pair_count,all_core_retained_counts,core_retention_histogram⟩

theorem source_A2_diagonal : SourceA2Diagonal := by
  refine ⟨?_,normalized_reference_count,normalized_reference_histogram,reference_orbit_histogram,
    diagonalInvariant_complete⟩
  intro f hf hn _ K hK hg
  exact source_A4_normal_form f hf hn K hK hg.2.2 (mul_ne_zero hg.1 hg.2.1)

theorem source_A2_full_even : SourceA2FullEven :=
  ⟨full_even_reference_first,full_even_actual_partition,evenRouteReferences_disjoint,
    evenRouteReferences_coverage,full_even_actual_phase_histogram⟩

theorem source_A2_odd : SourceA2Odd :=
  ⟨source_A2v_odd_counts,odd_actual_table_counts,source_A2v_normalized_odd,
    odd_exceptional_count_and_exit.2,odd_remaining_shift_semantics,
    odd_native_rank_table_actual,odd_dense_residue_table_actual⟩

/-- Every printed clause of Proposition A.2, with no candidate coverage or
retention certificate supplied by its caller. -/
theorem source_A2 : SourceA2Certificate :=
  ⟨source_A2_inputs,source_A2_diagonal,source_A2_support_four,source_A2_full_even,source_A2_odd⟩

end
end Holant.Certificates.AffineEndpointCounts
