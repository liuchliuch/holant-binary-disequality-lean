import Holant.Proofs.Algorithms.CyclicBoundary.ZeroEndpointRealization
import Holant.Proofs.Algorithms.CyclicBoundary.CoordinateFactors


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.ZeroEndpointSource
open Holant.Pauli.ExoticKlein.Fiber Holant.Projective.CyclicQuaternary
open ZeroEndpointFactor ZeroEndpointJoin ZeroEndpointDressing
open PhysicalAttachments ZeroEndpointRealization CoordinateFactors
noncomputable section

/-- Every parameter in this statement describes original input data: a
concrete zero-endpoint Walsh table, genuine physical nonvanishing/primality,
and actual retained binaries. No output, classification or hardness leaf is
assumed. The output has its exact full even table, not just two endpoints. -/
theorem zero_endpoint_physical {F : SignatureFamily ℂ} {N : ℕ}
    (R : Representatives F N) (hNpos : 0 < N) (hNeven : Even N)
    (q : Signature ℂ 4) (hq : Gadget.RealizesUpTo F .disequality q)
    (hn : q ≠ 0) (hp : ¬HasProperTensorFactor q)
    (r a : Fin 3 → ℂ) (ha : ∀ k, (a k)^N=1)
    (hcoordinates : q = physical (table r a)) :
    ∃ i : Fin 3,
      delta r a i ≠ 0 ∧
      Gadget.RealizesUpTo F .disequality
        (physical (dress (join r a i).denote (phases a i))) ∧
      physical (dress (join r a i).denote (phases a i)) =
        ofCoordinates (2*(endpoint₀ r a i + commonMiddle r a i))
          (2*(endpoint₀ r a i + commonMiddle r a i))
          ![(2*(endpoint₀ r a i-commonMiddle r a i),2*(endpoint₀ r a i-commonMiddle r a i)),
            (2*(endpoint₀ r a i+commonMiddle r a i),2*(endpoint₀ r a i+commonMiddle r a i)),
            (2*(endpoint₀ r a i-commonMiddle r a i),2*(endpoint₀ r a i-commonMiddle r a i))] ∧
      physical (dress (join r a i).denote (phases a i)) (fun _ => false) ≠ 0 ∧
      physical (dress (join r a i).denote (phases a i)) (fun _ => true) ≠ 0 ∧
      ¬HasProperTensorFactor (physical (dress (join r a i).denote (phases a i))) := by
  have ha0 : ∀ k, a k ≠ 0 := by
    intro k hk
    have h := ha k
    simp [hk,ne_of_gt hNpos] at h
  rw [hcoordinates] at hq hn hp
  have hn' : table r a ≠ 0 := fun h => hn ((physical_zero_iff _).2 h)
  have hp' : ¬HasProperTensorFactor (table r a) :=
    fun h => hp ((physical_factor_iff _).2 h)
  obtain ⟨i,hi⟩ := ZeroEndpointAlternative.nonzero_delta r a ha0 hn' hp'
  refine ⟨i,hi,dressed_zero_join_upTo R r a ha hNeven hq i,?_,
    (endpoints_nondegenerate r a ha0 i hi).1,
    (endpoints_nondegenerate r a ha0 i hi).2,
    SupportPrime.dressed_join_prime r a ha0 i hi⟩
  rw [dress_join r a i (ha0 i),physical_matched]

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.ZeroEndpointSource
