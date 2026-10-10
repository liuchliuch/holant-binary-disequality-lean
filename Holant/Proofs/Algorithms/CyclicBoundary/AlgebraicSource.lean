import Holant.Proofs.Algorithms.CyclicBoundary.NonsquareExit
import Holant.Proofs.Algorithms.CyclicBoundary.AlgebraicRepresentatives
import Holant.Proofs.Algorithms.PrimalityInterfaces


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.AlgebraicSource
open Holant.Tractable Holant.Projective.CyclicQuaternary
open Holant.Projective.CyclicPhasePencil
open RingHomRealization AlgebraicRepresentatives
noncomputable section

def ambient (q : Signature AlgebraicComplex 4) : Signature ℂ 4 :=
  mapSignature inclusion q

theorem walsh_embed (q : Signature AlgebraicComplex 4) :
    ZeroDeckBoundary.walsh (ambient q) = mapSignature inclusion (Physical.walsh q) := by
  have hp (a b : Bool) : inclusion (Physical.Pinv a b) = CoordinateFactors.inverseHadamard a b := by
    cases a <;> cases b <;>
      norm_num [Physical.Pinv,Physical.P,CoordinateFactors.inverseHadamard,ZeroEndpointDressing.hadamard] <;>
      change (2 : ℂ)⁻¹ = 1 / 2 <;> norm_num
  funext x
  simp only [ZeroDeckBoundary.walsh,Physical.walsh,ambient,mapSignature,
    Signature.coordinateAction,map_sum,map_mul,map_prod,hp]

theorem transfer_embed (q : Signature AlgebraicComplex 4)
    (i : Fin 3) (side order : Bool) (s : AlgebraicComplex) (u v : Bool) :
    inclusion (transferCard q i side order s u v) =
      transferCard (mapSignature inclusion q) i side order (inclusion s) u v := by
  cases order <;> cases u <;> cases v <;>
    simp [transferCard,orderedContraction,contraction,Kernel.mul,Kernel.transpose,
      diagonal,Z,mapSignature,inclusion]

theorem phase_embed {N : ℕ} (T : Kernel AlgebraicComplex) (h : IsPhase N T) :
    IsPhase N (fun u v => inclusion (T u v)) := by
  obtain ⟨s,c,hs,hc,he⟩ := h
  refine ⟨inclusion s,inclusion c,?_,?_,?_⟩
  · simpa using congrArg inclusion hs
  · intro hz
    exact hc (inclusion.injective (hz.trans inclusion.map_zero.symm))
  · funext u v
    have h := congrFun (congrFun he u) v
    rw [h]
    cases u <;> cases v <;> simp [phase,diagonal]

theorem deck_embed {N : ℕ} (hN : 0 < N) (q : Signature AlgebraicComplex 4)
    (h : AllPhaseCards N q) : AllPhaseCards N (mapSignature inclusion q) := by
  intro i side order s hs
  let t := liftRoot hN ⟨s,hs⟩
  have ht : inclusion t.val=s := rfl
  have he : (fun u v => inclusion (transferCard q i side order t.val u v)) =
      transferCard (mapSignature inclusion q) i side order s := by
    funext u v
    rw [transfer_embed,ht]
  rcases h i side order t.val t.property with hz | hp
  · left
    rw [←he,hz]
    funext u v
    exact inclusion.map_zero
  · right
    rw [←he]
    exact phase_embed _ hp

theorem physical_deck_embed {N : ℕ} (hN : 0 < N)
    {F : SignatureFamily AlgebraicComplex} (R : Physical.Representatives F N)
    (q : Signature AlgebraicComplex 4) (hd : Physical.PhysicalCards R q) :
    AllPhaseCards N (ZeroDeckBoundary.walsh (ambient q)) := by
  rw [walsh_embed]
  exact deck_embed hN _ ((Physical.physicalCards_iff R q).mp hd)

/-- The ambient prime condition comes from exact factor descent through
the source embedding. Literal membership supplies the actual original q. -/
theorem source_order_at_least_four {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (R : Physical.Representatives F N) (hN : 3 ≤ N) (hNeven : Even N)
    (q : Signature AlgebraicComplex 4) (hq : (⟨4,q⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hp : Holant.LocalDrafts.FinitePGL2.Stabilization.Prime ⟨4,q⟩)
    (hd : Physical.PhysicalCards R q) :
    SourceDispatch.EndpointOutput (mapFamily inclusion F) ∨
      Nonempty (ActualCards.OutsideCard (mapFamily inclusion F) N) ∨
      Nonempty (NonsquareExit.DoubledOutside (mapFamily inclusion F) N) := by
  have hpos : 0 < N := by omega
  have hpr := PrimalityInterfaces.embedded_prime inclusion q hp
  have hr := realizes_map inclusion (Gadget.realizes_of_mem F .disequality q hq)
  have hr' : Gadget.RealizesUpTo (mapFamily inclusion F) .disequality (ambient q) := by
    refine ⟨1,one_ne_zero,?_⟩
    convert hr using 1
    funext x
    exact one_mul _
  exact NonsquareExit.cyclic_boundary_dispatch (ofSource hpos R) hN hNeven
    (ambient q) hr' hpr.1 hpr.2 (physical_deck_embed hpos R q hd)

/-- The N=2 row retains its exact weaker mixed-sign outcome. Source
primality is converted to the historical counted-certificate definition. -/
theorem source_order_two {F : SignatureFamily AlgebraicComplex}
    (R : Physical.Representatives F 2) (q : Signature AlgebraicComplex 4)
    (hq : (⟨4,q⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hI : (⟨2,Holant.Tractable.kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hp : Holant.LocalDrafts.FinitePGL2.Stabilization.Prime ⟨4,q⟩)
    (hd : Physical.PhysicalCards R q) :
    ∃ M : Network AlgebraicComplex 4,
      Holant.Certificates.EqualityQuaternary.Counted.Allowed q M ∧
      Holant.Certificates.EqualityQuaternary.Counted.copies M≤2 ∧
      Holant.EightVertex.ProductAnchor.EndpointEven M.denote ∧
      ¬Holant.Certificates.EqualityQuaternary.GroupMatching
        Holant.Certificates.EqualityQuaternary.C2.group M.denote ∧
      Gadget.Realizes F .disequality M.denote :=
  C2Bridge.source_order_two F q hq hI
    ((PrimalityInterfaces.retained_equality_prime q).mp hp)
    ((Physical.physicalCards_iff R q).mp hd)

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.AlgebraicSource
