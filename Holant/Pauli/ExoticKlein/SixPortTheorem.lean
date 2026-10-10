import Holant.Pauli.ExoticKlein.SixPortAnchorCoverage
import Holant.Pauli.ExoticKlein.SixPortOrbitCoverage
import Holant.Pauli.ExoticKlein.SixPortFactorization

/-! Lemma 8.5 and Theorem A.13. All actual pair contractions, all zero-card
patterns, and every arbitrary complex scale/cancellation locus are retained. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section

/-- Every direction triple is covered by a checked physical symmetry endpoint
and a checked denominator-cleared arbitrary-scale certificate. -/
theorem all_direction_triples_solved (state : DirectionTriple) : Solved state :=
  solved_of_all_representatives all_representatives_solved_via_anchors state

/-- A nonzero six-port tensor whose every exotic dual pair card is zero or
an actual two-edge matching product is an actual three-edge matching product. -/
theorem six_port_product (h : Signature ℂ 6) (hn : h ≠ 0) (hs : AllPhysicalSafe h) : IsProduct h :=
  six_port_product_of_solved all_direction_triples_solved h hn hs

/-- The product supplies a genuine proper partition of the six original ports. -/
theorem six_port_has_proper_tensor_factor (h : Signature ℂ 6) (hn : h ≠ 0)
    (hs : AllPhysicalSafe h) : HasProperTensorFactor h :=
  isProduct_hasProperTensorFactor h hn (six_port_product h hn hs)

/-- In particular there is no tensor-prime six-port survivor. -/
theorem no_tensor_prime_six_port (h : Signature ℂ 6) (hs : AllPhysicalSafe h) : ¬TensorPrime h := by
  rintro ⟨hn,hprime⟩
  exact hprime (six_port_has_proper_tensor_factor h hn hs)

end
end Holant.Pauli.ExoticKlein.SixPort
