import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSupportGeometry
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentSquareClass
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPhaseOccurrences
import Holant.ReedMuller.AffinePatching.ReconstructionSupport

/-! An actual positive eight-copy support block for an ordinary row whose
pointwise square is Affine. The block uses only unchanged original coordinates;
no signed substitution, inverse coefficient, or compressed physical row is
introduced. Its common coefficient and affine support are internally obtained.
This does not classify the unsquared row as Affine or LocalAffine. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineSquareSupport
open Holant Holant.Tractable
open scoped BigOperators
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseBundle
  (evaluate evaluate_replicate)
end B
namespace O
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseOccurrences
  (occurrences occurrences_replicate rawPorts)
end O
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
variable {n m : ℕ} (f : Signature AlgebraicComplex n)
variable (hs : Affine (fun x=>f x^2)) (hn : f≠0)


def system : AffineSystem n := (exists_support_system f hs hn).choose

theorem system_exact (x : Fin n→Bool) : (system f hs hn).Holds x ↔ f x≠0 :=
  (exists_support_system f hs hn).choose_spec x


def base : Fin n→Bool := (exists_base f hn).choose

theorem base_nonzero : f (base f hn)≠0 := (exists_base f hn).choose_spec

def scale : AlgebraicComplex := f (base f hn)^8

theorem scale_nonzero : scale f hn≠0 := pow_ne_zero 8 (base_nonzero f hn)

include hs in
theorem eighth_equal (x y : Fin n→Bool) (hx : f x≠0) (hy : f y≠0) : f x^8=f y^8 := by
  have h := hs.fourth_power_eq x y (pow_ne_zero 2 hx) (pow_ne_zero 2 hy)
  simpa only [←pow_mul] using h

/-- Exact support indicator with a single original, nonzero coefficient. -/
theorem eighth_value (x : Fin n→Bool) :
    f x^8=if (system f hs hn).Holds x then scale f hn else 0 := by
  by_cases hx : f x=0
  · simp [system_exact,hx]
  · rw [ite_eq_left ((system_exact f hs hn x).mpr hx)]
    exact eighth_equal f hs x (base f hn) hx (base_nonzero f hn)

/-- Eight literal unchanged copies, rather than access to an inverse row. -/
def ports : List (Fin n→Bool ⊕ Fin n) := List.replicate 8 (fun i=>Sum.inr i)

theorem ports_value (x : Fin n→Bool) :
    B.evaluate f (ports (n:=n)) x=if (system f hs hn).Holds x then scale f hn else 0 := by
  rw [ports,B.evaluate_replicate]
  exact eighth_value f hs hn x

theorem free_count (j : Fin n) : O.occurrences (ports (n:=n)) j=8 := by
  rw [ports,O.occurrences_replicate]
  simp

theorem constant_count (b : Bool) : (O.rawPorts (ports (n:=n))).count (Sum.inl b)=0 := by
  simp only [ports,O.rawPorts,List.flatMap_replicate,List.count_flatten,List.map_replicate,List.sum_replicate]
  simp [Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseOccurrences.count_ofFn]

/-- Every emitted original free port has even incidence; no odd boundary
incidence is hidden in a compressed support coordinate. -/
theorem free_even (j : Fin n) : Even (O.occurrences (ports (n:=n)) j) := by
  rw [free_count]
  decide

/-- Arbitrary ordinary identifications and pinnings can be repeated eight
 times directly, with their real original-port counts retained. -/
theorem restriction_value (p : Fin n→Bool ⊕ Fin m) (z : Fin m→Bool) :
    B.evaluate f (List.replicate 8 p) z=
      if (system f hs hn).Holds (T.substitute p z) then scale f hn else 0 := by
  rw [B.evaluate_replicate]
  exact eighth_value f hs hn _

theorem restriction_even (p : Fin n→Bool ⊕ Fin m) (j : Fin m) :
    Even (O.occurrences (List.replicate 8 p) j) := by
  rw [O.occurrences_replicate]
  exact Even.mul_right (by decide : Even 8) _

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineSquareSupport
end
