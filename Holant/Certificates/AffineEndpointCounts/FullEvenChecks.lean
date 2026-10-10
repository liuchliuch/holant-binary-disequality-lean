import Holant.Certificates.AffineReference.FullEvenCertificate
import Holant.Certificates.AffineReference.Plane

/-! Literal first-priority tests for source A.2(iv). The last test uses the
whole actual output support and its determinant, not a proposed witness tag. -/
namespace Holant.Certificates.AffineEndpointCounts
open Holant Holant.Certificates.TwelveLoops Holant.Certificates.FourthRootOdd
open Holant.Certificates.AffineReference

def HasEvenDense (p : EvenParameters) : Prop :=
  ∃ u : Fin 4, ∃ m : Fin 16, ValidEvenWitness p (.dense u m)
instance (p : EvenParameters) : Decidable (HasEvenDense p) :=
  inferInstanceAs (Decidable (∃ u : Fin 4, ∃ m : Fin 16, ValidEvenWitness p (.dense u m)))

def HasEvenRankOne (p : EvenParameters) : Prop :=
  ∃ e : Fin 6, rankOneTest (evenLoopPair p e)=true
instance (p : EvenParameters) : Decidable (HasEvenRankOne p) :=
  inferInstanceAs (Decidable (∃ e : Fin 6, rankOneTest (evenLoopPair p e)=true))

def RawSupportFourProduct (q : Signature Gaussian 4) : Prop :=
  ∃ b : Fin 3, (∀ x, q x≠(0,0) ↔ OnPlane b x) ∧
    gmul (q (fun _ => false)) (q (fun _ => true))=
      gmul (q (planeChart b ![false,true])) (q (planeChart b ![true,false]))
instance (q : Signature Gaussian 4) : Decidable (RawSupportFourProduct q) :=
  inferInstanceAs (Decidable (∃ b : Fin 3, (∀ x, q x≠(0,0) ↔ OnPlane b x) ∧ _))

/-- All earlier routes fail; for the crossed route every smaller physical
edge choice fails the full support-four product test. -/
def FirstEvenWitness (p : EvenParameters) : EvenWitness → Prop
  | .dense _ _ => True
  | .rankOne _ => ¬HasEvenDense p
  | .product e _ _ => ¬HasEvenDense p ∧ ¬HasEvenRankOne p ∧
      ∀ j : Fin 3, j<e → ¬RawSupportFourProduct (crossedTable p j)
instance (p : EvenParameters) (w : EvenWitness) : Decidable (FirstEvenWitness p w) := by
  cases w <;> unfold FirstEvenWitness <;> infer_instance

/-- Five disjoint routes in the paper's order; physical edge 0 is j=1. -/
def evenRoute (p : EvenParameters) : Fin 5 :=
  match evenWitness p with
  | .dense _ _ => 0
  | .rankOne _ => 1
  | .product e _ _ => ⟨e.val+2,by omega⟩

def evenRouteCount (r : Fin 5) : ℕ :=
  ((Finset.univ : Finset EvenParameters).filter (fun p => evenRoute p=r)).card

def evenWitnessPhase (p : EvenParameters) : Option (Fin 4) :=
  match evenWitness p with | .product _ _ u => some u | _ => none

def evenPhaseCount (r : Fin 4) : ℕ :=
  ((Finset.univ : Finset EvenParameters).filter (fun p => evenWitnessPhase p=some r)).card

set_option maxRecDepth 200000 in
set_option maxHeartbeats 10000000 in
theorem full_even_first_histogram :
    evenRouteCount 0=16 ∧ evenRouteCount 1=336 ∧ evenRouteCount 2=96 ∧
    evenRouteCount 3=48 ∧ evenRouteCount 4=16 := by decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 10000000 in
theorem full_even_ratio_histogram :
    evenPhaseCount 0=56 ∧ evenPhaseCount 2=56 ∧
    evenPhaseCount 1=24 ∧ evenPhaseCount 3=24 := by decide +kernel

end Holant.Certificates.AffineEndpointCounts
