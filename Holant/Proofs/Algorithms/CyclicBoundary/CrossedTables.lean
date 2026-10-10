import Holant.Proofs.Algorithms.CyclicBoundary.CrossedTemplates
import Holant.Proofs.Algorithms.CyclicBoundary.SquareDressing
import Holant.Proofs.Algorithms.CyclicBoundary.FourthRootRigidity


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.CrossedTables
open Holant.Projective.CyclicQuaternary Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
open TwoCopyKernels ZeroEndpointDressing ZeroEndpointJoin SquareDressing CrossedTemplates
noncomputable section
set_option maxHeartbeats 800000

def complementPair : Fin 3 → Fin 6 := ![5,4,3]

def crossedTable (lam : ℂ) (a : Fin 3 → ℂ) (i : Fin 3) : Signature ℂ 4 :=
  ofCoordinates (1+(a i)^2) (lam^2*(1+((a i)⁻¹)^2))
    ![(-lam*(a i+(a i)⁻¹),-lam*(a i+(a i)⁻¹)),
      (-2*lam^2/(a (other₁ i)*a (other₂ i)),-2*a (other₁ i)*a (other₂ i)),
      (-2*lam,-2*lam)]

theorem crossed_table (lam : ℂ) (a : Fin 3 → ℂ) (ha : ∀ k, a k ≠ 0) (i : Fin 3) :
    analyticCrossed (sourceTable 1 lam a) (complementPair i) = crossedTable lam a i := by
  unfold analyticCrossed
  funext x
  simp only [TwoCopyKernels.contraction]
  simp_rw [swapped_word]
  fin_cases i <;>
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [sourceTable,crossedTable,complementPair,other₁,other₂,ofCoordinates,
      TwoCopyKernels.diagonal,insertPair,portEquiv,portInverse,firstHalf,secondHalf,
      h0,h1,h2,h3]
  all_goals field_simp [ha 0,ha 1,ha 2]
  all_goals ring

theorem actual_crossed_table {F : SignatureFamily ℂ} (lam : ℂ) (a : Fin 3 → ℂ)
    (ha : ∀ k, a k ≠ 0)
    (hq : Gadget.RealizesUpTo F .disequality (physical (sourceTable 1 lam a))) (i : Fin 3) :
    Gadget.RealizesUpTo F .disequality (physical (crossedTable lam a i)) := by
  rw [←crossed_table lam a ha i]
  exact actual_crossed _ hq _

/-- If every actual crossed output still has a cyclic deck, its three source
phases are fourth roots. An unsafe card is not suppressed by this implication:
closing that alternative needs the separate actual binary dispatch. -/
theorem cyclic_crossed_fourth_roots {N : ℕ} (hN : 3 ≤ N) (hNeven : Even N)
    (lam : ℂ) (a : Fin 3 → ℂ) (hlam : lam^N=1) (ha : ∀ i, (a i)^N=1)
    (hcards : ∀ i, AllPhaseCards N (crossedTable lam a i)) :
    ∀ i, (a i)^2=1 ∨ (a i)^2=-1 := by
  intro i
  apply FourthRootRigidity.crossed_coefficient_fourth_root hN hNeven
    (a i) lam (ha i) hlam (crossedTable lam a i) 2 (hcards i)
  · rfl
  · rfl

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.CrossedTables
