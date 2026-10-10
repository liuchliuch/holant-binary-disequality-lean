import Holant.Platonic.RainbowLocalization.PhysicalAssembly
import Holant.Pauli.ExoticKlein.EightPortAllCards

/-! The source's canonical ordered-pair convention suffices for the
all-orderings input used in the physical collection theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Platonic.RainbowLocalization.Physical
open Holant Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.RainbowOrbit (Proportional)

theorem matchingOrZero_smul {P : Type*} (G : Set (Binary (K := ℂ)))
    (F : Tensor ℂ P) (hF : MatchingOrZero G F) (c : ℂ) : MatchingOrZero G (c • F) := by
  by_cases hc : c = 0
  · simp only [hc,zero_smul]
    exact Or.inl rfl
  rcases hF with rfl | ⟨M,hM,hs,he⟩
  · exact Or.inl (smul_zero c)
  · let N : Presentation ℂ P := { M with scalar := c * M.scalar }
    refine Or.inr ⟨N,hM,mul_ne_zero hc hs,?_⟩
    rw [he]
    funext x
    simp only [Presentation.tensor,productValue,N,Pi.smul_apply,smul_eq_mul,mul_assoc]

theorem contractPair_kernel_smul {P : Type*} [DecidableEq P]
    (u v : P) (K : Kernel ℂ) (f : Tensor ℂ P) (c : ℂ) :
    contractPair u v (c • K) f = c • contractPair u v K f := by
  funext x
  simp only [contractPair,Pi.smul_apply,smul_eq_mul,Fintype.sum_bool]
  ring

/-- The actual representatives cover every projective class of the current
group, retaining the specific nonzero representative-change scalar. -/
def CompleteKernelRepresentatives (G : Set (Binary (K := ℂ))) (D : Set (Kernel ℂ)) : Prop :=
  ∀ K ∈ G, ∃ L ∈ D, Proportional K L

theorem actualKernel_safe (G : Set (Binary (K := ℂ))) (hG : ProjectiveMatrixGroup G)
    (hX : (X : Binary (K := ℂ)) ∈ G) (D : Set (Kernel ℂ)) (hD : D ⊆ G) :
    ∀ K ∈ D, SafeBinary G K := by
  intro K hK
  exact hG.mul_mem _ (hD hK) _ hX

theorem transpose_actualKernel (G : Set (Binary (K := ℂ))) (hG : ProjectiveMatrixGroup G)
    (hX : (X : Binary (K := ℂ)) ∈ G) (hrev : ReversalStable G)
    (D : Set (Kernel ℂ)) (hD : D ⊆ G) (hcomplete : CompleteKernelRepresentatives G D)
    (K : Kernel ℂ) (hK : K ∈ D) : ∃ L ∈ D, Proportional (Kernel.transpose K) L := by
  have hs := SafeBinary.transpose hrev (actualKernel_safe G hG hX D hD K hK)
  have hm := hG.mul_mem _ hs _ hX
  have hm' : Matrix.transpose (K : Matrix Bool Bool ℂ) ∈ G := by
    simpa only [SafeBinary,transfer,Matrix.mul_assoc,X_mul_X,Matrix.mul_one] using hm
  exact hcomplete (Matrix.transpose K) hm'

/-- Reversal of a canonical pair changes the actual effective kernel only
by a covered transpose representative and a recorded nonzero scalar. -/
theorem all_orderings_of_canonical {n : ℕ}
    (G : Set (Binary (K := ℂ))) (hG : ProjectiveMatrixGroup G)
    (hX : (X : Binary (K := ℂ)) ∈ G) (hrev : ReversalStable G)
    (D : Set (Kernel ℂ)) (hD : D ⊆ G) (hcomplete : CompleteKernelRepresentatives G D)
    (f : Signature ℂ n)
    (hcanonical : ∀ u v : Fin n, u < v → ∀ K ∈ D, MatchingOrZero G (contractPair u v K f)) :
    ∀ u v : Fin n, u ≠ v → ∀ K ∈ D, MatchingOrZero G (contractPair u v K f) := by
  intro u v huv K hK
  rcases lt_or_gt_of_ne huv with huv' | hvu'
  · exact hcanonical u v huv' K hK
  · obtain ⟨B,hB,c,hc,he⟩ := transpose_actualKernel G hG hX hrev D hD hcomplete K hK
    rw [Holant.Pauli.ExoticKlein.MatchingCard.contractPair_swap u v huv,he,
      contractPair_kernel_smul]
    exact (matchingOrZero_smul G _ (hcanonical v u hvu' B hB) c).reindex
      (Holant.Pauli.ExoticKlein.MatchingCard.swapRemaining v u)

end Holant.Platonic.RainbowLocalization.Physical
