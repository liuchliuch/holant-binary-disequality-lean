import Holant.Proofs.Algorithms.CyclicBoundary.DihedralFactor
import Holant.Proofs.Algorithms.CyclicBoundary.CoordinateFactors


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.StraightFactor
open Holant.Projective.CyclicQuaternary Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops Holant.Pauli.ExoticKlein.Fiber
open TwoCopyKernels ZeroEndpointDressing ZeroEndpointJoin SquareDressing
open CrossedTemplates CrossedTables CoordinateFactors
noncomputable section
set_option maxHeartbeats 800000

def straightTable (lam : ℂ) (a : Fin 3 → ℂ) (i : Fin 3) : Signature ℂ 4 :=
  ofCoordinates (1+(a i)^2) (lam^2*(1+((a i)⁻¹)^2))
    ![(-lam*(a i+(a i)⁻¹),-lam*(a i+(a i)⁻¹)),
      (-lam^2*(((a (other₁ i))⁻¹)^2+((a (other₂ i))⁻¹)^2),
        -((a (other₁ i))^2+(a (other₂ i))^2)),
      (-lam*(a (other₁ i)/a (other₂ i)+a (other₂ i)/a (other₁ i)),
        -lam*(a (other₁ i)/a (other₂ i)+a (other₂ i)/a (other₁ i)))]

theorem straight_table (lam : ℂ) (a : Fin 3 → ℂ) (ha : ∀ k, a k ≠ 0) (i : Fin 3) :
    analyticStraight (sourceTable 1 lam a) (complementPair i) = straightTable lam a i := by
  unfold analyticStraight
  funext x
  fin_cases i <;>
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [TwoCopyKernels.contraction,sourceTable,straightTable,complementPair,
      other₁,other₂,ofCoordinates,TwoCopyKernels.diagonal,insertPair,portEquiv,
      portInverse,firstHalf,secondHalf,h0,h1,h2,h3]
  all_goals field_simp [ha 0,ha 1,ha 2]
  all_goals ring

def binary (r : ℂ) : Signature ℂ 2 := fun x => DihedralFactor.anti r (x 0) (x 1)
def factorScale (b : ℂ) : ℂ := -2*b^2
def factorRatio (lam b c : ℂ) : ℂ := lam/(b*c)

theorem binary_nonzero (r : ℂ) : binary r ≠ 0 := by
  intro h
  have hh := congrArg (fun f : Signature ℂ 2 => f ![false,true]) h
  norm_num [binary,DihedralFactor.anti] at hh

theorem scaled_binary_nonzero (r b : ℂ) (hb : b ≠ 0) : factorScale b • binary r ≠ 0 := by
  intro h
  have hh := congrArg (fun f : Signature ℂ 2 => f ![false,true]) h
  have hs : factorScale b ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hb)
  exact hs (by simpa [binary,DihedralFactor.anti] using hh)

theorem inverse_of_square_neg_one (a : ℂ) (ha : a^2=-1) : a⁻¹ = -a := by
  apply inv_eq_of_mul_eq_one_right
  linear_combination -ha

theorem equal_squares_cases (b c : ℂ) (h : b^2=c^2) : c=b ∨ c=-b := by
  have hz : (c-b)*(c+b)=0 := by linear_combination -h
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

theorem factor_table (lam : ℂ) (a : Fin 3 → ℂ) (ha : ∀ k, a k ≠ 0) (i : Fin 3)
    (hi : (a i)^2=-1) (hother : (a (other₁ i))^2=(a (other₂ i))^2) :
    straightTable lam a i = Tensor.reindex (ZeroEndpointFactor.ports 0)
      (Tensor.tensor
        (factorScale (a (other₁ i)) • binary (factorRatio lam (a (other₁ i)) (a (other₂ i))))
        (binary (factorRatio lam (a (other₁ i)) (a (other₂ i))))) := by
  have hinv := inverse_of_square_neg_one (a i) hi
  rcases equal_squares_cases _ _ hother with hc | hc
  all_goals
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
      simp [straightTable,Tensor.reindex,Tensor.tensor,ZeroEndpointFactor.ports,
        binary,DihedralFactor.anti,factorScale,factorRatio,ofCoordinates,
        h0,h1,h2,h3,hinv,hi,hc]
  all_goals field_simp [ha (other₁ i)]
  all_goals ring

theorem straight_has_factor (lam : ℂ) (a : Fin 3 → ℂ) (ha : ∀ k, a k ≠ 0) (i : Fin 3)
    (hi : (a i)^2=-1) (hother : (a (other₁ i))^2=(a (other₂ i))^2) :
    HasProperTensorFactor (analyticStraight (sourceTable 1 lam a) (complementPair i)) := by
  rw [straight_table lam a ha i]
  exact ⟨2,2,by decide,by decide,ZeroEndpointFactor.ports 0,
    factorScale (a (other₁ i)) • binary (factorRatio lam (a (other₁ i)) (a (other₂ i))),
    binary (factorRatio lam (a (other₁ i)) (a (other₂ i))),
    scaled_binary_nonzero _ _ (ha _),binary_nonzero _,factor_table lam a ha i hi hother⟩

/-- The actual native join has a genuine nonzero proper tensor factor in
physical coordinates. This output is suitable for a separately proved factor
extraction reduction; no direct realization of the binary is an input. -/
theorem actual_factored_join {F : SignatureFamily ℂ} (lam : ℂ) (a : Fin 3 → ℂ)
    (ha : ∀ k, a k ≠ 0) (i : Fin 3)
    (hi : (a i)^2=-1) (hother : (a (other₁ i))^2=(a (other₂ i))^2)
    (hq : Gadget.RealizesUpTo F .disequality (physical (sourceTable 1 lam a))) :
    Gadget.RealizesUpTo F .disequality
        (physical (analyticStraight (sourceTable 1 lam a) (complementPair i))) ∧
      HasProperTensorFactor
        (physical (analyticStraight (sourceTable 1 lam a) (complementPair i))) :=
  ⟨actual_straight _ hq _,(physical_factor_iff _).mpr (straight_has_factor lam a ha i hi hother)⟩

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.StraightFactor
