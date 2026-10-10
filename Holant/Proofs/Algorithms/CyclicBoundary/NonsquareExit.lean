import Holant.Proofs.Algorithms.CyclicBoundary.ActualCards


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.NonsquareExit
open Holant.Projective.CyclicQuaternary Holant.Projective.CyclicPhasePencil
open Holant.Pauli.ExoticKlein.Fiber
open ZeroEndpointDressing ZeroEndpointJoin SquareDressing CrossedTables
open CrossedTemplates StraightFactor NonsquareIndex ActualCards SourceDispatch
noncomputable section

def doubled (B : Signature ℂ 2) : Signature ℂ 4 :=
  Tensor.reindex (ZeroEndpointFactor.ports 0) (Tensor.tensor B B)

theorem factor_physical_double (lam : ℂ) (a : Fin 3 → ℂ) (ha : ∀ k, a k ≠ 0)
    (i : Fin 3) (hi : (a i)^2=-1) (hother : (a (other₁ i))^2=(a (other₂ i))^2) :
    physical (straightTable lam a i) = factorScale (a (other₁ i)) •
      doubled (physical₂ (DihedralFactor.anti (factorRatio lam (a (other₁ i)) (a (other₂ i))))) := by
  rw [factor_table lam a ha i hi hother]
  unfold physical
  rw [CoordinateFactors.action_split]
  funext x
  simp [doubled,physical₂,Tensor.reindex,Tensor.tensor,Signature.coordinateAction,
    StraightFactor.binary,PhysicalAttachments.binary,← Finset.mul_sum,mul_left_comm,mul_assoc]

/-- A strictly weaker interface than a realized binary: only its ordered
tensor square is realized. All properties are computed from the straight
join. A general factor-extraction consumer must justify access to B. -/
structure DoubledOutside (F : SignatureFamily ℂ) (N : ℕ) where
  ratio : ℂ
  ratio_nonzero : ratio ≠ 0
  ratio_root : ratio^N=1
  doubled_actual : Gadget.RealizesUpTo F .disequality
    (doubled (physical₂ (DihedralFactor.anti ratio)))

theorem DoubledOutside.binary_nonzero {F : SignatureFamily ℂ} {N : ℕ}
    (d : DoubledOutside F N) : physical₂ (DihedralFactor.anti d.ratio) ≠ 0 :=
  CoordinateFactors.action_nonzero _ (fun _ => CoordinateFactors.inverseHadamard)
    (fun _ => CoordinateFactors.inverse_hadamard) _ (StraightFactor.binary_nonzero _)

theorem DoubledOutside.binary_outside {F : SignatureFamily ℂ} {N : ℕ}
    (d : DoubledOutside F N) :
    ¬IsPhase N (walshTransfer (physical₂ (DihedralFactor.anti d.ratio))) := by
  rw [walshTransfer_physical₂]
  exact DihedralFactor.outside_cyclic N d.ratio

theorem DoubledOutside.transfer_inverse {F : SignatureFamily ℂ} {N : ℕ}
    (d : DoubledOutside F N) :
    Kernel.mul (walshTransfer (physical₂ (DihedralFactor.anti d.ratio)))
      ((-d.ratio)⁻¹ • walshTransfer (physical₂ (DihedralFactor.anti d.ratio))) =
        Signature.equality := by
  rw [walshTransfer_physical₂]
  exact (DihedralFactor.transfer_inverse d.ratio d.ratio_nonzero).1

theorem cyclic_doubled_exit {F : SignatureFamily ℂ} {N : ℕ}
    (hN : 3 ≤ N) (hNeven : Even N) (q : Signature ℂ 4)
    (o : SquareObstruction N q) (hq : Gadget.RealizesUpTo F .disequality q)
    (hcards : ∀ i, AllPhaseCards N (crossedTable o.lam o.a i)) :
    Nonempty (DoubledOutside F N) := by
  have ha0 : ∀ i, o.a i ≠ 0 := fun i => root_ne_zero (by omega) (o.a_root i)
  have hl0 : o.lam ≠ 0 := root_ne_zero (by omega) o.lam_root
  obtain ⟨i,hi,he⟩ := cyclic_crossed_select hN hNeven o.order_four o.lam o.a
    o.lam_root o.a_root o.nonsquare hcards
  have hreal := actual_straight _ (normalized_realization q o hq) (complementPair i)
  rw [straight_table o.lam o.a ha0 i,factor_physical_double o.lam o.a ha0 i hi he] at hreal
  refine ⟨⟨factorRatio o.lam (o.a (other₁ i)) (o.a (other₂ i)),
    div_ne_zero hl0 (mul_ne_zero (ha0 _) (ha0 _)),?_,?_⟩⟩
  · simp [factorRatio,div_pow,mul_pow,o.lam_root,o.a_root]
  · exact PhysicalAttachments.upTo_of_scale _ _
      (mul_ne_zero (by norm_num) (pow_ne_zero _ (ha0 _))) hreal

theorem obstruction_exit {F : SignatureFamily ℂ} {N : ℕ}
    (R : PhysicalAttachments.Representatives F N) (hN : 3 ≤ N) (hNeven : Even N)
    (q : Signature ℂ 4) (o : SquareObstruction N q)
    (hq : Gadget.RealizesUpTo F .disequality q) :
    Nonempty (OutsideCard F N) ∨ Nonempty (DoubledOutside F N) := by
  classical
  by_cases hcards : ∀ i, AllPhaseCards N (crossedTable o.lam o.a i)
  · exact Or.inr (cyclic_doubled_exit hN hNeven q o hq hcards)
  · push_neg at hcards
    obtain ⟨i,hi⟩ := hcards
    have ha0 : ∀ j, o.a j ≠ 0 := fun j => root_ne_zero (by omega) (o.a_root j)
    exact Or.inl (failed_deck_actual R _
      (actual_crossed_table o.lam o.a ha0 (normalized_realization q o hq) i) hi)

/-- No classification conclusion is assumed or fabricated. The result is
either the desired actual prime endpoint tensor, an actual group-external
binary, or an actual tensor square requiring genuine factor extraction. -/
theorem cyclic_boundary_dispatch {F : SignatureFamily ℂ} {N : ℕ}
    (R : PhysicalAttachments.Representatives F N) (hN : 3 ≤ N) (hNeven : Even N)
    (q : Signature ℂ 4) (hq : Gadget.RealizesUpTo F .disequality q)
    (hn : q ≠ 0) (hp : ¬HasProperTensorFactor q)
    (hcards : AllPhaseCards N (ZeroDeckBoundary.walsh q)) :
    EndpointOutput F ∨ Nonempty (OutsideCard F N) ∨ Nonempty (DoubledOutside F N) := by
  cases dispatch_to_square_obstruction R hN hNeven q hq hn hp hcards with
  | inl h => exact Or.inl h
  | inr h =>
    obtain ⟨o⟩ := h
    exact Or.inr (obstruction_exit R hN hNeven q o hq)

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.NonsquareExit
