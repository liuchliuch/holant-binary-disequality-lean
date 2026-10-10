import Holant.Proofs.Tetrahedral.CyclicResource.Templates


namespace Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
open Holant Holant.Projective.CyclicQuaternary Holant.Projective.CyclicPhasePencil
open Holant.LocalDrafts.MainChain.CyclicBoundary
open PhysicalAttachments ZeroEndpointDressing ZeroEndpointJoin SquareDressing
open CrossedTables CrossedTemplates StraightFactor NonsquareIndex ActualCards NonsquareExit
noncomputable section
variable {F : SignatureFamily ℂ} {N : ℕ} (R : Representatives F N) (q : Signature ℂ 4)

def CountedOutside : Prop := ∃ b : Signature ℂ 2,
  Nonempty (Certificate q R.matrix b 2) ∧ b ≠ 0 ∧ ¬IsPhase N (walshTransfer b)

structure CountedDoubled where
  ratio : ℂ
  ratio_nonzero : ratio ≠ 0
  ratio_root : ratio^N=1
  certificate : Certificate q R.matrix (doubled (physical₂ (DihedralFactor.anti ratio))) 2

theorem obstruction_counted (hN : 3 ≤ N) (hNeven : Even N) (o : SourceDispatch.SquareObstruction N q) :
    CountedOutside R q ∨ Nonempty (CountedDoubled R q) := by
  classical
  let W := normalizeObstruction R o
  have ha0 : ∀ i, o.a i ≠ 0 := fun i => root_ne_zero (by omega) (o.a_root i)
  have hl0 : o.lam ≠ 0 := root_ne_zero (by omega) o.lam_root
  by_cases hcards : ∀ i, AllPhaseCards N (crossedTable o.lam o.a i)
  · obtain ⟨i,hi,he⟩ := cyclic_crossed_select hN hNeven o.order_four o.lam o.a
      o.lam_root o.a_root o.nonsquare hcards
    have J := straight R _ W (complementPair i)
    rw [straight_table o.lam o.a ha0 i,
      factor_physical_double o.lam o.a ha0 i hi he] at J
    refine Or.inr ⟨{
      ratio := factorRatio o.lam (o.a (other₁ i)) (o.a (other₂ i))
      ratio_nonzero := div_ne_zero hl0 (mul_ne_zero (ha0 _) (ha0 _))
      ratio_root := ?_
      certificate := J.rescale (mul_ne_zero (by norm_num) (pow_ne_zero _ (ha0 _))) }⟩
    simp [factorRatio,div_pow,mul_pow,o.lam_root,o.a_root]
  · push_neg at hcards
    obtain ⟨i,hi⟩ := hcards
    have J := crossed R _ W (complementPair i)
    rw [crossed_table o.lam o.a ha0 i] at J
    exact Or.inl (failed_deck_counted R _ J hi)

theorem CountedOutside.original_actual (h : CountedOutside R q)
    (hq : Gadget.RealizesUpTo F .disequality q) : Nonempty (OutsideCard F N) := by
  obtain ⟨b,⟨W⟩,hn,hout⟩ := h
  exact ⟨⟨b,W.actual_original F hq R.actual,hn,hout⟩⟩

def CountedDoubled.toOriginal (d : CountedDoubled R q)
    (hq : Gadget.RealizesUpTo F .disequality q) : DoubledOutside F N :=
  ⟨d.ratio,d.ratio_nonzero,d.ratio_root,d.certificate.actual_original F hq R.actual⟩

/-- The literal retained-label network has exactly two q vertices and its
full projective scale. Its auxiliary vertices are the supplied phase labels. -/
theorem CountedDoubled.network_data (d : CountedDoubled R q) :
    copies d.certificate.circuit.network = 2 ∧
      d.certificate.circuit.network.denote = d.certificate.scalar •
        doubled (physical₂ (DihedralFactor.anti d.ratio)) ∧
      d.certificate.scalar ≠ 0 ∧
      Gadget.Realizes (retained q R.matrix) .disequality d.certificate.circuit.network.denote :=
  ⟨d.certificate.count,d.certificate.equation,d.certificate.scalar_ne_zero,d.certificate.circuit.actual⟩

end
end Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
