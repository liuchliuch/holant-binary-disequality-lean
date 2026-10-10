import Holant.Proofs.Hardness.EOBinaryPlaneFullSupportImages

/-! Full support of the explicitly selected original-field candidate. This
supplies the nonzero root anchors of conjugate interpolation, including the
row/column weighted choices; no additional full-support premise is imposed on
the produced candidate. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCandidateFull
open Holant
namespace C
export EOBinaryPlaneCandidateGadgets (output)
end C
namespace N
export EOBinaryPlaneGramGraphComplex (matrix)
end N
namespace P
export EOBinaryPlanePositive (choice exceptional)
end P
namespace G
export EOBinaryPlaneGram (cross determinant)
end G
namespace F
export EOBinaryPlaneFlat (row_sums_good)
end F
set_option backward.isDefEq.respectTransparency false

theorem matrix_full (a b c d : ℂ) (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0) :
    ∀z,N.matrix a b c d z≠0 := by
  intro z
  cases h0 : z 0 <;> cases h1 : z 1 <;> simpa [N.matrix,h0,h1] using (by assumption : _)

theorem matrix_selected_full (a b c d : ℂ) (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd0 : d≠0)
    (he : ¬P.exceptional a b c d) :
    ∀z,C.output (N.matrix a b c d) (P.choice a b c d) z≠0 := by
  have hall := matrix_full a b c d ha hb hc hd0
  intro z
  unfold P.choice
  split_ifs with hx ht hs hab
  · exact hall z
  · exact hall ![z 1,z 0]
  · change N.matrix a b c d z*N.matrix a b c d z≠0
    exact mul_ne_zero (hall z) (hall z)
  · obtain ⟨hu,hv,_⟩ := F.row_sums_good a b c d ha hb hc
      (not_ne_iff.mp hx) (not_ne_iff.mp ht) (not_ne_iff.mp hs) hab
    change N.matrix a b c d z*(N.matrix a b c d ![z 1,false]+N.matrix a b c d ![z 1,true])≠0
    apply mul_ne_zero (hall z)
    cases hz : z 1
    · simpa [N.matrix,hz] using hu
    · simpa [N.matrix,hz] using hv
  · have hbad : a^4≠b^4 ∨ a^4≠c^4 ∨ a^4≠d^4 := by
      by_contra hn
      push Not at hn
      exact he ⟨hn.1,hn.2.1,hn.2.2,eq_neg_of_add_eq_zero_left (not_ne_iff.mp hs)⟩
    have hac : a^4≠c^4 := by
      intro hac
      have had : a*d= -(b*c) := eq_neg_of_add_eq_zero_left (not_ne_iff.mp hs)
      have hp := congrArg (fun z : ℂ=>z^4) had
      have hn : (-(b*c))^4=b^4*c^4 := by ring
      rw [mul_pow,hn,←not_ne_iff.mp hab,←hac] at hp
      have had4 : a^4=d^4 := (mul_left_cancel₀ (pow_ne_zero 4 ha) hp).symm
      rcases hbad with h|h|h
      · exact h (not_ne_iff.mp hab)
      · exact h hac
      · exact h had4
    obtain ⟨hu,hv,_⟩ := F.row_sums_good a c b d ha hc hb
      (not_ne_iff.mp ht) (not_ne_iff.mp hx)
      (by simpa only [mul_comm c b] using not_ne_iff.mp hs) hac
    change N.matrix a b c d z*(N.matrix a b c d ![false,z 1]+N.matrix a b c d ![true,z 1])≠0
    apply mul_ne_zero (hall z)
    cases hz : z 1
    · simpa [N.matrix,hz] using hu
    · simpa [N.matrix,hz] using hv

theorem selected_full (f : Signature ℂ 2) (hf : ∀z,f z≠0)
    (he : ¬P.exceptional (f ![false,false]) (f ![false,true]) (f ![true,false]) (f ![true,true])) :
    ∀z,C.output f (P.choice (f ![false,false]) (f ![false,true]) (f ![true,false]) (f ![true,true])) z≠0 := by
  have h := matrix_selected_full _ _ _ _ (hf _) (hf _) (hf _) (hf _) he
  rw [EOBinaryPlaneFullSupportImages.matrix_values] at h
  exact h

theorem selected_mapped_full {K : Type} [Field K] (into : K→+*ℂ) (f : Signature K 2)
    (hf : ∀z,f z≠0) (he : ¬P.exceptional
      (into (f ![false,false])) (into (f ![false,true])) (into (f ![true,false])) (into (f ![true,true]))) :
    ∀z,C.output f (P.choice (into (f ![false,false])) (into (f ![false,true]))
      (into (f ![true,false])) (into (f ![true,true]))) z≠0 := by
  have hfull (z : Fin 2→Bool) : into (f z)≠0 := by
    intro hz
    apply hf z
    apply into.injective
    simpa only [map_zero] using hz
  have h := selected_full (fun z=>into (f z)) hfull he
  intro z hz
  have hm := congrFun (EOBinaryPlaneFullSupportImages.candidate_map into f
    (P.choice (into (f ![false,false])) (into (f ![false,true]))
      (into (f ![true,false])) (into (f ![true,true])))) z
  rw [hz,map_zero] at hm
  exact h z hm.symm

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCandidateFull
