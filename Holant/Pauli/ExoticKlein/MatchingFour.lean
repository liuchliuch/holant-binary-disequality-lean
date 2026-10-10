import Holant.Pauli.ExoticKlein.MatchingSupport

namespace Holant.Pauli.ExoticKlein
noncomputable section
open scoped BigOperators
namespace Matching
variable {P : Type*} {r : ℕ} [Fintype P] [LinearOrder P]

 theorem cycleLength_one_iff_common (M N : Matching P r) (c : M.CycleHead N) :
    M.cycleLength N c = 1 ↔ M.mate c.val = N.mate c.val := by
  have h := (M.isCycleOn_orbitSet N c.val).pow_apply_eq (M.self_mem_orbitSet N c.val) (n := 1)
  simp only [pow_one,Nat.dvd_one] at h
  change (M.alternating N) c.val = c.val ↔ M.cycleLength N c = 1 at h
  rw [← h]
  constructor
  · intro he
    apply N.mate.injective
    simpa only [alternating,Equiv.Perm.coe_mul,Function.comp_apply,mate_mate] using he
  · intro he
    change N.mate (M.mate c.val) = c.val
    rw [he,mate_mate]

 theorem sum_cycle_extras (M N : Matching P r) :
    ∑ c, (M.cycleLength N c-1) = r-M.cycleCount N := by
  rw [Finset.sum_tsub_distrib Finset.univ (f := M.cycleLength N) (g := fun _ => 1)
    (fun c _ => M.cycleLength_pos N c),M.sum_cycleLength N]
  simp [cycleCount]

/-- Support four determines one genuine alternating four-cycle and common
matching edges everywhere else. -/
 theorem support_four_cycle_shape (M N : Matching P r) (fixed : Fin r → Label)
    (h : Fintype.card {labels : Fin r → Label // M.overlap N fixed labels ≠ 0} = 4) :
    ∃ c : M.CycleHead N, M.cycleLength N c = 2 ∧
      ∀ d, d ≠ c → M.cycleLength N d = 1 := by
  classical
  rw [M.overlap_support_card N] at h
  have hexp : r-M.cycleCount N = 1 := Nat.pow_right_injective (by decide : 2 ≤ 4) (by simpa using h)
  have hsum : ∑ c, (M.cycleLength N c-1) = 1 := by rw [M.sum_cycle_extras N,hexp]
  obtain ⟨c,hc⟩ : ∃ c, M.cycleLength N c-1 ≠ 0 := by
    by_contra hn
    push_neg at hn
    simp only [hn,Finset.sum_const_zero] at hsum
    contradiction
  have hcpos := M.cycleLength_pos N c
  have hcle : M.cycleLength N c-1 ≤ ∑ d, (M.cycleLength N d-1) :=
    Finset.single_le_sum (f := fun d => M.cycleLength N d-1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  have hc2 : M.cycleLength N c = 2 := by omega
  refine ⟨c,hc2,?_⟩
  intro d hdc
  have hs := Finset.sum_erase_add Finset.univ (fun e => M.cycleLength N e-1) (Finset.mem_univ c)
  rw [hsum,hc2] at hs
  have hz : (Finset.univ.erase c).sum (fun e => M.cycleLength N e-1) = 0 := by omega
  have hdle : M.cycleLength N d-1 ≤ (Finset.univ.erase c).sum (fun e => M.cycleLength N e-1) :=
    Finset.single_le_sum (f := fun e => M.cycleLength N e-1) (fun _ _ => Nat.zero_le _) (by simp [hdc])
  have hdpos := M.cycleLength_pos N d
  omega

end Matching
end
end Holant.Pauli.ExoticKlein
