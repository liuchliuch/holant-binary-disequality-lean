import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralSixDressing
import Holant.Pauli.ExoticKlein.FiberFactor
import Holant.Platonic.RankDeficientLocalization.FixedMatching


namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralSix.Rank
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralSix.Normalization
open Holant.Pauli.ExoticKlein.Fiber
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem actualMap_injective : Function.Injective actualMap := by
  intro h g he
  funext x
  let U : Binary := fun a b => if a = x 0 ∧ b = x 1 then 1 else 0
  have hv := congrArg (fun Φ : Binary →ₗ[ℂ] FourTensor => Φ U (fun j => x j.succ.succ)) he
  simp only [actualMap_apply,Signature.contract,U] at hv
  have hx : Fin.cons (x 0) (Fin.cons (x 1) (fun j : Fin 4 => x j.succ.succ)) = x := by
    funext j
    fin_cases j <;> rfl
  simpa [ite_and,hx] using hv

def currentRank (f : Signature ℂ 6) : ℕ := Module.finrank ℂ (actualMap f).range

theorem actualMap_zero : actualMap (0 : Signature ℂ 6) = 0 := by
  ext K x
  simp [actualMap, Signature.contract]

theorem zero_rank : currentRank (0 : Signature ℂ 6) = 0 := by
  simp [currentRank, actualMap_zero]

theorem rank_zero_iff (f : Signature ℂ 6) : currentRank f = 0 ↔ f = 0 := by
  constructor
  · intro hr
    have hbot : (actualMap f).range = ⊥ := Submodule.finrank_eq_zero.mp hr
    have he : actualMap f = 0 := LinearMap.range_eq_bot.mp hbot
    exact actualMap_injective (he.trans actualMap_zero.symm)
  · rintro rfl
    exact zero_rank

def delta (a b : Bool) : Binary := fun s t => if s = a ∧ t = b then 1 else 0

theorem delta_card (f : Signature ℂ 6) (a b : Bool) (x : Fin 4 → Bool) :
    actualMap f (delta a b) x = f (Fin.cons a (Fin.cons b x)) := by
  cases a <;> cases b <;>
    simp [actualMap, Signature.contract, delta,
      Fintype.sum_bool]

/-- A rank-one range makes every actual card proportional to one nonzero
card, with proportionality recovered from one nonzero evaluation. -/
theorem rank_one_cards (f : Signature ℂ 6) (hr : currentRank f = 1) :
    ∃ g : Signature ℂ 4, ∃ x : Fin 4 → Bool, g x ≠ 0 ∧
      ∀ K : Binary, actualMap f K = (actualMap f K x / g x) • g := by
  classical
  have hex : ∃ K : Binary, actualMap f K ≠ 0 := by
    by_contra hn
    push_neg at hn
    have he : actualMap f = 0 := LinearMap.ext hn
    have hz : currentRank f = 0 := by simp [currentRank, he]
    omega
  obtain ⟨K, hK⟩ := hex
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hK
  let v : (actualMap f).range := ⟨actualMap f K, ⟨K, rfl⟩⟩
  have hv : v ≠ 0 := fun h => hK (congrArg Subtype.val h)
  refine ⟨actualMap f K, x, hx, ?_⟩
  intro J
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp hr
    ⟨actualMap f J, ⟨J, rfl⟩⟩
  have he : c • actualMap f K = actualMap f J := congrArg Subtype.val hc
  have hx' : actualMap f J x / actualMap f K x = c := by
    rw [←he]
    change c * actualMap f K x / actualMap f K x = c
    exact mul_div_cancel_right₀ c (show actualMap f K x ≠ 0 from hx)
  rw [hx']
  exact he.symm

/-- The displayed split uses exactly the two contracted ports and the four
remaining original ports. No factor-access premise is needed. -/
theorem rank_one_factorization (f : Signature ℂ 6) (hr : currentRank f = 1) :
    ∃ u : Signature ℂ 2, ∃ v : Signature ℂ 4,
      u ≠ 0 ∧ v ≠ 0 ∧
      f = Tensor.reindex (finSumFinEquiv : Fin 2 ⊕ Fin 4 ≃ Fin 6) (Tensor.tensor u v) := by
  obtain ⟨g, x, hx, he⟩ := rank_one_cards f hr
  let u : Signature ℂ 2 := fun z => f (Fin.cons (z 0) (Fin.cons (z 1) x)) / g x
  have hf : f ≠ 0 := by intro hz; rw [hz, zero_rank] at hr; omega
  have hsplit : f = Tensor.reindex (finSumFinEquiv : Fin 2 ⊕ Fin 4 ≃ Fin 6)
      (Tensor.tensor u g) := by
    funext z
    have hh := congrFun (he (delta (z 0) (z 1))) (fun j => z j.succ.succ)
    simp only [delta_card, Pi.smul_apply, smul_eq_mul] at hh
    have hz : Fin.cons (z 0) (Fin.cons (z 1) (fun j : Fin 4 => z j.succ.succ)) = z := by
      funext j
      fin_cases j <;> rfl
    rw [hz] at hh
    have hrest : (fun j : Fin 4 => z
        ((finSumFinEquiv : Fin 2 ⊕ Fin 4 ≃ Fin 6) (Sum.inr j))) =
        (fun j : Fin 4 => z j.succ.succ) := by
      funext j
      congr 1
      apply Fin.ext
      rw [finSumFinEquiv_apply_right]
      change 2 + j.val = (j.val + 1) + 1
      omega
    change f z = u (fun j : Fin 2 => z
        ((finSumFinEquiv : Fin 2 ⊕ Fin 4 ≃ Fin 6) (Sum.inl j))) *
      g (fun j : Fin 4 => z
        ((finSumFinEquiv : Fin 2 ⊕ Fin 4 ≃ Fin 6) (Sum.inr j)))
    rw [hrest]
    exact hh
  have hu : u ≠ 0 := by
    intro hz
    apply hf
    rw [hsplit, hz]
    funext z
    simp [Tensor.reindex, Tensor.tensor]
  exact ⟨u, g, hu, fun hz => hx (by rw [hz]; rfl), hsplit⟩

theorem rank_one_factor (f : Signature ℂ 6) (hr : currentRank f = 1) :
    HasProperTensorFactor f := by
  obtain ⟨u, v, hu, hv, he⟩ := rank_one_factorization f hr
  exact ⟨2, 4, by decide, by decide, finSumFinEquiv, u, v, hu, hv, he⟩

theorem rank_bound (f : Signature ℂ 6) : currentRank f ≤ 4 :=
  Holant.Platonic.RankDeficientLocalization.map_rank_le_four (actualMap f)

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralSix.Rank
