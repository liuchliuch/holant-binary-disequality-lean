import Holant.Platonic.TetrahedralLocalization.Reconstruction
import Holant.Pauli.ExoticKlein.FiberFactor

/-! Rank zero or one of the actual first-pair contraction map gives zero
or an original-port 2|m proper tensor factor, at arbitrary positive m. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicHigherRank
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Platonic.TetrahedralLocalization Holant.Platonic.StabilizerShortening
open Holant.Pauli.ExoticKlein.Fiber
variable {m : ℕ}

def currentRank (f : Signature ℂ (m+2)) : ℕ := Module.finrank ℂ (frobeniusMap f).range

theorem frobenius_zero : frobeniusMap (0 : Signature ℂ (m+2))=0 := by
  ext K x
  simp [frobeniusMap,pairCard]

theorem frobenius_injective : Function.Injective (frobeniusMap (n:=m)) := by
  intro f g h
  funext x
  have he := congrArg (fun Φ : Binary →ₗ[ℂ] Signature ℂ m =>
    Φ (fun a b => if a=x 0 ∧ b=x 1 then 1 else 0) (fun j => x j.succ.succ)) h
  simp only [frobeniusMap_unit] at he
  have hx : Fin.cons (x 0) (Fin.cons (x 1) (fun j => x j.succ.succ))=x := by
    ext j
    cases j using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases <;> rfl
  simpa only [hx] using he

theorem rank_zero_iff (f : Signature ℂ (m+2)) : currentRank f=0 ↔ f=0 := by
  constructor
  · intro h
    have he : frobeniusMap f=0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h)
    exact frobenius_injective (he.trans frobenius_zero.symm)
  · rintro rfl
    simp [currentRank,frobenius_zero]

theorem rank_one_cards (f : Signature ℂ (m+2)) (hr : currentRank f=1) :
    ∃ g : Signature ℂ m, ∃ x : Fin m → Bool, g x≠0 ∧
      ∀ K : Binary, frobeniusMap f K=(frobeniusMap f K x/g x) • g := by
  classical
  have hex : ∃ K : Binary,frobeniusMap f K≠0 := by
    by_contra hn
    push_neg at hn
    have he : frobeniusMap f=0 := LinearMap.ext hn
    have hz : currentRank f=0 := by simp [currentRank,he]
    omega
  obtain ⟨K,hK⟩ := hex
  obtain ⟨x,hx⟩ := Function.ne_iff.mp hK
  let v : (frobeniusMap f).range := ⟨frobeniusMap f K,⟨K,rfl⟩⟩
  have hv : v≠0 := fun h => hK (congrArg Subtype.val h)
  refine ⟨frobeniusMap f K,x,hx,?_⟩
  intro J
  obtain ⟨c,hc⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp hr
    ⟨frobeniusMap f J,⟨J,rfl⟩⟩
  have he : c • frobeniusMap f K=frobeniusMap f J := congrArg Subtype.val hc
  have hx' : frobeniusMap f J x/frobeniusMap f K x=c := by
    rw [←he]
    change c*frobeniusMap f K x/frobeniusMap f K x=c
    exact mul_div_cancel_right₀ c (show frobeniusMap f K x≠0 from hx)
  rw [hx']
  exact he.symm

def splitPorts (m : ℕ) : Fin 2 ⊕ Fin m ≃ Fin (m+2) :=
  (Equiv.sumCongr finTwoEquiv (Equiv.refl (Fin m))).trans (firstPair m)

theorem rank_one_factor (f : Signature ℂ (m+2)) (hm : 0<m) (hr : currentRank f=1) :
    HasProperTensorFactor f := by
  obtain ⟨g,x,hx,he⟩ := rank_one_cards f hr
  let u : Signature ℂ 2 := fun z => f (Fin.cons (z 0) (Fin.cons (z 1) x))/g x
  have hf : f≠0 := by
    intro hz
    have h0 := (rank_zero_iff f).mpr hz
    omega
  have hsplit : f=Tensor.reindex (splitPorts m) (Tensor.tensor u g) := by
    funext z
    have hh := congrFun (he (fun a b => if a=z 0 ∧ b=z 1 then 1 else 0))
      (fun j => z j.succ.succ)
    simp only [frobeniusMap_unit,Pi.smul_apply,smul_eq_mul] at hh
    have hz : Fin.cons (z 0) (Fin.cons (z 1) (fun j => z j.succ.succ))=z := by
      ext j
      cases j using Fin.cases with
      | zero => rfl
      | succ j => cases j using Fin.cases <;> rfl
    rw [hz] at hh
    exact hh
  have hu : u≠0 := by
    intro hz
    apply hf
    rw [hsplit,hz]
    funext z
    simp [Tensor.reindex,Tensor.tensor]
  exact ⟨2,m,by decide,hm,splitPorts m,u,g,hu,fun hz => hx (by rw [hz];rfl),hsplit⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicHigherRank
end
