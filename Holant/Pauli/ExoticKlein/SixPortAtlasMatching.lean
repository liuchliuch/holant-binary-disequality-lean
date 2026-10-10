import Holant.Pauli.ExoticKlein.SixPortModel
import Holant.Pauli.ExoticKlein.RulingCoordinates

/-! Exhaustive original-port normalization of all six-port matching products.
The small finite obligation concerns only involutive pairings of six ports;
all factor coefficients and orientation scales remain symbolic. -/
namespace Holant.Pauli.ExoticKlein.SixPort.Atlas
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option Elab.async false

def canonicalMate (j : Fin 5) (m : Fin 3) (p : Fin 6) : Fin 6 :=
  if p = productPort j m (0,false) then productPort j m (0,true)
  else if p = productPort j m (0,true) then productPort j m (0,false)
  else if p = productPort j m (1,false) then productPort j m (1,true)
  else if p = productPort j m (1,true) then productPort j m (1,false)
  else if p = productPort j m (2,false) then productPort j m (2,true)
  else productPort j m (2,false)

theorem canonicalMate_port (j : Fin 5) (m : Fin 3) (e : Fin 3) (b : Bool) :
    canonicalMate j m (productPort j m (e,b)) = productPort j m (e,!b) := by
  revert j m e b
  decide +kernel

theorem productMatching_mate (j : Fin 5) (m : Fin 3) (p : Fin 6) :
    (productMatching j m).mate p = canonicalMate j m p := by
  obtain ⟨⟨e,b⟩,rfl⟩ := (productMatching j m).ports.surjective p
  rw [Matching.mate_port]
  exact (canonicalMate_port j m e b).symm

def residualCandidate (j : Fin 5) (f : Fin 4 → Fin 4) (p : Fin 6) : Fin 6 :=
  if p = 0 then j.succ else if p = j.succ then 0
  else remainingPort (firstPair j) (f (remainingRank (firstPair j) p))

/-- Once the first physical pair is fixed, there are only4^4 residual
functions to check. Involution and absence of fixed points force one of the
three literal residual matching shapes. -/
theorem all_residual_pairings :
    ∀ j : Fin 5, ∀ f : Fin 4 → Fin 4,
      (∀ p, residualCandidate j f (residualCandidate j f p) = p) →
      (∀ p, residualCandidate j f p ≠ p) →
      ∃ m : Fin 3, ∀ p, residualCandidate j f p = canonicalMate j m p := by
  decide +kernel

theorem matching_shape (M : Matching (Fin 6) 3) :
    ∃ j : Fin 5, ∃ m : Fin 3, M.mate = (productMatching j m).mate := by
  have h0 : M.mate 0 ≠ 0 := M.mate_ne_self 0
  let j : Fin 5 := ⟨(M.mate 0).val-1,by
    have hn := (M.mate 0).isLt
    have hne : (M.mate 0).val ≠ 0 := fun h => h0 (Fin.ext h)
    omega⟩
  have hj : j.succ = M.mate 0 := by
    apply Fin.ext
    have hne : (M.mate 0).val ≠ 0 := fun h => h0 (Fin.ext h)
    dsimp [j]
    omega
  have hj0 : M.mate j.succ = 0 := by rw [hj,M.mate_mate]
  have hremain (p : Fin 6) (hp0 : p ≠ 0) (hpj : p ≠ j.succ) :
      remainingPort (firstPair j) (remainingRank (firstPair j) p) = p := by
    apply remaining_port_rank
    rw [firstPair_value]
    exact ⟨hp0,hpj⟩
  let f : Fin 4 → Fin 4 := fun i => remainingRank (firstPair j) (M.mate (remainingPort (firstPair j) i))
  have hrep : residualCandidate j f = M.mate := by
    funext p
    unfold residualCandidate
    split_ifs with hp0 hpj
    · subst p
      exact hj
    · subst p
      exact hj0.symm
    · have hm0 : M.mate p ≠ 0 := fun h => hpj (M.mate.injective (h.trans hj0.symm))
      have hmj : M.mate p ≠ j.succ := fun h => hp0 (M.mate.injective (h.trans hj))
      dsimp only [f]
      rw [hremain p hp0 hpj,hremain (M.mate p) hm0 hmj]
  obtain ⟨m,he⟩ := all_residual_pairings j f (by rw [hrep]; exact M.mate_mate)
    (by rw [hrep]; exact M.mate_ne_self)
  rw [hrep] at he
  refine ⟨j,m,?_⟩
  apply Equiv.ext
  intro p
  rw [he p,productMatching_mate]

/-- Every arbitrary oriented matching product has one of the960 literal
product directions, up to its retained nonzero scalar. -/
theorem canonical_product (h : Signature ℂ 6) (hh : IsProduct h) :
    ∃ j : Fin 960, ∃ c : ℂ, c ≠ 0 ∧
      h = fun x => c*productTensor (productDirectionEquiv j) x := by
  obtain ⟨M,labels,c,hc,rfl⟩ := hh
  obtain ⟨j,m,hm⟩ := matching_shape M
  obtain ⟨fixed,d,hd,he⟩ := (productMatching j m).representation_of_same_ruling M hm.symm labels c hc
  let direction : ProductDirection := (j,fixed 0,m,fixed 1,fixed 2)
  have hl : productLabels direction = fixed := by
    funext i
    fin_cases i <;> rfl
  refine ⟨productDirectionEquiv.symm direction,d,hd,?_⟩
  rw [Equiv.apply_symm_apply,productTensor_matching,hl]
  exact he

end
end Holant.Pauli.ExoticKlein.SixPort.Atlas
