import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionChoice

/-! Every chosen opposite-pair restriction of a common-sign EO row has
ternary-XOR-closed support. This is an algebraic property of the restriction;
physical access to it is supplied separately by the DEQ4 filter compiler. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCommonSignPairing
open Holant Holant.Tractable
open scoped BigOperators
namespace L
export Holant.LocalDrafts.Tractability.EOEvaluation.PairLift (Compatible restrict word_compress compress)
end L
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} (p : OrientedPerfectPairing n)

theorem twice_count : 2*p.count=n := by
  have h := Fintype.card_congr p.ports
  simpa [Nat.mul_comm] using h

theorem word_weight (z : Fin p.count → Bool) : weight (p.word z)=p.count := by
  unfold weight
  rw [←p.ports.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [OrientedPerfectPairing.word,Equiv.symm_apply_apply,Fintype.sum_bool]
  calc
    _ = ∑ _ : Fin p.count, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      cases z i <;> simp
    _ = p.count := by simp

theorem word_charge (z : Fin p.count → Bool) : charge (p.word z)=0 := by
  have h := twice_count p
  rw [charge,word_weight]
  omega

theorem compatible_charge (x : Fin n → Bool) (hx : L.Compatible p x) : charge x=0 := by
  rw [←L.word_compress p x hx]
  exact word_charge p _

theorem compatible_triple (x y z : Fin n → Bool)
    (hx : L.Compatible p x) (hy : L.Compatible p y) (hz : L.Compatible p z) :
    L.Compatible p (tripleXor x y z) := by
  intro j
  have h₁ := hx j
  have h₂ := hy j
  have h₃ := hz j
  unfold tripleXor
  cases hxf : x (p.ports (j,false)) <;> cases hxt : x (p.ports (j,true)) <;>
    cases hyf : y (p.ports (j,false)) <;> cases hyt : y (p.ports (j,true)) <;>
    cases hzf : z (p.ports (j,false)) <;> cases hzt : z (p.ports (j,true)) <;> simp_all

variable (f : Signature AlgebraicComplex n) (sign : EOSign)
variable (hs : EONegativeWitness.Supports sign ⟨n,f⟩)

include hs in
theorem compressed_closed : GeneralEONegativeClosedSupport.Closed (p.restrict f) := by
  intro x y z hx hy hz
  change f (p.word (tripleXor x y z))≠0
  have h := hs (p.word x) (p.word y) (p.word z) hx hy hz
  rw [←GeneralEOPairedFamilyExtractionChoice.word_tripleXor] at h
  rw [word_charge,mul_zero] at h
  exact h.resolve_right (by omega)

include hs in
theorem restricted_closed : GeneralEONegativeClosedSupport.Closed (L.restrict p f) := by
  intro x y z hx hy hz
  have get (w : Fin n → Bool) (hw : L.restrict p f w≠0) :
      L.Compatible p w ∧ f w≠0 := by
    by_cases hc : L.Compatible p w
    · exact ⟨hc,by simpa only [L.restrict,ite_eq_left hc] using hw⟩
    · exact False.elim (hw (ite_eq_right hc))
  obtain ⟨hcx,hfx⟩ := get x hx
  obtain ⟨hcy,hfy⟩ := get y hy
  obtain ⟨hcz,hfz⟩ := get z hz
  have hc := compatible_triple p x y z hcx hcy hcz
  rw [L.restrict,ite_eq_left hc]
  have h := hs x y z hfx hfy hfz
  rw [compatible_charge p _ hc,mul_zero] at h
  exact h.resolve_right (by omega)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCommonSignPairing
