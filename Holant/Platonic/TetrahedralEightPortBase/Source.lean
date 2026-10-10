import Holant.Platonic.TetrahedralEightPortBase.FactorCards

/-! The hereditary tetrahedral eight-port base with the source's actual
six-port safe cone and all actual physical pair cards, including zero cards.
A direct factor argument strengthens the printed conclusion to affinity. -/
namespace Holant.Platonic.TetrahedralEightPortBase
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Certificates.MatchingProductBridge
open Holant.Certificates.TetrahedralEightPort.SafeAffine
open Holant.Platonic.StabilizerShortening Holant.Platonic.StabilizerLine
open Holant.Pauli.ExoticKlein.Fiber
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The unaltered source hypothesis: every actual tetrahedral kernel on every
physical pair has its complete six-port residual in the genuine safe cone. -/
def AllSafeCards (g : Signature ℂ 8) : Prop :=
  ∀ p : (Bool ⊕ Fin 6) ≃ Fin 8, ∀ K : Kernel ℂ,
    groupDirection .tetrahedral K → SafeCone (pairCard p K g)

theorem factor_swap {l m n : ℕ} (p : (Fin m ⊕ Fin n) ≃ Fin l)
    (f : Signature ℂ m) (g : Signature ℂ n) :
    Tensor.reindex ((Equiv.sumComm (Fin n) (Fin m)).trans p) (Tensor.tensor g f)=
      Tensor.reindex p (Tensor.tensor f g) := by
  funext x
  exact mul_comm _ _

theorem factor_right_affine {m n : ℕ} (p : (Fin (m+2) ⊕ Fin n) ≃ Fin 8)
    (f : Signature ℂ (m+2)) (g : Signature ℂ n) (hf : f≠0)
    (hcards : AllSafeCards (Tensor.reindex p (Tensor.tensor f g))) : ComplexAffine g := by
  have hdim := Fintype.card_congr p
  simp only [Fintype.card_sum,Fintype.card_fin] at hdim
  let r : (Fin m ⊕ Fin n) ≃ Fin 6 := Fintype.equivOfCardEq (by simp; omega)
  obtain ⟨K,hK,hKn⟩ := nonzero_internal_card f hf
  have h := hcards (factorPair p r) K hK
  rw [pairCard_factor] at h
  exact affine_factor_right r _ g hKn (safeCone_affine _ h)

theorem tensor_unary_separates {m : ℕ} (p : (Fin m ⊕ Fin 1) ≃ Fin 6)
    (f : Signature ℂ m) (g : Signature ℂ 1) :
    SeparatesAt (p (.inr 0)) (Tensor.reindex p (Tensor.tensor f g)) := by
  refine ⟨fun b=>g (fun _=>b),fun x=>f (fun j=>x (p (.inl j))),?_,?_⟩
  · intro x b
    apply congrArg f
    funext j
    exact Function.update_of_ne (p.injective.ne (Sum.inl_ne_inr)) b x
  · intro x
    change f (fun j=>x (p (.inl j))) * g (fun j=>x (p (.inr j))) =
      g (fun _=>x (p (.inr 0))) * f (fun j=>x (p (.inl j)))
    rw [mul_comm]
    congr 2
    funext j
    fin_cases j
    rfl

theorem unary_factor_impossible {m : ℕ} (p : (Fin (m+2) ⊕ Fin 1) ≃ Fin 8)
    (f : Signature ℂ (m+2)) (g : Signature ℂ 1) (hf : f≠0) (hg : g≠0)
    (hcards : AllSafeCards (Tensor.reindex p (Tensor.tensor f g))) : False := by
  have hdim := Fintype.card_congr p
  simp only [Fintype.card_sum,Fintype.card_fin] at hdim
  let r : (Fin m ⊕ Fin 1) ≃ Fin 6 := Fintype.equivOfCardEq (by simp; omega)
  obtain ⟨K,hK,hKn⟩ := nonzero_internal_card f hf
  have h := hcards (factorPair p r) K hK
  rw [pairCard_factor] at h
  exact safeCone_noUnary _ h (tensor_ne_zero r _ _ hKn hg) _
    (tensor_unary_separates r _ g)

/-- Any genuine proper factor is affine under the hereditary safe-card
hypothesis. Unary factors are excluded by the literal six-port orbit invariant;
for larger factors, nonzero internal cards recover both factors by affine
coordinate restriction. -/
theorem properFactor_safeCards_affine (g : Signature ℂ 8)
    (hfactor : HasProperTensorFactor g) (hcards : AllSafeCards g) : ComplexAffine g := by
  obtain ⟨m,n,hm,hn,p,f,h,hf,hh,rfl⟩ := hfactor
  have hdim := Fintype.card_congr p
  simp only [Fintype.card_sum,Fintype.card_fin] at hdim
  cases m with
  | zero => omega
  | succ m => cases m with
    | zero =>
      have hn7 : n=7 := by omega
      subst n
      let q := (Equiv.sumComm (Fin 7) (Fin 1)).trans p
      have hs : AllSafeCards (Tensor.reindex q (Tensor.tensor h f)) := by
        simpa only [q,factor_swap] using hcards
      exact False.elim (unary_factor_impossible (m:=5) q h f hh hf hs)
    | succ m => cases n with
      | zero => omega
      | succ n => cases n with
        | zero => exact False.elim (unary_factor_impossible p f h hf hh hcards)
        | succ n =>
          apply affine_tensor p f h
          · let q := (Equiv.sumComm (Fin (n+2)) (Fin (m+2))).trans p
            have hs : AllSafeCards (Tensor.reindex q (Tensor.tensor h f)) := by
              simpa only [q,factor_swap] using hcards
            exact factor_right_affine q h f hh hs
          · exact factor_right_affine p f h hf hcards

/-- Strong hereditary base: every complex eight-port tensor whose literal
actual tetrahedral pair cards lie in the genuine source safe cone is affine. -/
theorem safeCards_affine (g : Signature ℂ 8) (hcards : AllSafeCards g) :
    ComplexAffine g := by
  rcases safeCards_factor_or_affine g hcards with hf|ha
  · exact properFactor_safeCards_affine g hf hcards
  · exact ha

/-- Proposition 9.17, with the exact 2|6 factor alternative expressed by an
actual original-port bijection and two nonzero tensor factors. -/
theorem source_hereditary_tetrahedral_eight_port (g : Signature ℂ 8) (_hg : g≠0)
    (hcards : ∀ p : (Bool ⊕ Fin 6) ≃ Fin 8, ∀ K : Kernel ℂ,
      groupDirection .tetrahedral K → SafeCone (pairCard p K g)) :
    (∃ p : (Fin 2 ⊕ Fin 6) ≃ Fin 8, ∃ f : Signature ℂ 2, ∃ h : Signature ℂ 6,
      f≠0 ∧ h≠0 ∧ g=Tensor.reindex p (Tensor.tensor f h)) ∨ ComplexAffine g :=
  Or.inr (safeCards_affine g hcards)

end
end Holant.Platonic.TetrahedralEightPortBase
