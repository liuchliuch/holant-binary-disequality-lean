import Holant.Platonic.TetrahedralLocalization.Reconstruction

/-! The one-step physical tetrahedral descent. It is proved for every complex
signature, a stronger algebraic statement than the marked-state restriction. -/
namespace Holant.Platonic.TetrahedralLocalization
open Holant Holant.Tractable.AffinePhase
open Holant.Platonic.StabilizerShortening Holant.Platonic.StabilizerLine
open Holant.Certificates.MatchingProductBridge
open Holant.Certificates.TetrahedralAffine
open Holant.Pauli.ExoticKlein.Fiber
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Proper factor or nonzero nonaffine card, using literal tetrahedral kernels.
No asserted encoding witness or all-card hypothesis occurs in the statement. -/
theorem factor_or_nonaffine_pair {n : ℕ} (f : Signature ℂ n)
    (hn : 8≤n) (hf : ¬ComplexAffine f) :
    HasProperTensorFactor f ∨ HasNonaffineTetrahedralCard f := by
  by_cases hcard : HasNonaffineTetrahedralCard f
  · exact Or.inr hcard
  cases n with
  | zero => omega
  | succ n => cases n with
    | zero => omega
    | succ n =>
      have htests : ∀K,tetrahedralBase K →
          frobeniusMap f K=0 ∨ ComplexAffine (frobeniusMap f K) := by
        intro K hK
        obtain ⟨r,rfl⟩ := base_covered hK
        by_cases hz : frobeniusMap f (complexKernel r)=0
        · exact Or.inl hz
        · apply Or.inr
          by_contra ha
          exact hcard ⟨n,firstPair n,r,hz,ha⟩
      obtain ⟨k,hk,V,hV,xi,hxi,he⟩ := source_frobenius_reconstruction f hf htests
      have h := source_stabilizer_code_tetrahedral_shortening 2 V.map hV hk (by omega)
        (by omega) xi hxi
      rwa [he] at h

/-- Proposition9.22's first assertion, with tensor primeness expressed by the
absence of an actual nonzero factorization over two nonempty physical blocks. -/
theorem source_nonaffine_actual_pair {n : ℕ} (g : Signature ℂ n)
    (hn : 10≤n) (hprime : ¬HasProperTensorFactor g) (hg : ¬ComplexAffine g) :
    HasNonaffineTetrahedralCard g :=
  (factor_or_nonaffine_pair g (by omega) hg).resolve_left hprime

/-- The selected residual has exactly two fewer ports. -/
theorem pair_arity {m n : ℕ} (p : (Bool ⊕ Fin n) ≃ Fin m) : n+2=m := by
  have h := Fintype.card_congr p
  simpa [Nat.add_comm] using h

/-- The source card has distinct original ports and a proved strict arity drop. -/
theorem source_pair_with_arity {n : ℕ} (g : Signature ℂ n)
    (hn : 10≤n) (hprime : ¬HasProperTensorFactor g) (hg : ¬ComplexAffine g) :
    ∃m : ℕ,∃p : (Bool ⊕ Fin m) ≃ Fin n,∃r : Representative,
      m+2=n ∧ p (.inl false)≠p (.inl true) ∧
      pairCard p (complexKernel r) g≠0 ∧ ¬ComplexAffine (pairCard p (complexKernel r) g) := by
  obtain ⟨m,p,r,hd,hnz,ha⟩ := actual_card_distinct_witness g
    (source_nonaffine_actual_pair g hn hprime hg)
  exact ⟨m,p,r,pair_arity p,hd,hnz,ha⟩

end
end Holant.Platonic.TetrahedralLocalization
