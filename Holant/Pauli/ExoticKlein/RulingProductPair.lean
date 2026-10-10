import Holant.Pauli.ExoticKlein.RulingSameSemantics
import Holant.Pauli.ExoticKlein.MatchingGroup
import Holant.Pauli.ExoticKlein.RulingUniqueness

/-! A product has one fixed residual ruling at any deleted pair. The actual
remaining-port matching is fixed before the kernel is chosen. Vanishing
same-edge traces are retained explicitly. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
open scoped BigOperators
namespace MatchingCard
open Holant.Certificates.MatchingContractionClosure MatchingSurgery

 def presentationMatching {P : Type*} (M : Presentation ℂ P) : Matching P M.edges := ⟨M.ports⟩

 theorem presentation_exotic_form {P : Type*} (M : Presentation ℂ P) (hM : M.Valid binaryGroup)
     (hw : M.scalar ≠ 0) :
     ∃ labels : Fin M.edges → Label, ∃ c : ℂ, c ≠ 0 ∧
       M.tensor = fun x => c*(presentationMatching M).tensor labels x := by
   have hm : ∀ e, ∃ a : Label, ∃ c : ℂ, c ≠ 0 ∧ M.matrix e = c • asMatrix (E a) :=
     fun e => (safe_iff_mem _).mp (hM e)
   choose labels scalars hscalars hmatrix using hm
   refine ⟨labels,M.scalar*∏ e, scalars e,
     mul_ne_zero hw (Finset.prod_ne_zero_iff.mpr (fun e he => hscalars e)),?_⟩
   funext x
   simp only [Presentation.tensor,productValue,hmatrix,Matrix.smul_apply,smul_eq_mul,
     asMatrix,Matrix.of_apply,Finset.prod_mul_distrib,Matching.tensor,presentationMatching,mul_assoc]

 theorem scaled_matching_ne_zero {P : Type*} [DecidableEq P] {r : ℕ} (M : Matching P r)
     (labels : Fin r → Label) (c : ℂ) (hc : c ≠ 0) : (fun x => c*M.tensor labels x) ≠ 0 :=
   productValue_nonzero M.ports (fun e => asMatrix (E (labels e))) c (fun e => E_nonsingular _) hc

 theorem product_pair_fixed_matching {P : Type*} [DecidableEq P] {r : ℕ} (M : Matching P r)
     (labels : Fin r → Label) (weight : ℂ) (hw : weight ≠ 0) (u v : P) (huv : u ≠ v) :
     ∃ s : ℕ, ∃ R : Matching (Remaining u v) s, ∀ k : Label,
       contractPair u v (asMatrix (dual k)) (fun x => weight*M.tensor labels x) = 0 ∨
       ∃ fixed : Fin s → Label, ∃ c : ℂ, c ≠ 0 ∧
         contractPair u v (asMatrix (dual k)) (fun x => weight*M.tensor labels x) = fun x => c*R.tensor fixed x := by
   let A : Fin r → Binary (K := ℂ) := fun e => asMatrix (E (labels e))
   have hA : ∀ e, SafeBinary binaryGroup (A e) := fun e => E_safe _
   by_cases hpair : M.mate u = v
   · refine ⟨_,sameMatching M u v huv hpair,?_⟩
     intro k
     let P := samePresentation M u v huv hpair A weight (asMatrix (dual k))
     have he : contractPair u v (asMatrix (dual k)) (fun x => weight*M.tensor labels x) = P.tensor :=
       same_card_exact M u v huv hpair A weight (asMatrix (dual k))
     have hv : P.Valid binaryGroup :=
       same_presentation_valid binaryGroup_reversal M u v huv hpair A weight (asMatrix (dual k)) hA
     by_cases hz : P.scalar = 0
     · exact Or.inl (he.trans (presentation_zero_of_scalar_zero P hz))
     · obtain ⟨fixed,c,hc,hh⟩ := presentation_exotic_form P hv hz
       exact Or.inr ⟨fixed,c,hc,he.trans hh⟩
   · refine ⟨_,crossMatching M u v huv hpair,?_⟩
     intro k
     let P := crossPresentation M u v huv hpair A weight (asMatrix (dual k))
     have he : contractPair u v (asMatrix (dual k)) (fun x => weight*M.tensor labels x) = P.tensor :=
       cross_card_exact M u v huv hpair A weight (asMatrix (dual k))
     have hv : P.Valid binaryGroup :=
       cross_presentation_valid binaryGroup_projective X_mem binaryGroup_reversal M u v huv hpair
         A weight (asMatrix (dual k)) hA (dual_safe k)
     have hw' : P.scalar ≠ 0 := hw
     obtain ⟨fixed,c,hc,hh⟩ := presentation_exotic_form P hv hw'
     exact Or.inr ⟨fixed,c,hc,he.trans hh⟩

end MatchingCard

namespace Matching
variable {P : Type*} [Fintype P] [LinearOrder P] {r s : ℕ}

 theorem mate_eq_of_scaled_equality (M : Matching P r) (N : Matching P s)
     (labels : Fin r → Label) (fixed : Fin s → Label) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
     (he : (fun x => a*M.tensor labels x) = fun x => b*N.tensor fixed x) : M.mate = N.mate := by
   have hr : s = r := by
     have hM := M.port_card
     have hN := N.port_card
     omega
   subst s
   apply M.mate_eq_of_scaled_tensor N labels fixed (a⁻¹*b) (mul_ne_zero (inv_ne_zero ha) hb)
   funext x
   apply mul_left_cancel₀ ha
   have hx := congrFun he x
   calc
     a*M.tensor labels x = b*N.tensor fixed x := hx
     _ = a*(a⁻¹*b*N.tensor fixed x) := by
       rw [←mul_assoc,←mul_assoc,mul_inv_cancel₀ ha,one_mul]

end Matching
end
end Holant.Pauli.ExoticKlein
