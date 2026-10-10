import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramCertificate
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramAnalysis

/-! A real Gram matrix that is a literal Pauli matching is either a positive
scalar identity or comes from a rank-one input matrix. The finite table guard
is derived from positivity, not supplied by the caller. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinGramPauli
namespace C
export GlobalCloseCompletionKleinGramCertificate (entry rowCondition conclusion certificate)
end C
namespace A
export GlobalCloseCompletionKleinGramAnalysis (gram symmetric diagonal_nonnegative zero_row positive_diagonal factor_of_minors)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {J : Type*} [Fintype J]
variable (M : Fin 4→J→ℝ) (p : Fin 4→Fin 4) (injective : Function.Injective p)
variable (a b : Fin 4) (c : ℝ) (hc : c≠0)
variable (equation : ∀i j,A.gram M i j=c*(C.entry p a b i j : ℝ))

include hc equation in
theorem row_condition : C.rowCondition p a b := by
  constructor
  · intro i zero j
    have h : A.gram M i i=0 := by rw [equation,zero,Int.cast_zero,mul_zero]
    have hz := A.zero_row M i h j
    rw [equation] at hz
    have integer_zero : (C.entry p a b i j : ℝ)=0 := (mul_eq_zero.mp hz).resolve_left hc
    exact_mod_cast integer_zero
  · intro i j
    have hi := A.diagonal_nonnegative M i
    have hj := A.diagonal_nonnegative M j
    rw [equation] at hi hj
    have h : 0≤(c*c)*((C.entry p a b i i : ℝ)*(C.entry p a b j j : ℝ)) := by
      nlinarith [mul_nonneg hi hj]
    have positive : 0<c*c := mul_self_pos.mpr hc
    have h' := (mul_nonneg_iff_of_pos_left positive).mp h
    exact_mod_cast h'

include injective hc equation in
theorem orthogonal_or_factor (i₀ : Fin 4) (j₀ : J) (nonzero : M i₀ j₀≠0) :
    (∃d : ℝ,0<d ∧ ∀i j,A.gram M i j=if i=j then d else 0) ∨
      ∃u : Fin 4→ℝ,∃v : J→ℝ,∀i j,M i j=u i*v j := by
  rcases C.certificate p injective a b (row_condition M p a b c hc equation) with scalar|minors
  · obtain ⟨s,hs⟩ := scalar
    let d : ℝ := c*(if s=0 then 1 else -1)
    have hd : d≠0 := mul_ne_zero hc (by split_ifs <;> norm_num)
    have value (i j : Fin 4) : A.gram M i j=if i=j then d else 0 := by
      rw [equation,hs]
      split_ifs <;> simp_all [d]
    have positive : 0<d := by
      have h := A.diagonal_nonnegative M 0
      rw [value,if_pos rfl] at h
      exact lt_of_le_of_ne h (Ne.symm hd)
    exact Or.inl ⟨d,positive,value⟩
  · right
    apply A.factor_of_minors M i₀ j₀ nonzero
    intro i k
    have integer : (C.entry p a b i k : ℝ)*(C.entry p a b i₀ i₀ : ℝ)=
        (C.entry p a b i i₀ : ℝ)*(C.entry p a b i₀ k : ℝ) := by
      exact_mod_cast minors i k i₀ i₀
    rw [←A.symmetric M i₀ k]
    simp only [equation]
    calc
      (c*(C.entry p a b i k : ℝ))*(c*(C.entry p a b i₀ i₀ : ℝ))=
          c^2*((C.entry p a b i k : ℝ)*(C.entry p a b i₀ i₀ : ℝ)) := by ring
      _=c^2*((C.entry p a b i i₀ : ℝ)*(C.entry p a b i₀ k : ℝ)) := by rw [integer]
      _=_ := by ring


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinGramPauli
end
