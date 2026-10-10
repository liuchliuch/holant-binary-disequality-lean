import Holant.Certificates.RainbowOrbit.ExternalGroup

/-! Two-way comparison with the literal displayed source set, including every
choice of the two independent signs. -/
namespace Holant.Certificates.RainbowOrbit.External
noncomputable section
open Holant.Certificates.OctahedralSeparator
open Holant.Certificates.MatchingProductBridge
set_option backward.isDefEq.respectTransparency false

/-- The four plus eight representatives of eq:external-a4-domain. -/
def PrintedBase (U : Matrix Bool Bool ℂ) : Prop :=
  U = complexMatrix (q 0) ∨ U = complexMatrix (q 1) ∨
  (∃ b : Bool, U = complexMatrix (q 2+ms (scalarSign b) (q 3))) ∨
  ∃ ε δ : Bool,
    U = complexMatrix (q 0+ms (scalarSign ε) (q 1)+ms (scalarSign δ*root) (q 2)) ∨
    U = complexMatrix (q 0+ms (scalarSign ε) (q 1)+ms (scalarSign δ*root) (q 3))

/-- This states the source display using its actual Pauli matrices and sqrt(2). -/
theorem printedBase_literal (U : Matrix Bool Bool ℂ) : PrintedBase U ↔
    U = Matrix.of Q0 ∨ U = Matrix.of Q1 ∨
    (∃ b : Bool, U = Matrix.of Q2+(signBit b : ℂ) • Matrix.of Q3) ∨
    ∃ ε δ : Bool,
      U = Matrix.of Q0+(signBit ε : ℂ) • Matrix.of Q1+
        ((signBit δ : ℂ)*(Real.sqrt 2 : ℂ)) • Matrix.of Q2 ∨
      U = Matrix.of Q0+(signBit ε : ℂ) • Matrix.of Q1+
        ((signBit δ : ℂ)*(Real.sqrt 2 : ℂ)) • Matrix.of Q3 := by
  simp only [PrintedBase,complexMatrix_add,complexMatrix_ms,complexMatrix_q,
    embed_scalarSign,embed_mul,root,embed_coeff,rootTwo,quaternionBasis]
  norm_num

theorem printedScalar_complex {U : Mat} (h : PrintedScalar U) : PrintedBase (complexMatrix U) := by
  rcases h with rfl | rfl | ⟨b,rfl⟩ | ⟨ε,δ,h | h⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl ⟨b,rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ε,δ,Or.inl (congrArg complexMatrix h)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ε,δ,Or.inr (congrArg complexMatrix h)⟩))

theorem displayed_base (k : Fin 12) : PrintedBase (complexMatrix (displayed k)) :=
  printedScalar_complex (displayed_printed k)

theorem printedBase_complete {U : Matrix Bool Bool ℂ} (h : PrintedBase U) :
    ∃ k : Fin 12, U = complexMatrix (displayed k) := by
  rcases h with rfl | rfl | ⟨b,rfl⟩ | ⟨ε,δ,h | h⟩
  · obtain ⟨k,h⟩ := printed_covers_Q0
    exact ⟨k,congrArg complexMatrix h.symm⟩
  · obtain ⟨k,h⟩ := printed_covers_Q1
    exact ⟨k,congrArg complexMatrix h.symm⟩
  · obtain ⟨k,h⟩ := printed_covers_pairs b
    exact ⟨k,congrArg complexMatrix h.symm⟩
  · obtain ⟨k,hk⟩ := printed_covers_signs2 ε δ
    exact ⟨k,h.trans (congrArg complexMatrix hk.symm)⟩
  · obtain ⟨k,hk⟩ := printed_covers_signs3 ε δ
    exact ⟨k,h.trans (congrArg complexMatrix hk.symm)⟩

theorem representative_displayed (k : Fin 12) :
    representative k = embed (displayScale k) • complexMatrix (displayed k) := by
  rw [representative,raw_displayed,complexMatrix_ms]

/-- Equality of the whole complex projective sets, not just a subset check. -/
theorem direction_iff_printed (U : Matrix Bool Bool ℂ) : Direction U ↔
    ∃ c : ℂ, c ≠ 0 ∧ ∃ V : Matrix Bool Bool ℂ, PrintedBase V ∧ U = c • V := by
  constructor
  · rintro ⟨k,c,hc,rfl⟩
    refine ⟨c*embed (displayScale k),mul_ne_zero hc (embed_ne_zero (displayScale_ne_zero k)),
      complexMatrix (displayed k),displayed_base k,?_⟩
    rw [representative_displayed,smul_smul]
  · rintro ⟨c,hc,V,hV,rfl⟩
    obtain ⟨k,rfl⟩ := printedBase_complete hV
    refine ⟨k,c*(embed (displayScale k))⁻¹,
      mul_ne_zero hc (inv_ne_zero (embed_ne_zero (displayScale_ne_zero k))),?_⟩
    rw [representative_displayed,smul_smul]
    congr 1
    field_simp [embed_ne_zero (displayScale_ne_zero k)]

/-- All the literal displayed directions, with no exhaustive classification hypothesis. -/
theorem literal_external_dictionary :
    (∀ i : Fin 12, PrintedBase (complexMatrix (displayed i))) ∧
    (∀ U : Matrix Bool Bool ℂ, PrintedBase U → ∃ i : Fin 12, U = complexMatrix (displayed i)) ∧
    (∀ i j : Fin 12, ∀ c : ℂ, representative i = c • representative j → i=j) ∧
    Direction (Matrix.of X) ∧ ¬ Direction (Matrix.of Q2) ∧ ¬ Direction (Matrix.of Q3) :=
  ⟨displayed_base,fun _ h => printedBase_complete h,projectively_injective,
    direction_X,not_direction_Q2,not_direction_Q3⟩

end
end Holant.Certificates.RainbowOrbit.External
