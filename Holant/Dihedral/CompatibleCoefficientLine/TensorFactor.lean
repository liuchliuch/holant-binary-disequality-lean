import Holant.Dihedral.CompatibleCoefficientLine.Factor

/-! The inversion conclusion is the literal tensor product on the original
ordered edge and complementary ports, using an explicit finite port bijection. -/
noncomputable section
namespace Holant.Dihedral.CompatibleCoefficientLine
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure

/-- The common original edge is ports 2,3; the complement retains 0,1,4,... . -/
def factorPorts (n : ℕ) : Fin 2 ⊕ Fin (n+2) ≃ Fin (n+4) where
  toFun z := match z with
    | .inl i => ⟨i.val+2,by omega⟩
    | .inr i => if h : i.val<2 then ⟨i.val,by omega⟩ else ⟨i.val+2,by omega⟩
  invFun i := if h : i.val<2 then .inr ⟨i.val,by omega⟩
    else if h' : i.val<4 then .inl ⟨i.val-2,by omega⟩
    else .inr ⟨i.val-2,by omega⟩
  left_inv := by
    rintro (i|i)
    · have h₂ : ¬ (i.val+2<2) := by omega
      have h₄ : i.val+2<4 := by omega
      simp [h₂,h₄]
    · by_cases h : i.val<2
      · simp [h]
      · have h₂ : ¬ (i.val+2<2) := by omega
        have h₄ : ¬ (i.val+2<4) := by omega
        simp [h,h₂,h₄]
  right_inv := by
    intro i
    by_cases h₂ : i.val<2
    · simp [h₂]
    · by_cases h₄ : i.val<4
      · have h : i.val-2<2 := by omega
        simp [h₂,h₄,h]
        apply Fin.ext
        simp
        omega
      · have h : ¬ (i.val-2<2) := by omega
        simp [h₂,h₄,h]
        apply Fin.ext
        simp
        omega

private theorem factorPorts_left (n : ℕ) (i : Fin 2) :
    factorPorts n (.inl i) = ⟨i.val+2,by omega⟩ := rfl
private theorem factorPorts_right_zero (n : ℕ) : factorPorts n (.inr 0) = 0 := rfl
private theorem factorPorts_right_one (n : ℕ) : factorPorts n (.inr 1) = 1 := rfl
private theorem factorPorts_right_succ_succ (n : ℕ) (i : Fin n) :
    factorPorts n (.inr i.succ.succ) = i.succ.succ.succ.succ := by
  apply Fin.ext
  simp [factorPorts]

/-- The pointwise reconstructed slices give f=B_e tensor h with a literal
reindexing, not merely a projective equality or matching support statement. -/
theorem tensor_factor_of_slices {n : ℕ} (f : Signature Scalar (n+4)) (B : Mat)
    (h : Signature Scalar (n+2))
    (he : ∀ a b c d x, f (pair a b (pair c d x)) = B c d * h (pair a b x)) :
    f = Tensor.reindex (factorPorts n) (Tensor.tensor (Tractable.kernelSignature B) h) := by
  funext x
  have hx : pair (x 0) (x 1) (pair (tail x 0) (tail x 1) (tail (tail x))) = x := by
    rw [pair_eta,pair_eta]
  have hh := he (x 0) (x 1) (tail x 0) (tail x 1) (tail (tail x))
  rw [hx] at hh
  rw [hh]
  change B _ _ * h _ = B _ _ * h _
  congr 1
  apply congrArg h
  funext i
  change pair (x 0) (x 1) (tail (tail x)) i = x (factorPorts n (.inr i))
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · rw [factorPorts_right_zero]
    rfl
  · change _ = x (factorPorts n (.inr 1))
    rw [factorPorts_right_one]
    rfl
  · rw [factorPorts_right_succ_succ]
    rfl

theorem source_genuine_tensor_factor {n r : ℕ} {F : SignatureFamily Scalar} {t₀ t₁ : Scalar}
    {f : Signature Scalar (n+4)} (D : FourProducts (r:=r) F t₀ t₁ f)
    (ht : t₀ ≠ t₁) (B : Mat) (hB : IsMonomial B)
    (hline : ∀ i, ProjectivelyEqual (D.factors i (D.edge i)) B) :
    ∃ h : Signature Scalar (n+2), IsMonomial B ∧
      f = Tensor.reindex (factorPorts n) (Tensor.tensor (Tractable.kernelSignature B) h) := by
  obtain ⟨h,hB,hh⟩ := source_genuine_factor D ht B hB hline
  exact ⟨h,hB,tensor_factor_of_slices f B h hh⟩

end Holant.Dihedral.CompatibleCoefficientLine
