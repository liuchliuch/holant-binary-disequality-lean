import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationAlgebra

/-! Normalization is semantic scalar bookkeeping. The actual circuit keeps
the original nonzero corner and all four-copy scale factors. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationScale
open Holant
namespace A
export GlobalCloseCompletionComplementQ4ClassificationAlgebra (outerLeft outerRight middle Paired alternatives)
end A
namespace S
export GlobalCloseCompletionComplementQ4Series (row)
end S
set_option maxHeartbeats 600000
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

theorem left_scale (a b c d : K) (ha : a≠0) :
    A.outerLeft a b c d=a^4*A.outerLeft 1 (b/a) (c/a) (d/a) := by
  unfold A.outerLeft
  field_simp
  <;> ring

theorem right_scale (a b c d : K) (ha : a≠0) :
    A.outerRight a b c d=a^4*A.outerRight 1 (b/a) (c/a) (d/a) := by
  unfold A.outerRight
  field_simp
  <;> ring

theorem nonzero_lift (a b c d : K) (ha : a≠0)
    (h : A.outerLeft 1 (b/a) (c/a) (d/a)^2≠A.outerRight 1 (b/a) (c/a) (d/a)^2) :
    A.outerLeft a b c d ^2≠A.outerRight a b c d ^2 := by
  intro e
  rw [left_scale a b c d ha,right_scale a b c d ha,mul_pow,mul_pow] at e
  exact h (mul_left_cancel₀ (pow_ne_zero _ (pow_ne_zero _ ha)) e)

theorem alternatives (a b c d : K) (ha : a≠0) (hb : b≠0) (hd : d≠0) :
    A.Paired (b/a) (c/a) (d/a) ∨
      ∃u v w : K, (u=b ∧ v=c ∧ w=d ∨ u=d ∧ v=c ∧ w=b ∨ u=b ∧ v=d ∧ w=c) ∧
        A.outerLeft a u v w ^2≠A.outerRight a u v w ^2 := by
  rcases A.alternatives (b/a) (c/a) (d/a) (div_ne_zero hb ha) (div_ne_zero hd ha) with paired|⟨u,v,w,chart,live⟩
  · exact Or.inl paired
  · right
    rcases chart with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
    · exact ⟨b,c,d,Or.inl ⟨rfl,rfl,rfl⟩,nonzero_lift a b c d ha live⟩
    · exact ⟨d,c,b,Or.inr (Or.inl ⟨rfl,rfl,rfl⟩),nonzero_lift a d c b ha live⟩
    · exact ⟨b,d,c,Or.inr (Or.inr ⟨rfl,rfl,rfl⟩),nonzero_lift a b d c ha live⟩

theorem row_smul (a b c d t : K) : t • S.row a b c d=S.row (t*a) (t*b) (t*c) (t*d) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [S.row,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3]

theorem normalized (a b c d : K) (ha : a≠0) :
    S.row a b c d=a • S.row 1 (b/a) (c/a) (d/a) := by
  rw [row_smul,mul_one]
  congr 1 <;> field_simp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationScale
end
