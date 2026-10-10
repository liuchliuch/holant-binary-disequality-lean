import Holant.Proofs.Algorithms.TransformRecognition.AffineNormalForm


namespace Holant.LocalDrafts.MainChain.TransformRecognition.ExtensionAffine
open Holant.Tractable
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type*} [Field E] (φ : AlgebraicComplex →+* E)

def coefficient {n : ℕ} (C : AffineNormalForm.Code n) (x : Fin n → Bool) : AlgebraicComplex :=
  if AffineNormalForm.supportHolds C.1 x then fourthRootPhase ((AffineNormalForm.phase C.2).eval x) else 0

def formula {n : ℕ} (C : AffineNormalForm.Code n) (c : E) : Signature E n :=
  fun x => c * φ (coefficient C x)

def sourceFormula {n : ℕ} (c : E) (S : AffineSystem n) (Q : QuadraticPhase n) :
    Signature E n := fun x => if S.Holds x then c * φ (fourthRootPhase (Q.eval x)) else 0

/-- The same displayed source class, now with genuinely extension-valued scale. -/
def AffineOver {n : ℕ} (f : Signature E n) : Prop :=
  f=0 ∨ ∃ c : E, c ≠ 0 ∧ ∃ S : AffineSystem n, ∃ Q : QuadraticPhase n,
    f=sourceFormula φ c S Q

theorem sourceFormula_affine {n : ℕ} (c : E) (S : AffineSystem n) (Q : QuadraticPhase n) :
    AffineOver φ (sourceFormula φ c S Q) := by
  by_cases hc : c=0
  · left
    subst c
    funext x
    simp [sourceFormula]
  · exact Or.inr ⟨c,hc,S,Q,rfl⟩

theorem formula_source {n : ℕ} (C : AffineNormalForm.Code n) (c : E) :
    formula φ C c=sourceFormula φ c (AffineNormalForm.system C.1) (AffineNormalForm.phase C.2) := by
  funext x
  simp only [formula,coefficient,sourceFormula,AffineNormalForm.system_holds]
  split_ifs <;> simp

theorem compressed_source {n : ℕ} (c : E) (S : AffineSystem n) (Q : QuadraticPhase n) :
    formula φ (AffineNormalForm.compress S,AffineNormalForm.encodePhase Q) c=sourceFormula φ c S Q := by
  funext x
  simp only [formula,coefficient,sourceFormula,AffineNormalForm.compress_holds,AffineNormalForm.phase_eval]
  split_ifs <;> simp

theorem affine_iff {n : ℕ} (f : Signature E n) :
    AffineOver φ f ↔ ∃ C : AffineNormalForm.Code n, ∃ c : E, f=formula φ C c := by
  constructor
  · rintro (rfl | ⟨c,hc,S,Q,rfl⟩)
    · refine ⟨(∅,0,(fun _ => 0),(fun _ _ => false)),0,?_⟩
      funext x
      simp [formula]
    · exact ⟨(AffineNormalForm.compress S,AffineNormalForm.encodePhase Q),c,(compressed_source φ c S Q).symm⟩
  · rintro ⟨C,c,rfl⟩
    rw [formula_source]
    exact sourceFormula_affine φ c _ _

theorem formula_id {n : ℕ} (C : AffineNormalForm.Code n) (c : AlgebraicComplex) :
    formula (RingHom.id AlgebraicComplex) C c=AffineNormalForm.formula C c := by
  funext x
  exact (AffineNormalForm.entry_formula C c x).symm

theorem affine_id_iff {n : ℕ} (f : Signature AlgebraicComplex n) :
    AffineOver (RingHom.id AlgebraicComplex) f ↔ Affine f := by
  rw [affine_iff,AffineNormalForm.affine_iff]
  simp only [formula_id]

end
end Holant.LocalDrafts.MainChain.TransformRecognition.ExtensionAffine
