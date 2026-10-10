import Holant.Marked.Basic

/-! Pairwise one-coordinate variation has one global varying coordinate.
This uses the actual factor-line equivalence relation, not an assumed common
factor or a quotient that erases endpoint orientation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureStableFactor
open Holant Holant.Marked

theorem global_varying_coordinate {I E A : Type*} [Nonempty E]
    (R : A → A → Prop) (symm : ∀ {a b},R a b → R b a)
    (trans : ∀ {a b c},R a b → R b c → R a c)
    (tables : I → E → A) (anchor : I)
    (distance : ∀ i j e d, e≠d → R (tables j e) (tables i e) ∨ R (tables j d) (tables i d)) :
    ∃ varying : E, ∀ i d, d≠varying → R (tables i d) (tables anchor d) := by
  classical
  by_cases all : ∀ i d, R (tables i d) (tables anchor d)
  · exact ⟨Classical.choice inferInstance,fun i d _ => all i d⟩
  · push Not at all
    obtain ⟨other,varying,disagree⟩ := all
    refine ⟨varying,?_⟩
    intro i d different
    have otherFixed : R (tables other d) (tables anchor d) :=
      (distance anchor other varying d different.symm).resolve_left disagree
    by_cases atVarying : R (tables i varying) (tables anchor varying)
    · have differentFromOther : ¬R (tables i varying) (tables other varying) := by
        intro same
        exact disagree (trans (symm same) atVarying)
      exact trans ((distance other i varying d different.symm).resolve_left differentFromOther) otherFixed
    · exact (distance anchor i varying d different.symm).resolve_left atVarying

/-- At least two literal residual edges leave one nonvarying coordinate.
All projective multipliers will subsequently be absorbed in the residual. -/
theorem fixed_coordinate {I E A : Type*} [Nontrivial E]
    (R : A → A → Prop) (symm : ∀ {a b},R a b → R b a)
    (trans : ∀ {a b c},R a b → R b c → R a c)
    (tables : I → E → A) (anchor : I)
    (distance : ∀ i j e d, e≠d → R (tables j e) (tables i e) ∨ R (tables j d) (tables i d)) :
    ∃ fixed : E, ∀ i, R (tables i fixed) (tables anchor fixed) := by
  obtain ⟨varying,constant⟩ := global_varying_coordinate R symm trans tables anchor distance
  obtain ⟨fixed,different⟩ := exists_ne varying
  exact ⟨fixed,fun i => constant i fixed different⟩

theorem projective_fixed_coordinate {I E : Type*} [Nontrivial E]
    (tables : I → E → Mat) (anchor : I)
    (distance : ∀ i j e d, e≠d →
      ProjectivelyEqual (tables j e) (tables i e) ∨ ProjectivelyEqual (tables j d) (tables i d)) :
    ∃ fixed : E, ∀ i, ProjectivelyEqual (tables i fixed) (tables anchor fixed) :=
  fixed_coordinate ProjectivelyEqual ProjectivelyEqual.symm ProjectivelyEqual.trans
    tables anchor distance

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureStableFactor
