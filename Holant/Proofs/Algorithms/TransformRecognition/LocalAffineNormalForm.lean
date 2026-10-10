import Holant.Proofs.Algorithms.TransformRecognition.AffineNormalForm
import Holant.Proofs.Algorithms.LocalAffine.Twists


namespace Holant.LocalDrafts.MainChain.TransformRecognition.LocalAffineNormalForm
open Holant.Tractable
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Word (n : ℕ) := Fin n → Bool
abbrev Code (n : ℕ) := Finset (Word n) × (Word n → AffineNormalForm.Code n)
abbrev Parameters (n : ℕ) := Word n → AlgebraicComplex

def Matches {n : ℕ} (C : Code n) (c : Parameters n) (f : Signature AlgebraicComplex n) : Prop :=
  (∀ x, f x ≠ 0 ↔ x ∈ C.1) ∧
    ∀ alpha ∈ C.1, localTwist alpha f=AffineNormalForm.formula (C.2 alpha) (c alpha)

theorem matches_localAffine {n : ℕ} {C : Code n} {c : Parameters n}
    {f : Signature AlgebraicComplex n} (h : Matches C c f) : LocalAffine f := by
  intro alpha ha
  rw [h.2 alpha ((h.1 alpha).mp ha)]
  exact AffineNormalForm.formula_affine _ _

theorem localAffine_matches {n : ℕ} (f : Signature AlgebraicComplex n) (hf : LocalAffine f) :
    ∃ C : Code n, ∃ c : Parameters n, Matches C c f := by
  let masked (alpha : Word n) : Signature AlgebraicComplex n :=
    if f alpha ≠ 0 then localTwist alpha f else 0
  have ha (alpha : Word n) : Affine (masked alpha) := by
    unfold masked
    split_ifs with h
    · exact hf alpha h
    · exact affine_zero _
  have hex (alpha : Word n) := (AffineNormalForm.affine_iff (masked alpha)).mp (ha alpha)
  choose types scalars hs using hex
  refine ⟨(Finset.univ.filter (fun x => f x ≠ 0),types),scalars,?_,?_⟩
  · intro x
    simp
  · intro alpha halpha
    have hn : f alpha ≠ 0 := (Finset.mem_filter.mp halpha).2
    simpa [masked,hn] using hs alpha

theorem localAffine_iff {n : ℕ} (f : Signature AlgebraicComplex n) :
    LocalAffine f ↔ ∃ C : Code n, ∃ c : Parameters n, Matches C c f :=
  ⟨localAffine_matches f,fun ⟨_,_,h⟩ => matches_localAffine h⟩

def allCodes (n : ℕ) : Finset (Code n) := Finset.univ

theorem finite_enumeration {n : ℕ} (f : Signature AlgebraicComplex n) :
    LocalAffine f ↔ ∃ C ∈ allCodes n, ∃ c : Parameters n, Matches C c f := by
  simpa [allCodes] using localAffine_iff f

def coefficient {n : ℕ} (C : Code n) (alpha x : Word n) : AlgebraicComplex :=
  if AffineNormalForm.supportHolds (C.2 alpha).1 x then
    fourthRootPhase ((AffineNormalForm.phase (C.2 alpha).2).eval x) else 0

/-- Every condition is an equality or inequation of actual entries and
the bounded scalar parameters. Twisting contributes a fixed algebraic root
coefficient, not a fresh variable or an unknown support certificate. -/
theorem entry_constraints {n : ℕ} (C : Code n) (c : Parameters n)
    (f : Signature AlgebraicComplex n) : Matches C c f ↔
    (∀ x ∈ C.1, f x ≠ 0) ∧ (∀ x, x ∉ C.1 → f x=0) ∧
      ∀ alpha ∈ C.1, ∀ x,
        LocalAffineTwists.phaseWeight alpha x*f x=c alpha*coefficient C alpha x := by
  constructor
  · intro h
    refine ⟨fun x hx => (h.1 x).mpr hx,?_,?_⟩
    · intro x hx
      by_contra hn
      exact hx ((h.1 x).mp hn)
    · intro alpha ha x
      have he := congrFun (h.2 alpha ha) x
      simpa only [LocalAffineTwists.localTwist_formula,
        AffineNormalForm.entry_formula,coefficient] using he
  · rintro ⟨hn,hz,he⟩
    constructor
    · intro x
      constructor
      · intro hx
        by_contra hm
        exact hx (hz x hm)
      · exact hn x
    · intro alpha ha
      funext x
      simpa only [LocalAffineTwists.localTwist_formula,
        AffineNormalForm.entry_formula,coefficient] using he alpha ha x

theorem parameter_count (n : ℕ) : Fintype.card (Word n)=2^n := by
  simp [Word,Fintype.card_fun]

end
end Holant.LocalDrafts.MainChain.TransformRecognition.LocalAffineNormalForm
