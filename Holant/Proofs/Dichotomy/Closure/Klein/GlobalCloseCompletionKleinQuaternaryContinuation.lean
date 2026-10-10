import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinQuaternaryRestart
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinQuaternaryResolved

/-! An unchanged-group stable return from the actual arbitrary nonmatching q4 restart is
consumed by the completed small-four quaternary engine. Its common criterion
restricts to the entire old current family; other stable returns carry strict
actual group growth. The true structural stops remain the worklist's stops. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinQuaternaryContinuation
open Holant Holant.Tractable Holant.Algebraic
open Holant.Certificates Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
namespace D
export GlobalCloseCompletionKleinQuaternaryRestart.D (Output)
end D
namespace R
export GlobalCloseCompletionKleinQuaternaryRestart (finalPalette retains_old final_stable_minimum_or_growth)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

private theorem tractX_mono {F H : SignatureFamily AlgebraicComplex} (subset : F⊆H) (tract : TractX H) :
    TractX F := by
  have sub := preprocess_mono subset
  refine ⟨tract.1.subset sub,?_⟩
  rcases tract.2 with small|affine|product|localAffine
  · exact Or.inl (small.mono_family sub)
  · exact Or.inr (Or.inl (affine.mono_family sub))
  · exact Or.inr (Or.inr (Or.inl (product.mono_family sub)))
  · exact Or.inr (Or.inr (Or.inr (localAffine.mono_family sub)))

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family) (d : D.Output G P)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))

theorem tract_back (tract : GlobalCloseCompletionKleinEq4Source.CurrentTract G (R.finalPalette G P d)) :
    GlobalCloseCompletionKleinEq4Source.CurrentTract G P := by
  apply tractX_mono _ tract
  apply familyAction_mono
  rintro f ⟨g,hg,rfl⟩
  exact ⟨g,R.retains_old G P d hg,rfl⟩

include cardinal noncyclic in
theorem stable_classified_or_growth (currentTorsion : ResidualTorsion (R.finalPalette G P d).family)
    {m : ℕ} (f : Signature (OI.K G) (m+2)) (proper : 2≤m) (even : Even (m+2))
    (core : MinimumCore (R.finalPalette G P d).family) (literal : core.signature=⟨m+2,f⟩)
    (noUnary : ¬RetainedUnary (R.finalPalette G P d).family)
    (stable : ∀g∈rawDeck (R.finalPalette G P d).family currentTorsion f,
      MatchingOrZero (actualTransfers (R.finalPalette G P d).family) g) :
    GlobalCloseCompletionKleinEq4Source.CurrentTract G P ∨ GlobalCloseCompletionKleinEq4Source.Hard G ∨
      completeGroup P.family torsion<completeGroup (R.finalPalette G P d).family currentTorsion := by
  classical
  by_cases same : completeGroup (R.finalPalette G P d).family currentTorsion=completeGroup P.family torsion
  · have progress := R.final_stable_minimum_or_growth G P torsion d currentTorsion f proper even core literal noUnary
    have small : m=2 := by
      rcases progress with small|growth
      · exact small
      · rw [same] at growth
        exact (lt_irrefl _ growth).elim
    subst m
    have hc : Nat.card (completeGroup (R.finalPalette G P d).family currentTorsion)=4 := by rw [same];exact cardinal
    have hn : ¬IsCyclic (completeGroup (R.finalPalette G P d).family currentTorsion) := by rw [same];exact noncyclic
    rcases GlobalCloseCompletionKleinQuaternaryResolved.classified G (R.finalPalette G P d)
      currentTorsion hc hn f core literal stable with tract|hard
    · exact Or.inl (tract_back G P d tract)
    · exact Or.inr (Or.inl hard)
  · exact Or.inr (Or.inr (lt_of_le_of_ne
      (completeGroup_mono (R.retains_old G P d) torsion currentTorsion) (fun h=>same h.symm)))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinQuaternaryContinuation
end
