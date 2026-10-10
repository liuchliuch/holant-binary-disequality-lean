import Holant.Proofs.Closure.ClosureBStableSix

/-! The actual literal B stable prime core is necessarily quaternary.
The six-port base and higher fixed-factor reconstruction cover every remaining
even arity. This is an arity refinement of the CURRENT structural exit, not a
whole-family classification or a global complexity conclusion. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureBStableCore
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

private theorem even_core_cases (m : ℕ) (proper : 2 ≤ m) (even : Even (m+2)) :
    m=2 ∨ m=4 ∨ ∃ r : ℕ, 2 ≤ r ∧ m=2*r+2 := by
  rcases even with ⟨k,hk⟩
  by_cases two : m=2
  · exact Or.inl two
  by_cases four : m=4
  · exact Or.inr (Or.inl four)
  have large : 4 ≤ k := by omega
  exact Or.inr (Or.inr ⟨k-2,by omega,by omega⟩)

/-- No factor, root-pencil classification or localization policy is input:
both forbidden arity ranges use their closed CURRENT-deck constructions. -/
theorem stable_prime_residual_eq_two (P : Palette G) (torsion : ResidualTorsion P.family)
    (N : ClosureMarkedDihedralB.NativeB
      (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
    {m : ℕ} (f : Signature (OI.K G) (m+2)) (proper : 2 ≤ m)
    (even : Even (m+2)) (prime : Prime (⟨m+2,f⟩ : AnySignature (OI.K G)))
    (stable : ∀ g ∈ rawDeck P.family torsion f, MatchingOrZero (actualTransfers P.family) g) : m=2 := by
  rcases even_core_cases m proper even with two | four | ⟨r,large,shape⟩
  · exact two
  · subst m
    exact False.elim (ClosureBStable.current_six_not_prime G P torsion N f prime.1 stable prime)
  · subst m
    exact False.elim (ClosureBStable.current_nativeB_not_prime G P torsion N f
      (Equiv.refl _) stable large prime)

/-- For every literal B model of a returned stable CURRENT family, the recorded
minimum has residual arity2, hence full arity4. Other exits keep their domain. -/
def ForExit (P : Palette G) (E : StructuralExit G P) : Prop :=
  match E with
  | .stable m _ _ _ torsion _ _ _ _ _ =>
      ∀ _N : ClosureMarkedDihedralB.NativeB
        (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion), m=2
  | _ => True

theorem forExit (P : Palette G) (E : StructuralExit G P) : ForExit G P E := by
  cases E with
  | unary => trivial
  | infinite => trivial
  | odd => trivial
  | stable m f proper even torsion core hcore noUnary noOdd stable =>
      intro N
      apply stable_prime_residual_eq_two G P torsion N f proper even
      · simpa only [hcore] using core.prime
      · exact stable

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureBStableCore
end
