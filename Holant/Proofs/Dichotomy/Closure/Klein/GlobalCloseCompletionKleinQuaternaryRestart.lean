import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinNonrealDescent
import Holant.Proofs.Closure.ProgrammeSaturation
import Holant.Proofs.Closure.GroupPreparedStability
import Holant.Proofs.Closure.RetainedFinalAccess

/-! Any genuine nonmatching quaternary, including the real Gram and RM-phase
outputs, is installed with its complete exact
factor tree and sent through the actual current-group worklist. Every old
tree survives. The returned fresh stable exit has minimum arity four or a
strictly larger complete group; no future classification callback is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinQuaternaryRestart
open Holant Holant.Tractable Holant.Algebraic
open Holant.Certificates Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
namespace D
structure Output {s : ℕ} {a : ℕ→ℕ}
    (G : (i : Fin s)→Signature AlgebraicComplex (a i.val)) (P : Palette G) where
  q : Signature (OI.K G) 4
  actual : Gadget.Realizes P.family .disequality q
  nonmatching : ¬MatchingOrZero (actualTransfers P.family) q
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
attribute [local irreducible] GeneratedGroupWorklist.result

private theorem safe_back {L : Type*} [Field L] {F H : SignatureFamily L}
    (retained : F⊆H) (oldTorsion : ResidualTorsion F) (newTorsion : ResidualTorsion H)
    (same : completeGroup H newTorsion=completeGroup F oldTorsion)
    (B : Binary (K:=L)) (safe : SafeBinary (actualTransfers H) B) : SafeBinary (actualTransfers F) B := by
  obtain ⟨j,c,hc,he⟩ := safe_binary_eq_representative H newTorsion B safe
  obtain ⟨k,d,hd,hde⟩ := (frozen_representatives_cover_retained retained oldTorsion newTorsion same).2
    (actualRepresentative H newTorsion j) (actualRepresentative_actual H newTorsion j)
  refine ⟨actualRepresentative F oldTorsion k,actualRepresentative_actual F oldTorsion k,
    c*d,mul_ne_zero hc hd,?_⟩
  rw [he,hde,smul_smul]
  simp only [transfer,Matrix.smul_mul]

private theorem matching_back {L : Type*} [Field L] {F H : SignatureFamily L}
    (retained : F⊆H) (oldTorsion : ResidualTorsion F) (newTorsion : ResidualTorsion H)
    (same : completeGroup H newTorsion=completeGroup F oldTorsion)
    {n : ℕ} (f : Signature L n) (matching : MatchingOrZero (actualTransfers H) f) :
    MatchingOrZero (actualTransfers F) f := by
  rcases matching with zero|⟨M,valid,nonzero,equation⟩
  · exact Or.inl zero
  · exact Or.inr ⟨M,fun e=>safe_back retained oldTorsion newTorsion same _ (valid e),nonzero,equation⟩

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family) (d : D.Output G P)

theorem nonzero : d.q≠0 := fun zero=>d.nonmatching (Or.inl zero)
abbrev root : AnySignature (OI.K G) := ⟨4,d.q⟩
abbrev tree := RetainedFactorCatalogue.tree G (root G P d) (nonzero G P d)

abbrev installed : Palette G := ProgrammeSaturation.palette G P (root G P d) (nonzero G P d) (by change 0<4; decide) d.actual

def preparation : GeneratedGroupWorklist.Result G (installed G P d) := GeneratedGroupWorklist.result G (installed G P d)
abbrev finalSource := (preparation G P d).finalSource G (installed G P d)
abbrev finalPalette : Palette G := (finalSource G P d).palette

def oldLabel (i : Fin P.count) : Fin (finalPalette G P d).count :=
  (finalSource G P d).rootLabel (RetainedFactorCatalogue.oldLabel G P (root G P d) (nonzero G P d) i)

theorem oldLabel_injective : Function.Injective (oldLabel G P d) :=
  (finalSource G P d).rootInjective.comp (RetainedFactorCatalogue.oldLabel_injective G P (root G P d) (nonzero G P d))

theorem old_saved (i : Fin P.count) :
    Frontier.paletteRoot G (finalPalette G P d) (oldLabel G P d i)=Frontier.paletteRoot G P i :=
  ((finalSource G P d).rootSaved _).trans (ProgrammeSaturation.old_saved G P (root G P d)
    (nonzero G P d) (by change 0<4; decide) d.actual i)

theorem retains_old : P.family⊆(finalPalette G P d).family := by
  rintro f ⟨i,rfl⟩
  exact ⟨oldLabel G P d i,congrArg Sigma.fst (old_saved G P d i)⟩

def rootLabel : Fin (finalPalette G P d).count :=
  (finalSource G P d).rootLabel (RetainedFactorCatalogue.rootLabel G P (root G P d) (nonzero G P d))

theorem root_saved : Frontier.paletteRoot G (finalPalette G P d) (rootLabel G P d)=
    (⟨root G P d,tree G P d⟩ : TreeOccurrence (OI.K G)) :=
  ((finalSource G P d).rootSaved _).trans (ProgrammeSaturation.root_saved G P (root G P d)
    (nonzero G P d) (by change 0<4; decide) d.actual)

theorem leaves_retained (f : AnySignature (OI.K G)) (member : f∈(tree G P d).leaves) :
    f∈(finalPalette G P d).family := by
  have equality := congrArg (fun t : TreeOccurrence (OI.K G)=>t.2.leaves) (root_saved G P d)
  change ((finalPalette G P d).trees (rootLabel G P d)).leaves=(tree G P d).leaves at equality
  apply (finalPalette G P d).leavesRetained (rootLabel G P d) f
  rw [equality]
  exact member

include torsion in
theorem final_stable_minimum_or_growth (currentTorsion : ResidualTorsion (finalPalette G P d).family)
    {m : ℕ} (f : Signature (OI.K G) (m+2)) (proper : 2≤m) (even : Even (m+2))
    (core : MinimumCore (finalPalette G P d).family) (literal : core.signature=⟨m+2,f⟩)
    (noUnary : ¬RetainedUnary (finalPalette G P d).family) :
    m=2 ∨ completeGroup P.family torsion<completeGroup (finalPalette G P d).family currentTorsion := by
  classical
  by_cases small : m=2
  · exact Or.inl small
  right
  apply lt_of_le_of_ne (completeGroup_mono (retains_old G P d) torsion currentTorsion)
  intro same
  have large : 6≤core.signature.1 := by
    have hc := congrArg Sigma.fst literal
    change core.signature.1=m+2 at hc
    obtain ⟨k,hk⟩ := even
    omega
  have matching := retained_card_matching core (by decide : 0<4) large noUnary d.q (tree G P d)
    (leaves_retained G P d)
  exact d.nonmatching (matching_back (retains_old G P d) torsion currentTorsion same.symm d.q matching)

variable (oldCore : MinimumCore P.family)

include oldCore in
theorem installed_nonbinary : ∃f∈(installed G P d).family,Prime f∧3≤f.1 :=
  ⟨oldCore.signature,ProgrammeSaturation.retains_old G P (root G P d) (nonzero G P d) (by change 0<4; decide) d.actual oldCore.retained,
    oldCore.prime,oldCore.nonbinary⟩

def exit : StructuralExit G (finalPalette G P d) :=
  GroupPreparedStability.resultExit G (installed G P d) (preparation G P d) (installed_nonbinary G P d oldCore)

def exitAccess := RetainedFinalAccess.forStructuralExit G (finalPalette G P d) (exit G P d oldCore)

def Progress (E : StructuralExit G (finalPalette G P d)) : Prop := match E with
  | .stable m _ _ _ currentTorsion _ _ _ _ _ =>
      m=2 ∨ completeGroup P.family torsion<completeGroup (finalPalette G P d).family currentTorsion
  | _ => True

theorem progress_for_exit (E : StructuralExit G (finalPalette G P d)) : Progress G P torsion d E := by
  cases E with
  | unary => trivial
  | infinite => trivial
  | odd => trivial
  | stable m f proper even currentTorsion core literal noUnary noOdd matching =>
      exact final_stable_minimum_or_growth G P torsion d currentTorsion f proper even core literal noUnary

theorem progress : Progress G P torsion d (exit G P d oldCore) := progress_for_exit G P torsion d _


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinQuaternaryRestart
end
