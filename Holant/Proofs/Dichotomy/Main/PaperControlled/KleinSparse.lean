import Holant.Proofs.Dichotomy.Main.PaperControlled.StableCurrentEvenEOHardness
import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.KleinEq4Source
import Holant.Proofs.Dichotomy.Closure.Macro.GlobalCloseCompletionMacroFamily
import Holant.Proofs.Closure.ClosureSourceRowsKleinNative

/-! A sparse actual standard-Klein q4 closes the whole current family. The
finite current deck derives parity and complementary support; a literal missing
word selects the real I-flip EO graph. Its actual EO test yields hardness or
an actual scalar-Eq4 graph, immediately consumed by the whole-family source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.KleinSparse
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked Holant.Marked.SupportAtlas
open Holant.Certificates.EqualityQuaternary
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace S
export PaperControlled.KleinEq4Source (mapped identityLabel identity_literal CurrentTract Hard classified)
end S
namespace T
export StableCurrentEvenEOTransport (embedded graph_uses eo_of_missing_parity_word)
end T
namespace M
export GlobalCloseCompletionMacroFamily (labels labels_exact)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)

include core literal in
theorem sparse_closed_classified (mask : Word)
    (supported : ∀x,T.embedded G q x≠0 → parity x=parity mask)
    (missing : T.embedded G q mask=0)
    (closed : ∀x,T.embedded G q (complement x)=0 ↔ T.embedded G q x=0) :
    S.CurrentTract G P ∨ S.Hard G := by
  classical
  let graph := Flip.network (T.embedded G q) mask
  let uses := T.graph_uses G P q core literal mask
  let access := ClosurePhysicalBridge.fromNetwork G P (ClosureSourceRows.embedding G) graph uses (Flip.native _ _)
  have eo : DenseEOUnitLocal.EOSupport graph.denote := by
    rw [Flip.denote]
    exact T.eo_of_missing_parity_word _ mask supported missing ((closed mask).mpr missing)
  have prime : TensorPrime graph.denote := by
    rw [Flip.denote]
    exact flip_prime (ClosureSourceRows.core_ambient_prime G P q core literal) mask
  have complementary : ∀x,graph.denote (complementWord x)=0 ↔ graph.denote x=0 := by
    intro x
    rw [Flip.denote]
    change T.embedded G q (xorWord (complementWord x) mask)=0 ↔ _
    rw [StableCurrentEvenEOTract.xorWord_complement]
    exact closed _
  by_cases tract : EOTract {⟨4,graph.denote⟩}
  · obtain ⟨C,member,_⟩ := StableCurrentEvenEOTract.eoTract_actual_class graph.denote eo complementary tract
    have usesFinite : ∀v,∃j : Fin P.count,
        (⟨P.arity j.val,S.mapped G P j⟩ : AnySignature AlgebraicComplex)=⟨graph.shape.arity v,graph.vertex v⟩ := by
      intro v
      obtain ⟨g,⟨i,rfl⟩,he⟩ := uses v
      exact ⟨i,he⟩
    obtain ⟨d⟩ := GlobalCloseCompletionBPrimeEq4.class_output (S.mapped G P)
      (S.identityLabel G P) (S.identity_literal G P) graph (M.labels G P graph usesFinite)
      (M.labels_exact G P graph usesFinite) (Flip.native _ _) eo prime complementary C member
    exact S.classified G P d
  · right
    apply PaperControlled.StableCurrentEvenEOHardness.witnessCountingHard G P graph uses access
    · rw [StableCurrentEvenEOHardness.mappedOutput,access.mappedOutput]
      exact eo
    · rw [StableCurrentEvenEOHardness.mappedOutput,access.mappedOutput]
      exact tract

variable (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureSourceRows.nativeKleinKind G P torsion cardinal noncyclic=.standard)

private def coverage : ClosureSourceRows.KleinCoverage G P torsion .standard := by
  rw [←standard]
  exact ClosureSourceRows.nativeKleinResources G P torsion cardinal noncyclic

private def representatives : Klein.Representatives (ClosureSourceRows.ambientFamily G P) .standard where
  matrix k := ClosureSourceRows.representative G P torsion
    (ClosureSourceRows.kleinIndex G P torsion .standard (coverage G P torsion cardinal noncyclic standard) k).key
  multiplier k := ClosureSourceRows.embedding G
    (ClosureSourceRows.kleinIndex G P torsion .standard (coverage G P torsion cardinal noncyclic standard) k).coefficient
  multiplier_ne_zero k := (map_ne_zero _).mpr
    (ClosureSourceRows.kleinIndex G P torsion .standard (coverage G P torsion cardinal noncyclic standard) k).nonzero
  actual k := ClosureSourceRows.representative_actual G P torsion _
  normal_form k := (ClosureSourceRows.kleinIndex G P torsion .standard
    (coverage G P torsion cardinal noncyclic standard) k).normal

include torsion cardinal noncyclic standard core literal in
theorem standard_sparse_classified
    (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)
    (noDense : ¬∃p : Bool,∀x,T.embedded G q x≠0 ↔ parity x=p) :
    S.CurrentTract G P ∨ S.Hard G := by
  classical
  have physical : Klein.PhysicalDeck (representatives G P torsion cardinal noncyclic standard) (T.embedded G q) :=
    ClosureSourceRows.klein_sourceDeck G P torsion .standard (coverage G P torsion cardinal noncyclic standard)
      q core literal stable
  obtain ⟨j,parityRule,complementRule⟩ := Klein.source_standard_planes _ (T.embedded G q) physical
  have sign : Klein.standardSign j≠0 := by
    unfold Klein.standardSign
    split_ifs <;> norm_num
  have supported : ∀x,T.embedded G q x≠0 → parity x=Klein.standardParity j := by
    intro x hx
    by_contra h
    exact hx (parityRule x h)
  have closed : ∀x,T.embedded G q (complement x)=0 ↔ T.embedded G q x=0 := by
    intro x
    rw [complementRule]
    simp [sign]
  have absent : ∃mask : Word,parity mask=Klein.standardParity j ∧ T.embedded G q mask=0 := by
    by_contra h
    push Not at h
    exact noDense ⟨_,fun x=>⟨supported x,h x⟩⟩
  obtain ⟨mask,same,missing⟩ := absent
  exact sparse_closed_classified G P q core literal mask (fun x hx=>(supported x hx).trans same.symm) missing closed


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.KleinSparse
end
