import Holant.Proofs.Reductions.RootPreprocessing.ForestEndpoint
import Holant.Proofs.Reductions.FrozenFactorNormalization.PaletteCodec
import Holant.Proofs.Reductions.FrozenFactorNormalization.OriginalLCodec


noncomputable section
namespace Holant.LocalDrafts.Hardness.OriginalFrozenForest
open Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open FactorSaturation FrozenFactorNormalization GeneralExtraction
variable {L : Type} [Field L] [NumberField L] (φ : L →ₐ[ℚ] AlgebraicComplex)
variable {s : ℕ} {a : ℕ → ℕ} (G : (i : Fin s) → Signature L (a i.val))

abbrev embedded := OriginalLCodec.mapped φ G
variable (hI : RetainsIdentity (Set.range (fun i =>
  (⟨a i.val,embedded φ G i⟩ : AnySignature AlgebraicComplex))))
abbrev roots := RootPreprocessing.roots (embedded φ G) hI
abbrev rootCount := RootPreprocessing.count (embedded φ G)
abbrev oldCount := rootCount φ G + WholeForest.count (roots φ G hI)
abbrev oldArity := WholeForest.A (roots φ G hI)
abbrev oldTable := WholeForest.outputFamily (roots φ G hI)
abbrev oldAny := PaletteCodec.catalogue (oldTable φ G hI)

/-- Retained roots are literal original L tensors, with original index receipts. -/
def literal (i : Fin (rootCount φ G)) : AnySignature L :=
  let j := RootPreprocessing.includeLabel (embedded φ G) i
  ⟨a j.val,G j⟩
theorem literal_map (i : Fin (rootCount φ G)) :
    RH.mapAny φ.toRingHom (literal φ G i) = (roots φ G hI).signature i := rfl
def rootKey (i : Fin (rootCount φ G)) : KeyLift φ.toRingHom ((roots φ G hI).signature i) := by
  rw [←literal_map φ G hI i]
  exact KeyLift.ofLiteral φ.toRingHom (literal φ G i)

/-- This definition traverses the existing FactorSaturation.tree slots. -/
def storedKey (i : Fin (oldCount φ G hI)) : KeyLift φ.toRingHom (oldAny φ G hI i) :=
  catalogueLift φ.toRingHom (roots φ G hI).signature (roots φ G hI).nonzero
    (rootKey φ G hI) i
theorem storedKey_exact (i : Fin (oldCount φ G hI)) :
    RH.mapSignature φ.toRingHom (storedKey φ G hI i).table = canonicalKey (oldTable φ G hI i) :=
  (storedKey φ G hI i).equation

def rootToOld (i : Fin (rootCount φ G)) : Fin (oldCount φ G hI) := ⟨i.val,by
  change i.val < rootCount φ G + WholeForest.count (roots φ G hI)
  exact Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)⟩
theorem literal_old (i : Fin (rootCount φ G)) :
    RH.mapAny φ.toRingHom (literal φ G i) = oldAny φ G hI (rootToOld φ G hI i) := by
  rw [literal_map]
  exact (lookup_old (roots φ G hI).signature (roots φ G hI).nonzero i).symm
theorem old_nonzero (i : Fin (oldCount φ G hI)) : oldTable φ G hI i≠0 :=
  (WholeForest.output_preprocessed (roots φ G hI) _ ⟨i,rfl⟩).2
theorem old_positive (i : Fin (oldCount φ G hI)) : 0 < oldArity φ G hI i.val :=
  (WholeForest.output_preprocessed (roots φ G hI) _ ⟨i,rfl⟩).1

/-- The original root tree or an actual stored subtree, never exists_factorTree again. -/
def actualTree (i : Fin (oldCount φ G hI)) : FactorTree (oldAny φ G hI i) :=
  catalogueTree (roots φ G hI).signature (roots φ G hI).nonzero i
theorem actualTree_leaves (i : Fin (oldCount φ G hI)) :
    ∀ f ∈ (actualTree φ G hI i).leaves, f ∈ Set.range (oldAny φ G hI) :=
  catalogueTree_leaves (roots φ G hI).signature (roots φ G hI).nonzero i

theorem kept_original (i : Fin s) (hi : RootPreprocessing.Keep (embedded φ G) i) :
    literal φ G (RootPreprocessing.compact (embedded φ G) i hi) = ⟨a i.val,G i⟩ := by
  exact congrArg (fun j : Fin s => (⟨a j.val,G j⟩ : AnySignature L))
    (RootPreprocessing.include_compact (embedded φ G) i hi)

end Holant.LocalDrafts.Hardness.OriginalFrozenForest
