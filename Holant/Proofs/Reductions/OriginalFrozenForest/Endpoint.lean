import Holant.Proofs.Reductions.OriginalFrozenForest.ForestCodec


noncomputable section
namespace Holant.LocalDrafts.Hardness.OriginalFrozenForest
open Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open FactorSaturation FrozenFactorNormalization
variable {L : Type} [Field L] [NumberField L] (φ : L →ₐ[ℚ] AlgebraicComplex)
variable {s : ℕ} {a : ℕ → ℕ} (G : (i : Fin s) → Signature L (a i.val))
variable (hI : Holant.LocalDrafts.FinitePGL2.Stabilization.RetainsIdentity (Set.range (fun i : Fin s =>
  (⟨a i.val,embedded φ G i⟩ : AnySignature AlgebraicComplex))))

def rootsToOriginal := (RootPreprocessing.reverse (embedded φ G) hI).compose
  (sourceToOriginal φ G).reduction

/-- Same chain, same forest, now with the genuine ORIGINAL L terminal. -/
def forestToOriginal : PolyTimeOracleReduction
    (catalogueEncoding φ G hI) (WholeForest.presentation (roots φ G hI)).encoding
    (originalEncoding (s:=s) (a:=a)) (originalPresentation (L:=L)).encoding
    (WholeForest.sourceValue (roots φ G hI)) (originalValue G) :=
  let D := roots φ G hI
  PrefixMachine.withTerminal (CommonField.table D.signature D.nonzero D.identity)
    (WholeForest.presentation D)
    ((CommonField.originalTransport D.signature D.nonzero D.identity).compose
      ((OriginalCodec.transport D).compose (rootsToOriginal φ G hI)))
    (WholeForest.chain D)

def publicToOriginal : PolyTimeOracleReduction
    (publicEncoding φ G hI) (publicPresentation (L:=L)).encoding
    (originalEncoding (s:=s) (a:=a)) (originalPresentation (L:=L)).encoding
    (publicValue φ G hI) (originalValue G) :=
  (publicToCoefficient φ G hI).compose
    ((toCatalogue φ G hI).compose
      ((catalogueToForest φ G hI).compose (forestToOriginal φ G hI)))

def originalToPublic : PolyTimeOracleReduction
    (originalEncoding (s:=s) (a:=a)) (originalPresentation (L:=L)).encoding
    (publicEncoding φ G hI) (publicPresentation (L:=L)).encoding
    (originalValue G) (publicValue φ G hI) :=
  (originalToSource φ G).compose
    ((RootPreprocessing.controlled (embedded φ G) hI).compose
      ((OriginalCodec.reverse (roots φ G hI)).compose
        ((forestToCatalogue φ G hI).compose
          ((fromCatalogue φ G hI).compose (publicFromCoefficient φ G hI).reduction))))

theorem equivalent :
    OracleReducible (publicEncoding φ G hI) (publicPresentation (L:=L)).encoding
      (originalEncoding (s:=s) (a:=a)) (originalPresentation (L:=L)).encoding
      (publicValue φ G hI) (originalValue G) ∧
    OracleReducible (originalEncoding (s:=s) (a:=a)) (originalPresentation (L:=L)).encoding
      (publicEncoding φ G hI) (publicPresentation (L:=L)).encoding
      (originalValue G) (publicValue φ G hI) :=
  ⟨⟨publicToOriginal φ G hI⟩,⟨originalToPublic φ G hI⟩⟩

theorem public_to_original_cost (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (originalEncoding (s:=s) (a:=a)) (originalPresentation (L:=L)).encoding
      (originalValue G) oracle)
    (r : ExactSignatureTables.Input (publicCount φ G hI) 1 (publicArity φ G hI)) :
    let M := publicToOriginal φ G hI
    ∃ t ≤ M.time.eval ((publicEncoding φ G hI).encode r).length,
      (fun c => c.bind (M.machine.step oracle))^[t]
        (some (M.machine.init ((publicEncoding φ G hI).encode r))) =
        some (M.machine.output ((publicPresentation (L:=L)).encoding.encode (publicValue φ G hI r))) ∧
      OracleBatch.primitiveCount M.machine oracle
        (M.machine.init ((publicEncoding φ G hI).encode r)) t ≤
        M.machine.primitiveBudget * M.time.eval ((publicEncoding φ G hI).encode r).length := by
  let M := publicToOriginal φ G hI
  let run := M.correct oracle ho r
  exact ⟨run.steps,run.steps_le_m,run.evals_in_steps,
    (OracleBatch.primitiveCount_le M.machine oracle
      (M.machine.init ((publicEncoding φ G hI).encode r)) run.steps).trans
      (Nat.mul_le_mul_left M.machine.primitiveBudget run.steps_le_m)⟩

theorem original_to_public_cost (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (publicEncoding φ G hI) (publicPresentation (L:=L)).encoding
      (publicValue φ G hI) oracle) (r : ExactSignatureTables.Input s 1 a) :
    let M := originalToPublic φ G hI
    ∃ t ≤ M.time.eval ((originalEncoding (s:=s) (a:=a)).encode r).length,
      (fun c => c.bind (M.machine.step oracle))^[t]
        (some (M.machine.init ((originalEncoding (s:=s) (a:=a)).encode r))) =
        some (M.machine.output ((originalPresentation (L:=L)).encoding.encode (originalValue G r))) ∧
      OracleBatch.primitiveCount M.machine oracle
        (M.machine.init ((originalEncoding (s:=s) (a:=a)).encode r)) t ≤
        M.machine.primitiveBudget * M.time.eval ((originalEncoding (s:=s) (a:=a)).encode r).length := by
  let M := originalToPublic φ G hI
  let run := M.correct oracle ho r
  exact ⟨run.steps,run.steps_le_m,run.evals_in_steps,
    (OracleBatch.primitiveCount_le M.machine oracle
      (M.machine.init ((originalEncoding (s:=s) (a:=a)).encode r)) run.steps).trans
      (Nat.mul_le_mul_left M.machine.primitiveBudget run.steps_le_m)⟩

end Holant.LocalDrafts.Hardness.OriginalFrozenForest
