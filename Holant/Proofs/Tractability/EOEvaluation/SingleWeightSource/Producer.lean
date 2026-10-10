import Holant.Proofs.Tractability.EOEvaluation.OneSidedSource.Producer
import Holant.Proofs.Reductions.SingleWeightCompletion.OptionalQuery


namespace Holant.LocalDrafts.Tractability.EOEvaluation.SingleWeightSource.Producer
open Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
    (Gamma : SignatureFamily AlgebraicComplex)
    (hmem : ∀ i, (⟨arity i.val, G i⟩ : AnySignature AlgebraicComplex) ∈ Gamma)
    (h : SingleWeightAlternative (preprocess Gamma))

abbrev native := KSourceTransport.nativeSignatures G

/-- This is fixed finite alphabet data, never a runtime witness supplied to
the graph machine. Zero labels and nullary labels take the literal layer 0. -/
def layer (i : Fin s) : ℕ :=
  if hz : G i = 0 then 0
  else if hp : 0 < arity i.val then
    Classical.choose (h.1 _ (OneSidedSource.Producer.native_member G Gamma hmem i hp hz))
  else 0

theorem layer_zero (i : Fin s) (hz : G i = 0) : layer G Gamma hmem h i = 0 := by
  simp [layer, hz]

theorem layer_nullary (i : Fin s) (ha : arity i.val = 0) : layer G Gamma hmem h i = 0 := by
  simp [layer, ha]

theorem layer_spec (i : Fin s) :
    Signature.SingleLayer (native G i) (layer G Gamma hmem h i) := by
  dsimp only [layer]
  split_ifs with hz hp
  · intro x _
    simp [native, KSourceTransport.nativeSignatures, InvertibleKernel.action, hz]
  · exact Classical.choose_spec
      (h.1 _ (OneSidedSource.Producer.native_member G Gamma hmem i hp hz))
  · intro x hx
    have hw := Holant.weight_le x
    have hw0 : Holant.weight x = 0 := by omega
    exact False.elim (hx hw0)

abbrev completedArity := SingleWeightCompletion.arity (a := arity) (layer G Gamma hmem h)
abbrev completedTable := SingleWeightCompletion.table (native G) (layer G Gamma hmem h)
abbrev count := RootPreprocessing.count (completedTable G Gamma hmem h)
abbrev targetArity := RootPreprocessing.targetArity (completedTable G Gamma hmem h)
abbrev targetTable := RootPreprocessing.targetTable (completedTable G Gamma hmem h)
abbrev Input := ExactSignatureTables.Input s 1 arity

theorem completed_nullary (i : Fin s) (ha : arity i.val = 0) :
    completedArity G Gamma hmem h i.val = 0 := by
  simp [completedArity, SingleWeightCompletion.arity, i.isLt, ha,
    layer_nullary G Gamma hmem h i ha, SingleWeightCompletion.extra]

theorem completed_positive_original (i : Fin s)
    (hp : 0 < completedArity G Gamma hmem h i.val) : 0 < arity i.val := by
  by_contra hn
  have hz : arity i.val = 0 := by omega
  have hc := completed_nullary G Gamma hmem h i hz
  omega

theorem target_signature (j : Fin (count G Gamma hmem h)) :
    (⟨targetArity G Gamma hmem h j.val, targetTable G Gamma hmem h j⟩ :
      AnySignature AlgebraicComplex) =
    ⟨completedArity G Gamma hmem h
        (RootPreprocessing.includeLabel (completedTable G Gamma hmem h) j).val,
      completedTable G Gamma hmem h
        (RootPreprocessing.includeLabel (completedTable G Gamma hmem h) j)⟩ := by
  exact (Sigma.eta (FactorSaturation.OriginalCodec.rootLookup
    (RootPreprocessing.signature (completedTable G Gamma hmem h)) j.val)).trans
      (FactorSaturation.OriginalCodec.rootLookup_old
        (RootPreprocessing.signature (completedTable G Gamma hmem h)) j)

theorem target_preprocessed :
    Preprocessed (Source.signatureSet (targetTable G Gamma hmem h)) := by
  rintro f ⟨j, rfl⟩
  exact (congrArg (fun f : AnySignature AlgebraicComplex => 0 < f.1 ∧ f.2 ≠ 0)
    (target_signature G Gamma hmem h j)).mpr
      (RootPreprocessing.included_kept (completedTable G Gamma hmem h) j)

/-- Actual EO promise producer, tracing each kept label to an ORIGINAL
positive nonzero G member and its fixed native single-layer witness. -/
theorem target_subset : Source.signatureSet (targetTable G Gamma hmem h) ⊆
    completionFamily (kCoordinates (preprocess Gamma)) := by
  rintro f ⟨j, rfl⟩
  let i := RootPreprocessing.includeLabel (completedTable G Gamma hmem h) j
  have hk : 0 < completedArity G Gamma hmem h i.val ∧
      completedTable G Gamma hmem h i ≠ 0 :=
    RootPreprocessing.included_kept (completedTable G Gamma hmem h) j
  have hn : native G i ≠ 0 :=
    (SingleWeightCompletion.table_nonzero (native G) (layer G Gamma hmem h) i).mp hk.2
  have hm : SingleWeightCompletion.label (native G) (layer G Gamma hmem h) i ∈
      completionFamily (kCoordinates (preprocess Gamma)) :=
    ⟨⟨arity i.val, native G i⟩,
      OneSidedSource.Producer.native_member G Gamma hmem i
        (completed_positive_original G Gamma hmem h i hk.1)
        (OneSidedSource.Producer.native_nonzero_original G i hn),
      hn, layer G Gamma hmem h i, layer_spec G Gamma hmem h i, rfl⟩
  have hc : (⟨completedArity G Gamma hmem h i.val,
      completedTable G Gamma hmem h i⟩ : AnySignature AlgebraicComplex) ∈
      completionFamily (kCoordinates (preprocess Gamma)) :=
    (SingleWeightCompletion.table_label (native G) (layer G Gamma hmem h) i).symm ▸ hm
  exact (congrArg (fun f : AnySignature AlgebraicComplex =>
    f ∈ completionFamily (kCoordinates (preprocess Gamma)))
      (target_signature G Gamma hmem h j)).mpr hc

/-- No desired EO Family, per-layer solver, EO machine or expected branch
conclusion is an input. The shared sign/class come from the original h.2.2. -/
def family : Source.Family (count G Gamma hmem h) (targetArity G Gamma hmem h) where
  signatures := targetTable G Gamma hmem h
  preprocessed := target_preprocessed G Gamma hmem h
  tract := h.2.2.mono_family (target_subset G Gamma hmem h)

end
end Holant.LocalDrafts.Tractability.EOEvaluation.SingleWeightSource.Producer
