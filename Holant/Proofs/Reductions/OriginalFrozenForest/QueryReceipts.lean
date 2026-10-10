import Holant.Proofs.Reductions.OriginalFrozenForest.ForestCodec


noncomputable section
namespace Holant.LocalDrafts.Hardness.OriginalFrozenForest
open Holant.Tractable Holant.Algebraic Holant.Complexity
open UniversalPairReduction.Surgery
open Holant.LocalDrafts.FinitePGL2.Stabilization
open FactorSaturation FrozenFactorNormalization GeneralExtraction
variable {L : Type} [Field L] [NumberField L] (φ : L →ₐ[ℚ] AlgebraicComplex)
variable {s : ℕ} {a : ℕ → ℕ} (G : (i : Fin s) → Signature L (a i.val))
variable (hI : RetainsIdentity (Set.range (fun i =>
  (⟨a i.val,embedded φ G i⟩ : AnySignature AlgebraicComplex))))

abbrev forwardIndex := Palette.target (rootToOld φ G hI)
abbrev forwardScalar : Fin (publicCount φ G hI) → AlgebraicComplex :=
  Palette.correction (m:=rootCount φ G) (t:=oldCount φ G hI)
    (oldAny φ G hI) (old_nonzero φ G hI)
abbrev reverseIndex := Palette.keyIndex (m:=rootCount φ G) (t:=oldCount φ G hI)
abbrev reverseScalar := Palette.pivot (oldAny φ G hI) (old_nonzero φ G hI)
abbrev forwardArity := PaletteCodec.forwardArity φ.toRingHom (literal φ G)
  (oldTable φ G hI) (storedKey φ G hI) (old_nonzero φ G hI) (rootToOld φ G hI) (literal_old φ G hI)
abbrev reverseArity := PaletteCodec.backwardArity φ.toRingHom (literal φ G)
  (oldTable φ G hI) (storedKey φ G hI)
abbrev toOldQuery := ScalarProgram.query (forwardIndex φ G hI) (forwardArity φ G hI)
abbrev fromOldQuery := ScalarProgram.query (reverseIndex φ G hI) (reverseArity φ G hI)
abbrev toOldQueryComputes := ScalarProgram.queryComputes (forwardIndex φ G hI) (forwardArity φ G hI)
abbrev fromOldQueryComputes := ScalarProgram.queryComputes (reverseIndex φ G hI) (reverseArity φ G hI)

theorem forward_root_scalar (i : Fin (rootCount φ G)) :
    forwardScalar φ G hI (Palette.rootIndex (t:=oldCount φ G hI) i) = 1 := by
  unfold forwardScalar Palette.correction Palette.rootIndex
  split_ifs with h
  · rfl
  · exact (h i.isLt).elim
theorem forward_key_scalar (i : Fin (oldCount φ G hI)) :
    forwardScalar φ G hI (reverseIndex φ G hI i) = (reverseScalar φ G hI i)⁻¹ := by
  have hi : ¬ rootCount φ G+i.val < rootCount φ G := by omega
  simp [forwardScalar,reverseIndex,reverseScalar,Palette.correction,Palette.keyIndex,hi]
theorem reverse_scalar_ne (i : Fin (oldCount φ G hI)) : reverseScalar φ G hI i≠0 :=
  Palette.pivot_ne (oldAny φ G hI) (old_nonzero φ G hI) i

theorem forward_row (i : Fin (publicCount φ G hI)) (bits : List Bool) :
    Choice.table (publicTable φ G hI) i.val bits = forwardScalar φ G hI i *
      Choice.table (oldTable φ G hI) (forwardIndex φ G hI i).val bits :=
  PaletteCodec.forwardRow φ.toRingHom (literal φ G) (oldTable φ G hI) (storedKey φ G hI)
    (old_nonzero φ G hI) (rootToOld φ G hI) (literal_old φ G hI) i bits
theorem reverse_row (i : Fin (oldCount φ G hI)) (bits : List Bool) :
    Choice.table (oldTable φ G hI) i.val bits = reverseScalar φ G hI i *
      Choice.table (publicTable φ G hI) (reverseIndex φ G hI i).val bits :=
  PaletteCodec.backwardRow φ.toRingHom (literal φ G) (oldTable φ G hI) (storedKey φ G hI)
    (old_nonzero φ G hI) i bits

theorem public_value_exact (r : ExactSignatureTables.Input (publicCount φ G hI) 1 (publicArity φ G hI)) :
    (GeneralOriginalTarget.originalValue (publicTable φ G hI) r : AlgebraicComplex) =
      φ (publicValue φ G hI r) := by
  rw [GeneralOriginalTarget.target_exact]
  exact (original_exact φ (publicTableL φ G hI) r).symm
theorem forward_value (r : ExactSignatureTables.Input (publicCount φ G hI) 1 (publicArity φ G hI)) :
    φ (publicValue φ G hI r) = RootPreprocessing.OccurrenceProduct.value (forwardScalar φ G hI) r.val *
      (catalogueValue φ G hI (toOldQuery φ G hI r) : AlgebraicComplex) := by
  rw [←public_value_exact φ G hI r]
  exact ScalarProgram.ambient (publicTable φ G hI) (oldTable φ G hI)
    (forwardIndex φ G hI) (forwardArity φ G hI) (forwardScalar φ G hI) (forward_row φ G hI) r
theorem reverse_value (r : ExactSignatureTables.Input (oldCount φ G hI) 1 (oldArity φ G hI)) :
    (catalogueValue φ G hI r : AlgebraicComplex) =
      RootPreprocessing.OccurrenceProduct.value (reverseScalar φ G hI) r.val *
        φ (publicValue φ G hI (fromOldQuery φ G hI r)) := by
  rw [←public_value_exact φ G hI (fromOldQuery φ G hI r)]
  exact ScalarProgram.ambient (oldTable φ G hI) (publicTable φ G hI)
    (reverseIndex φ G hI) (reverseArity φ G hI) (reverseScalar φ G hI) (reverse_row φ G hI) r

theorem to_old_ports (r : ExactSignatureTables.Input (publicCount φ G hI) 1 (publicArity φ G hI)) :
    (toOldQuery φ G hI r).val.vertices.map Prod.snd = r.val.vertices.map Prod.snd :=
  ScalarProgram.ordered_ports (forwardIndex φ G hI) (forwardArity φ G hI) r
theorem from_old_ports (r : ExactSignatureTables.Input (oldCount φ G hI) 1 (oldArity φ G hI)) :
    (fromOldQuery φ G hI r).val.vertices.map Prod.snd = r.val.vertices.map Prod.snd :=
  ScalarProgram.ordered_ports (reverseIndex φ G hI) (reverseArity φ G hI) r
theorem to_old_edges (r : ExactSignatureTables.Input (publicCount φ G hI) 1 (publicArity φ G hI)) :
    (toOldQuery φ G hI r).val.edges = r.val.edges := rfl
theorem from_old_edges (r : ExactSignatureTables.Input (oldCount φ G hI) 1 (oldArity φ G hI)) :
    (fromOldQuery φ G hI r).val.edges = r.val.edges := rfl
theorem to_old_query_bound (r : ExactSignatureTables.Input (publicCount φ G hI) 1 (publicArity φ G hI)) :
    ((catalogueEncoding φ G hI).encode (toOldQuery φ G hI r)).length ≤
      (toOldQueryComputes φ G hI).outputBound.bound.eval ((publicEncoding φ G hI).encode r).length :=
  (toOldQueryComputes φ G hI).outputBound.length_le r
theorem from_old_query_bound (r : ExactSignatureTables.Input (oldCount φ G hI) 1 (oldArity φ G hI)) :
    ((publicEncoding φ G hI).encode (fromOldQuery φ G hI r)).length ≤
      (fromOldQueryComputes φ G hI).outputBound.bound.eval ((catalogueEncoding φ G hI).encode r).length :=
  (fromOldQueryComputes φ G hI).outputBound.length_le r

end Holant.LocalDrafts.Hardness.OriginalFrozenForest
