import Holant.Proofs.Reductions.OriginalFrozenForest.Roots
import Holant.Tractable.Criteria


noncomputable section
namespace Holant.LocalDrafts.Hardness.OriginalFrozenForest
open Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
open FactorSaturation FrozenFactorNormalization GeneralExtraction
variable {L : Type} [Field L] [NumberField L] (φ : L →ₐ[ℚ] AlgebraicComplex)
variable {s : ℕ} {a : ℕ → ℕ} (G : (i : Fin s) → Signature L (a i.val))
variable (hI : RetainsIdentity (Set.range (fun i =>
  (⟨a i.val,embedded φ G i⟩ : AnySignature AlgebraicComplex))))

abbrev publicCount := rootCount φ G + oldCount φ G hI
abbrev publicSignature := Palette.signature φ.toRingHom (literal φ G)
  (oldAny φ G hI) (storedKey φ G hI)
abbrev publicFamily := Palette.family φ.toRingHom (literal φ G)
  (oldAny φ G hI) (storedKey φ G hI)
abbrev publicArity := PaletteCodec.arity φ.toRingHom (literal φ G)
  (oldTable φ G hI) (storedKey φ G hI)
abbrev publicTableL := PaletteCodec.tableL φ.toRingHom (literal φ G)
  (oldTable φ G hI) (storedKey φ G hI)
abbrev publicTable := PaletteCodec.table φ.toRingHom (literal φ G)
  (oldTable φ G hI) (storedKey φ G hI)
abbrev publicEncoding := RawClosedNetwork.validatedEncoding (publicCount φ G hI) 1 (publicArity φ G hI)
abbrev publicPresentation := OriginalLCodec.presentation (L:=L)
abbrev publicValue := OriginalLCodec.value (publicTableL φ G hI)

theorem saturated : FactorSaturated (publicFamily φ G hI) :=
  Palette.saturated φ.toRingHom (literal φ G) (oldAny φ G hI) (storedKey φ G hI)
    (old_nonzero φ G hI) (rootToOld φ G hI) (literal_old φ G hI)
    (actualTree φ G hI) (actualTree_leaves φ G hI)
theorem retains_kept (i : Fin s) (hi : RootPreprocessing.Keep (embedded φ G) i) :
    (⟨a i.val,G i⟩ : AnySignature L) ∈ publicFamily φ G hI := by
  rw [←kept_original φ G i hi]
  exact Palette.retains_root φ.toRingHom _ _ _ _

/-- A strict charge witness is never a zero or nullary row, so its ORIGINAL
literal tensor (and word) survives the filter and the normalized augmentation. -/
theorem retains_charge_witness (i : Fin s) (x : Fin (a i.val) → Bool)
    (hx : embedded φ G i x≠0) (hc : Holant.charge x≠0) :
    (⟨a i.val,G i⟩ : AnySignature L) ∈ publicFamily φ G hI := by
  have ha : 0 < a i.val := by
    have hw := Holant.weight_le x
    unfold Holant.charge at hc
    omega
  have hn : embedded φ G i≠0 := by
    intro hz
    exact hx (congrFun hz x)
  exact retains_kept φ G hI i ⟨ha,hn⟩
theorem preserves_both_charge_signs
    (h : BothChargeSigns (Set.range (fun i => (⟨a i.val,embedded φ G i⟩ : AnySignature AlgebraicComplex)))) :
    BothChargeSigns (RH.mapFamily φ.toRingHom (publicFamily φ G hI)) := by
  obtain ⟨⟨f,⟨i,rfl⟩,x,hx,hc⟩,⟨g,⟨j,rfl⟩,y,hy,hd⟩⟩ := h
  constructor
  · refine ⟨⟨a i.val,embedded φ G i⟩,?_,x,hx,hc⟩
    exact ⟨⟨a i.val,G i⟩,retains_charge_witness φ G hI i x hx (ne_of_lt hc),rfl⟩
  · refine ⟨⟨a j.val,embedded φ G j⟩,?_,y,hy,hd⟩
    exact ⟨⟨a j.val,G j⟩,retains_charge_witness φ G hI j y hy (ne_of_gt hd),rfl⟩
theorem nonzero (i : Fin (publicCount φ G hI)) : (publicSignature φ G hI i).2≠0 :=
  Palette.nonzero φ.toRingHom _ _ _ (old_nonzero φ G hI) (rootToOld φ G hI) (literal_old φ G hI) i
theorem positive (i : Fin (publicCount φ G hI)) : 0 < (publicSignature φ G hI i).1 := by
  have he := congrArg Sigma.fst (Palette.projective φ.toRingHom (literal φ G)
    (oldAny φ G hI) (storedKey φ G hI) (old_nonzero φ G hI) (rootToOld φ G hI) (literal_old φ G hI) i)
  change (publicSignature φ G hI i).1 = oldArity φ G hI _ at he
  rw [he]
  exact old_positive φ G hI _
theorem finite_family : (publicFamily φ G hI).Finite := Set.finite_range _
theorem public_image : Set.range (fun i => (⟨publicArity φ G hI i.val,publicTable φ G hI i⟩ :
    AnySignature AlgebraicComplex)) = RH.mapFamily φ.toRingHom (publicFamily φ G hI) :=
  PaletteCodec.public_image φ.toRingHom _ _ _

theorem identity : RetainsIdentity (publicFamily φ G hI) := by
  have hh := (roots φ G hI).identity
  obtain ⟨i,hi⟩ := hh
  let I : AnySignature L := ⟨2,Holant.OpenNetworkComposition.OrdinaryNormalization.identitySignature⟩
  have hm : RH.mapAny φ.toRingHom I =
      (⟨2,Holant.OpenNetworkComposition.OrdinaryNormalization.identitySignature⟩ : AnySignature AlgebraicComplex) := by
    apply congrArg (fun f : Signature AlgebraicComplex 2 => (⟨2,f⟩ : AnySignature AlgebraicComplex))
    funext x
    simp [I,RH.mapAny,RH.mapSignature,Holant.OpenNetworkComposition.OrdinaryNormalization.identitySignature,
      Signature.equality]
  have he : literal φ G i=I := mapAny_injective φ.toRingHom ((literal_map φ G hI i).trans (hi.trans hm.symm))
  change I ∈ publicFamily φ G hI
  rw [←he]
  exact Palette.retains_root φ.toRingHom _ _ _ i

theorem original_field_boundary : GeneralOriginalTarget.originalField (publicTable φ G hI) ≤ φ.fieldRange :=
  OriginalLCodec.field_le φ (publicTableL φ G hI)
theorem degree_bound : Module.finrank ℚ (GeneralOriginalTarget.originalField (publicTable φ G hI)) ≤
    Module.finrank ℚ L := OriginalLCodec.degree_bound φ (publicTableL φ G hI)

def toCatalogue := PaletteCodec.toOld φ.toRingHom (literal φ G) (oldTable φ G hI)
  (storedKey φ G hI) (old_nonzero φ G hI) (rootToOld φ G hI) (literal_old φ G hI)
def fromCatalogue := PaletteCodec.fromOld φ.toRingHom (literal φ G) (oldTable φ G hI)
  (storedKey φ G hI) (old_nonzero φ G hI)
def publicToCoefficient := OriginalLCodec.toCoefficient φ (publicTableL φ G hI)
def publicFromCoefficient := OriginalLCodec.fromCoefficient φ (publicTableL φ G hI)

end Holant.LocalDrafts.Hardness.OriginalFrozenForest
