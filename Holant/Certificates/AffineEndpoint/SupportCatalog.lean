import Holant.Certificates.AffineEndpoint.SupportCatalogLinearChecks
import Holant.Certificates.AffineEndpoint.SupportCatalogRouteChecks

/-! Semantic coverage by the literal canonical affine support charts. -/
namespace Holant.Certificates.AffineEndpoint.SupportCatalog
open Holant Holant.Tractable Holant.Tractable.AffinePhase
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem decodeSupport_image_xor (C : Finset (Fin 16)) (a : Fin 16) :
    decodeSupport (C.image (codeXor a)) = translateSet (codeWord a) (decodeSupport C) := by
  simp [decodeSupport, Finset.map_eq_image, translateSet, Finset.image_image,
    Function.comp_def, codeWord_codeXor]

theorem translation_route (l : LinearIndex) (a : Fin 16) :
    supportWords (translationRoute l a) = translateSet (codeWord a) (linearWords l) := by
  unfold supportWords linearWords
  rw [translation_route_codes, decodeSupport_image_xor]

theorem supportWords_translate (s : SupportIndex) :
    supportWords s = translateSet (supportOrigin s) (linearWords (supportLinearIndex s)) := by
  have h := translation_route (supportRows s).linearIndex (supportRows s).originCode
  rw [support_route_retract] at h
  exact h

theorem coordinates_chart (s : SupportIndex) (y : Word (supportDim s)) :
    supportCoordinates s (supportChart s y) = y := by
  unfold supportCoordinates supportChart
  rw [xor_cancel_left, linear_coordinates_chart]

theorem chart_coordinates_iff (s : SupportIndex) (x : Word 4) :
    supportChart s (supportCoordinates s x) = x ↔ x ∈ supportWords s := by
  rw [supportWords_translate, mem_translateSet_iff]
  unfold supportChart supportCoordinates
  constructor
  · intro h
    have hh := congrArg (xor (supportOrigin s)) h
    rw [xor_cancel_left] at hh
    exact (linear_chart_coordinates_iff _ _).mp hh
  · intro h
    rw [(linear_chart_coordinates_iff _ _).mpr h, xor_cancel_left]

theorem supportChart_mem (s : SupportIndex) (y : Word (supportDim s)) :
    supportChart s y ∈ supportWords s := by
  apply (chart_coordinates_iff s _).mp
  rw [coordinates_chart]

theorem supportSystem_holds (s : SupportIndex) (x : Word 4) :
    (supportSystem s).Holds x ↔ x ∈ supportWords s := by
  rw [supportSystem_shift_holds, linear_system_holds, supportWords_translate, mem_translateSet_iff]

theorem supportOrigin_mem (s : SupportIndex) : supportOrigin s ∈ supportWords s :=
  Finset.mem_map.mpr ⟨(supportRows s).originCode, (support_origin_checked s).1, rfl⟩

theorem supportOrigin_least (s : SupportIndex) (x : Word 4) (hx : x ∈ supportWords s) :
    wordCode (supportOrigin s) ≤ wordCode x := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
  simpa [supportOrigin, wordCode_codeWord] using (support_origin_checked s).2 a ha

theorem support_canonical_basis (s : SupportIndex) :
    List.ofFn (linearRows (supportLinearIndex s)).generators =
      sourceCanonicalBasis (linearRows (supportLinearIndex s)).codes (supportDim s) :=
  linear_canonical_basis _

theorem linearWords_injective : Function.Injective linearWords := by
  intro a b hab
  exact linear_codes_distinct (decodeSupport_injective hab)

theorem supportWords_injective : Function.Injective supportWords := by
  intro a b hab
  have ho : (supportRows a).originCode = (supportRows b).originCode := by
    have hab' := supportOrigin_least b (supportOrigin a) (hab ▸ supportOrigin_mem a)
    have hba' := supportOrigin_least a (supportOrigin b) (hab.symm ▸ supportOrigin_mem b)
    simpa [supportOrigin, wordCode_codeWord] using le_antisymm hba' hab'
  have how : supportOrigin a = supportOrigin b := congrArg codeWord ho
  have hl : supportLinearIndex a = supportLinearIndex b := by
    apply linearWords_injective
    calc
      linearWords (supportLinearIndex a) = translateSet (supportOrigin a) (supportWords a) := by
        rw [supportWords_translate, translateSet_twice]
      _ = translateSet (supportOrigin b) (supportWords b) := by rw [how, hab]
      _ = linearWords (supportLinearIndex b) := by rw [supportWords_translate, translateSet_twice]
  calc
    a = translationRoute (supportRows a).linearIndex (supportRows a).originCode :=
      (support_route_retract a).symm
    _ = translationRoute (supportRows b).linearIndex (supportRows b).originCode := by
      change translationRoute (supportLinearIndex a) _ = translationRoute (supportLinearIndex b) _
      rw [hl, ho]
    _ = b := support_route_retract b

/-- Literal equality to the independently proved structural enumeration. -/
theorem affine_catalog_eq : affineCatalog 4 = Finset.univ.image supportWords := by
  ext S
  constructor
  · intro hS
    obtain ⟨L, hL, hS⟩ := Finset.mem_biUnion.mp hS
    rw [linear_catalog_eq] at hL
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hS
    refine Finset.mem_image.mpr ⟨translationRoute l (wordCode a), Finset.mem_univ _, ?_⟩
    rw [translation_route, codeWord_wordCode]
  · intro hS
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hS
    apply Finset.mem_biUnion.mpr
    refine ⟨linearWords (supportLinearIndex s), ?_, ?_⟩
    · rw [linear_catalog_eq]
      exact Finset.mem_image.mpr ⟨supportLinearIndex s, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨supportOrigin s, Finset.mem_univ _, (supportWords_translate s).symm⟩

theorem supportWords_card (s : SupportIndex) : (supportWords s).card = 2 ^ supportDim s := by
  rw [supportWords_translate]
  have hi : Function.Injective (xor (supportOrigin s)) := by
    intro x y h
    have hh := congrArg (xor (supportOrigin s)) h
    simpa using hh
  rw [translateSet, Finset.card_image_of_injective _ hi, linearWords, decodeSupport_card]
  exact linear_codes_card _

theorem supportWords_ternaryClosed (s : SupportIndex) : TernaryClosed (supportWords s) := by
  intro x hx y hy z hz
  apply (supportSystem_holds s _).mp
  have hx' := (supportSystem_holds s x).mpr hx
  have hy' := (supportSystem_holds s y).mpr hy
  have hz' := (supportSystem_holds s z).mpr hz
  intro r
  change TwoTranslate.rowDot ((supportSystem s).matrix r) (xor (xor x y) z) = _
  rw [TwoTranslate.rowDot_xor, TwoTranslate.rowDot_xor]
  change TwoTranslate.rowDot ((supportSystem s).matrix r) x +
      TwoTranslate.rowDot ((supportSystem s).matrix r) y +
      TwoTranslate.rowDot ((supportSystem s).matrix r) z = _
  have hxrow : TwoTranslate.rowDot ((supportSystem s).matrix r) x = (supportSystem s).rhs r := hx' r
  have hyrow : TwoTranslate.rowDot ((supportSystem s).matrix r) y = (supportSystem s).rhs r := hy' r
  have hzrow : TwoTranslate.rowDot ((supportSystem s).matrix r) z = (supportSystem s).rhs r := hz' r
  rw [hxrow, hyrow, hzrow]
  have h : ∀ a : ZMod 2, a + a + a = a := by decide
  exact h _

/-- Coverage of all nonempty ternary-XOR-closed supports, independently of
any supplied affine signature or catalog membership premise. -/
theorem ternary_support_coverage (S : Finset (Word 4)) (hne : S.Nonempty)
    (hS : TernaryClosed S) : ∃ s : SupportIndex, supportWords s = S := by
  have h := affineCatalog_complete S hne hS
  rw [affine_catalog_eq] at h
  exact (Finset.mem_image.mp h).imp (fun s hs => hs.2)

theorem mem_support_catalog_iff (S : Finset (Word 4)) :
    (∃ s : SupportIndex, supportWords s = S) ↔ S.Nonempty ∧ TernaryClosed S := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨⟨supportOrigin s, supportOrigin_mem s⟩, supportWords_ternaryClosed s⟩
  · rintro ⟨hne, hS⟩
    exact ternary_support_coverage S hne hS

/-- Every nonzero actual affine signature has one of these literal supports. -/
theorem affine_support_coverage (f : Signature AlgebraicComplex 4) (hf : Affine f) (hn : f ≠ 0) :
    ∃ s : SupportIndex, ∀ x, f x ≠ 0 ↔ x ∈ supportWords s := by
  classical
  have hc := affine_support_catalog f hf hn
  rw [affine_catalog_eq] at hc
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hc
  refine ⟨s, ?_⟩
  intro x
  rw [hs]
  simp

theorem linear_catalog_card : (linearCatalog 4).card = 67 := by
  rw [linear_catalog_eq, Finset.card_image_of_injective _ linearWords_injective]
  simp [LinearIndex]

theorem affine_catalog_card : (affineCatalog 4).card = 307 := by
  rw [affine_catalog_eq, Finset.card_image_of_injective _ supportWords_injective]
  simp [SupportIndex]

end Holant.Certificates.AffineEndpoint.SupportCatalog
