import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralQuotientCertificates

/-! Coefficient extraction from the preserved marked-octahedral proof. Semantic consumer of the literal finite quotient
certificate. The original rank-two map's actual dual range supplies the
secant index internally; no complete enumeration is a caller premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.QuotientEnumeration
open Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open scoped Matrix

theorem embed_cross (f : Form) (t : Fin 122) (r s : Fin 24) :
    embed (cross (projected f t r) (projected f t s)) =
      pairing (point f (canonicalPair t 0)) (point f r)*
        pairing (point f (canonicalPair t 1)) (point f s)-
      pairing (point f (canonicalPair t 0)) (point f s)*
        pairing (point f (canonicalPair t 1)) (point f r) := by
  change embed (rawPair (rawPoint f (canonicalPair t 0)) (rawPoint f r)*
      rawPair (rawPoint f (canonicalPair t 1)) (rawPoint f s)-
      rawPair (rawPoint f (canonicalPair t 1)) (rawPoint f r)*
      rawPair (rawPoint f (canonicalPair t 0)) (rawPoint f s)) = _
  rw [embed_sub,embed_mul,embed_mul]
  simp only [RankThree.embed_pair,RankThree.lift_point]
  change pairing (point f (canonicalPair t 0)) (point f r)*
      pairing (point f (canonicalPair t 1)) (point f s)-
      pairing (point f (canonicalPair t 1)) (point f r)*
      pairing (point f (canonicalPair t 0)) (point f s) = _
  ring

theorem projected_separate (f : Form) (t : Fin 122) {r s : Fin 24}
    (hr : r ∈ projectedIndices f t) (hs : s ∈ projectedIndices f t) (hne : r ≠ s) :
    pairing (point f (canonicalPair t 0)) (point f r)*
      pairing (point f (canonicalPair t 1)) (point f s)-
    pairing (point f (canonicalPair t 0)) (point f s)*
      pairing (point f (canonicalPair t 1)) (point f r) ≠ 0 := by
  have hr' := (Finset.mem_filter.mp hr).2
  have hs' := (Finset.mem_filter.mp hs).2
  rw [←embed_cross]
  apply embed_ne_zero
  rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
  · have hh := hs'.2 r h hr'.1
    intro hz
    apply hh
    have he : cross (projected f t s) (projected f t r) =
        -cross (projected f t r) (projected f t s) := by
      unfold cross
      ring
    rw [he,hz,neg_zero]
  · exact hr'.2 s h hs'.1

/-- The first five computed indices, in their original order. The sorted
finite-set embedding is explicit, with no arbitrary root selection. -/
def fiveWitness (f : Form) (t : Fin 122) (h : 5 ≤ (projectedIndices f t).card) :
    Fin 5 → Fin 24 := fun a => (projectedIndices f t).orderEmbOfFin rfl
      ⟨a.val,lt_of_lt_of_le a.isLt h⟩

theorem fiveWitness_mem (f : Form) (t : Fin 122) (h : 5 ≤ (projectedIndices f t).card)
    (a : Fin 5) : fiveWitness f t h a ∈ projectedIndices f t :=
  Finset.orderEmbOfFin_mem _ _ _

theorem fiveWitness_injective (f : Form) (t : Fin 122)
    (h : 5 ≤ (projectedIndices f t).card) : Function.Injective (fiveWitness f t h) := by
  intro a b he
  have hh := (projectedIndices f t).orderEmbOfFin rfl |>.injective he
  exact Fin.ext (congrArg (fun z : Fin (projectedIndices f t).card=>z.val) hh)

theorem fiveWitness_valid (f : Form) (t : Fin 122)
    (h : 5 ≤ (projectedIndices f t).card) :
    FiveDirections f (canonicalPair t) (fiveWitness f t h) := by
  intro a b hab
  apply projected_separate f t (fiveWitness_mem f t h a) (fiveWitness_mem f t h b)
  intro he
  exact hab (fiveWitness_injective f t h he)

/-- Actual canonical root-pair membership is restored from the actual
secant receipt. Nothing is inferred merely from the line's cardinality. -/
theorem canonicalPair_range (f : Form) (A : End) (t : Fin 122)
    (ht : rootIndices f (LinearMap.range A.mulVecLin) = globalLine .octahedral t) :
    ∀ i : Fin 2,point f (canonicalPair t i) ∈ LinearMap.range A.mulVecLin := by
  intro i
  apply (mem_rootIndices f _ _).mp
  rw [ht]
  exact canonicalPair_mem t i

theorem canonicalPair_finrank (f : Form) (t : Fin 122) :
    Module.finrank ℂ (rootPlane f (canonicalPair t)) = 2 := by
  have hs : rootPlane f (canonicalPair t) = Submodule.span ℂ
      ({point f (canonicalPair t 0),point f (canonicalPair t 1)} : Set V) := by
    unfold rootPlane
    congr 1
    ext v
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (rfl|hv)
      · exact ⟨0,rfl⟩
      · exact ⟨1,(Set.mem_singleton_iff.mp hv).symm⟩
  have hm : (rootPlane f (canonicalPair t)).map (coefficientPull f) = Submodule.span ℂ
      ({RainbowOrbit.representative .octahedral (canonicalPair t 0),
        RainbowOrbit.representative .octahedral (canonicalPair t 1)} : Set PlatonicIncidence.Mat) := by
    rw [hs,←Submodule.span_image]
    simp only [Set.image_insert_eq,Set.image_singleton,coefficientPull_point]
  rw [(Submodule.equivMapOfInjective (coefficientPull f) (coefficientPull_injective f)
    (rootPlane f (canonicalPair t))).finrank_eq,hm]
  exact pair_finrank .octahedral _ _ (canonicalPair_ne t)

/-- The canonical pair spans the actual range, not just the same list of
root indices. This restores the coordinate plane needed for reconstruction. -/
theorem canonicalPair_span (f : Form) (A : End) (hr : A.rank = 2) (t : Fin 122)
    (ht : rootIndices f (LinearMap.range A.mulVecLin) = globalLine .octahedral t) :
    rootPlane f (canonicalPair t) = LinearMap.range A.mulVecLin := by
  have hle : rootPlane f (canonicalPair t) ≤ LinearMap.range A.mulVecLin := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact canonicalPair_range f A t ht i
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [canonicalPair_finrank]
  exact hr.le

theorem dual_secant_four (f : Form) (A : End) (hA : OneSided (Roots f) A)
    (hr : A.rank = 2) (t : Fin 122)
    (ht : rootIndices f (LinearMap.range (sharp A).mulVecLin) = globalLine .octahedral t) :
    t ∈ fourLines := by
  by_contra hn
  have hc := six_projections f t hn
  have h5 : 5 ≤ (projectedIndices f t).card := by omega
  exact no_five_directions f A (canonicalPair t) hA hr
    (canonicalPair_range f (sharp A) t ht) (fiveWitness f t h5) (fiveWitness_valid f t h5)

abbrev FourLineCode := {t : Fin 122 // t ∈ fourLines}

theorem fourLineCode_card : Fintype.card FourLineCode = 18 := by
  simpa only [Fintype.card_coe] using fourLines_card

/-- Literal increasing enumeration, backed by the old 122-entry table and
proved eighteen count; this introduces no arbitrary numbering. -/
def fourEnumeration : Fin 18 ≃o FourLineCode := fourLines.orderIsoOfFin fourLines_card

structure PairedRanges (f : Form) (A : End) (l r : FourLineCode) : Prop where
  left : rootIndices f (LinearMap.range A.mulVecLin) = globalLine .octahedral l.val
  right : rootIndices f (LinearMap.range (sharp A).mulVecLin) = globalLine .octahedral r.val
  leftPair : ∀ i : Fin 2,point f (canonicalPair l.val i) ∈ LinearMap.range A.mulVecLin
  rightPair : ∀ i : Fin 2,point f (canonicalPair r.val i) ∈ LinearMap.range (sharp A).mulVecLin
  leftSpan : rootPlane f (canonicalPair l.val) = LinearMap.range A.mulVecLin
  rightSpan : rootPlane f (canonicalPair r.val) = LinearMap.range (sharp A).mulVecLin
  polynomials : Equations f A
  rank : A.rank = 2

/-- Internally produce the two eighteen-line indices for the SAME arbitrary
actual map. This is not yet the at-most-eight projectivity classification. -/
theorem rank_two_paired_ranges (f : Form) (A : End)
    (h : TwoSided (Roots f) A) (hr : A.rank = 2) :
    ∃ l r : FourLineCode,PairedRanges f A l r := by
  obtain ⟨lt,hlt⟩ := range_secant f A h.1 hr
  obtain ⟨rt,hrt⟩ := range_secant f (sharp A) h.2 (by rw [rank_sharp,hr])
  have hl : lt ∈ fourLines := dual_secant_four f (sharp A) h.2
    (by rw [rank_sharp,hr]) lt (by simpa only [sharp_sharp] using hlt)
  have hrr := dual_secant_four f A h.1 hr rt hrt
  exact ⟨⟨lt,hl⟩,⟨rt,hrr⟩,hlt,hrt,canonicalPair_range f A lt hlt,
    canonicalPair_range f (sharp A) rt hrt,canonicalPair_span f A hr lt hlt,
    canonicalPair_span f (sharp A) (by rw [rank_sharp,hr]) rt hrt,
    (twoSided_iff_equations f A).mp h,hr⟩

theorem rank_two_iff_paired_ranges (f : Form) (A : End) :
    TwoSided (Roots f) A ∧ A.rank = 2 ↔
      ∃ l r : FourLineCode,PairedRanges f A l r := by
  constructor
  · rintro ⟨h,hr⟩
    exact rank_two_paired_ranges f A h hr
  · rintro ⟨l,r,h⟩
    exact ⟨(twoSided_iff_equations f A).mpr h.polynomials,h.rank⟩

theorem rank_two_iff_18cells (f : Form) (A : End) :
    TwoSided (Roots f) A ∧ A.rank = 2 ↔
      ∃ i j : Fin 18,PairedRanges f A (fourEnumeration i) (fourEnumeration j) := by
  rw [rank_two_iff_paired_ranges]
  constructor
  · rintro ⟨l,r,h⟩
    refine ⟨fourEnumeration.symm l,fourEnumeration.symm r,?_⟩
    simpa only [OrderIso.apply_symm_apply] using h
  · rintro ⟨i,j,h⟩
    exact ⟨fourEnumeration i,fourEnumeration j,h⟩

theorem paired_code_card : Fintype.card (FourLineCode × FourLineCode) = 324 := by
  rw [Fintype.card_prod,fourLineCode_card]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.QuotientEnumeration
