import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPlanes

/-! Coefficient extraction from the preserved marked-octahedral proof. A real finite quotient filter, not the unproved
S4 quotient-direction histogram. Any five pairwise different projections
of the literal 24 roots contradict a rank-two preserver's image bound.
All coefficients in this filter are fixed current-row root pairings. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo
open Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.OctahedralSeparator
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open scoped Matrix

def FiveDirections (f : Form) (u : PairCode) (w : Fin 5 → Fin 24) : Prop :=
  ∀ a b : Fin 5,a ≠ b →
    pairing (point f (u 0)) (point f (w a))*pairing (point f (u 1)) (point f (w b))-
      pairing (point f (u 0)) (point f (w b))*pairing (point f (u 1)) (point f (w a)) ≠ 0

/-- Different literal quotient directions force different actual nonzero
images. All image scalars below are used only in the proof of injection. -/
theorem five_directions_bound (f : Form) (A : End) (u : PairCode)
    (hA : OneSided (Roots f) A)
    (hu : ∀ i,point f (u i) ∈ LinearMap.range (sharp A).mulVecLin)
    (w : Fin 5 → Fin 24) (hw : FiveDirections f u w) :
    5 ≤ (rootIndices f (LinearMap.range A.mulVecLin)).card := by
  classical
  have hn (a : Fin 5) : A *ᵥ point f (w a) ≠ 0 := by
    have hb : ∃ b : Fin 5,a ≠ b := by
      by_cases ha : a = 0
      · refine ⟨1,?_⟩
        subst a
        decide
      · exact ⟨0,ha⟩
    obtain ⟨b,hab⟩ := hb
    intro hz
    apply hw a b hab
    exact pairing_range_cross_zero (hu 0) (hu 1) (c:=0) (by simp [hz])
  have hc (a : Fin 5) : ∃ k : Fin 24,∃ c : ℂ,c ≠ 0 ∧
      A *ᵥ point f (w a) = c • point f k :=
    (roots_iff f _).mp ((hA _ (point_mem f _)).resolve_left (hn a))
  choose k c hc he using hc
  have hi : Function.Injective k := by
    intro a b hab
    by_contra hne
    apply hw a b hne
    apply pairing_range_cross_zero (hu 0) (hu 1) (c:=c a*(c b)⁻¹)
    rw [he a,he b,hab,smul_smul]
    congr 1
    field_simp [hc b]
  have hk (a : Fin 5) : point f (k a) ∈ LinearMap.range A.mulVecLin := by
    refine ⟨(c a)⁻¹ • point f (w a),?_⟩
    change A *ᵥ ((c a)⁻¹ • point f (w a)) = point f (k a)
    rw [Matrix.mulVec_smul,he a,smul_smul,inv_mul_cancel₀ (hc a),one_smul]
  let g : Fin 5 → ↑(rootIndices f (LinearMap.range A.mulVecLin)) :=
    fun a => ⟨k a,(mem_rootIndices _ _ _).mpr (hk a)⟩
  have hg : Function.Injective g := fun a b hh => hi (congrArg Subtype.val hh)
  simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective g hg

theorem no_five_directions (f : Form) (A : End) (u : PairCode)
    (hA : OneSided (Roots f) A) (hr : A.rank = 2)
    (hu : ∀ i,point f (u i) ∈ LinearMap.range (sharp A).mulVecLin) :
    ∀ w : Fin 5 → Fin 24,¬FiveDirections f u w := by
  intro w hw
  have hlo := five_directions_bound f A u hA hu w hw
  have hhi := rootIndices_bound f (LinearMap.range A.mulVecLin) hr.le
  omega

/-- Exact two-way reduction with a finite, A-independent root-coefficient
filter. Classifying which pair codes survive this filter is still open. -/
theorem rank_two_iff_filtered_cells (f : Form) (A : End) :
    TwoSided (Roots f) A ∧ A.rank = 2 ↔
      ∃ d : CellCode,Cell f d A ∧
        (∀ w : Fin 5 → Fin 24,¬FiveDirections f d.1 w) ∧
        (∀ w : Fin 5 → Fin 24,¬FiveDirections f d.2 w) := by
  constructor
  · rintro ⟨h,hr⟩
    obtain ⟨d,hd⟩ := (rank_two_iff_cells f A).mp ⟨h,hr⟩
    have hL (i : Fin 2) : point f (d.1 i) ∈ LinearMap.range A.mulVecLin := by
      rw [hd.leftRange]
      exact Submodule.subset_span ⟨i,rfl⟩
    have hR (i : Fin 2) : point f (d.2 i) ∈ LinearMap.range (sharp A).mulVecLin := by
      rw [hd.rightRange]
      exact Submodule.subset_span ⟨i,rfl⟩
    refine ⟨d,hd,?_,no_five_directions f A d.2 h.1 hr hR⟩
    apply no_five_directions f (sharp A) d.1 h.2
    · rw [rank_sharp,hr]
    · simpa only [sharp_sharp] using hL
  · rintro ⟨d,hd,_,_⟩
    exact (rank_two_iff_cells f A).mpr ⟨d,hd⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo
