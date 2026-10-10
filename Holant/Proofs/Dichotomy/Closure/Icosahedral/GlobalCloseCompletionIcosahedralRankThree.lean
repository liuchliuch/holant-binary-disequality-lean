import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorTables
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralRankTwo

/-! Generic I/opposite-I coefficient proof extracted from RankThree/Source.
No old saved-State dispatcher or caller-supplied classification is imported.
This candidate retains the actual full sixty-point hypotheses and proof. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankThree
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.RainbowOrbit
open Holant.Certificates.TetrahedralPreservers
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Preserver.Completion
open scoped BigOperators Matrix

def planeFrame (opposite : Bool) (i : Fin 60) : TetrahedralPreservers.BinaryMatrix ≃ₗ[ℂ] V :=
  (leftEquiv (representative .icosahedral i) (representative_det_ne_zero .icosahedral i)).trans
    (RankTwo.coefficientPush opposite)

def mappedPlane (opposite : Bool) (i : Fin 60) (b c : Fin 31) : Submodule ℂ V :=
  (anchorPlane b c).map (planeFrame opposite i).toLinearMap

theorem frame_one (opposite : Bool) (i : Fin 60) :
    planeFrame opposite i 1 = RankTwo.rootPoint opposite i := by
  change RankTwo.coefficientPush opposite (representative .icosahedral i*1) = _
  rw [Matrix.mul_one,RankTwo.push_point]

theorem frame_point (opposite : Bool) (i r : Fin 60) :
    planeFrame opposite i (representative .icosahedral r) =
      (productScale .icosahedral i r : ℂ) •
        RankTwo.rootPoint opposite (leftPermutation .icosahedral i r) := by
  change RankTwo.coefficientPush opposite
    (representative .icosahedral i * representative .icosahedral r) = _
  rw [mul_exact,map_smul,RankTwo.push_point] <;> rfl

private theorem mem_map_equiv {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (e : M ≃ₗ[ℂ] N) (S : Submodule ℂ M) (v : M) :
    e v ∈ S.map e.toLinearMap ↔ v ∈ S := by
  constructor
  · rintro ⟨w,hw,he⟩
    exact e.injective he ▸ hw
  · intro hv
    exact ⟨v,hv,rfl⟩

theorem rootIndices_frame (opposite : Bool) (i : Fin 60) (b c : Fin 31) :
    RankTwo.rootIndices opposite (mappedPlane opposite i b c) =
      (deletion .icosahedral (anchorPlane b c)).image (leftPermutation .icosahedral i) := by
  ext k
  obtain ⟨r,rfl⟩ := (leftPermutation .icosahedral i).surjective k
  have hscale : (productScale .icosahedral i r : ℂ) ≠ 0 :=
    Int.cast_ne_zero.mpr (raw_certificate .icosahedral i r).1
  have hm := mem_map_equiv (planeFrame opposite i) (anchorPlane b c)
    (representative .icosahedral r)
  rw [frame_point,Submodule.smul_mem_iff _ hscale] at hm
  rw [RankTwo.mem_rootIndices]
  change (RankTwo.rootPoint opposite (leftPermutation .icosahedral i r) ∈
    (anchorPlane b c).map (planeFrame opposite i).toLinearMap) ↔ _
  rw [hm,Finset.mem_image]
  constructor
  · intro hr
    exact ⟨r,(mem_deletion _ _ _).mpr hr,rfl⟩
  · rintro ⟨s,hs,he⟩
    have : s=r := (leftPermutation .icosahedral i).injective he
    subst s
    exact (mem_deletion _ _ _).mp hs

theorem mappedPlane_bound (opposite : Bool) (i : Fin 60) (b c : Fin 31) (hbc : b ≠ c) :
    (RankTwo.rootIndices opposite (mappedPlane opposite i b c)).card ≤ 15 := by
  rw [rootIndices_frame]
  exact Finset.card_image_le.trans (anchorPlane_bound b c hbc)

/-- A root basis is extracted from the actual preserved range. This uses
the original sixty-root span producer rather than a plane supplied by a caller. -/
theorem range_root_basis (opposite : Bool) (A : End)
    (hA : OneSided (Preserver.roots opposite) A) {r : ℕ} (hr : A.rank = r) :
    ∃ u : Fin r → Fin 60, LinearIndependent ℂ (fun a => RankTwo.rootPoint opposite (u a)) ∧
      (∀ a,RankTwo.rootPoint opposite (u a) ∈ LinearMap.range A.mulVecLin) ∧
      Submodule.span ℂ (Set.range (fun a => RankTwo.rootPoint opposite (u a))) =
        LinearMap.range A.mulVecLin := by
  classical
  let D := {i : Fin 60 // RankTwo.rootPoint opposite i ∈ LinearMap.range A.mulVecLin}
  let v : D → V := fun i => RankTwo.rootPoint opposite i.val
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' ℂ v
  letI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = r := by
    rw [←finrank_span_eq_card hli,hspan]
    change Module.finrank ℂ (Submodule.span ℂ (Set.range v)) = r
    rw [show Submodule.span ℂ (Set.range v) = LinearMap.range A.mulVecLin
      from RankTwo.span_root_range opposite A hA]
    exact hr
  let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun j => (a (e j)).val,hli.comp e e.injective,fun j => (a (e j)).property,?_⟩
  have he : Set.range (fun j : Fin r => RankTwo.rootPoint opposite (a (e j)).val) =
      Set.range (v ∘ a) := by
    ext x
    constructor
    · rintro ⟨j,rfl⟩; exact ⟨e j,rfl⟩
    · rintro ⟨j,rfl⟩
      obtain ⟨k,rfl⟩ := e.surjective j
      exact ⟨k,rfl⟩
  rw [he,hspan]
  exact RankTwo.span_root_range opposite A hA

private theorem image_pair_mem (e : TetrahedralPreservers.BinaryMatrix ≃ₗ[ℂ] V) (W : Submodule ℂ V)
    {u v w : TetrahedralPreservers.BinaryMatrix} (hu : e u ∈ W) (hv : e v ∈ W)
    (hw : w ∈ Submodule.span ℂ ({u,v} : Set TetrahedralPreservers.BinaryMatrix)) : e w ∈ W := by
  obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hw
  rw [map_add,map_smul,map_smul]
  exact W.add_mem (W.smul_mem _ hu) (W.smul_mem _ hv)

private theorem pair_le_anchorPlane (b c : Fin 31) (d : Fin 31) (hd : d=b ∨ d=c) :
    Submodule.span ℂ ({(1 : TetrahedralPreservers.BinaryMatrix),representative .icosahedral (baseAnchor .icosahedral d)} :
      Set TetrahedralPreservers.BinaryMatrix) ≤ anchorPlane b c := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with rfl | hx
  · exact Submodule.subset_span ⟨0,rfl⟩
  · have he : x=representative .icosahedral (baseAnchor .icosahedral d) := by
      simpa only [Set.mem_singleton_iff] using hx
    subst x
    rcases hd with rfl | rfl
    · exact Submodule.subset_span ⟨1,rfl⟩
    · exact Submodule.subset_span ⟨2,rfl⟩

/-- Every three-dimensional actual root span is one of the old literal
left translates of an identity/two-anchor plane. Both anchor indices and
their inequality are derived internally from the original range basis. -/
theorem plane_normalization (opposite : Bool) (W : Submodule ℂ V)
    (u : Fin 3 → Fin 60) (hu : LinearIndependent ℂ (fun a => RankTwo.rootPoint opposite (u a)))
    (hspan : Submodule.span ℂ (Set.range (fun a => RankTwo.rootPoint opposite (u a))) = W) :
    ∃ i : Fin 60, ∃ b c : Fin 31, b ≠ c ∧ W = mappedPlane opposite i b c := by
  classical
  let i := u 0
  let p := leftPermutation .icosahedral i
  let j := p.symm (u 1)
  let k := p.symm (u 2)
  have hj : j ≠ identityIndex .icosahedral := by
    intro h
    have he : u 1 = u 0 := by
      calc
        u 1 = p j := (p.apply_symm_apply _).symm
        _ = u 0 := by rw [h,leftPermutation_apply,product_identity_right]
    have hh : (1 : Fin 3) = 0 := hu.injective (congrArg (RankTwo.rootPoint opposite) he)
    exact (by decide : (1 : Fin 3) ≠ 0) hh
  have hk : k ≠ identityIndex .icosahedral := by
    intro h
    have he : u 2 = u 0 := by
      calc
        u 2 = p k := (p.apply_symm_apply _).symm
        _ = u 0 := by rw [h,leftPermutation_apply,product_identity_right]
    have hh : (2 : Fin 3) = 0 := hu.injective (congrArg (RankTwo.rootPoint opposite) he)
    exact (by decide : (2 : Fin 3) ≠ 0) hh
  let b := baseLineOf .icosahedral j
  let c := baseLineOf .icosahedral k
  let e := planeFrame opposite i
  let S := anchorPlane b c
  have hm (a : Fin 3) : RankTwo.rootPoint opposite (u a) ∈ W := by
    rw [←hspan]
    exact Submodule.subset_span ⟨a,rfl⟩
  have h1 : e 1 ∈ W := by rw [frame_one]; exact hm 0
  have hjs : e (representative .icosahedral j) ∈ W := by
    rw [frame_point,show leftPermutation .icosahedral i j = u 1 from p.apply_symm_apply _]
    exact W.smul_mem _ (hm 1)
  have hks : e (representative .icosahedral k) ∈ W := by
    rw [frame_point,show leftPermutation .icosahedral i k = u 2 from p.apply_symm_apply _]
    exact W.smul_mem _ (hm 2)
  have hab : representative .icosahedral (baseAnchor .icosahedral b) ∈
      Submodule.span ℂ ({(1 : TetrahedralPreservers.BinaryMatrix),representative .icosahedral j} : Set TetrahedralPreservers.BinaryMatrix) := by
    rw [←base_span_same .icosahedral j hj]
    exact Submodule.subset_span (Or.inr rfl)
  have hac : representative .icosahedral (baseAnchor .icosahedral c) ∈
      Submodule.span ℂ ({(1 : TetrahedralPreservers.BinaryMatrix),representative .icosahedral k} : Set TetrahedralPreservers.BinaryMatrix) := by
    rw [←base_span_same .icosahedral k hk]
    exact Submodule.subset_span (Or.inr rfl)
  have hjb : representative .icosahedral j ∈
      Submodule.span ℂ ({(1 : TetrahedralPreservers.BinaryMatrix),representative .icosahedral (baseAnchor .icosahedral b)} :
        Set TetrahedralPreservers.BinaryMatrix) := by
    rw [base_span_same .icosahedral j hj]
    exact Submodule.subset_span (by simp)
  have hkc : representative .icosahedral k ∈
      Submodule.span ℂ ({(1 : TetrahedralPreservers.BinaryMatrix),representative .icosahedral (baseAnchor .icosahedral c)} :
        Set TetrahedralPreservers.BinaryMatrix) := by
    rw [base_span_same .icosahedral k hk]
    exact Submodule.subset_span (by simp)
  have hle : S.map e.toLinearMap ≤ W := by
    have hS : S ≤ W.comap e.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a,rfl⟩
      change e (anchorTriple b c a) ∈ W
      fin_cases a
      · exact h1
      · exact image_pair_mem e W h1 hjs hab
      · exact image_pair_mem e W h1 hks hac
    rintro _ ⟨v,hv,rfl⟩
    exact hS hv
  have hge : W ≤ S.map e.toLinearMap := by
    rw [←hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    fin_cases a
    · change RankTwo.rootPoint opposite i ∈ S.map e.toLinearMap
      rw [←frame_one opposite i]
      exact (mem_map_equiv e S 1).mpr (Submodule.subset_span ⟨0,rfl⟩)
    · have hv := (mem_map_equiv e S (representative .icosahedral j)).mpr
        ((pair_le_anchorPlane b c b (Or.inl rfl)) hjb)
      rw [frame_point,show leftPermutation .icosahedral i j = u 1 from p.apply_symm_apply _] at hv
      exact (Submodule.smul_mem_iff _ (Int.cast_ne_zero.mpr (raw_certificate .icosahedral i j).1)).mp hv
    · have hv := (mem_map_equiv e S (representative .icosahedral k)).mpr
        ((pair_le_anchorPlane b c c (Or.inr rfl)) hkc)
      rw [frame_point,show leftPermutation .icosahedral i k = u 2 from p.apply_symm_apply _] at hv
      exact (Submodule.smul_mem_iff _ (Int.cast_ne_zero.mpr (raw_certificate .icosahedral i k).1)).mp hv
  have hW : W=S.map e.toLinearMap := le_antisymm hge hle
  have hdim : Module.finrank ℂ W=3 := by
    rw [←hspan,finrank_span_eq_card hu]
    simp
  have hSdim : Module.finrank ℂ S=3 := by
    have he := (Submodule.equivMapOfInjective e.toLinearMap e.injective S).finrank_eq
    rw [←hW] at he
    exact he ▸ hdim
  have hbc : b ≠ c := by
    intro h
    have hs : S ≤ Submodule.span ℂ
        ({(1 : TetrahedralPreservers.BinaryMatrix),representative .icosahedral (baseAnchor .icosahedral b)} : Set TetrahedralPreservers.BinaryMatrix) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a,rfl⟩
      fin_cases a <;> simp only [anchorTriple,h] <;> exact Submodule.subset_span (by simp)
    have hpd : Module.finrank ℂ (Submodule.span ℂ
        ({(1 : TetrahedralPreservers.BinaryMatrix),representative .icosahedral (baseAnchor .icosahedral b)} : Set TetrahedralPreservers.BinaryMatrix))=2 := by
      rw [←representative_identity .icosahedral]
      exact pair_finrank .icosahedral _ _ (base_anchors .icosahedral b).1.symm
    have hd := Submodule.finrank_mono hs
    rw [hSdim,hpd] at hd
    omega
  exact ⟨i,b,c,hbc,hW⟩

theorem root_plane_bound (opposite : Bool) (W : Submodule ℂ V) (u : Fin 3 → Fin 60)
    (hu : LinearIndependent ℂ (fun a => RankTwo.rootPoint opposite (u a)))
    (hspan : Submodule.span ℂ (Set.range (fun a => RankTwo.rootPoint opposite (u a))) = W) :
    (RankTwo.rootIndices opposite W).card ≤ 15 := by
  obtain ⟨i,b,c,hbc,rfl⟩ := plane_normalization opposite W u hu hspan
  exact mappedPlane_bound opposite i b c hbc

def projectedWitness (opposite : Bool) (i r : Fin 60) : V :=
  coordinates (RankTwo.sourceFrame opposite
    ((representative .icosahedral i).transpose⁻¹ * representative .icosahedral r))

theorem projectedWitness_mem (opposite : Bool) (i r : Fin 60) :
    projectedWitness opposite i r ∈ Preserver.roots opposite := by
  refine ⟨_,RankTwo.sourceFrame_mem opposite ?_,rfl⟩
  exact RainbowOrbit.groupDirection_mul .icosahedral
    (MatchingProductBridge.groupDirection_inverse .icosahedral
      (MatchingProductBridge.groupDirection_transpose .icosahedral (representative_mem .icosahedral i)))
    (representative_mem .icosahedral r)

theorem projectedWitness_pairing (opposite : Bool) (i r : Fin 60) (U : TetrahedralPreservers.BinaryMatrix) :
    pairing (planeFrame opposite i U) (projectedWitness opposite i r) =
      pairing (coordinates U) (RankTwo.rootPoint false r) :=
  RankTwo.frame_left_pairing opposite (representative .icosahedral i) U
    (representative .icosahedral r) (representative_det_ne_zero .icosahedral i)

/-- Arbitrary image-plane normalization supplies at least sixteen actual
source directions with cross witnesses against three vectors in that SAME
plane. The coefficient inverse is never treated as a physical binary. -/
theorem plane_quotient_directions (opposite : Bool) (W : Submodule ℂ V) (u : Fin 3 → Fin 60)
    (hu : LinearIndependent ℂ (fun a => RankTwo.rootPoint opposite (u a)))
    (hspan : Submodule.span ℂ (Set.range (fun a => RankTwo.rootPoint opposite (u a))) = W) :
    ∃ v : Fin 3 → V, (∀ a,v a ∈ W) ∧ ∃ m : ℕ, 16 ≤ m ∧ ∃ w : Fin m → V,
      (∀ a,w a ∈ Preserver.roots opposite) ∧
      ∀ a d : Fin m, a ≠ d → ∃ p q : Fin 3,
        pairing (v p) (w a)*pairing (v q) (w d)-
          pairing (v p) (w d)*pairing (v q) (w a) ≠ 0 := by
  obtain ⟨i,b,c,hbc,hW⟩ := plane_normalization opposite W u hu hspan
  obtain ⟨m,hm,w,hw⟩ := anchor_quotient_directions b c hbc
  refine ⟨fun a => planeFrame opposite i (anchorTriple b c a),?_,m,hm,
    fun a => projectedWitness opposite i (w a),fun a => projectedWitness_mem _ _ _,?_⟩
  · intro a
    rw [hW]
    exact (mem_map_equiv _ _ _).mpr (Submodule.subset_span ⟨a,rfl⟩)
  · intro a d had
    obtain ⟨p,q,hpq⟩ := hw a d had
    refine ⟨p,q,?_⟩
    simpa only [projectedWitness_pairing] using hpq

theorem image_directions_bound (opposite : Bool) (A : End)
    (hA : OneSided (Preserver.roots opposite) A) {n m : ℕ} (hm : 2 ≤ m)
    (u : Fin n → V) (hu : ∀ a,u a ∈ LinearMap.range (sharp A).mulVecLin)
    (w : Fin m → V) (hw : ∀ a,w a ∈ Preserver.roots opposite)
    (hc : ∀ a d : Fin m, a ≠ d → ∃ p q : Fin n,
      pairing (u p) (w a)*pairing (u q) (w d)-
        pairing (u p) (w d)*pairing (u q) (w a) ≠ 0) :
    m ≤ (RankTwo.rootIndices opposite (LinearMap.range A.mulVecLin)).card := by
  classical
  letI : NeZero m := ⟨by omega⟩
  have hn (a : Fin m) : A *ᵥ w a ≠ 0 := by
    have hb : ∃ d : Fin m, a ≠ d := by
      by_cases ha : a=0
      · refine ⟨⟨1,by omega⟩,?_⟩
        subst a
        simp
      · exact ⟨0,ha⟩
    obtain ⟨d,had⟩ := hb
    obtain ⟨p,q,hpq⟩ := hc a d had
    intro hz
    apply hpq
    exact pairing_range_cross_zero (hu p) (hu q) (c:=0) (by simp [hz])
  have he (a : Fin m) : ∃ k : Fin 60, ∃ c : ℂ, c ≠ 0 ∧
      A *ᵥ w a = c • RankTwo.rootPoint opposite k :=
    (roots_iff opposite _).mp ((hA _ (hw a)).resolve_left (hn a))
  choose k c hk he using he
  have hi : Function.Injective k := by
    intro a d had
    by_contra hn
    obtain ⟨p,q,hpq⟩ := hc a d hn
    apply hpq
    apply pairing_range_cross_zero (hu p) (hu q) (c:=c a*(c d)⁻¹)
    rw [he a,he d,had,smul_smul]
    congr 1
    field_simp [hk d]
  have hmem (a : Fin m) : RankTwo.rootPoint opposite (k a) ∈ LinearMap.range A.mulVecLin := by
    refine ⟨(c a)⁻¹ • w a,?_⟩
    change A *ᵥ ((c a)⁻¹ • w a) = RankTwo.rootPoint opposite (k a)
    rw [Matrix.mulVec_smul,he a,smul_smul,inv_mul_cancel₀ (hk a),one_smul]
  let f : Fin m → ↑(RankTwo.rootIndices opposite (LinearMap.range A.mulVecLin)) :=
    fun a => ⟨k a,(RankTwo.mem_rootIndices _ _ _).mpr (hmem a)⟩
  have hf : Function.Injective f := fun a d hh => hi (congrArg Subtype.val hh)
  simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- Full sixty-point two-sided preservation excludes rank three. Both
actual ranges supply their bases. No general kernel-center count or
precomputed plane/certificate is a hypothesis. -/
theorem no_rank_three (opposite : Bool) (A : End)
    (h : TwoSided (Preserver.roots opposite) A) : A.rank ≠ 3 := by
  classical
  intro hr
  obtain ⟨u,hu,_,hspan⟩ := range_root_basis opposite (sharp A) h.2 (by rw [rank_sharp,hr])
  obtain ⟨v,hv,m,hm,w,hw,hc⟩ := plane_quotient_directions opposite
    (LinearMap.range (sharp A).mulVecLin) u hu hspan
  have hlo := image_directions_bound opposite A h.1 (by omega : 2 ≤ m) v hv w hw hc
  obtain ⟨t,ht,_,hsp⟩ := range_root_basis opposite A h.1 hr
  have hhi := root_plane_bound opposite (LinearMap.range A.mulVecLin) t ht hsp
  omega

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankThree
end
