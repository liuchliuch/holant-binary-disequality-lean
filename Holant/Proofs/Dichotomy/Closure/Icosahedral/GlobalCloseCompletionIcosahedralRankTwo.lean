import Holant.Certificates.MatchingProductBridge.GroupInverses
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralGoldenSix

/-! Generic I/opposite-I coefficient proof extracted from RankTwo/Source.
No old saved-State dispatcher or caller-supplied classification is imported.
This candidate retains the actual full sixty-point hypotheses and proof. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankTwo
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.RainbowOrbit
open Holant.Certificates.TetrahedralPreservers
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Preserver.Completion
open scoped BigOperators Matrix

/-- The exact existing kernel dictionary on binary coefficients. -/
def binaryFrame (opposite : Bool) :
    Matrix Bool Bool ℂ ≃ₗ[ℂ] Matrix Bool Bool ℂ := by
  cases opposite
  · exact LinearEquiv.refl ℂ (Matrix Bool Bool ℂ)
  · exact
      { toFun := OppositeIcosahedral.kappa
        invFun := OppositeIcosahedral.unkappa
        left_inv := OppositeIcosahedral.unkappa_kappa
        right_inv := OppositeIcosahedral.kappa_unkappa
        map_add' := by
          intro U W
          simp [OppositeIcosahedral.kappa,Matrix.mul_add,Matrix.add_mul]
        map_smul' := OppositeIcosahedral.kappa_smul }

def coefficientPush (opposite : Bool) : Matrix Bool Bool ℂ ≃ₗ[ℂ] V :=
  (binaryFrame opposite).trans coordinates
def coefficientPull (opposite : Bool) : V ≃ₗ[ℂ] Matrix Bool Bool ℂ :=
  (coefficientPush opposite).symm

theorem push_point (opposite : Bool) (i : Fin 60) :
    coefficientPush opposite (representative .icosahedral i) = rootPoint opposite i := by
  cases opposite <;> rfl

theorem pull_point (opposite : Bool) (i : Fin 60) :
    coefficientPull opposite (rootPoint opposite i) = representative .icosahedral i := by
  rw [←push_point]
  exact (coefficientPush opposite).symm_apply_apply _

private theorem pull_point_linear (opposite : Bool) (i : Fin 60) :
    (coefficientPull opposite).toLinearMap (rootPoint opposite i) =
      representative .icosahedral i :=
  pull_point opposite i

private theorem standard_point (i : Fin 60) :
    rootPoint false i = coordinates (representative .icosahedral i) :=
  (push_point false i).symm

private theorem map_span_pair (f : V →ₗ[ℂ] Matrix Bool Bool ℂ) (u v : V) :
    (Submodule.span ℂ ({u,v} : Set V)).map f =
      Submodule.span ℂ ({f u,f v} : Set (Matrix Bool Bool ℂ)) := by
  rw [Submodule.map_span]
  simp only [Set.image_insert_eq,Set.image_singleton]

private theorem push_product (opposite : Bool) (i j : Fin 60) :
    coefficientPush opposite (representative .icosahedral i * representative .icosahedral j) =
      (productScale .icosahedral i j : ℂ) • rootPoint opposite (productIndex .icosahedral i j) := by
  calc
    _ = coefficientPush opposite ((productScale .icosahedral i j : ℂ) •
        representative .icosahedral (productIndex .icosahedral i j)) :=
      congrArg (coefficientPush opposite) (mul_exact .icosahedral i j)
    _ = (productScale .icosahedral i j : ℂ) •
        coefficientPush opposite (representative .icosahedral (productIndex .icosahedral i j)) :=
      (coefficientPush opposite).map_smul _ _
    _ = _ := congrArg (fun v : V => (productScale .icosahedral i j : ℂ) • v)
      (push_point opposite (productIndex .icosahedral i j))

private theorem member_of_eq (W : Submodule ℂ V) {u v : V}
    (h : u = v) (hv : v ∈ W) : u ∈ W :=
  h.symm ▸ hv

private theorem smul_member_of_eq (W : Submodule ℂ V) {u v : V} {c : ℂ}
    (h : u = c • v) (hv : v ∈ W) : u ∈ W :=
  member_of_eq W h (W.smul_mem c hv)

def rootIndices (opposite : Bool) (W : Submodule ℂ V) : Finset (Fin 60) := by
  classical
  exact Finset.univ.filter (fun i => rootPoint opposite i ∈ W)

@[simp] theorem mem_rootIndices (opposite : Bool) (W : Submodule ℂ V) (i : Fin 60) :
    i ∈ rootIndices opposite W ↔ rootPoint opposite i ∈ W := by
  classical
  simp [rootIndices]

/-- Same indices, not an abstract isomorphism of unordered configurations. -/
theorem rootIndices_pull (opposite : Bool) (W : Submodule ℂ V) :
    rootIndices opposite W =
      deletion .icosahedral (W.map (coefficientPull opposite).toLinearMap) := by
  apply Finset.ext
  intro i
  have hmem : rootPoint opposite i ∈ W ↔
      representative .icosahedral i ∈ W.map (coefficientPull opposite).toLinearMap := by
    constructor
    · intro hi
      exact ⟨rootPoint opposite i,hi,pull_point_linear opposite i⟩
    · rintro ⟨v,hv,he⟩
      have hvp : v = rootPoint opposite i := (coefficientPull opposite).injective
        (he.trans (pull_point_linear opposite i).symm)
      exact member_of_eq W hvp.symm hv
  exact (mem_rootIndices opposite W i).trans
    (hmem.trans (mem_deletion .icosahedral (W.map (coefficientPull opposite).toLinearMap) i).symm)

theorem rootIndices_bound (opposite : Bool) (W : Submodule ℂ V)
    (hW : Module.finrank ℂ W ≤ 2) : (rootIndices opposite W).card ≤ 5 := by
  have he : Module.finrank ℂ W =
      Module.finrank ℂ (W.map (coefficientPull opposite).toLinearMap) :=
    (Submodule.equivMapOfInjective (coefficientPull opposite).toLinearMap
      (coefficientPull opposite).injective W).finrank_eq
  have hd : Module.finrank ℂ (W.map (coefficientPull opposite).toLinearMap) ≤ 2 :=
    he.symm.le.trans hW
  have hcard : (rootIndices opposite W).card =
      (deletion .icosahedral (W.map (coefficientPull opposite).toLinearMap)).card :=
    congrArg Finset.card (rootIndices_pull opposite W)
  exact hcard.le.trans (deletion_bound .icosahedral _ hd)

/-- Root bases come from the actual map range and the existing complete
FULL sixty directions. T axes only span the domain, not the image target. -/
theorem span_root_range (opposite : Bool) (A : End) (hA : OneSided (Preserver.roots opposite) A) :
    Submodule.span ℂ (Set.range
      (fun i : {i : Fin 60 // rootPoint opposite i ∈ LinearMap.range A.mulVecLin} =>
        rootPoint opposite i.val)) = LinearMap.range A.mulVecLin := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact i.property
  · conv_lhs => rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    have hh := hA _ (roots_axis opposite j)
    rw [Matrix.mulVec_single_one] at hh
    rcases hh with hz | hm
    · rw [hz]
      exact Submodule.zero_mem _
    · obtain ⟨k,c,hc,he⟩ := (roots_iff opposite _).mp hm
      have hk : rootPoint opposite k ∈ LinearMap.range A.mulVecLin := by
        refine ⟨c⁻¹ • Pi.single j 1,?_⟩
        change A *ᵥ (c⁻¹ • Pi.single j 1) = rootPoint opposite k
        rw [Matrix.mulVec_smul,Matrix.mulVec_single_one,he,smul_smul,
          inv_mul_cancel₀ hc,one_smul]
      rw [he]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨k,hk⟩,rfl⟩)

theorem range_root_pair (opposite : Bool) (A : End)
    (hA : OneSided (Preserver.roots opposite) A) (hr : A.rank = 2) :
    ∃ u : Fin 2 → Fin 60, LinearIndependent ℂ (fun i => rootPoint opposite (u i)) ∧
      (∀ i,rootPoint opposite (u i) ∈ LinearMap.range A.mulVecLin) ∧
      Submodule.span ℂ (Set.range (fun i => rootPoint opposite (u i))) =
        LinearMap.range A.mulVecLin := by
  classical
  let D := {i : Fin 60 // rootPoint opposite i ∈ LinearMap.range A.mulVecLin}
  let v : D → V := fun i => rootPoint opposite i.val
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' ℂ v
  letI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = 2 := by
    rw [←finrank_span_eq_card hli,hspan]
    change Module.finrank ℂ (Submodule.span ℂ (Set.range v)) = 2
    rw [show Submodule.span ℂ (Set.range v) = LinearMap.range A.mulVecLin
      from span_root_range opposite A hA]
    exact hr
  let e : Fin 2 ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => (a (e i)).val,hli.comp e e.injective,fun i => (a (e i)).property,?_⟩
  have he : Set.range (fun i : Fin 2 => rootPoint opposite (a (e i)).val) = Set.range (v ∘ a) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨e i,rfl⟩
    · rintro ⟨i,rfl⟩
      obtain ⟨j,rfl⟩ := e.surjective i
      exact ⟨j,rfl⟩
  rw [he,hspan]
  exact span_root_range opposite A hA

/-- BOTH image root-pair spans are produced, with the original bilinear
sharp and no assumed secant or factorization. -/
theorem two_ranges_root_pairs (opposite : Bool) (A : End)
    (h : TwoSided (Preserver.roots opposite) A) (hr : A.rank = 2) :
    ∃ u v : Fin 2 → Fin 60,
      LinearIndependent ℂ (fun i => rootPoint opposite (u i)) ∧
      LinearIndependent ℂ (fun i => rootPoint opposite (v i)) ∧
      (∀ i,rootPoint opposite (u i) ∈ LinearMap.range A.mulVecLin) ∧
      (∀ i,rootPoint opposite (v i) ∈ LinearMap.range (sharp A).mulVecLin) ∧
      Submodule.span ℂ (Set.range (fun i => rootPoint opposite (u i))) =
        LinearMap.range A.mulVecLin ∧
      Submodule.span ℂ (Set.range (fun i => rootPoint opposite (v i))) =
        LinearMap.range (sharp A).mulVecLin := by
  obtain ⟨u,hu,hm,hsp⟩ := range_root_pair opposite A h.1 hr
  obtain ⟨v,hv,hn,ht⟩ := range_root_pair opposite (sharp A) h.2 (by rw [rank_sharp,hr])
  exact ⟨u,v,hu,hv,hm,hn,hsp,ht⟩

theorem subspace_secant (opposite : Bool) (W : Submodule ℂ V)
    (hW : Module.finrank ℂ W ≤ 2) (i j : Fin 60) (hij : i ≠ j)
    (hi : rootPoint opposite i ∈ W) (hj : rootPoint opposite j ∈ W) :
    ∃ t : Fin 722, rootIndices opposite W = globalLine .icosahedral t := by
  classical
  have htwo : 2 ≤ (rootIndices opposite W).card := by
    have hh := Finset.one_lt_card.mpr
      ⟨i,(mem_rootIndices _ _ _).mpr hi,j,(mem_rootIndices _ _ _).mpr hj,hij⟩
    omega
  have he : Module.finrank ℂ W =
      Module.finrank ℂ (W.map (coefficientPull opposite).toLinearMap) :=
    (Submodule.equivMapOfInjective (coefficientPull opposite).toLinearMap
      (coefficientPull opposite).injective W).finrank_eq
  have hd : Module.finrank ℂ (W.map (coefficientPull opposite).toLinearMap) ≤ 2 :=
    he.symm.le.trans hW
  rcases deletion_classification .icosahedral _ hd with h | ⟨t,ht⟩
  · have hsmall : (rootIndices opposite W).card ≤ 1 :=
      (congrArg Finset.card (rootIndices_pull opposite W)).le.trans h
    omega
  · exact ⟨t,(rootIndices_pull _ _).trans ht⟩

private theorem translated_identity_mem (g : PlatonicModel) (i : Fin (size g))
    (b : Fin (baseCount g)) : i ∈ translatedLine g i b :=
  Finset.mem_image.mpr
    ⟨identityIndex g,(base_anchors g b).2.2.1,product_identity_right g i⟩

private theorem translated_anchor_mem (g : PlatonicModel) (i : Fin (size g))
    (b : Fin (baseCount g)) : productIndex g i (baseAnchor g b) ∈ translatedLine g i b :=
  Finset.mem_image.mpr ⟨baseAnchor g b,(base_anchors g b).2.2.2,rfl⟩

private theorem root_of_line_member (opposite : Bool) (W : Submodule ℂ V)
    (T : Finset (Fin 60)) (h : rootIndices opposite W = T)
    (x : Fin 60) (hx : x ∈ T) : rootPoint opposite x ∈ W := by
  subst T
  exact (mem_rootIndices opposite W x).mp hx

/-- Every produced image line is a literal translate of one of the old
31 identity secants. The selected two vectors belong to the actual range. -/
theorem translated_pair_in_subspace (opposite : Bool) (W : Submodule ℂ V)
    (hW : Module.finrank ℂ W ≤ 2) (j k : Fin 60) (hjk : j ≠ k)
    (hjW : rootPoint opposite j ∈ W) (hkW : rootPoint opposite k ∈ W) :
    ∃ i : Fin 60, ∃ b : Fin 31,
      coefficientPush opposite (representative .icosahedral i) ∈ W ∧
      coefficientPush opposite
        (representative .icosahedral i * representative .icosahedral (baseAnchor .icosahedral b)) ∈ W := by
  classical
  obtain ⟨t,ht⟩ := subspace_secant opposite W hW j k hjk hjW hkW
  let i : Fin 60 := (globalWitness .icosahedral t).1
  let b : Fin 31 := (globalWitness .icosahedral t).2
  have hline : globalLine .icosahedral t = translatedLine .icosahedral i b :=
    globalLine_eq_translated .icosahedral t
  have hsaved : rootIndices opposite W = translatedLine .icosahedral i b := ht.trans hline
  have him : rootPoint opposite i ∈ W :=
    root_of_line_member opposite W _ hsaved i (translated_identity_mem .icosahedral i b)
  have hjm : rootPoint opposite (productIndex .icosahedral i (baseAnchor .icosahedral b)) ∈ W :=
    root_of_line_member opposite W _ hsaved _ (translated_anchor_mem .icosahedral i b)
  refine ⟨i,b,?_,?_⟩
  · exact member_of_eq W (push_point opposite i) him
  · exact smul_member_of_eq W (push_product opposite i (baseAnchor .icosahedral b)) hjm

/-- Dual inverse of the exact dictionary frame, used only on coefficients.
For opposite=true this is unkappa, not a falsely identified native-X row. -/
def sourceFrame (opposite : Bool) (U : Matrix Bool Bool ℂ) : Matrix Bool Bool ℂ :=
  if opposite then OppositeIcosahedral.unkappa U else U

theorem sourceFrame_mem (opposite : Bool) {U : Matrix Bool Bool ℂ}
    (hU : groupDirection .icosahedral U) : Dictionary.direction opposite (sourceFrame opposite U) := by
  cases opposite
  · exact hU
  · have ht := (OppositeIcosahedral.output_transfer_iff U).mpr
        ((Dictionary.right_X false U).mpr hU)
    have hh := (Dictionary.right_X true (OppositeIcosahedral.binaryTransport U)).mp ht
    simpa only [sourceFrame,if_true,Dictionary.direction,OppositeIcosahedral.unkappa,
      OppositeIcosahedral.binaryTransport,OppositeIcosahedral.D_transpose] using hh

private theorem assemble_coordinates (U : Matrix Bool Bool ℂ) :
    assemble (coordinates U) = U :=
  assemble_coefficient U

private theorem sandwich_coordinates (L R U : Matrix Bool Bool ℂ) :
    sandwich L R *ᵥ coordinates U = coordinates (L * U * R) := by
  rw [sandwich_action,assemble_coordinates]

theorem frame_pairing (opposite : Bool) (U W : Matrix Bool Bool ℂ) :
    pairing (coefficientPush opposite U) (coordinates (sourceFrame opposite W)) =
      pairing (coordinates U) (coordinates W) := by
  cases opposite
  · rfl
  · change pairing (coordinates (OppositeIcosahedral.kappa U))
      (coordinates (OppositeIcosahedral.unkappa W)) = _
    calc
      _ = pairing ((sandwich OppositeIcosahedral.Dinv OppositeIcosahedral.Dinv) *ᵥ coordinates U)
          (coordinates (OppositeIcosahedral.unkappa W)) := by
        rw [sandwich_coordinates]
        rw [OppositeIcosahedral.kappa,OppositeIcosahedral.Dinv_transpose]
      _ = pairing (coordinates U)
          (sharp (sandwich OppositeIcosahedral.Dinv OppositeIcosahedral.Dinv) *ᵥ
            coordinates (OppositeIcosahedral.unkappa W)) := pairing_adjoint _ _ _
      _ = pairing (coordinates U) (coordinates W) := by
        rw [sharp_sandwich,OppositeIcosahedral.Dinv_transpose,sandwich_coordinates]
        change pairing (coordinates U) (coordinates (OppositeIcosahedral.kappa
          (OppositeIcosahedral.unkappa W))) = _
        rw [OppositeIcosahedral.kappa_unkappa]

theorem left_pairing_cancel (U W R : Matrix Bool Bool ℂ) (hU : U.det ≠ 0) :
    pairing (coordinates (U*W)) (coordinates (U.transpose⁻¹*R)) =
      pairing (coordinates W) (coordinates R) := by
  have ht : U.transpose.det ≠ 0 := by simpa only [Matrix.det_transpose] using hU
  calc
    _ = pairing ((sandwich U 1) *ᵥ coordinates W) (coordinates (U.transpose⁻¹*R)) := by
      rw [sandwich_coordinates,Matrix.mul_one]
    _ = pairing (coordinates W) (sharp (sandwich U 1) *ᵥ coordinates (U.transpose⁻¹*R)) :=
      pairing_adjoint _ _ _
    _ = pairing (coordinates W) (coordinates R) := by
      rw [sharp_sandwich,Matrix.transpose_one,sandwich_coordinates,Matrix.mul_one,
        ←Matrix.mul_assoc,Matrix.mul_nonsing_inv U.transpose (isUnit_iff_ne_zero.mpr ht),Matrix.one_mul]

theorem frame_left_pairing (opposite : Bool) (U W R : Matrix Bool Bool ℂ) (hU : U.det ≠ 0) :
    pairing (coefficientPush opposite (U*W))
      (coordinates (sourceFrame opposite (U.transpose⁻¹*R))) =
        pairing (coordinates W) (coordinates R) := by
  rw [frame_pairing,left_pairing_cancel U W R hU]

theorem standard_identity : rootPoint false 0 = coordinates (1 : Matrix Bool Bool ℂ) := by
  change coordinates (representative .icosahedral (0 : Fin 60)) =
    coordinates (1 : Matrix Bool Bool ℂ)
  exact congrArg coordinates (representative_identity .icosahedral)

def transportedWitness (opposite : Bool) (i : Fin 60) (b : Fin 31) (a : Fin 6) : V :=
  coordinates (sourceFrame opposite ((representative .icosahedral i).transpose⁻¹ *
    representative .icosahedral (sixWitness b a)))

theorem transportedWitness_mem (opposite : Bool) (i : Fin 60) (b : Fin 31) (a : Fin 6) :
    transportedWitness opposite i b a ∈ Preserver.roots opposite := by
  let R : Matrix Bool Bool ℂ := (representative .icosahedral i).transpose⁻¹ *
    representative .icosahedral (sixWitness b a)
  have hR : groupDirection .icosahedral R :=
    RainbowOrbit.groupDirection_mul .icosahedral
      (MatchingProductBridge.groupDirection_inverse .icosahedral
        (MatchingProductBridge.groupDirection_transpose .icosahedral
          (representative_mem .icosahedral i)))
      (representative_mem .icosahedral (sixWitness b a))
  exact ⟨sourceFrame opposite R,sourceFrame_mem opposite hR,rfl⟩

/-- The exact finite certificate survives actual U multiplication and the
correct Frobenius dual inverse of the opposite coefficient dictionary. -/
theorem transported_six (opposite : Bool) (i : Fin 60) (b : Fin 31) (a d : Fin 6) (had : a ≠ d) :
    pairing (coefficientPush opposite (representative .icosahedral i)) (transportedWitness opposite i b a) *
      pairing (coefficientPush opposite (representative .icosahedral i *
        representative .icosahedral (baseAnchor .icosahedral b))) (transportedWitness opposite i b d) -
    pairing (coefficientPush opposite (representative .icosahedral i)) (transportedWitness opposite i b d) *
      pairing (coefficientPush opposite (representative .icosahedral i *
        representative .icosahedral (baseAnchor .icosahedral b))) (transportedWitness opposite i b a) ≠ 0 := by
  let U := representative .icosahedral i
  have hU : U.det ≠ 0 := representative_det_ne_zero .icosahedral i
  have h0 (a : Fin 6) : pairing (coefficientPush opposite U) (transportedWitness opposite i b a) =
      pairing (rootPoint false 0) (rootPoint false (sixWitness b a)) := by
    change pairing (coefficientPush opposite U)
      (coordinates (sourceFrame opposite (U.transpose⁻¹ *
        representative .icosahedral (sixWitness b a)))) = _
    have hh : pairing (coefficientPush opposite U)
        (coordinates (sourceFrame opposite (U.transpose⁻¹ *
          representative .icosahedral (sixWitness b a)))) =
        pairing (coordinates 1) (coordinates (representative .icosahedral (sixWitness b a))) := by
      simpa only [Matrix.mul_one] using
        frame_left_pairing opposite U 1 (representative .icosahedral (sixWitness b a)) hU
    exact hh.trans
      (congrArg₂ pairing standard_identity.symm (standard_point (sixWitness b a)).symm)
  have h1 (a : Fin 6) : pairing (coefficientPush opposite (U *
      representative .icosahedral (baseAnchor .icosahedral b))) (transportedWitness opposite i b a) =
      pairing (rootPoint false (baseAnchor .icosahedral b)) (rootPoint false (sixWitness b a)) := by
    change pairing (coefficientPush opposite (U * representative .icosahedral (baseAnchor .icosahedral b)))
      (coordinates (sourceFrame opposite (U.transpose⁻¹ *
        representative .icosahedral (sixWitness b a)))) = _
    exact (frame_left_pairing opposite U (representative .icosahedral (baseAnchor .icosahedral b))
      (representative .icosahedral (sixWitness b a)) hU).trans
        (congrArg₂ pairing (standard_point (baseAnchor .icosahedral b)).symm
          (standard_point (sixWitness b a)).symm)
  change pairing (coefficientPush opposite U) (transportedWitness opposite i b a) *
      pairing (coefficientPush opposite (U * representative .icosahedral (baseAnchor .icosahedral b)))
        (transportedWitness opposite i b d) -
    pairing (coefficientPush opposite U) (transportedWitness opposite i b d) *
      pairing (coefficientPush opposite (U * representative .icosahedral (baseAnchor .icosahedral b)))
        (transportedWitness opposite i b a) ≠ 0
  rw [h0 a,h0 d,h1 a,h1 d]
  exact identity_six b a d had

private theorem pairing_add_left (u v r : V) :
    pairing (u+v) r = pairing u r + pairing v r := by
  simp [pairing,mul_add,add_mul,Finset.sum_add_distrib]

private theorem cross_zero_of_span {r s u v a b : V}
    (hu : u ∈ Submodule.span ℂ ({r,s} : Set V))
    (hv : v ∈ Submodule.span ℂ ({r,s} : Set V))
    (h : pairing r a*pairing s b-pairing r b*pairing s a = 0) :
    pairing u a*pairing v b-pairing u b*pairing v a = 0 := by
  obtain ⟨c,d,he⟩ := Submodule.mem_span_pair.mp hu
  obtain ⟨e,f,hf⟩ := Submodule.mem_span_pair.mp hv
  calc
    _ = (c*f-d*e)*(pairing r a*pairing s b-pairing r b*pairing s a) := by
      rw [←he,←hf]
      simp only [pairing_add_left,pairing_smul_left]
      ring
    _ = 0 := by rw [h,mul_zero]

/-- Every actual independent root pair, in EITHER original dictionary,
has at least six distinct nonzero directions in its bilinear quotient.
The witnesses are produced from old complete secants and GoldenSix;
neither secant completeness nor a failed-certificate premise is supplied. -/
theorem pair_quotient_six (opposite : Bool) (j k : Fin 60) (hjk : j ≠ k) :
    ∃ w : Fin 6 → V, (∀ a, w a ∈ Preserver.roots opposite) ∧
      ∀ a b : Fin 6, a ≠ b →
        pairing (rootPoint opposite j) (w a)*pairing (rootPoint opposite k) (w b)-
        pairing (rootPoint opposite j) (w b)*pairing (rootPoint opposite k) (w a) ≠ 0 := by
  let W : Submodule ℂ V := Submodule.span ℂ ({rootPoint opposite j,rootPoint opposite k} : Set V)
  have hmap : W.map (coefficientPull opposite).toLinearMap =
      Submodule.span ℂ
        ({representative .icosahedral j,representative .icosahedral k} : Set (Matrix Bool Bool ℂ)) := by
    calc
      _ = Submodule.span ℂ
          ({(coefficientPull opposite).toLinearMap (rootPoint opposite j),
            (coefficientPull opposite).toLinearMap (rootPoint opposite k)} :
              Set (Matrix Bool Bool ℂ)) :=
        map_span_pair (coefficientPull opposite).toLinearMap (rootPoint opposite j) (rootPoint opposite k)
      _ = _ := congrArg₂ (fun U W : Matrix Bool Bool ℂ =>
        Submodule.span ℂ ({U,W} : Set (Matrix Bool Bool ℂ)))
        (pull_point_linear opposite j) (pull_point_linear opposite k)
  have he : Module.finrank ℂ W =
      Module.finrank ℂ (W.map (coefficientPull opposite).toLinearMap) :=
    (Submodule.equivMapOfInjective (coefficientPull opposite).toLinearMap
      (coefficientPull opposite).injective W).finrank_eq
  have hdim : Module.finrank ℂ W = 2 :=
    he.trans ((congrArg (fun S : Submodule ℂ (Matrix Bool Bool ℂ) => Module.finrank ℂ S) hmap).trans
      (pair_finrank .icosahedral j k hjk))
  have hjW : rootPoint opposite j ∈ W := Submodule.subset_span (by simp)
  have hkW : rootPoint opposite k ∈ W := Submodule.subset_span (by simp)
  obtain ⟨i,t,hu,hv⟩ := translated_pair_in_subspace opposite W hdim.le j k hjk hjW hkW
  refine ⟨transportedWitness opposite i t,transportedWitness_mem opposite i t,?_⟩
  intro a b hab hz
  apply transported_six opposite i t a b hab
  exact cross_zero_of_span hu hv hz

/-- Distinct nonzero quotient directions inject into the ACTUAL target
root indices. Its premises are immediately produced by pair_quotient_six,
not caller-supplied equations or a universal reduction. -/
theorem six_image_bound (opposite : Bool) (A : End)
    (hA : OneSided (Preserver.roots opposite) A) (u v : V)
    (hu : u ∈ LinearMap.range (sharp A).mulVecLin)
    (hv : v ∈ LinearMap.range (sharp A).mulVecLin) (w : Fin 6 → V)
    (hw : ∀ a, w a ∈ Preserver.roots opposite)
    (hc : ∀ a b : Fin 6, a ≠ b →
      pairing u (w a)*pairing v (w b)-pairing u (w b)*pairing v (w a) ≠ 0) :
    6 ≤ (rootIndices opposite (LinearMap.range A.mulVecLin)).card := by
  classical
  have hn (a : Fin 6) : A *ᵥ w a ≠ 0 := by
    have hb : ∃ b : Fin 6, a ≠ b := by
      by_cases ha : a = 0
      · subst a
        exact ⟨1,by decide⟩
      · exact ⟨0,ha⟩
    obtain ⟨b,hab⟩ := hb
    intro hz
    apply hc a b hab
    exact pairing_range_cross_zero hu hv (c:=0) (by simp [hz])
  have hp (a : Fin 6) : ∃ k : Fin 60, ∃ c : ℂ, c ≠ 0 ∧ A *ᵥ w a = c • rootPoint opposite k :=
    (roots_iff opposite _).mp ((hA _ (hw a)).resolve_left (hn a))
  choose k c hcn he using hp
  have hi : Function.Injective k := by
    intro a b hab
    by_contra hn
    apply hc a b hn
    apply pairing_range_cross_zero hu hv (c:=c a*(c b)⁻¹)
    rw [he a,he b,hab,smul_smul]
    congr 1
    field_simp [hcn b]
  have hk (a : Fin 6) : rootPoint opposite (k a) ∈ LinearMap.range A.mulVecLin := by
    refine ⟨(c a)⁻¹ • w a,?_⟩
    change A *ᵥ ((c a)⁻¹ • w a) = rootPoint opposite (k a)
    rw [Matrix.mulVec_smul,he a,smul_smul,inv_mul_cancel₀ (hcn a),one_smul]
  let f : Fin 6 → ↑(rootIndices opposite (LinearMap.range A.mulVecLin)) :=
    fun a => ⟨k a,(mem_rootIndices _ _ _).mpr (hk a)⟩
  have hf : Function.Injective f := fun a b hh => hi (congrArg Subtype.val hh)
  simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- Arbitrary COMPLEX full-I/opposite-I two-sided maps cannot have rank
two. No finite atlas of maps and no prepared-tensor hypothesis is used. -/
theorem no_rank_two (opposite : Bool) (A : End) (h : TwoSided (Preserver.roots opposite) A) :
    A.rank ≠ 2 := by
  intro hr
  obtain ⟨u,v,hu,hv,hm,hn,hsp,ht⟩ := two_ranges_root_pairs opposite A h hr
  have hvne : v 0 ≠ v 1 := by
    intro he
    have hh := hv.injective (congrArg (rootPoint opposite) he)
    norm_num at hh
  obtain ⟨w,hw,hc⟩ := pair_quotient_six opposite (v 0) (v 1) hvne
  have hlo : 6 ≤ (rootIndices opposite (LinearMap.range A.mulVecLin)).card := by
    exact six_image_bound opposite A h.1 _ _ (hn 0) (hn 1) w hw hc
  have hdim : Module.finrank ℂ (LinearMap.range A.mulVecLin) = 2 := by
    rw [←hsp]
    simpa using finrank_span_eq_card hu
  have hhi := rootIndices_bound opposite (LinearMap.range A.mulVecLin) hdim.le
  omega

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankTwo
end
