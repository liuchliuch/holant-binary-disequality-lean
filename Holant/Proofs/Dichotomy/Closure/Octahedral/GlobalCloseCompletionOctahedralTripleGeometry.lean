import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralFrames
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralTripleCertificate

/-! Coefficient extraction from the preserved marked-octahedral proof. Genuine range bases, finite 3x3-minor certificates,
and bilinear kernel projections exclude rank three. All four marked rows
are covered directly, so no freely conjugated two-sided predicate is assumed.
The only rank hypothesis is the local exhaustive case rank=3.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
open Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open scoped BigOperators Matrix

def directions (f : Form) : Set V := CoefficientSet {K | Direction f K}

theorem directions_iff (f : Form) (r : V) : r ∈ directions f ↔
    ∃ i : Fin 24, ∃ c : ℂ, c ≠ 0 ∧ r = c • point f i := by
  rw [directions,mem_coefficientSet_iff,Set.mem_setOf_eq]
  constructor
  · rintro ⟨c,hc,i,he⟩
    refine ⟨i,c,hc,?_⟩
    have hh := congrArg coordinates he
    have hcoord : coordinates (assemble r)=r := coordinates.apply_symm_apply r
    simpa only [hcoord,map_smul,point] using hh
  · rintro ⟨i,c,hc,rfl⟩
    refine ⟨c,hc,i,?_⟩
    change coordinates.symm (c • coordinates _) = _
    simp

theorem point_mem (f : Form) (i : Fin 24) : point f i ∈ directions f :=
  (directions_iff f _).mpr ⟨i,1,one_ne_zero,by simp⟩

def similarity (f : Form) : BinaryMatrix ≃ₗ[ℂ] BinaryMatrix where
  toFun := complexTheta f
  invFun := complexPull f
  left_inv := complexPull_complexTheta f
  right_inv := complexTheta_complexPull f
  map_add' U W := by simp [complexTheta,Matrix.mul_add,Matrix.add_mul]
  map_smul' c U := complexTheta_smul f c U

def chart (f : Form) : V ≃ₗ[ℂ] V :=
  (coordinates.symm.trans (similarity f)).trans coordinates

def axis (i : Fin 4) : Fin 24 := ⟨i.val,by omega⟩

theorem point_axis (f : Form) (i : Fin 4) :
    point f (axis i) = chart f (Pi.single i 1) := by
  have hs : OctahedralSeparator.standard (axis i) = OctahedralSeparator.q i := by
    fin_cases i <;> rfl
  have ha : assemble (Pi.single i 1) = complexMatrix (OctahedralSeparator.q i) := by
    rw [complexMatrix_q]
    ext a b
    fin_cases i <;> cases a <;> cases b <;>
      simp [assemble,Pi.single_apply,
        Holant.Certificates.MatchingProductBridge.quaternionBasis,
        Holant.Certificates.MatchingProductBridge.Q0,
        Holant.Certificates.MatchingProductBridge.Q1,
        Holant.Certificates.MatchingProductBridge.Q2,
        Holant.Certificates.MatchingProductBridge.Q3,Holant.Signature.equality]
  simp only [point,hs,complexMatrix_theta]
  change coordinates (complexTheta f _) = coordinates (complexTheta f (assemble (Pi.single i 1)))
  rw [ha]

theorem root_expansion (f : Form) (v : V) :
    v = ∑ i : Fin 4, (chart f).symm v i • point f (axis i) := by
  have hs : (∑ i : Fin 4, (chart f).symm v i • Pi.single i (1 : ℂ)) = (chart f).symm v := by
    ext j
    simp [Pi.single_apply]
  calc
    v = chart f ((chart f).symm v) := ((chart f).apply_symm_apply v).symm
    _ = chart f (∑ i : Fin 4, (chart f).symm v i • Pi.single i (1 : ℂ)) :=
      congrArg (chart f) hs.symm
    _ = _ := by simp only [map_sum,map_smul,←point_axis]

def rootIndices (f : Form) (W : Submodule ℂ V) : Finset (Fin 24) := by
  classical
  exact Finset.univ.filter fun i => point f i ∈ W

@[simp] theorem mem_rootIndices (f : Form) (W : Submodule ℂ V) (i : Fin 24) :
    i ∈ rootIndices f W ↔ point f i ∈ W := by
  classical
  simp [rootIndices]

/-- The actual preserved images of the four chart axes span the range.
No root basis or supporting subspace is an input to this producer. -/
theorem span_root_range (f : Form) (A : End) (hA : OneSided (directions f) A) :
    Submodule.span ℂ (Set.range (fun i : {i : Fin 24 // point f i ∈ LinearMap.range A.mulVecLin} =>
      point f i.val)) = LinearMap.range A.mulVecLin := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact i.property
  · rintro _ ⟨v,rfl⟩
    rw [root_expansion f v,map_sum]
    apply Submodule.sum_mem
    intro j hj
    rw [map_smul]
    have hh := hA _ (point_mem f (axis j))
    rcases hh with hz | hm
    · change (chart f).symm v j • (A *ᵥ point f (axis j)) ∈ _
      rw [hz,smul_zero]
      exact Submodule.zero_mem _
    · obtain ⟨k,c,hc,he⟩ := (directions_iff f _).mp hm
      have hk : point f k ∈ LinearMap.range A.mulVecLin := by
        refine ⟨c⁻¹ • point f (axis j),?_⟩
        change A *ᵥ (c⁻¹ • point f (axis j)) = point f k
        rw [Matrix.mulVec_smul,he,smul_smul,inv_mul_cancel₀ hc,one_smul]
      change (chart f).symm v j • (A *ᵥ point f (axis j)) ∈ _
      rw [he]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨k,hk⟩,rfl⟩))

theorem range_root_basis (f : Form) (A : End) (hA : OneSided (directions f) A)
    {r : ℕ} (hr : A.rank = r) :
    ∃ u : Fin r → Fin 24, LinearIndependent ℂ (fun i => point f (u i)) ∧
      (∀ i, point f (u i) ∈ LinearMap.range A.mulVecLin) ∧
      Submodule.span ℂ (Set.range (fun i => point f (u i))) = LinearMap.range A.mulVecLin := by
  classical
  let D := {i : Fin 24 // point f i ∈ LinearMap.range A.mulVecLin}
  let v : D → V := fun i => point f i.val
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' ℂ v
  letI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = r := by
    rw [←finrank_span_eq_card hli,hspan]
    change Module.finrank ℂ (Submodule.span ℂ (Set.range v)) = r
    rw [show Submodule.span ℂ (Set.range v) = LinearMap.range A.mulVecLin from span_root_range f A hA]
    exact hr
  let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => (a (e i)).val,hli.comp e e.injective,fun i => (a (e i)).property,?_⟩
  have he : Set.range (fun i : Fin r => point f (a (e i)).val) = Set.range (v ∘ a) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨e i,rfl⟩
    · rintro ⟨i,rfl⟩
      obtain ⟨j,rfl⟩ := e.surjective i
      exact ⟨j,rfl⟩
  rw [he,hspan]
  exact span_root_range f A hA

def normalFunctional (n : RawVector) : V →ₗ[ℂ] ℂ where
  toFun v := ∑ i : Fin 4, embed (n i)*v i
  map_add' u v := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' c v := by
    simp [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem embed_dot (n v : RawVector) :
    embed (rawDot n v) = normalFunctional n (lift v) := by
  simp [rawDot,normalFunctional,lift,Fin.sum_univ_succ,embed_add,embed_mul,add_assoc]


/-- A literal nonzero normal defines a genuine hyperplane; no rank flag is
supplied by the finite dictionary. -/
theorem normalFunctional_ne_zero (n : RawVector) (hn : n≠0) : normalFunctional n≠0 := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hn
  intro hz
  have he := congrArg (fun F : V→ₗ[ℂ] ℂ=>F (Pi.single i 1)) hz
  apply embed_ne_zero hi
  simpa [normalFunctional,Pi.single_apply] using he

theorem normal_kernel_bound (n : RawVector) (hn : n≠0) :
    Module.finrank ℂ (LinearMap.ker (normalFunctional n))≤3 := by
  have hp : 0<Module.finrank ℂ (LinearMap.range (normalFunctional n)) := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply normalFunctional_ne_zero n hn
    exact LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)
  have hd : Module.finrank ℂ V=4 := by
    simp only [V,Module.finrank_pi,Fintype.card_fin,Module.finrank_self]
  have hs := LinearMap.finrank_range_add_finrank_ker (normalFunctional n)
  rw [hd] at hs
  omega

theorem plane_membership (f : Form) (p : Fin 120) (i : Fin 24) (hf : f=0) :
    normalFunctional (planeNormal f p) (point f i)=0 ↔ i∈planeMask p := by
  rw [←lift_point,←embed_dot]
  have he (a : Scalar) : embed a=0 ↔ a=0 := by
    constructor
    · intro ha
      exact embed_injective (ha.trans embed_zero.symm)
    · rintro rfl
      exact embed_zero
  rw [he]
  exact (plane_certificate f p hf).2.1 i

/-- An actual independent root triple selects a checked hyperplane through
the old root indices. Its actual three-dimensional span equals that kernel. -/
theorem plane_of_span (f : Form) (W : Submodule ℂ V) (u : Fin 3→Fin 24)
    (hspan : Submodule.span ℂ (Set.range (fun i=>point f (u i)))=W)
    (hd : Module.finrank ℂ W=3) (hf : f=0) :
    ∃ p : Fin 120,rootIndices f W=planeMask p ∧
      ∀i : Fin 3,point f (planeTriple p i)∈W := by
  let p := planeCode (u 0) (u 1) (u 2)
  have cover := plane_covers_triple (u 0) (u 1) (u 2)
  have members (i : Fin 3) : u i∈planeMask p := by
    fin_cases i
    · exact cover.1
    · exact cover.2.1
    · exact cover.2.2
  have hW : W≤LinearMap.ker (normalFunctional (planeNormal f p)) := by
    rw [←hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact (plane_membership f p (u i) hf).mpr (members i)
  have eq : W=LinearMap.ker (normalFunctional (planeNormal f p)) :=
    Submodule.eq_of_le_of_finrank_le hW (by
      rw [hd]
      exact normal_kernel_bound _ (plane_certificate f p hf).1)
  refine ⟨p,?_,?_⟩
  · ext i
    rw [mem_rootIndices,eq,LinearMap.mem_ker]
    exact plane_membership f p i hf
  · intro i
    rw [eq,LinearMap.mem_ker]
    exact (plane_membership f p _ hf).mpr (plane_triple_mem p i)

theorem range_plane (f : Form) (A : End) (hA : OneSided (directions f) A)
    (hr : A.rank=3) (hf : f=0) :
    ∃p : Fin 120,rootIndices f (LinearMap.range A.mulVecLin)=planeMask p ∧
      ∀i : Fin 3,point f (planeTriple p i)∈LinearMap.range A.mulVecLin := by
  obtain ⟨u,_hu,_hm,hspan⟩ := range_root_basis f A hA hr
  exact plane_of_span f _ u hspan hr hf

theorem embed_table_cross (f : Form) (p : Fin 120) (r s : Fin 24) (i j : Fin 3) (hf : f=0) :
    embed (cross (projectedTable f p r) (projectedTable f p s) i j)=
      pairing (point f (planeTriple p i)) (point f r)*pairing (point f (planeTriple p j)) (point f s)-
      pairing (point f (planeTriple p i)) (point f s)*pairing (point f (planeTriple p j)) (point f r) := by
  subst f
  simp only [cross,projectedTable,embed_sub,embed_mul,pair_table_exact,embed_pair,lift_point]
  ring

theorem plane_separation (f : Form) (p : Fin 120) (a b : Fin 10) (hne : a≠b) (hf : f=0) :
    pairing (point f (planeTriple p (planeMinor f p a b 0))) (point f (planeWitness f p a))*
        pairing (point f (planeTriple p (planeMinor f p a b 1))) (point f (planeWitness f p b))-
      pairing (point f (planeTriple p (planeMinor f p a b 0))) (point f (planeWitness f p b))*
        pairing (point f (planeTriple p (planeMinor f p a b 1))) (point f (planeWitness f p a))≠0 := by
  rw [←embed_table_cross f p _ _ _ _ hf]
  exact embed_ne_zero ((plane_certificate f p hf).2.2 a b hne)

theorem projected_directions_bound (f : Form) (A : End) (hA : OneSided (directions f) A)
    {n m : ℕ} (hm : 2 ≤ m) (u : Fin n → V)
    (hu : ∀ i, u i ∈ LinearMap.range (sharp A).mulVecLin) (w : Fin m → Fin 24)
    (hw : ∀ a b : Fin m, a ≠ b → ∃ i j : Fin n,
      pairing (u i) (point f (w a))*pairing (u j) (point f (w b))-
        pairing (u i) (point f (w b))*pairing (u j) (point f (w a)) ≠ 0) :
    m ≤ (rootIndices f (LinearMap.range A.mulVecLin)).card := by
  classical
  letI : NeZero m := ⟨by omega⟩
  have hn (a : Fin m) : A *ᵥ point f (w a) ≠ 0 := by
    have hb : ∃ b : Fin m, a ≠ b := by
      by_cases ha : a=0
      · refine ⟨⟨1,by omega⟩,?_⟩
        subst a
        simp
      · exact ⟨0,ha⟩
    obtain ⟨b,hab⟩ := hb
    obtain ⟨i,j,hij⟩ := hw a b hab
    intro hz
    apply hij
    exact pairing_range_cross_zero (hu i) (hu j) (c:=0) (by simp [hz])
  have hc (a : Fin m) : ∃ k : Fin 24, ∃ c : ℂ, c ≠ 0 ∧
      A *ᵥ point f (w a) = c • point f k :=
    (directions_iff f _).mp ((hA _ (point_mem f _)).resolve_left (hn a))
  choose k c hc he using hc
  have hi : Function.Injective k := by
    intro a b hab
    by_contra hn
    obtain ⟨i,j,hij⟩ := hw a b hn
    apply hij
    apply pairing_range_cross_zero (hu i) (hu j) (c:=c a*(c b)⁻¹)
    rw [he a,he b,hab,smul_smul]
    congr 1
    field_simp [hc b]
  have hk (a : Fin m) : point f (k a) ∈ LinearMap.range A.mulVecLin := by
    refine ⟨(c a)⁻¹ • point f (w a),?_⟩
    change A *ᵥ ((c a)⁻¹ • point f (w a)) = point f (k a)
    rw [Matrix.mulVec_smul,he a,smul_smul,inv_mul_cancel₀ (hc a),one_smul]
  let g : Fin m → ↑(rootIndices f (LinearMap.range A.mulVecLin)) :=
    fun a => ⟨k a,(mem_rootIndices f _ _).mpr (hk a)⟩
  have hg : Function.Injective g := fun a b hh => hi (congrArg Subtype.val hh)
  simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective g hg


/-- The same genuine range/adjoint contradiction: at most nine root images
in a rank-three range, versus ten separated images forced by its adjoint. -/
theorem standard_no_rank_three (f : Form) (hf : f=0) (A : End) (h : TwoSided (directions f) A) : A.rank≠3 := by
  intro hA
  have hs : (sharp A).rank=3 := by rw [rank_sharp,hA]
  obtain ⟨p,_hp,hm⟩ := range_plane f (sharp A) h.2 hs hf
  have hlo : 10≤(rootIndices f (LinearMap.range A.mulVecLin)).card := by
    apply projected_directions_bound f A h.1 (by decide : 2≤10)
      (fun i : Fin 3=>point f (planeTriple p i)) hm (planeWitness f p)
    intro a b hab
    exact ⟨planeMinor f p a b 0,planeMinor f p a b 1,plane_separation f p a b hab hf⟩
  obtain ⟨q,hq,_⟩ := range_plane f A h.1 hA hf
  have hhi : (rootIndices f (LinearMap.range A.mulVecLin)).card≤9 := by
    rw [hq]
    exact plane_mask_bound q
  omega

/-- Every marked row uses the original Frobenius adjoint and its proved
Gram correction. No conjugated two-sided condition is assumed. -/
theorem no_rank_three (f : Form) (A : End) (h : TwoSided (directions f) A) : A.rank≠3 := by
  intro hr
  have pulled := RankFour.TwoSidedCompleteness.pull_twoSided f A h
  have rank : (RankFour.ExactAutomorphisms.pull f A).rank=3 :=
    (RankFour.TwoSidedCompleteness.pull_rank f A).trans hr
  exact standard_no_rank_three 0 rfl (RankFour.ExactAutomorphisms.pull f A) pulled rank

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
