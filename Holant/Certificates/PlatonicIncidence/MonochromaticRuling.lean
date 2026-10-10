import Holant.Certificates.RainbowOrbit.MaximalLines

/-! The two-factor Segre ruling from literal complex coefficient minors. -/
namespace Holant.Certificates.PlatonicIncidence
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Vanishing coefficient minors characterize proportional nonzero vectors. -/
theorem proportional_of_minors {ι : Type*} (u v : ι → ℂ)
    (hu : ∃ i, u i ≠ 0) (hv : ∃ i, v i ≠ 0)
    (h : ∀ i j, u i * v j - v i * u j = 0) : Proportional u v := by
  obtain ⟨j,hj⟩ := hv
  have huj : u j ≠ 0 := by
    intro hz
    obtain ⟨i,hi⟩ := hu
    have hh := h i j
    simp only [hz,mul_zero,sub_zero] at hh
    exact (mul_ne_zero hi hj) hh
  refine ⟨u j / v j,div_ne_zero huj hj,?_⟩
  funext i
  simp only [Pi.smul_apply,smul_eq_mul]
  apply (mul_right_cancel₀ hj)
  have hh := sub_eq_zero.mp (h i j)
  calc u i * v j = v i * u j := hh
    _ = (u j / v j * v i) * v j := by field_simp

/-- A nontrivial complex linear combination of two simple tensors has rank at
most one only if their left factors or their right factors are proportional.
The proof uses all actual 2-by-2 coefficient minors. -/
theorem outer_sum_rank_le_one_ruling {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u u' : ι → ℂ) (v v' : κ → ℂ)
    (hu : ∃ i,u i≠0) (hu' : ∃ i,u' i≠0)
    (hv : ∃ j,v j≠0) (hv' : ∃ j,v' j≠0)
    (a b : ℂ) (ha : a≠0) (hb : b≠0)
    (h : (a • Matrix.vecMulVec u v + b • Matrix.vecMulVec u' v').rank≤1) :
    Proportional u u' ∨ Proportional v v' := by
  have hm (i k : ι) (j l : κ) :
      a*b*(u i*u' k-u' i*u k)*(v j*v' l-v' j*v l)=0 := by
    have hh := minor_two_eq_zero_of_rank_le_one _ h i k j l
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec,
      Matrix.of_apply] at hh
    linear_combination hh
  by_cases huP : Proportional u u'
  · exact Or.inl huP
  · right
    apply proportional_of_minors v v' hv hv'
    have huM : ∃ i k,u i*u' k-u' i*u k≠0 := by
      by_contra hn
      push_neg at hn
      exact huP (proportional_of_minors u u' hu hu' hn)
    obtain ⟨i,k,hik⟩ := huM
    intro j l
    exact (mul_eq_zero.mp (hm i k j l)).resolve_left
      (mul_ne_zero (mul_ne_zero ha hb) hik)

/-- The ruling criterion for any of the three ordered actual matching maps. -/
theorem matching_sum_ruling (r : Fin 3) (U V U' V' S T : BinaryMatrix)
    (hU : U.det≠0) (hV : V.det≠0) (hU' : U'.det≠0) (hV' : V'.det≠0)
    (a b : ℂ) (ha : a≠0) (hb : b≠0)
    (he : matchingTensor r S T=a • matchingTensor r U V+b • matchingTensor r U' V') :
    Proportional U U' ∨ Proportional V V' := by
  have hr : (a • Matrix.vecMulVec (fun p : Bool×Bool => U p.1 p.2)
      (fun p : Bool×Bool => V p.1 p.2)+
      b • Matrix.vecMulVec (fun p : Bool×Bool => U' p.1 p.2)
      (fun p : Bool×Bool => V' p.1 p.2)).rank≤1 := by
    have hh := congrArg (flatten r) he
    simp only [flatten_add,flatten_smul] at hh
    have hh' : Matrix.vecMulVec (fun p : Bool×Bool => S p.1 p.2)
        (fun p : Bool×Bool => T p.1 p.2)=
        a • Matrix.vecMulVec (fun p : Bool×Bool => U p.1 p.2)
          (fun p : Bool×Bool => V p.1 p.2)+
        b • Matrix.vecMulVec (fun p : Bool×Bool => U' p.1 p.2)
          (fun p : Bool×Bool => V' p.1 p.2) := by
      fin_cases r <;> simpa [flatten,matchingTensor] using hh
    rw [←hh']
    exact Matrix.rank_vecMulVec_le _ _
  obtain ⟨i,j,hij⟩ := binary_has_nonzero_entry U hU
  obtain ⟨i',j',hij'⟩ := binary_has_nonzero_entry U' hU'
  obtain ⟨k,l,hkl⟩ := binary_has_nonzero_entry V hV
  obtain ⟨k',l',hkl'⟩ := binary_has_nonzero_entry V' hV'
  have hp := outer_sum_rank_le_one_ruling _ _ _ _ ⟨(i,j),hij⟩ ⟨(i',j'),hij'⟩
    ⟨(k,l),hkl⟩ ⟨(k',l'),hkl'⟩ a b ha hb hr
  rcases hp with ⟨c,hc,hp⟩ | ⟨c,hc,hp⟩
  · left
    exact ⟨c,hc,by ext i j; exact congrFun hp (i,j)⟩
  · right
    exact ⟨c,hc,by ext i j; exact congrFun hp (i,j)⟩

/-- Three distinct collinear actual products of one matching lie on a Segre
ruling: one of the two ordered binary factors is fixed projectively. -/
theorem matching_collinear_ruling (r : Fin 3) (U V U' V' S T : BinaryMatrix)
    (hU : U.det≠0) (hV : V.det≠0) (hU' : U'.det≠0) (hV' : V'.det≠0)
    (hS : S.det≠0) (hT : T.det≠0)
    (h01 : ¬Proportional (matchingTensor r U V) (matchingTensor r U' V'))
    (h20 : ¬Proportional (matchingTensor r S T) (matchingTensor r U V))
    (h21 : ¬Proportional (matchingTensor r S T) (matchingTensor r U' V'))
    (hcol : Projectivization.IsCollinear
      {Projectivization.mk ℂ (matchingTensor r U V) (matching_nonzero r U V hU hV),
       Projectivization.mk ℂ (matchingTensor r U' V') (matching_nonzero r U' V' hU' hV'),
       Projectivization.mk ℂ (matchingTensor r S T) (matching_nonzero r S T hS hT)}) :
    Proportional U U' ∨ Proportional V V' := by
  obtain ⟨a,b,ha,hb,he⟩ := (collinear_triple_iff _ _ _ _ _ _ h01 h20 h21).mp hcol
  exact matching_sum_ruling r U V U' V' S T hU hV hU' hV' a b ha hb he

/-- The ordered matching construction is linear in its second factor. -/
def matchingRightLinear (r : Fin 3) (U : BinaryMatrix) : BinaryMatrix →ₗ[ℂ] FourTensor where
  toFun := matchingTensor r U
  map_add' V W := by
    fin_cases r <;> funext x <;> simp [matchingTensor,P0,P1,P2,mul_add]
  map_smul' c V := by
    fin_cases r <;> funext x <;> simp [matchingTensor,P0,P1,P2,mul_left_comm]

/-- The ordered matching construction is linear in its first factor. -/
def matchingLeftLinear (r : Fin 3) (V : BinaryMatrix) : BinaryMatrix →ₗ[ℂ] FourTensor where
  toFun := fun U => matchingTensor r U V
  map_add' U W := by
    fin_cases r <;> funext x <;> simp [matchingTensor,P0,P1,P2,add_mul]
  map_smul' c U := by
    fin_cases r <;> funext x <;> simp [matchingTensor,P0,P1,P2,mul_assoc]

/-- Complete actual deck intersection with a ruling with fixed first factor.
This includes the exclusion of every other matching label. -/
theorem matching_mem_right_span_iff (r s : Fin 3) (U V V' S T : BinaryMatrix)
    (hU : U.det≠0) (hV : V.det≠0) (hV' : V'.det≠0)
    (hS : S.det≠0) (hT : T.det≠0) :
    matchingTensor s S T∈Submodule.span ℂ
      ({matchingTensor r U V,matchingTensor r U V'} : Set FourTensor) ↔
    s=r ∧ Proportional S U ∧ T∈Submodule.span ℂ ({V,V'} : Set BinaryMatrix) := by
  constructor
  · intro hm
    obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp hm
    have hsr : s=r := by
      by_contra hn
      exact no_mixed_matching_line r s (Ne.symm hn) U V U V' S T hU hV hU hV' hS hT a b he
    subst s
    have hsum : matchingTensor r U (a • V+b • V')=matchingTensor r S T := by
      change matchingRightLinear r U (a • V+b • V')=_
      simpa only [map_add,map_smul,matchingRightLinear,matchingLeftLinear,LinearMap.coe_mk,AddHom.coe_mk] using he
    obtain ⟨hSU,c,hc,hTc⟩ := proportional_matching_factors r S T U (a • V+b • V') hS hT
      ⟨1,one_ne_zero,by simpa using hsum.symm⟩
    refine ⟨rfl,hSU,?_⟩
    rw [hTc]
    exact Submodule.smul_mem _ c (Submodule.mem_span_pair.mpr ⟨a,b,rfl⟩)
  · rintro ⟨hs,⟨c,hc,rfl⟩,hm⟩
    subst s
    obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp hm
    rw [←he]
    have hlin : matchingTensor r (c • U) (a • V+b • V')=
        (c*a) • matchingTensor r U V+(c*b) • matchingTensor r U V' := by
      change matchingLeftLinear r (a • V+b • V') (c • U)=_
      rw [map_smul]
      change c • matchingRightLinear r U (a • V+b • V')=_
      rw [map_add,map_smul,map_smul,smul_add,smul_smul,smul_smul]
      rfl
    rw [hlin]
    exact Submodule.mem_span_pair.mpr ⟨c*a,c*b,rfl⟩

/-- Complete actual deck intersection with a ruling with fixed second factor. -/
theorem matching_mem_left_span_iff (r s : Fin 3) (U U' V S T : BinaryMatrix)
    (hU : U.det≠0) (hU' : U'.det≠0) (hV : V.det≠0)
    (hS : S.det≠0) (hT : T.det≠0) :
    matchingTensor s S T∈Submodule.span ℂ
      ({matchingTensor r U V,matchingTensor r U' V} : Set FourTensor) ↔
    s=r ∧ Proportional T V ∧ S∈Submodule.span ℂ ({U,U'} : Set BinaryMatrix) := by
  constructor
  · intro hm
    obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp hm
    have hsr : s=r := by
      by_contra hn
      exact no_mixed_matching_line r s (Ne.symm hn) U V U' V S T hU hV hU' hV hS hT a b he
    subst s
    have hsum : matchingTensor r (a • U+b • U') V=matchingTensor r S T := by
      change matchingLeftLinear r V (a • U+b • U')=_
      simpa only [map_add,map_smul,matchingRightLinear,matchingLeftLinear,LinearMap.coe_mk,AddHom.coe_mk] using he
    obtain ⟨⟨c,hc,hSc⟩,hTV⟩ := proportional_matching_factors r S T (a • U+b • U') V hS hT
      ⟨1,one_ne_zero,by simpa using hsum.symm⟩
    refine ⟨rfl,hTV,?_⟩
    rw [hSc]
    exact Submodule.smul_mem _ c (Submodule.mem_span_pair.mpr ⟨a,b,rfl⟩)
  · rintro ⟨hs,⟨c,hc,rfl⟩,hm⟩
    subst s
    obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp hm
    rw [←he]
    have hlin : matchingTensor r (a • U+b • U') (c • V)=
        (c*a) • matchingTensor r U V+(c*b) • matchingTensor r U' V := by
      change matchingRightLinear r (a • U+b • U') (c • V)=_
      rw [map_smul]
      change c • matchingLeftLinear r V (a • U+b • U')=_
      rw [map_add,map_smul,map_smul,smul_add,smul_smul,smul_smul]
      rfl
    rw [hlin]
    exact Submodule.mem_span_pair.mpr ⟨c*a,c*b,rfl⟩

end
end Holant.Certificates.PlatonicIncidence
