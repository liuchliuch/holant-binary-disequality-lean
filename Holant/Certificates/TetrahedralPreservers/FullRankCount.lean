import Holant.Certificates.TetrahedralPreservers.FullRankClassification
import Holant.Certificates.TetrahedralPreservers.RankOneCount

/-! Exact projective rank-four counts, with arbitrary-input completeness. -/
noncomputable section
namespace Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.MatchingProductBridge
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

theorem complex_sign_injective : Function.Injective (fun b : Bool => (signBit b : ℂ)) := by
  intro a b h
  cases a <;> cases b
  · rfl
  · norm_num [signBit] at h
  · norm_num [signBit] at h
  · rfl

theorem signedMap_injective (σ τ : Equiv.Perm (Fin 3)) (ε δ : Fin 3 → Bool)
    (h : signedMap σ ε = signedMap τ δ) : σ=τ ∧ ε=δ := by
  have hcol (i : Fin 3) := congrArg (fun A : End => A *ᵥ Pi.single i.succ 1) h
  simp only [signedMap_axis] at hcol
  have hστ : σ=τ := by
    apply Equiv.ext
    intro i
    by_contra hi
    have hs : (σ i).succ ≠ (τ i).succ := fun hh => hi (Fin.succ_inj.mp hh)
    have hh := congrFun (hcol i) (σ i).succ
    simp [Pi.single_apply,hs,Ne.symm hs] at hh
    exact (signBit_ne_zero (ε i)) hh
  subst τ
  refine ⟨rfl,?_⟩
  funext i
  have hh := congrFun (hcol i) (σ i).succ
  simp only [Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,mul_one] at hh
  exact complex_sign_injective hh

theorem fullMap_first (i : FullIndex) : fullMap i *ᵥ Pi.single (0 : Fin 4) 1 = standardPoint i.1 := by
  rw [fullMap,← Matrix.mulVec_mulVec,signedMap_first,leftMap_first]

theorem fullMap_projectively_injective (a b : FullIndex) (c : ℂ)
    (h : fullMap a=c • fullMap b) : a=b := by
  have hfirst := congrArg (fun A : End => A *ᵥ Pi.single (0 : Fin 4) 1) h
  simp only [fullMap_first,Matrix.smul_mulVec] at hfirst
  have hindex := standardPoint_projectively_injective a.1 b.1 c hfirst
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (standardPoint_ne_zero a.1)
  have hc : c=1 := by
    rw [← hindex] at hfirst
    have hh := congrFun hfirst i
    apply mul_right_cancel₀ hi
    simpa using hh.symm
  rcases a with ⟨a,σ,ε⟩
  rcases b with ⟨b,τ,δ⟩
  change a=b at hindex
  subst b
  have hL := (rank_four_iff_det_ne_zero _).mp (leftMap_rank a)
  have hh := congrArg (fun A : End => (leftMap a)⁻¹*A) h
  simp only [hc,one_smul,fullMap,← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hL),Matrix.one_mul] at hh
  obtain ⟨rfl,rfl⟩ := signedMap_injective σ τ ε δ hh
  rfl

def RankFourClass (S : Set V) := {p : Projectivization ℂ End //
  ∃ A : End, ∃ hn : A ≠ 0, A.rank=4 ∧ TwoSided S A ∧ p=Projectivization.mk ℂ A hn}

theorem rank_four_ne_zero {A : End} (h : A.rank=4) : A ≠ 0 := by
  intro hh
  simp [hh] at h

def fullClass {S : Set V} (C : FullIndex → End) (hr : ∀ i, (C i).rank=4)
    (hp : ∀ i, TwoSided S (C i)) (i : FullIndex) : RankFourClass S :=
  ⟨Projectivization.mk ℂ (C i) (rank_four_ne_zero (hr i)),
    C i,rank_four_ne_zero (hr i),hr i,hp i,rfl⟩

theorem fullClass_bijective {S : Set V} (C : FullIndex → End) (hr : ∀ i, (C i).rank=4)
    (hp : ∀ i, TwoSided S (C i))
    (hi : ∀ (i j : FullIndex) (c : ℂ), C i=c • C j → i=j)
    (hc : ∀ A : End, A.rank=4 → TwoSided S A →
      ∃ i : FullIndex, ∃ c : ℂ, c ≠ 0 ∧ A=c • C i) :
    Function.Bijective (fullClass C hr hp) := by
  constructor
  · intro i j h
    obtain ⟨c,he⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp (congrArg Subtype.val h)
    exact hi i j c he.symm
  · rintro ⟨q,A,hA,hAr,hAp,hq⟩
    obtain ⟨i,c,hc,he⟩ := hc A hAr hAp
    refine ⟨i,Subtype.ext ?_⟩
    change Projectivization.mk ℂ (C i) _ = q
    rw [hq]
    symm
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨c,he.symm⟩

def standardRankFourEquiv : FullIndex ≃ RankFourClass Standard :=
  Equiv.ofBijective (fullClass fullMap fullMap_rank fullMap_twoSided)
    (fullClass_bijective fullMap fullMap_rank fullMap_twoSided fullMap_projectively_injective
      (fun A hA h => (standard_full_rank_twoSided A hA).mp h))

@[simp] theorem toExternal_smul (c : ℂ) (A : End) : toExternal (c • A)=c • toExternal A := by
  simp [toExternal,Matrix.mul_smul,Matrix.smul_mul]

@[simp] theorem toStandard_smul (c : ℂ) (A : End) : toStandard (c • A)=c • toStandard A := by
  simp [toStandard,Matrix.mul_smul,Matrix.smul_mul]

theorem external_full_rank_complete (A : End) (hA : A.rank=4) (h : TwoSided External A) :
    ∃ i : FullIndex, ∃ c : ℂ, c ≠ 0 ∧ A=c • toExternal (fullMap i) := by
  have hr : (toStandard A).rank=4 := by simpa using hA
  obtain ⟨i,c,hc,he⟩ := (standard_full_rank_twoSided (toStandard A) hr).mp
    ((standard_twoSided_iff A).mpr h)
  refine ⟨i,c,hc,?_⟩
  simpa only [toExternal_toStandard,toExternal_smul] using congrArg toExternal he

def externalRankFourEquiv : FullIndex ≃ RankFourClass External :=
  Equiv.ofBijective
    (fullClass (fun i => toExternal (fullMap i))
      (fun i => by rw [rank_toExternal,fullMap_rank])
      (fun i => (external_twoSided_iff _).mpr (fullMap_twoSided i)))
    (fullClass_bijective (fun i => toExternal (fullMap i))
      (fun i => by rw [rank_toExternal,fullMap_rank])
      (fun i => (external_twoSided_iff _).mpr (fullMap_twoSided i))
      (fun i j c h => fullMap_projectively_injective i j c (by
        simpa only [toStandard_toExternal,toStandard_smul] using congrArg toStandard h))
      external_full_rank_complete)

theorem fullIndex_count : Nat.card FullIndex=576 := by
  norm_num [FullIndex,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]

theorem standard_rank_four_count : Nat.card (RankFourClass Standard)=576 := by
  rw [← Nat.card_congr standardRankFourEquiv,fullIndex_count]

theorem external_rank_four_count : Nat.card (RankFourClass External)=576 := by
  rw [← Nat.card_congr externalRankFourEquiv,fullIndex_count]

end Holant.Certificates.TetrahedralPreservers
