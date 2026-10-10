import Holant.Platonic.RankDeficientLocalization.Normalization.DomainOrbit
import Holant.Certificates.RainbowOrbit.PointAction
import Holant.Certificates.PlatonicDeficient.NormalizedOutputs

/-! Exact source bridge equations are derived from the actual full card cone
and an actual rich rainbow line.  All operations are local group directions. -/
namespace Holant.Platonic.RankDeficientLocalization.Normalization
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Linear extension from the fixed actual dictionary retains every scalar. -/
theorem cards_of_representatives (g : PlatonicModel) (Φ : Mat →ₗ[ℂ] FourTensor)
    (hc : ∀i,matchingCone g (Φ (representative g i))) :
    ∀K : Mat,groupDirection g K → matchingCone g (Φ K) := by
  intro K hK
  obtain ⟨i,c,hc0,rfl⟩ := (complete g K).mp hK
  rw [map_smul]
  exact matchingCone_smul g (hc i) c

theorem action_matchingCone (g : PlatonicModel) (L : Legs) (hL : GroupLegs g L)
    (F : FourTensor) (hF : matchingCone g F) : matchingCone g (act L F) := by
  rcases matchingCone_presentation g F hF with rfl | ⟨r,U,V,hU,hV,rfl⟩
  · exact Or.inl (map_zero (actionLinear L))
  have hm (i j : Fin 4) (M : Mat) (hM : groupDirection g M) :
      groupDirection g (L i*M*(L j).transpose) :=
    groupDirection_mul g (groupDirection_mul g (hL i) hM) (direction_transpose g (hL j))
  fin_cases r
  · change matchingCone g (act L (P0 U V))
    rw [act_P0]
    exact matchingProduct_mem_cone g 0 (hm 0 1 U hU) (hm 2 3 V hV)
  · change matchingCone g (act L (P1 U V))
    rw [act_P1]
    exact matchingProduct_mem_cone g 1 (hm 0 2 U hU) (hm 1 3 V hV)
  · change matchingCone g (act L (P2 U V))
    rw [act_P2]
    exact matchingProduct_mem_cone g 2 (hm 0 3 U hU) (hm 1 2 V hV)

def dressedMap {g : PlatonicModel} (D : DomainAction g) (L : Legs)
    (Φ : Mat →ₗ[ℂ] FourTensor) : Mat →ₗ[ℂ] FourTensor :=
  (actionLinear L).comp (Φ.comp D.linear)

@[simp] theorem dressedMap_apply {g : PlatonicModel} (D : DomainAction g) (L : Legs)
    (Φ : Mat →ₗ[ℂ] FourTensor) (K : Mat) :
    dressedMap D L Φ K=act L (Φ (D.apply K)) := rfl

theorem dressedMap_cards {g : PlatonicModel} (D : DomainAction g) (L : Legs)
    (hL : GroupLegs g L) (Φ : Mat →ₗ[ℂ] FourTensor)
    (hc : ∀K : Mat,groupDirection g K → matchingCone g (Φ K)) :
    ∀K : Mat,groupDirection g K → matchingCone g (dressedMap D L Φ K) := by
  intro K hK
  exact action_matchingCone g L hL _ (hc _ (D.mem hK))

theorem dressedMap_rank {g : PlatonicModel} (D : DomainAction g) (L : Legs)
    (hL : GroupLegs g L) (Φ : Mat →ₗ[ℂ] FourTensor) :
    Module.finrank ℂ (dressedMap D L Φ).range=Module.finrank ℂ Φ.range := by
  let E : FourTensor ≃ₗ[ℂ] FourTensor := LinearEquiv.ofBijective (actionLinear L)
    ⟨actionLinear_injective L hL.det,
      LinearMap.injective_iff_surjective.mp (actionLinear_injective L hL.det)⟩
  have hd : D.linear.range=⊤ := D.equiv.range
  rw [dressedMap,LinearMap.range_comp,LinearMap.range_comp_of_range_eq_top Φ hd]
  exact E.finrank_map_eq Φ.range

theorem normal_test_directions (g : PlatonicModel) (j : Fin 3) :
    groupDirection g (TetrahedralBridge.normalPlus-(2 : ℂ) • quaternionBasis j.succ) ∧
    groupDirection g (TetrahedralBridge.normalMinus+(2 : ℂ) • quaternionBasis j.succ) := by
  have hp : tetrahedralBase (TetrahedralBridge.normalPlus-(2 : ℂ) • quaternionBasis j.succ) := by
    refine Or.inr ⟨fun k => decide (k=j),?_⟩
    fin_cases j <;> funext a b <;> cases a <;> cases b <;>
      simp [TetrahedralBridge.normalPlus,quaternionBasis,quaternion,signBit,
        Q0,Q1,Q2,Q3,Signature.equality] <;> ring
  have hm : tetrahedralBase (TetrahedralBridge.normalMinus+(2 : ℂ) • quaternionBasis j.succ) := by
    refine Or.inr ⟨fun k => decide (k≠j),?_⟩
    fin_cases j <;> funext a b <;> cases a <;> cases b <;>
      simp [TetrahedralBridge.normalMinus,quaternionBasis,quaternion,signBit,
        Q0,Q1,Q2,Q3,Signature.equality] <;> ring
  have hb {K : Binary} (h : tetrahedralBase K) : groupDirection g K := by
    refine ⟨1,one_ne_zero,K,?_,by simp⟩
    cases g
    · exact h
    · exact Or.inl h
    · exact Or.inl h
  exact ⟨hb hp,hb hm⟩

def SourceEquations (g : PlatonicModel) (Φ : Mat →ₗ[ℂ] FourTensor) : Prop :=
  (Φ TetrahedralBridge.normalPlus=A ∧ Φ TetrahedralBridge.normalMinus= -B) ∧
    ∀j : Fin 3,bridgeConditions g (Φ (quaternionBasis j.succ))

theorem sourceEquations_of_cards (g : PlatonicModel) (Φ : Mat →ₗ[ℂ] FourTensor)
    (hp : Φ TetrahedralBridge.normalPlus=A) (hm : Φ TetrahedralBridge.normalMinus= -B)
    (hc : ∀K : Mat,groupDirection g K → matchingCone g (Φ K)) : SourceEquations g Φ := by
  refine ⟨⟨hp,hm⟩,?_⟩
  intro j
  refine ⟨hc _ (quaternion_axis_direction g j.succ),?_,?_⟩
  · have h := hc _ (normal_test_directions g j).1
    rw [map_sub,map_smul,hp] at h
    exact h
  · have h := hc _ (normal_test_directions g j).2
    rw [map_add,map_smul,hm] at h
    simpa only [sub_eq_add_neg,add_comm] using h

/-- A genuine rainbow line yields the exact A.27 equations after two actual
domain dressings, an optional pair swap, and four actual residual dressings. -/
theorem source_normalization {g : PlatonicModel} (Φ : Mat →ₗ[ℂ] FourTensor)
    (R : RainbowDomainLine Φ (representative g))
    (hc : ∀i,matchingCone g (Φ (representative g i))) :
    ∃D : DomainAction g,∃L : Legs,GroupLegs g L ∧ SourceEquations g (dressedMap D L Φ) ∧
      Module.finrank ℂ (dressedMap D L Φ).range=Module.finrank ℂ Φ.range := by
  have hcards := cards_of_representatives g Φ hc
  obtain ⟨D,hD⟩ := ordered_domain_matching R hcards
  obtain ⟨U,V,hU,hV,h0⟩ := hD 0
  obtain ⟨S,T,hS,hT,h1⟩ := hD 1
  obtain ⟨M,N,hM,hN,h2⟩ := hD 2
  have he : P2 M N=(1/2 : ℂ) • P0 U V+(1/2 : ℂ) • P1 S T := by
    have hh := congrArg (fun K : Mat => Φ (D.linear K)) normalTriangle_relation
    simp only [map_add,map_smul,DomainAction.linear_apply,h0,h1,h2] at hh
    change P0 U V+P1 S T=(2 : ℂ) • P2 M N at hh
    rw [←smul_add,hh,smul_smul]
    norm_num
  let L := normalization U V S
  have hL : GroupLegs g L := normalization_mem g U V S hU hV hS
  obtain ⟨hn0,hn1,_⟩ := normalize_rainbow U V S T M N
    (groupDirection_det_ne_zero g hU) (groupDirection_det_ne_zero g hV)
    (groupDirection_det_ne_zero g hS) (groupDirection_det_ne_zero g hM)
    (groupDirection_det_ne_zero g hN) (1/2) (1/2) (by norm_num) (by norm_num) he
  have hp : dressedMap D L Φ TetrahedralBridge.normalPlus=A := by
    change act L (Φ (D.apply (normalTriangle 0)))=A
    rw [h0]
    exact hn0
  have hm : dressedMap D L Φ TetrahedralBridge.normalMinus= -B := by
    change act L (Φ (D.apply (normalTriangle 1)))= -B
    rw [h1]
    change act (normalization U V S) (P1 S T)= -B
    norm_num at hn1
    exact hn1
  exact ⟨D,L,hL,sourceEquations_of_cards g _ hp hm (dressedMap_cards D L hL Φ hcards),
    dressedMap_rank D L hL Φ⟩

end
end Holant.Platonic.RankDeficientLocalization.Normalization
