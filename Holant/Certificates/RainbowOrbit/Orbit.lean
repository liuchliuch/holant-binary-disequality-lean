import Holant.Certificates.RainbowOrbit.GroupActions

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev OrbitIndex (g : PlatonicModel) := Fin 3 → Fin (size g)

def orbitLegs (g : PlatonicModel) (t : OrbitIndex g) : Legs :=
  reducedLegs (representative g (t 0)) (representative g (t 1)) (representative g (t 2))

theorem orbitLegs_mem (g : PlatonicModel) (t : OrbitIndex g) : GroupLegs g (orbitLegs g t) := by
  intro j
  fin_cases j
  · exact direction_one g
  all_goals exact representative_mem g _

def orbitPoint (g : PlatonicModel) (t : OrbitIndex g) (r : Fin 3) : Point :=
  Projectivization.mk ℂ (act (orbitLegs g t) (base r))
    (act_nonzero _ (orbitLegs_mem g t).det (base_nonzero r))

theorem orbitPoint_injective (g : PlatonicModel) : Function.Injective (orbitPoint g) := by
  intro t s he
  have h0 := (proportional_point_iff _ _ _ _).mpr (congrFun he 0)
  have h1 := (proportional_point_iff _ _ _ _).mpr (congrFun he 1)
  obtain ⟨⟨a,ha,hA⟩,⟨b,hb,hB⟩,⟨c,hc,hC⟩⟩ := reduced_action_injective
    (representative g (t 0)) (representative g (t 1)) (representative g (t 2))
    (representative g (s 0)) (representative g (s 1)) (representative g (s 2))
    (representative_det_ne_zero g _) (representative_det_ne_zero g _)
    (representative_det_ne_zero g _) h0 h1
  funext j
  fin_cases j
  · exact projectively_injective g _ _ a hA
  · exact projectively_injective g _ _ b hB
  · exact projectively_injective g _ _ c hC

def rainbowOrbit (g : PlatonicModel) : Finset (Fin 3 → Point) := by
  classical
  exact Finset.univ.map ⟨orbitPoint g,orbitPoint_injective g⟩

theorem rainbowOrbit_card (g : PlatonicModel) : (rainbowOrbit g).card=(size g)^3 := by
  classical
  simp [rainbowOrbit,OrbitIndex]

theorem standard_rainbow_orbit_counts : (rainbowOrbit .tetrahedral).card=1728 ∧
    (rainbowOrbit .octahedral).card=13824 ∧ (rainbowOrbit .icosahedral).card=216000 := by
  simp [rainbowOrbit_card,size]

/-- Every genuinely local group tuple has a representative with first leg exactly I. -/
theorem group_action_enumerated (g : PlatonicModel) (L : Legs) (hL : GroupLegs g L) :
    ∃t : OrbitIndex g, ∀r, Proportional (act L (base r)) (act (orbitLegs g t) (base r)) := by
  let R := reducedTuple L
  have hR : GroupLegs g R := reducedTuple_mem g L hL
  obtain ⟨i,a,ha,hi⟩ := (complete g (R 1)).mp (hR 1)
  obtain ⟨j,b,hb,hj⟩ := (complete g (R 2)).mp (hR 2)
  obtain ⟨k,c,hc,hk⟩ := (complete g (R 3)).mp (hR 3)
  refine ⟨![i,j,k],?_⟩
  intro r
  have hr : act L (base r)=act R (base r) := (reducedTuple_action L (hL.det 0) r).symm
  rw [hr]
  have hlegs : R=(fun q => (![1,a,b,c] : Fin 4→ℂ) q • orbitLegs g ![i,j,k] q) := by
    rw [show R=reducedLegs (R 1) (R 2) (R 3) from reducedTuple_eq L (hL.det 0)]
    rw [hi,hj,hk]
    funext q
    fin_cases q <;> simp [reducedLegs,orbitLegs]
  rw [hlegs,act_rescale_legs]
  exact ⟨_,by simp [Fin.prod_univ_succ,ha,hb,hc],rfl⟩

/-- Semantic ordered rainbow lines: all three literal matching classes and
ordinary projective collinearity. The ordering is by the actual matching label. -/
def Rainbow (g : PlatonicModel) (p : Fin 3→Point) : Prop :=
  (∀ r, ∃F : FourTensor, ∃hF : F≠0, InMatching g r F ∧ p r=Projectivization.mk ℂ F hF) ∧
  Projectivization.IsCollinear {p 0,p 1,p 2}

theorem action_base_collinear (L : Legs) (hL : ∀j,(L j).det≠0) :
    Projectivization.IsCollinear
      {Projectivization.mk ℂ (act L A) (act_nonzero L hL (base_nonzero 0)),
       Projectivization.mk ℂ (act L B) (act_nonzero L hL (base_nonzero 1)),
       Projectivization.mk ℂ (act L C) (act_nonzero L hL (base_nonzero 2))} := by
  apply (collinear_triple_iff _ _ _ _ _ _ ?_ ?_ ?_).mpr
  · refine ⟨1,-1,one_ne_zero,neg_ne_zero.mpr one_ne_zero,?_⟩
    have hc : C=A+(-1:ℂ) • B := by rw [←A_sub_B]; module
    rw [hc,act_add,act_smul,one_smul]
  · intro h
    have he := base_labels 0 1 ((proportional_act_iff L hL A B).mp h)
    exact (by decide : (0 : Fin 3)≠1) he
  · intro h
    have he := base_labels 2 0 ((proportional_act_iff L hL C A).mp h)
    exact (by decide : (2 : Fin 3)≠0) he
  · intro h
    have he := base_labels 2 1 ((proportional_act_iff L hL C B).mp h)
    exact (by decide : (2 : Fin 3)≠1) he

theorem orbitPoint_rainbow (g : PlatonicModel) (t : OrbitIndex g) : Rainbow g (orbitPoint g t) := by
  constructor
  · intro r
    exact ⟨_,_,(base_inMatching g r).act _ (orbitLegs_mem g t),rfl⟩
  · exact action_base_collinear _ (orbitLegs_mem g t).det

end
end Holant.Certificates.RainbowOrbit
