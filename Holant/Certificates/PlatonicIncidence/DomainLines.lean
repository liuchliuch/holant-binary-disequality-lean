import Holant.Certificates.PlatonicIncidence.GlobalTetrahedral
import Holant.Certificates.PlatonicIncidence.GlobalOctahedral
import Holant.Certificates.PlatonicIncidence.GlobalIcosahedral

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem translation_certificate (g : PlatonicModel) (i : Fin (size g)) (b : Fin (baseCount g)) :
    translatedLine g i b=globalLine g (translateIndex g i b) := by
  cases g
  · fin_cases i
    · exact tetrahedral_translate_0 b
    · exact tetrahedral_translate_1 b
    · exact tetrahedral_translate_2 b
    · exact tetrahedral_translate_3 b
    · exact tetrahedral_translate_4 b
    · exact tetrahedral_translate_5 b
    · exact tetrahedral_translate_6 b
    · exact tetrahedral_translate_7 b
    · exact tetrahedral_translate_8 b
    · exact tetrahedral_translate_9 b
    · exact tetrahedral_translate_10 b
    · exact tetrahedral_translate_11 b
  · fin_cases i
    · exact octahedral_translate_0 b
    · exact octahedral_translate_1 b
    · exact octahedral_translate_2 b
    · exact octahedral_translate_3 b
    · exact octahedral_translate_4 b
    · exact octahedral_translate_5 b
    · exact octahedral_translate_6 b
    · exact octahedral_translate_7 b
    · exact octahedral_translate_8 b
    · exact octahedral_translate_9 b
    · exact octahedral_translate_10 b
    · exact octahedral_translate_11 b
    · exact octahedral_translate_12 b
    · exact octahedral_translate_13 b
    · exact octahedral_translate_14 b
    · exact octahedral_translate_15 b
    · exact octahedral_translate_16 b
    · exact octahedral_translate_17 b
    · exact octahedral_translate_18 b
    · exact octahedral_translate_19 b
    · exact octahedral_translate_20 b
    · exact octahedral_translate_21 b
    · exact octahedral_translate_22 b
    · exact octahedral_translate_23 b
  · fin_cases i
    · exact icosahedral_translate_0 b
    · exact icosahedral_translate_1 b
    · exact icosahedral_translate_2 b
    · exact icosahedral_translate_3 b
    · exact icosahedral_translate_4 b
    · exact icosahedral_translate_5 b
    · exact icosahedral_translate_6 b
    · exact icosahedral_translate_7 b
    · exact icosahedral_translate_8 b
    · exact icosahedral_translate_9 b
    · exact icosahedral_translate_10 b
    · exact icosahedral_translate_11 b
    · exact icosahedral_translate_12 b
    · exact icosahedral_translate_13 b
    · exact icosahedral_translate_14 b
    · exact icosahedral_translate_15 b
    · exact icosahedral_translate_16 b
    · exact icosahedral_translate_17 b
    · exact icosahedral_translate_18 b
    · exact icosahedral_translate_19 b
    · exact icosahedral_translate_20 b
    · exact icosahedral_translate_21 b
    · exact icosahedral_translate_22 b
    · exact icosahedral_translate_23 b
    · exact icosahedral_translate_24 b
    · exact icosahedral_translate_25 b
    · exact icosahedral_translate_26 b
    · exact icosahedral_translate_27 b
    · exact icosahedral_translate_28 b
    · exact icosahedral_translate_29 b
    · exact icosahedral_translate_30 b
    · exact icosahedral_translate_31 b
    · exact icosahedral_translate_32 b
    · exact icosahedral_translate_33 b
    · exact icosahedral_translate_34 b
    · exact icosahedral_translate_35 b
    · exact icosahedral_translate_36 b
    · exact icosahedral_translate_37 b
    · exact icosahedral_translate_38 b
    · exact icosahedral_translate_39 b
    · exact icosahedral_translate_40 b
    · exact icosahedral_translate_41 b
    · exact icosahedral_translate_42 b
    · exact icosahedral_translate_43 b
    · exact icosahedral_translate_44 b
    · exact icosahedral_translate_45 b
    · exact icosahedral_translate_46 b
    · exact icosahedral_translate_47 b
    · exact icosahedral_translate_48 b
    · exact icosahedral_translate_49 b
    · exact icosahedral_translate_50 b
    · exact icosahedral_translate_51 b
    · exact icosahedral_translate_52 b
    · exact icosahedral_translate_53 b
    · exact icosahedral_translate_54 b
    · exact icosahedral_translate_55 b
    · exact icosahedral_translate_56 b
    · exact icosahedral_translate_57 b
    · exact icosahedral_translate_58 b
    · exact icosahedral_translate_59 b

theorem global_witness (g : PlatonicModel) (t : Fin (secantCount g)) :
    translateIndex g (globalWitness g t).1 (globalWitness g t).2=t := by
  cases g
  · exact tetrahedral_witness t
  · exact octahedral_witness t
  · exact icosahedral_witness t

theorem globalLine_injective (g : PlatonicModel) : Function.Injective (globalLine g) := by
  cases g
  · exact fun i j h => tetrahedral_codes_strictMono.injective (congrArg lineCode h)
  · exact fun i j h => octahedral_codes_strictMono.injective (congrArg lineCode h)
  · exact fun i j h => icosahedral_codes_strictMono.injective (congrArg lineCode h)

theorem globalLine_eq_translated (g : PlatonicModel) (t : Fin (secantCount g)) :
    globalLine g t=translatedLine g (globalWitness g t).1 (globalWitness g t).2 := by
  rw [translation_certificate,global_witness]

theorem globalLine_semantics (g : PlatonicModel) (t : Fin (secantCount g)) :
    ∃i j : Fin (size g),i≠j ∧ ∀k : Fin (size g),k∈globalLine g t ↔
      representative g k∈Submodule.span ℂ ({representative g i,representative g j} : Set Mat) := by
  let i := (globalWitness g t).1
  let b := (globalWitness g t).2
  refine ⟨i,productIndex g i (baseAnchor g b),translated_endpoints_ne g i b,?_⟩
  intro k
  rw [globalLine_eq_translated]
  exact translatedLine_iff g i k b

theorem global_complete (g : PlatonicModel) (i j : Fin (size g)) (hij : i≠j) :
    ∃t : Fin (secantCount g),∀k : Fin (size g),k∈globalLine g t ↔
      representative g k∈Submodule.span ℂ ({representative g i,representative g j} : Set Mat) := by
  obtain ⟨b,hb⟩ := secant_complete g i j hij
  refine ⟨translateIndex g i b,?_⟩
  intro k
  rw [←translation_certificate]
  exact hb k

/-- Literal finite intersections with all actual two-point complex spans. -/
def DomainSecant (g : PlatonicModel) (S : Finset (Fin (size g))) : Prop :=
  ∃i j : Fin (size g),i≠j ∧ ∀k : Fin (size g),k∈S ↔
    representative g k∈Submodule.span ℂ ({representative g i,representative g j} : Set Mat)

def domainLines (g : PlatonicModel) : Finset (Finset (Fin (size g))) :=
  Finset.univ.map ⟨globalLine g,globalLine_injective g⟩

theorem domainLines_exact (g : PlatonicModel) (S : Finset (Fin (size g))) :
    S∈domainLines g ↔ DomainSecant g S := by
  constructor
  · intro h
    obtain ⟨t,_,rfl⟩ := Finset.mem_map.mp h
    exact globalLine_semantics g t
  · rintro ⟨i,j,hij,hS⟩
    obtain ⟨t,ht⟩ := global_complete g i j hij
    apply Finset.mem_map.mpr
    exact ⟨t,Finset.mem_univ t,Finset.ext (fun k => (ht k).trans (hS k).symm)⟩

theorem domainLines_card (g : PlatonicModel) : (domainLines g).card=secantCount g := by
  simp [domainLines]

theorem domainLines_filter_card (g : PlatonicModel) (n : ℕ) :
    ((domainLines g).filter (fun S => S.card=n)).card=
      (Finset.univ.filter (fun t : Fin (secantCount g) => (globalLine g t).card=n)).card := by
  simp [domainLines,Finset.filter_map]

end
end Holant.Certificates.PlatonicIncidence
