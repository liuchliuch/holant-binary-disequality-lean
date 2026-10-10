import Holant.Certificates.PlatonicIncidence.BaseTetrahedral
import Holant.Certificates.PlatonicIncidence.BaseOctahedral
import Holant.Certificates.PlatonicIncidence.BaseIcosahedral

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option backward.isDefEq.respectTransparency false

theorem base_certificate (g : PlatonicModel) (j : Fin (size g))
    (hj : j≠identityIndex g) : baseSecant g j=baseLine g (baseLineOf g j) := by
  cases g
  · fin_cases j
    · exact (hj rfl).elim
    · exact tetrahedral_base_1
    · exact tetrahedral_base_2
    · exact tetrahedral_base_3
    · exact tetrahedral_base_4
    · exact tetrahedral_base_5
    · exact tetrahedral_base_6
    · exact tetrahedral_base_7
    · exact tetrahedral_base_8
    · exact tetrahedral_base_9
    · exact tetrahedral_base_10
    · exact tetrahedral_base_11
  · fin_cases j
    · exact (hj rfl).elim
    · exact octahedral_base_1
    · exact octahedral_base_2
    · exact octahedral_base_3
    · exact octahedral_base_4
    · exact octahedral_base_5
    · exact octahedral_base_6
    · exact octahedral_base_7
    · exact octahedral_base_8
    · exact octahedral_base_9
    · exact octahedral_base_10
    · exact octahedral_base_11
    · exact octahedral_base_12
    · exact octahedral_base_13
    · exact octahedral_base_14
    · exact octahedral_base_15
    · exact octahedral_base_16
    · exact octahedral_base_17
    · exact octahedral_base_18
    · exact octahedral_base_19
    · exact octahedral_base_20
    · exact octahedral_base_21
    · exact octahedral_base_22
    · exact octahedral_base_23
  · fin_cases j
    · exact (hj rfl).elim
    · exact icosahedral_base_1
    · exact icosahedral_base_2
    · exact icosahedral_base_3
    · exact icosahedral_base_4
    · exact icosahedral_base_5
    · exact icosahedral_base_6
    · exact icosahedral_base_7
    · exact icosahedral_base_8
    · exact icosahedral_base_9
    · exact icosahedral_base_10
    · exact icosahedral_base_11
    · exact icosahedral_base_12
    · exact icosahedral_base_13
    · exact icosahedral_base_14
    · exact icosahedral_base_15
    · exact icosahedral_base_16
    · exact icosahedral_base_17
    · exact icosahedral_base_18
    · exact icosahedral_base_19
    · exact icosahedral_base_20
    · exact icosahedral_base_21
    · exact icosahedral_base_22
    · exact icosahedral_base_23
    · exact icosahedral_base_24
    · exact icosahedral_base_25
    · exact icosahedral_base_26
    · exact icosahedral_base_27
    · exact icosahedral_base_28
    · exact icosahedral_base_29
    · exact icosahedral_base_30
    · exact icosahedral_base_31
    · exact icosahedral_base_32
    · exact icosahedral_base_33
    · exact icosahedral_base_34
    · exact icosahedral_base_35
    · exact icosahedral_base_36
    · exact icosahedral_base_37
    · exact icosahedral_base_38
    · exact icosahedral_base_39
    · exact icosahedral_base_40
    · exact icosahedral_base_41
    · exact icosahedral_base_42
    · exact icosahedral_base_43
    · exact icosahedral_base_44
    · exact icosahedral_base_45
    · exact icosahedral_base_46
    · exact icosahedral_base_47
    · exact icosahedral_base_48
    · exact icosahedral_base_49
    · exact icosahedral_base_50
    · exact icosahedral_base_51
    · exact icosahedral_base_52
    · exact icosahedral_base_53
    · exact icosahedral_base_54
    · exact icosahedral_base_55
    · exact icosahedral_base_56
    · exact icosahedral_base_57
    · exact icosahedral_base_58
    · exact icosahedral_base_59

theorem base_anchors (g : PlatonicModel) (b : Fin (baseCount g)) :
    baseAnchor g b≠identityIndex g ∧ baseLineOf g (baseAnchor g b)=b ∧
    identityIndex g∈baseLine g b ∧ baseAnchor g b∈baseLine g b := by
  cases g
  · exact tetrahedral_anchors b
  · exact octahedral_anchors b
  · exact icosahedral_anchors b

theorem baseLine_iff (g : PlatonicModel) (b : Fin (baseCount g)) (k : Fin (size g)) :
    k∈baseLine g b ↔ representative g k∈Submodule.span ℂ
      ({(1 : Mat),representative g (baseAnchor g b)} : Set Mat) := by
  have h := base_certificate g (baseAnchor g b) (base_anchors g b).1
  rw [(base_anchors g b).2.1] at h
  rw [←h]
  exact baseSecant_iff g _ k (base_anchors g b).1

end Holant.Certificates.PlatonicIncidence
