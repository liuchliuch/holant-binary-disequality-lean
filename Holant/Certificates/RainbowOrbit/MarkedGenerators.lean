import Holant.Certificates.RainbowOrbit.MarkedTransport
import Holant.Certificates.RainbowOrbit.PhysicalSingleLeg

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
open OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false

def currentLegs (f : Form) (L : Legs) : Legs :=
  fun j => markLegs f j*L j*(markLegs f j)⁻¹

theorem currentLegs_intertwine (f : Form) (L : Legs) (F : FourTensor) :
    act (currentLegs f L) (act (markLegs f) F)=act (markLegs f) (act L F) := by
  rw [act_comp,act_comp]
  congr 1
  funext j
  simp only [currentLegs,mul_assoc,Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (markLegs_det f j)),mul_one]

theorem currentLegs_even (f : Form) (L : Legs) :
    currentLegs f L 0=complexTheta f (L 0) ∧ currentLegs f L 2=complexTheta f (L 2) := by
  have hi := isUnit_iff_ne_zero.mpr (markH_det f)
  constructor <;> simp [currentLegs,markLegs_eq,complexTheta,markH,
    Matrix.nonsing_inv_nonsing_inv _ hi,mul_assoc]
  all_goals rw [Matrix.nonsing_inv_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (complexMatrix_conjugator_det_ne_zero f))]

theorem conjugation_transposed_leg (f : Form) (U : BinaryMatrix) :
    (markH f).transpose*U*(markH f).transpose⁻¹=
      complexTheta f (markS f*U*markSinv f) := by
  have hi := isUnit_iff_ne_zero.mpr (markH_det f)
  change _=(markH f)⁻¹*((((markH f*(markH f).transpose)*U)*
      ((markH f)⁻¹.transpose*(markH f)⁻¹))*markH f)
  rw [Matrix.transpose_nonsing_inv]
  simp only [mul_assoc,Matrix.nonsing_inv_mul _ hi,mul_one]
  rw [←mul_assoc (markH f)⁻¹,Matrix.nonsing_inv_mul _ hi,one_mul]

theorem currentLegs_odd (f : Form) (L : Legs) :
    currentLegs f L 1=complexTheta f (markS f*L 1*markSinv f) ∧
    currentLegs f L 3=complexTheta f (markS f*L 3*markSinv f) := by
  constructor <;> simpa only [currentLegs,markLegs_eq,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,Matrix.cons_val_fin_one] using conjugation_transposed_leg f (L _)

theorem currentLegs_mem (f : Form) (L : Legs) (hL : GroupLegs .octahedral L) :
    ∀j,Direction f (currentLegs f L j) := by
  have he := currentLegs_even f L
  have ho := currentLegs_odd f L
  have hm (j : Fin 4) : Direction f (complexTheta f (markS f*L j*markSinv f)) := by
    apply (direction_iff_source_conjugate f _).mpr
    exact ⟨_,RainbowOrbit.groupDirection_mul .octahedral
      (RainbowOrbit.groupDirection_mul .octahedral (markS_source f) (hL j)) (markSinv_source f),rfl⟩
  intro j
  fin_cases j
  · change Direction f (currentLegs f L 0)
    rw [he.1]
    exact (direction_iff_source_conjugate f _).mpr ⟨L 0,hL 0,rfl⟩
  · change Direction f (currentLegs f L 1)
    rw [ho.1]
    exact hm 1
  · change Direction f (currentLegs f L 2)
    rw [he.2]
    exact (direction_iff_source_conjugate f _).mpr ⟨L 2,hL 2,rfl⟩
  · change Direction f (currentLegs f L 3)
    rw [ho.2]
    exact hm 3

/-- Every analytically transported generator is an actual current-group class. -/
theorem currentLegs_representatives (f : Form) (L : Legs) (hL : GroupLegs .octahedral L) :
    ∃k : Fin 4→Fin 24,∃c : Fin 4→ℂ,(∀j,c j≠0) ∧
      ∀j,currentLegs f L j=c j • complexMatrix (theta f (standard (k j))) := by
  have hh := currentLegs_mem f L hL
  choose c hc k hk using hh
  exact ⟨k,c,hc,hk⟩

/-- The source's analytic correspondence is implemented by current-group
binaries, with its exact nonzero representative scalar and original port order. -/
theorem current_generator_physical (f : Form) (L : Legs) (hL : GroupLegs .octahedral L)
    (F : FourTensor) :
    ∃k : Fin 4→Fin 24,∃c : Fin 4→ℂ,(∀j,c j≠0) ∧
      (physicalNetwork (act (markLegs f) F)
        (fun j => complexMatrix (theta f (standard (k j))))).denote=
          (∏j,c j)⁻¹ • act (markLegs f) (act L F) := by
  obtain ⟨k,c,hc,he⟩ := currentLegs_representatives f L hL
  refine ⟨k,c,hc,?_⟩
  have he' : currentLegs f L=(fun j => c j • complexMatrix (theta f (standard (k j)))) := funext he
  have hh := currentLegs_intertwine f L F
  rw [he',act_rescale_legs] at hh
  have hn : (∏j,c j)≠0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hc j)
  rw [physicalNetwork_denote_act,←hh,smul_smul,inv_mul_cancel₀ hn,one_smul]

end
end Holant.Certificates.RainbowOrbit
