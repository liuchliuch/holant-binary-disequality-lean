import Holant.Certificates.RainbowOrbit.Operations
import Holant.Certificates.RainbowOrbit.MarkedFamily
import Holant.Certificates.RainbowOrbit.MarkedWitness
import Holant.Certificates.RainbowOrbit.Witness

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
open OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false

def basePoint (r : Fin 3) : Point := Projectivization.mk ℂ (base r) (base_nonzero r)
def baseLine : Finset Point := points basePoint

theorem basePoint_rainbow (g : PlatonicModel) : Rainbow g basePoint := by
  constructor
  · exact fun r => ⟨base r,base_nonzero r,base_inMatching g r,rfl⟩
  · have hh := action_base_collinear (fun _ => (1 : BinaryMatrix)) (by simp)
    simpa only [act_identity,basePoint,base,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] using hh

def forwardIndices (g : PlatonicModel) (t : OrbitIndex g) : Fin 4→Fin (size g) :=
  ![identityIndex g,t 0,t 1,t 2]

theorem forwardLegs_eq (g : PlatonicModel) (t : OrbitIndex g) :
    representativeLegs g (forwardIndices g t)=orbitLegs g t := by
  funext j
  fin_cases j <;> simp [representativeLegs,forwardIndices,orbitLegs,reducedLegs,representative_identity]

theorem forward_word_exact (g : PlatonicModel) (t : OrbitIndex g) :
    runWord (representative g) (representative_det_ne_zero g) (fourWord (forwardIndices g t)) baseLine=line g t := by
  rw [runWord_four]
  change (points basePoint).map _=points (orbitPoint g t)
  rw [←points_map]
  congr 1
  funext r
  change pointAction (representativeLegs g (forwardIndices g t)) _ (basePoint r)=orbitPoint g t r
  change Projectivization.mk ℂ (act (representativeLegs g (forwardIndices g t)) (base r)) _=
    Projectivization.mk ℂ (act (orbitLegs g t) (base r)) _
  congr 1
  rw [forwardLegs_eq]

/-- The literal source generators: four possible single-leg ports with fixed
actual matrix representatives, and the three adjacent port permutations. -/
def GeneratedOrbit (g : PlatonicModel) (S : Finset Point) : Prop :=
  ∃w : List (Operation (size g)),runWord (representative g) (representative_det_ne_zero g) w baseLine=S

theorem generatedOrbit_iff_rainbowLine (g : PlatonicModel) (S : Finset Point) :
    GeneratedOrbit g S ↔ RainbowLine g S := by
  constructor
  · rintro ⟨w,rfl⟩
    have hb : FamilyRainbowLine (fun U => groupDirection g U) baseLine :=
      ⟨basePoint,basePoint_rainbow g,rfl⟩
    exact hb.word (standardMatrixFamily g) (representative g) (representative_mem g) w
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨t,rfl⟩ := rainbow_enumerated g p hp
    exact ⟨fourWord (forwardIndices g t),forward_word_exact g t⟩

theorem generatedOrbit_card (g : PlatonicModel) :
    {S : Finset Point | GeneratedOrbit g S}.ncard=(size g)^3 := by
  have he : {S : Finset Point | GeneratedOrbit g S}={S : Finset Point | RainbowLine g S} := by
    ext S
    exact generatedOrbit_iff_rainbowLine g S
  rw [he,all_rainbow_lines_card]

def markedBasePoint (f : Form) (r : Fin 3) : Point :=
  Projectivization.mk ℂ (markedInitial f r) (markedInitial_nonzero f r)
def markedBaseLine (f : Form) : Finset Point := points (markedBasePoint f)

def markedRepresentative (f : Form) (i : Fin 24) : BinaryMatrix := complexMatrix (theta f (standard i))

theorem markedRepresentative_det (f : Form) (i : Fin 24) : (markedRepresentative f i).det≠0 :=
  (Direction.standard f i).det_ne_zero

theorem markedBasePoint_rainbow (f : Form) : MarkedRainbow f (markedBasePoint f) :=
  rainbow_mark_forward f basePoint (basePoint_rainbow .octahedral)

theorem marked_forward_word_exact (f : Form) (t : OrbitIndex .octahedral) :
    ∃k : Fin 4→Fin 24,runWord (markedRepresentative f) (markedRepresentative_det f)
      (fourWord k) (markedBaseLine f)=markedLine f t := by
  obtain ⟨k,c,hc,he⟩ := currentLegs_representatives f (orbitLegs .octahedral t) (orbitLegs_mem .octahedral t)
  refine ⟨k,?_⟩
  have hn : (∏j,c j)≠0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hc j)
  have hp (r : Fin 3) : pointAction (fun j => markedRepresentative f (k j))
      (fun j => markedRepresentative_det f (k j)) (markedBasePoint f r)=markedOrbitPoint f t r := by
    have hh := currentLegs_intertwine f (orbitLegs .octahedral t) (base r)
    have hlegs : currentLegs f (orbitLegs .octahedral t)=
        (fun j => c j • markedRepresentative f (k j)) := funext he
    rw [hlegs,act_rescale_legs] at hh
    apply (proportional_point_iff _ _ _ _).mp
    refine ⟨(∏j,c j)⁻¹,inv_ne_zero hn,?_⟩
    change act (fun j => markedRepresentative f (k j)) (act (markLegs f) (base r))=
      (∏j,c j)⁻¹ • act (markLegs f) (act (orbitLegs .octahedral t) (base r))
    rw [←hh,smul_smul,inv_mul_cancel₀ hn,one_smul]
  rw [runWord_four]
  change (points (markedBasePoint f)).map _=points (markedOrbitPoint f t)
  rw [←points_map]
  congr 1
  exact funext hp

def MarkedGeneratedOrbit (f : Form) (S : Finset Point) : Prop :=
  ∃w : List (Operation 24),runWord (markedRepresentative f) (markedRepresentative_det f) w (markedBaseLine f)=S

theorem marked_generatedOrbit_iff_rainbowLine (f : Form) (S : Finset Point) :
    MarkedGeneratedOrbit f S ↔ MarkedRainbowLine f S := by
  constructor
  · rintro ⟨w,rfl⟩
    have hb : FamilyRainbowLine (Direction f) (markedBaseLine f) :=
      ⟨markedBasePoint f,markedBasePoint_rainbow f,rfl⟩
    exact hb.word (markedMatrixFamily f) (markedRepresentative f) (Direction.standard f) w
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨t,rfl⟩ := marked_rainbow_enumerated f p hp
    obtain ⟨k,hk⟩ := marked_forward_word_exact f t
    exact ⟨fourWord k,hk⟩

theorem marked_generatedOrbit_card (f : Form) :
    {S : Finset Point | MarkedGeneratedOrbit f S}.ncard=13824 := by
  have he : {S : Finset Point | MarkedGeneratedOrbit f S}={S : Finset Point | MarkedRainbowLine f S} := by
    ext S
    exact marked_generatedOrbit_iff_rainbowLine f S
  rw [he,marked_all_lines_card]

end
end Holant.Certificates.RainbowOrbit
