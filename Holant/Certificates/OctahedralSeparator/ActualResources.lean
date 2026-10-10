import Holant.Certificates.OctahedralSeparator.OutputData
import Holant.Certificates.OctahedralSeparator.GroupMembership

namespace Holant.Certificates.OctahedralSeparator
open Holant
noncomputable section

theorem theta_q0 (f : Form) : theta f (q 0)=q 0 := by
  simp only [theta,q0_mm]
  exact (conjugator_inverses f).2

theorem direction_identity (f : Form) : Direction f (complexMatrix (q 0)) := by
  have h := Direction.standard f 0
  change Direction f (complexMatrix (theta f (q 0))) at h
  rwa [theta_q0] at h

theorem firstKernel_available (f : Form) : Direction f (complexMatrix (theta f firstKernel)) :=
  Direction.standard f 12

theorem endpointLegs_available (j : Fin 48) (a : Fin 4) :
    Direction (rowForm j) (complexMatrix (endpointLegs j a)) := by
  unfold endpointLegs
  split
  · exact direction_flip _
  · exact Direction.standard _ _

theorem corrections_available (f : Form) (a : Fin 4) :
    Direction f (complexMatrix (corrections f a)) := by
  fin_cases a
  · exact direction_identity f
  · exact direction_correction f
  · exact direction_identity f
  · exact direction_correction f

theorem finalLegs_available (j : Fin 48) (a : Fin 4) :
    Direction (rowForm j) (complexMatrix (finalLegs j a)) := by
  unfold finalLegs
  split
  · exact endpointLegs_available j a
  · rw [complexMatrix_mm]
    exact (endpointLegs_available j a).mul (corrections_available _ a)

theorem closureKernel_available (j : Fin 48) :
    Direction (rowForm j) (complexMatrix (closureKernel j)) := Direction.standard _ _

end
end Holant.Certificates.OctahedralSeparator
