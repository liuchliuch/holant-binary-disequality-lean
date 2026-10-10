import Holant.Certificates.EqualityQuaternary.KleinPlaneChecks.Standard00
import Holant.Certificates.EqualityQuaternary.KleinPlaneChecks.Standard01
import Holant.Certificates.EqualityQuaternary.KleinPlaneChecks.Standard02
import Holant.Certificates.EqualityQuaternary.KleinPlaneChecks.Standard03

noncomputable section
namespace Holant.Certificates.EqualityQuaternary.Klein
open Holant Holant.Marked Holant.Tractable Holant.Marked.SupportAtlas
open Finite
set_option backward.isDefEq.respectTransparency false

theorem standard_support_Q : ∀ (j r : Fin 4) (i : Fin 16),
    parity (word i)≠standardParity j → planeTensorQ .standard j r (word i)=0 := by
  intro j
  fin_cases j
  · exact standardSupportQ00
  · exact standardSupportQ01
  · exact standardSupportQ02
  · exact standardSupportQ03

theorem standard_complement_Q : ∀ (j r : Fin 4) (i : Fin 16),
    planeTensorQ .standard j r (complement (word i))=
      standardSignQ j*planeTensorQ .standard j r (word i) := by
  intro j
  fin_cases j
  · exact standardComplementQ00
  · exact standardComplementQ01
  · exact standardComplementQ02
  · exact standardComplementQ03

theorem standard_support (j r : Fin 4) (w : Word) (h : parity w≠standardParity j) :
    planeTensor .standard j r w=0 := by
  obtain ⟨i,rfl⟩ := words_complete w
  rw [planeTensor_embed .standard j r (word i),standard_support_Q j r i h,map_zero]

theorem standard_complement (j r : Fin 4) (w : Word) :
    planeTensor .standard j r (complement w)=standardSign j*planeTensor .standard j r w := by
  obtain ⟨i,rfl⟩ := words_complete w
  rw [planeTensor_embed .standard j r (complement (word i)),
    planeTensor_embed .standard j r (word i),standard_complement_Q,map_mul]
  by_cases hj : standardMinus j <;> simp [standardSign,standardSignQ,hj]


end Holant.Certificates.EqualityQuaternary.Klein
