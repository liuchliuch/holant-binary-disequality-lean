import Holant.Certificates.OctahedralSeparator.PreparedInteger

namespace Holant.Certificates.OctahedralSeparator
open Holant

/-- The integer checker proves the same actual coordinate-action equality as
the direct rational reduction, with denominator factors kept explicit. -/
theorem prepared_exact_cached (j : Fin 48) :
    prepared j=Signature.coordinateAction (preparedLegs (rowForm j)) (cachedBase (rowBase j)) := by
  exact integer_action_certificate _ _ _ 4 4 (preparedIntegerLegs (rowForm j))
    (baseInteger (rowBase j)) (preparedInteger j) (by norm_num) (by norm_num)
    (preparedIntegerLegs_eval (rowForm j)) (baseInteger_eval (rowBase j))
    (preparedInteger_eval j) (preparedInteger_check j)

theorem prepared_exact (j : Fin 48) :
    prepared j=Signature.coordinateAction (preparedLegs (rowForm j)) (baseCard (rowBase j)) := by
  rw [prepared_exact_cached,base_exact]

theorem rows_complete : ∀ f : Form, ∀ r : Fin 15, admissible f r ↔ ∃ j : Fin 48, rowForm j=f ∧ rowBase j=r := by decide
theorem rows_distinct : Function.Injective (fun j : Fin 48 => (rowForm j,rowBase j)) := by decide
end Holant.Certificates.OctahedralSeparator
