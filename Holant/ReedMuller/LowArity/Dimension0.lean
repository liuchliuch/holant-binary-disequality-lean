import Holant.ReedMuller.LowArity.Basic

namespace Holant.ReedMuller.LowArity.Dimension0
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def rawPorts (_a : Fin 1) (p : Fin 0 × Fin 2) : Fin 0 := Fin.elim0 p.1
theorem rawPorts_bijective (a : Fin 1) : Function.Bijective (rawPorts a) := by
  fin_cases a <;> decide
noncomputable def model (a : Fin 1) : Matching 0 0 := Equiv.ofBijective (rawPorts a) (rawPorts_bijective a)

theorem model_orthogonal (a : Fin 1) :
    ∀ x y : BinaryVector 0, (model a).Holds x → (model a).Holds y → dot x y = 0 := by
  fin_cases a <;> decide

def proposal : Certificate (BinaryVector 0) (Fin 1) :=
  (.leaf 0)

theorem proposal_checked : check orth (fun a x => decide ((model a).Holds x))
    (Finset.univ.filter fun x => orth x x) proposal = true := by decide

theorem selfDual_matching (D : BinaryCode 0) (hD : SelfDual D) :
    ∃ a, ∀ x, x ∈ D ↔ (model a).Holds x :=
  selfDual_eq_matching model model_orthogonal proposal proposal_checked D hD

end Holant.ReedMuller.LowArity.Dimension0
